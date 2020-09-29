/*
 * FreeRTOS OTA V1.2.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file aws_iot_ota_mqtt.c
 * @brief Routines for supporting over the air updates using MQTT.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* OTA includes. */
#include "aws_iot_ota_agent.h"
#include "aws_iot_ota_agent_private.h"
#include "aws_iot_ota_cbor_private.h"

/* Include firmware version struct definition. */
#include "iot_appversion32.h"
extern const AppVersion32_t appFirmwareVersion;

/* General constants. */
#define OTA_SUBSCRIBE_WAIT_MS          30000UL
#define OTA_UNSUBSCRIBE_WAIT_MS        1000UL
#define OTA_PUBLISH_WAIT_MS            10000UL
#define OTA_SUBSCRIBE_WAIT_TICKS       pdMS_TO_TICKS( OTA_SUBSCRIBE_WAIT_MS )
#define OTA_UNSUBSCRIBE_WAIT_TICKS     pdMS_TO_TICKS( OTA_UNSUBSCRIBE_WAIT_MS )
#define OTA_PUBLISH_WAIT_TICKS         pdMS_TO_TICKS( OTA_SUBSCRIBE_WAIT_TICKS )
#define OTA_MAX_PUBLISH_RETRIES        3                    /* Max number of publish retries */
#define OTA_RETRY_DELAY_MS             1000UL               /* Delay between publish retries */
#define U32_MAX_PLACES                 10U                  /* Maximum number of output digits of an unsigned long value. */
#define OTA_MAX_TOPIC_LEN              256U                 /* Max length of a dynamically generated topic string (usually on the stack). */

/* Stream GET message constants. */
#define OTA_CLIENT_TOKEN               "rdy"                /* Arbitrary client token sent in the stream "GET" message. */

/* Agent to Job Service status message constants. */
#define OTA_STATUS_MSG_MAX_SIZE        128U             /* Max length of a job status message to the service. */
#define OTA_UPDATE_STATUS_FREQUENCY    64U              /* Update the job status every 64 unique blocks received. */

/*lint -e830 -e9003 Keep these in one location for easy discovery should they change in the future. */
/* Topic strings used by the OTA process. */
/* These first few are topic extensions to the dynamic base topic that includes the Thing name. */
static const char pcOTA_JobsGetNextAccepted_TopicTemplate[] = "$aws/things/%s/jobs/$next/get/accepted";
static const char pcOTA_JobsNotifyNext_TopicTemplate[] = "$aws/things/%s/jobs/notify-next";
static const char pcOTA_JobsGetNext_TopicTemplate[] = "$aws/things/%s/jobs/$next/get";
static const char pcOTA_JobStatus_TopicTemplate[] = "$aws/things/%s/jobs/%s/update";
static const char pcOTA_StreamData_TopicTemplate[] = "$aws/things/%s/streams/%s/data/cbor";
static const char pcOTA_GetStream_TopicTemplate[] = "$aws/things/%s/streams/%s/get/cbor";
static const char pcOTA_GetNextJob_MsgTemplate[] = "{\"clientToken\":\"%u:%s\"}";
static const char pcOTA_JobStatus_StatusTemplate[] = "{\"status\":\"%s\",\"statusDetails\":{";
static const char pcOTA_JobStatus_ReceiveDetailsTemplate[] = "\"%s\":\"%u/%u\"}}";
static const char pcOTA_JobStatus_SelfTestDetailsTemplate[] = "\"%s\":\"%s\",\"" OTA_JSON_UPDATED_BY_KEY "\":\"0x%x\"}}";
static const char pcOTA_JobStatus_ReasonStrTemplate[] = "\"reason\":\"%s: 0x%08x\"}}";
static const char pcOTA_JobStatus_SucceededStrTemplate[] = "\"reason\":\"%s v%u.%u.%u\"}}";
static const char pcOTA_JobStatus_ReasonValTemplate[] = "\"reason\":\"0x%08x: 0x%08x\"}}";
static const char pcOTA_String_Receive[] = "receive";

/* We map all of the above status cases to one of these 4 status strings.
 * These are the only strings that are supported by the Job Service. You
 * shall not change them to arbitrary strings or the job will not change
 * states.
 * */
const char pcOTA_String_InProgress[] = "IN_PROGRESS";
const char pcOTA_String_Failed[] = "FAILED";
const char pcOTA_String_Succeeded[] = "SUCCEEDED";
const char pcOTA_String_Rejected[] = "REJECTED";

const char * pcOTA_JobStatus_Strings[ NumJobStatusMappings ] =
{
    pcOTA_String_InProgress,
    pcOTA_String_Failed,
    pcOTA_String_Succeeded,
    pcOTA_String_Rejected,
    pcOTA_String_Failed, /* eJobStatus_FailedWithVal */
};

/* These are the associated statusDetails 'reason' codes that go along with
 * the above enums during the OTA update process. The 'Receiving' state is
 * updated with transfer progress as #blocks received of #total.
 */
const char * pcOTA_JobReason_Strings[ NumJobReasons ] = { "", "ready", "active", "accepted", "rejected", "aborted" };


/* Subscribe to the jobs notification topic (i.e. New file version available). */

static bool prvSubscribeToJobNotificationTopics( const OtaAgentContext_t * pxAgentCtx );

/* Subscribe to the OTA job notification topics. */

static bool prvSubscribeToJobNotificationTopics( const OtaAgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvSubscribeToJobNotificationTopics" );

    bool bResult = false;
    char pcJobTopic[ OTA_MAX_TOPIC_LEN ];
    uint16_t usTopicLen = 0;

    /* Build the first topic. */
    usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
                                        sizeof( pcJobTopic ),
                                        pcOTA_JobsGetNextAccepted_TopicTemplate,
                                        pxAgentCtx->pThingName );

    if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcJobTopic ) ) )
    {
        pxAgentCtx->pOTAMqttInterface->subscribe( pcJobTopic ,
                                                  usTopicLen, 
                                                  1,
                                                  pxAgentCtx->pOTAMqttInterface->jobCallback );

            OTA_LOG_L1( "[%s] OK: %s\n\r", OTA_METHOD_NAME, pcJobTopic );

            /* Build the second topic. */
            usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
                                                sizeof( pcJobTopic ),
                                                pcOTA_JobsNotifyNext_TopicTemplate,
                                                pxAgentCtx->pThingName );
    }
    else
    {
         OTA_LOG_L1( "[%s] Invalid Topic length: %d\n\r", OTA_METHOD_NAME, usTopicLen );
    }
    

    if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcJobTopic ) ) )
    {
        pxAgentCtx->pOTAMqttInterface->subscribe( pcJobTopic ,
                                                  usTopicLen, 
                                                  1,
                                                  pxAgentCtx->pOTAMqttInterface->jobCallback );

    }

    return true;
}

/*
 * Publish a message to the job status topic.
 */
static void prvPublishStatusMessage( OtaAgentContext_t * pxAgentCtx,
                                     OtaJobStatus_t eStatus,
                                     const char * pcMsg,
                                     uint32_t ulMsgSize,
                                     uint8_t ucQoS )
{
    DEFINE_OTA_METHOD_NAME( "prvPublishStatusMessage" );

    uint32_t ulTopicLen = 0;
    char pcTopicBuffer[ OTA_MAX_TOPIC_LEN ];
    int32_t ret;

    /* Try to build the dynamic job status topic . */
    ulTopicLen = ( uint32_t ) snprintf( pcTopicBuffer, /*lint -e586 Intentionally using snprintf. */
                                        sizeof( pcTopicBuffer ),
                                        pcOTA_JobStatus_TopicTemplate,
                                        pxAgentCtx->pThingName,
                                        pxAgentCtx->pOtaSingletonActiveJobName );

    /* If the topic name was built, try to publish the status message to it. */
    if( ( ulTopicLen > 0UL ) && ( ulTopicLen < sizeof( pcTopicBuffer ) ) )
    {
        OTA_LOG_L1( "[%s] Msg: %s\r\n", OTA_METHOD_NAME, pcMsg );
        ret = pxAgentCtx->pOTAMqttInterface->publish(
                                                    pcTopicBuffer,
                                                    ( uint16_t ) ulTopicLen,
                                                    &pcMsg[ 0 ],
                                                    ulMsgSize,
                                                    1 );

        if( ret != 0 )
        {
            OTA_LOG_L1( "[%s] Failed: %s\r\n", OTA_METHOD_NAME, pcTopicBuffer );
        }
        else
        {
            OTA_LOG_L1( "[%s] '%s' to %s\r\n", OTA_METHOD_NAME, pcOTA_JobStatus_Strings[ eStatus ], pcTopicBuffer );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Failed to build job status topic!\r\n", OTA_METHOD_NAME );
    }
}

static uint32_t prvBuildStatusMessageReceiving( char * pcMsgBuffer,
                                                size_t xMsgBufferSize,
                                                OtaJobStatus_t eStatus,
                                                OtaFileContext_t * pxOTAFileCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvBuildStatusMessageReceiving" );

    uint32_t ulNumBlocks = 0;
    uint32_t ulReceived = 0;
    uint32_t ulMsgSize = 0;

    if( pxOTAFileCtx != NULL )
    {
        ulNumBlocks = ( pxOTAFileCtx->fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
        ulReceived = ulNumBlocks - pxOTAFileCtx->blocksRemaining;

        if( ( ulReceived % OTA_UPDATE_STATUS_FREQUENCY ) == 0U ) /* Output a status update once in a while. */
        {
            ulMsgSize = ( uint32_t ) snprintf( pcMsgBuffer,      /*lint -e586 Intentionally using snprintf. */
                                               xMsgBufferSize,
                                               pcOTA_JobStatus_StatusTemplate,
                                               pcOTA_JobStatus_Strings[ eStatus ] );
            ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                                xMsgBufferSize - ulMsgSize,
                                                pcOTA_JobStatus_ReceiveDetailsTemplate,
                                                pcOTA_String_Receive,
                                                ulReceived,
                                                ulNumBlocks );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Error: null context pointer!\r\n", OTA_METHOD_NAME );
    }

    return ulMsgSize;
}

static uint32_t prvBuildStatusMessageSelfTest( char * pcMsgBuffer,
                                               size_t xMsgBufferSize,
                                               OtaJobStatus_t eStatus,
                                               int32_t lReason )
{
    uint32_t ulMsgSize = 0;

    ulMsgSize = ( uint32_t ) snprintf( pcMsgBuffer, /*lint -e586 Intentionally using snprintf. */
                                       xMsgBufferSize,
                                       pcOTA_JobStatus_StatusTemplate,
                                       pcOTA_JobStatus_Strings[ eStatus ] );
    ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                        xMsgBufferSize - ulMsgSize,
                                        pcOTA_JobStatus_SelfTestDetailsTemplate,
                                        OTA_JSON_SELF_TEST_KEY,
                                        pcOTA_JobReason_Strings[ lReason ],
                                        appFirmwareVersion.u.unsignedVersion32 );

    return ulMsgSize;
}

static uint32_t prvBuildStatusMessageFinish( char * pcMsgBuffer,
                                             size_t xMsgBufferSize,
                                             OtaJobStatus_t eStatus,
                                             int32_t lReason,
                                             int32_t lSubReason )
{
    uint32_t ulMsgSize = 0;

    ulMsgSize = ( uint32_t ) snprintf( pcMsgBuffer, /*lint -e586 Intentionally using snprintf. */
                                       xMsgBufferSize,
                                       pcOTA_JobStatus_StatusTemplate,
                                       pcOTA_JobStatus_Strings[ eStatus ] );

    /* FailedWithVal uses a numeric OTA error code and sub-reason code to cover the case where there
     * may be too many description strings to reasonably include in the code.
     */
    if( eStatus == JobStatusFailedWithVal )
    {
        ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                            xMsgBufferSize - ulMsgSize,
                                            pcOTA_JobStatus_ReasonValTemplate,
                                            lReason,
                                            lSubReason );
    }

    /* If the status update is for "Succeeded," we are identifying the version of firmware
     * that has been accepted. This makes it easy to find the version associated with each
     * device (aka Thing) when examining the OTA jobs on the service side via the CLI or
     * possibly with some console tool.
     */
    else if( eStatus == JobStatusSucceeded )
    {
        AppVersion32_t xNewVersion;

        xNewVersion.u.unsignedVersion32 = lSubReason;

        ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                            xMsgBufferSize - ulMsgSize,
                                            pcOTA_JobStatus_SucceededStrTemplate,
                                            pcOTA_JobReason_Strings[ lReason ],
                                            xNewVersion.u.x.ucMajor,
                                            xNewVersion.u.x.ucMinor,
                                            xNewVersion.u.x.usBuild );
    }

    /* Status updates that are NOT "InProgress" or "Succeeded" or "FailedWithVal" map status and
     * reason codes to a string plus a sub-reason code.
     */
    else
    {
        ulMsgSize += ( uint32_t ) snprintf( &pcMsgBuffer[ ulMsgSize ], /*lint -e586 Intentionally using snprintf. */
                                            xMsgBufferSize - ulMsgSize,
                                            pcOTA_JobStatus_ReasonStrTemplate,
                                            pcOTA_JobReason_Strings[ lReason ],
                                            lSubReason );
    }

    return ulMsgSize;
}

/*
 * Check for next available OTA job from the job service by publishing
 * a "get next job" message to the job service.
 */

OtaErr_t requestJob_Mqtt( OtaAgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvRequestJob_Mqtt" );

    char pcJobTopic[ OTA_MAX_TOPIC_LEN ];
    static uint32_t ulReqCounter = 0;
    int32_t ret;
    uint32_t ulMsgLen;
    uint16_t usTopicLen;
    OtaErr_t xError = OTA_ERR_PUBLISH_FAILED;

    /* The following buffer is big enough to hold a dynamically constructed $next/get job message.
     * It contains a client token that is used to track how many requests have been made. */
    char pcMsg[ CONST_STRLEN( pcOTA_GetNextJob_MsgTemplate ) + U32_MAX_PLACES + otaconfigMAX_THINGNAME_LEN ];

    /* Subscribe to the OTA job notification topic. */
    if( prvSubscribeToJobNotificationTopics( pxAgentCtx ) )
    {
        OTA_LOG_L1( "[%s] Request #%u\r\n", OTA_METHOD_NAME, ulReqCounter );
        /*lint -e586 Intentionally using snprintf. */
        ulMsgLen = ( uint32_t ) snprintf( pcMsg,
                                          sizeof( pcMsg ),
                                          pcOTA_GetNextJob_MsgTemplate,
                                          ulReqCounter,
                                          pxAgentCtx->pThingName );
        ulReqCounter++;
        usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
                                            sizeof( pcJobTopic ),
                                            pcOTA_JobsGetNext_TopicTemplate,
                                            pxAgentCtx->pThingName );

        if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcJobTopic ) ) )
        {
            ret = pxAgentCtx->pOTAMqttInterface->publish( pcJobTopic, usTopicLen, pcMsg, ulMsgLen, 1 );

            if( ret != 0 )
            {
                OTA_LOG_L1( "[%s] Failed to publish MQTT message.\r\n", OTA_METHOD_NAME );
                xError = OTA_ERR_PUBLISH_FAILED;
            }
            else
            {
                /* Nothing special to do. We succeeded. */
                xError = OTA_ERR_NONE;
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Topic too large for supplied buffer.\r\n", OTA_METHOD_NAME );
            xError = OTA_ERR_TOPIC_TOO_LARGE;
        }
    }

    return xError;
}


/*
 * Update the job status on the service side with progress or completion info.
 */
OtaErr_t updateJobStatus_Mqtt( OtaAgentContext_t * pxAgentCtx,
                                  OtaJobStatus_t eStatus,
                                  int32_t lReason,
                                  int32_t lSubReason )
{
    DEFINE_OTA_METHOD_NAME( "updateJobStatus_Mqtt" );

    /* A message size of zero means don't publish anything. */
    uint32_t ulMsgSize = 0;
    /* All job state transitions except streaming progress use QOS 1 since it is required to have status in the job document. */
    char pcMsg[ OTA_STATUS_MSG_MAX_SIZE ];
    uint8_t ucQoS = 1;

    /* Get the current file context. */
    OtaFileContext_t * C = &( pxAgentCtx->pOtaFiles[ pxAgentCtx->fileIndex ] );

    if( eStatus == JobStatusInProgress )
    {
        if( lReason == ( int32_t ) JobReasonReceiving )
        {
            ulMsgSize = prvBuildStatusMessageReceiving( pcMsg, sizeof( pcMsg ), eStatus, C );

            if( ulMsgSize > 0 )
            {
                /* Downgrade Progress updates to QOS 0 to avoid overloading MQTT buffers during active streaming. */
                ucQoS = 0;
            }
        }
        else
        {
            /* We're no longer receiving but we're still In Progress so we are implicitly in the Self
             * Test phase. Prepare to update the job status with the self_test phase (ready or active). */
            ulMsgSize = prvBuildStatusMessageSelfTest( pcMsg, sizeof( pcMsg ), eStatus, lReason );
        }
    }
    else
    {
        if( eStatus < NumJobStatusMappings )
        {
            ulMsgSize = prvBuildStatusMessageFinish( pcMsg, sizeof( pcMsg ), eStatus, lReason, lSubReason );
        }
        else
        {
            OTA_LOG_L1( "[%s] Unknown status code: %d\r\n", OTA_METHOD_NAME, eStatus );
        }
    }

    if( ulMsgSize > 0UL )
    {
        prvPublishStatusMessage( pxAgentCtx, eStatus, pcMsg, ulMsgSize, 0 );
    }

    return OTA_ERR_NONE;
}

/*
 * Init file transfer by subscribing to the OTA data stream topic.
 */
OtaErr_t initFileTransfer_Mqtt( OtaAgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvInitFileTransfer_Mqtt" );

    OtaErr_t xResult = OTA_ERR_PUBLISH_FAILED;

    char pcOTA_RxStreamTopic[ OTA_MAX_TOPIC_LEN ];
    uint16_t usTopicLen = 0;
    const OtaFileContext_t * pFileContext = &( pxAgentCtx->pOtaFiles[ pxAgentCtx->fileIndex ] );

    usTopicLen = ( uint16_t ) snprintf( pcOTA_RxStreamTopic,
                                        sizeof( pcOTA_RxStreamTopic ),
                                        pcOTA_StreamData_TopicTemplate,
                                        pxAgentCtx->pThingName,
                                        ( const char * ) pFileContext->pStreamName );

    if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcOTA_RxStreamTopic ) ) )
    {

    }

    return xResult;
}

/*
 * Request file block by publishing to the get stream topic.
 */
OtaErr_t requestFileBlock_Mqtt( OtaAgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvRequestFileBlock_Mqtt" );

    size_t xMsgSizeFromStream;
    uint32_t ulNumBlocks, ulBitmapLen;
    uint32_t ulMsgSizeToPublish = 0;
    uint32_t ulTopicLen = 0;
    OtaErr_t xErr = OTA_ERR_UNINITIALIZED;
    char pcMsg[ OTA_REQUEST_MSG_MAX_SIZE ];
    char pcTopicBuffer[ OTA_MAX_TOPIC_LEN ];
    int32_t ret;

    /*
     * Get the current file context.
     */
    OtaFileContext_t * C = &( pxAgentCtx->pOtaFiles[ pxAgentCtx->fileIndex ] );

    /* Reset number of blocks requested. */
    pxAgentCtx->numOfBlocksToReceive = otaconfigMAX_NUM_BLOCKS_REQUEST;

    if( C != NULL )
    {
        ulNumBlocks = ( C->fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
        ulBitmapLen = ( ulNumBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;

        if( OTA_CBOR_Encode_GetStreamRequestMessage(
                ( uint8_t * ) pcMsg,
                sizeof( pcMsg ),
                &xMsgSizeFromStream,
                OTA_CLIENT_TOKEN,
                ( int32_t ) C->serverFileID,
                ( int32_t ) ( OTA_FILE_BLOCK_SIZE & 0x7fffffffUL ), /* Mask to keep lint happy. It's still a constant. */
                0,
                C->pRxBlockBitmap,
                ulBitmapLen,
                otaconfigMAX_NUM_BLOCKS_REQUEST ) )
        {
            xErr = OTA_ERR_NONE;
        }
        else
        {
            OTA_LOG_L1( "[%s] CBOR encode failed.\r\n", OTA_METHOD_NAME );
            xErr = OTA_ERR_FAILED_TO_ENCODE_CBOR;
        }
    }

    if( xErr == OTA_ERR_NONE )
    {
        ulMsgSizeToPublish = ( uint32_t ) xMsgSizeFromStream;

        /* Try to build the dynamic data REQUEST topic to publish to. */
        ulTopicLen = ( uint32_t ) snprintf( pcTopicBuffer, /*lint -e586 Intentionally using snprintf. */
                                            sizeof( pcTopicBuffer ),
                                            pcOTA_GetStream_TopicTemplate,
                                            pxAgentCtx->pThingName,
                                            ( const char * ) C->pStreamName );

        if( ( ulTopicLen > 0U ) && ( ulTopicLen < sizeof( pcTopicBuffer ) ) )
        {
            xErr = OTA_ERR_NONE;
        }
        else
        {
            /* 0 should never happen since we supply the format strings. It must be overflow. */
            OTA_LOG_L1( "[%s] Failed to build stream topic!\r\n", OTA_METHOD_NAME );
            xErr = OTA_ERR_TOPIC_TOO_LARGE;
        }
    }

    if( xErr == OTA_ERR_NONE )
    {
        ret = pxAgentCtx->pOTAMqttInterface->publish( 
                                        pcTopicBuffer,
                                        ( uint16_t ) ulTopicLen,
                                        &pcMsg[ 0 ],
                                        ulMsgSizeToPublish,
                                        0 );

        if( ret != 0 )
        {
            OTA_LOG_L1( "[%s] Failed: %s\r\n", OTA_METHOD_NAME, pcTopicBuffer );
            xErr = OTA_ERR_PUBLISH_FAILED;
        }
        else
        {
            OTA_LOG_L1( "[%s] OK: %s\r\n", OTA_METHOD_NAME, pcTopicBuffer );
            xErr = OTA_ERR_NONE;
        }
    }

    return xErr;
}

/*
 * Decode a cbor encoded fileblock received from streaming service.
 */
OtaErr_t decodeFileBlock_Mqtt( uint8_t * pucMessageBuffer,
                                   size_t xMessageSize,
                                   int32_t * plFileId,
                                   int32_t * plBlockId,
                                   int32_t * plBlockSize,
                                   uint8_t ** ppucPayload,
                                   size_t * pxPayloadSize )
{
    DEFINE_OTA_METHOD_NAME( "prvDecodeFileBlock_Mqtt" );
    OtaErr_t xErr = OTA_ERR_UNINITIALIZED;

    /* Decode the CBOR content. */
    if( !OTA_CBOR_Decode_GetStreamResponseMessage(
            pucMessageBuffer,
            xMessageSize,
            plFileId,
            plBlockId,   /*lint !e9087 CBOR requires pointer to int and our block index's never exceed 31 bits. */
            plBlockSize, /*lint !e9087 CBOR requires pointer to int and our block sizes never exceed 31 bits. */
            ppucPayload, /* This payload gets malloc'd by OTA_CBOR_Decode_GetStreamResponseMessage(). We must free it. */
            pxPayloadSize ) )
    {
        xErr = OTA_ERR_GENERIC_INGEST_ERROR;
    }
    else
    {
        /* Decode the CBOR content. */
        memcpy( pucMessageBuffer, *ppucPayload, *pxPayloadSize );

        /* Free the payload as it is copied in data buffer. */
        free( *ppucPayload );   //ToDo
        *ppucPayload = pucMessageBuffer;

        xErr = OTA_ERR_NONE;
    }

    return xErr;
}

/*
 * Perform any cleanup operations required like unsubscribing from
 * job topics.
 */
OtaErr_t cleanup_Mqtt( OtaAgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvCleanup_Mqtt" );

    return OTA_ERR_NONE;
}