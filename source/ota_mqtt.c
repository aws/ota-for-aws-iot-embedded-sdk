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
 * @file ota_mqtt.c
 * @brief Routines for supporting over the air updates using MQTT.
 */

/* Standard includes. */
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

/* OTA includes. */
#include "ota.h"
#include "ota_private.h"
#include "ota_cbor_private.h"

/* Private include. */
#include "ota_mqtt_private.h"

/* Include firmware version struct definition. */
#include "ota_appversion32.h"

/* General constants. */
#define U32_MAX_PLACES                 10U                                      /*!< Maximum number of output digits of an unsigned long value. */
#define OTA_MAX_TOPIC_LEN              256U                                     /*!< Max length of a dynamically generated topic string (usually on the stack). */
#define MAX_TOPIC_TEMPLATE_LEN         100U                                     /*!< Max length of the topic templates. */

/* Stream GET message constants. */
#define OTA_CLIENT_TOKEN               "rdy"                /*!< Arbitrary client token sent in the stream "GET" message. */

/* Agent to Job Service status message constants. */
#define OTA_STATUS_MSG_MAX_SIZE        128U             /*!< Max length of a job status message to the service. */
#define OTA_UPDATE_STATUS_FREQUENCY    64U              /*!< Update the job status every 64 unique blocks received. */


/**
 *  @addtogroup ota_mqtt_topic_strings
 *  @brief Topic strings used by the OTA process.
 *
 * These first few are topic extensions to the dynamic base topic that includes the Thing name.
 * lint -e830 -e9003 Keep these in one location for easy discovery should they change in the future.
 *  @{
 */
static const char pOtaJobsGetNextAcceptedTopicTemplate[] = "$aws/things/%s/jobs/$next/get/accepted";                        /*!< Topic template for getting next job. */
static const char pOtaJobsNotifyNextTopicTemplate[] = "$aws/things/%s/jobs/notify-next";                                    /*!< Topic template to notify next . */
static const char pOtaJobsGetNextTopicTemplate[] = "$aws/things/%s/jobs/$next/get";                                         /*!< Topic template to request next job. */
static const char pOtaJobStatusTopicTemplate[] = "$aws/things/%s/jobs/%s/update";                                           /*!< Topic template to update the current job. */
static const char pOtaStreamDataTopicTemplate[] = "$aws/things/%s/streams/%s/data/cbor";                                    /*!< Topic template to receive data over a stream. */
static const char pOtaGetStreamTopicTemplate[] = "$aws/things/%s/streams/%s/get/cbor";                                      /*!< Topic template to request next data over a stream. */
static const char pOtaGetNextJobMsgTemplate[] = "{\"clientToken\":\"%u:%s\"}";                                              /*!< Used to specify client token id to authenticate job. */
static const char pOtaJobStatusStatusTemplate[] = "{\"status\":\"%s\",\"statusDetails\":{";                                 /*!< Used to specify the status of the current job. */
static const char pOtaJobStatusReceiveDetailsTemplate[] = "\"%s\":\"%u/%u\"}}";                                             /*!< Tail of the job receive status. */
static const char pOtaJobStatusSelfTestDetailsTemplate[] = "\"%s\":\"%s\",\"" OTA_JSON_UPDATED_BY_KEY_ONLY "\":\"0x%x\"}}"; /*!< Tail os self test job status. */
static const char pOtaJobStatusReasonStrTemplate[] = "\"reason\":\"%s: 0x%08x\"}}";                                         /*!< Tail template to report job failure string. */
static const char pOtaJobStatusSucceededStrTemplate[] = "\"reason\":\"%s v%u.%u.%u\"}}";                                    /*!< Tail template to report job succeeded. */
static const char pOtaJobStatusReasonValTemplate[] = "\"reason\":\"0x%08x: 0x%08x\"}}";                                     /*!< Tail template to report job failure error code. */
static const char pOtaStringReceive[] = "receive";                                                                          /*!< Used to build the job receive template. */
/** @}*/

#if ( ( otaconfigMAX_THINGNAME_LEN + MAX_TOPIC_TEMPLATE_LEN ) >= OTA_MAX_TOPIC_LEN )
    #error "otaconfigMAX_THINGNAME_LEN is too long: otaconfigMAX_THINGNAME_LEN + MAX_TOPIC_TEMPLATE_LEN must be < OTA_MAX_TOPIC_LEN."
#endif

#if OTA_STATUS_MSG_MAX_SIZE

#endif

/** We map all of the above status cases to one of these 4 status strings.
 * These are the only strings that are supported by the Job Service. You
 * shall not change them to arbitrary strings or the job will not change
 * states.
 * */
static const char pOtaStringInProgress[] = "IN_PROGRESS"; /*!< The job document has be received on the device and update is in progress. */
static const char pOtaStringFailed[] = "FAILED";          /*!< OTA update failed due to an error. */
static const char pOtaStringSucceeded[] = "SUCCEEDED";    /*!< OTA update succeeded. */
static const char pOtaStringRejected[] = "REJECTED";      /*!< The job was rejected due to invalid parameters. */

/**
 * @brief List of all the status cases a job can be in.
 *
 */
static const char * pOtaJobStatusStrings[ NumJobStatusMappings ] =
{
    pOtaStringInProgress,
    pOtaStringFailed,
    pOtaStringSucceeded,
    pOtaStringRejected,
    pOtaStringFailed, /* eJobStatus_FailedWithVal */
};

/**
 * @brief These are the associated statusDetails 'reason' codes that go along with
 * the above enums during the OTA update process. The 'Receiving' state is
 * updated with transfer progress as number of blocks received of total blocks.
 *
 */
static const char * pOtaJobReasonStrings[ NumJobReasons ] = { "", "ready", "active", "accepted", "rejected", "aborted" };

/**
 * @brief Subscribe to the jobs notification topic (i.e. New file version available).
 *
 * @param[in] pAgentCtx Agent context which stores the thing details and mqtt interface.
 * @return OtaErr_t Result of the subscribe operation, OTA_ERR_NONE if the operation is successful
 */
static OtaErr_t subscribeToJobNotificationTopics( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief UnSubscribe from the firmware update receive topic.
 *
 * @param[in] pAgentCtx Agent context which stores the thing details and mqtt interface.
 * @return OtaErr_t Result of the unsubscribe operation, OTA_ERR_NONE if the operation is successful.
 */
static OtaErr_t unsubscribeFromDataStream( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief UnSubscribe from the jobs notification topic.
 *
 * @param[in] pAgentCtx Agent context which stores the thing details and mqtt interface.
 * @return OtaErr_t Result of the unsubscribe operation, OTA_ERR_NONE if the operation is successful.
 */
static OtaErr_t unsubscribeFromJobNotificationTopic( const OtaAgentContext_t * pAgentCtx );

/**
 * @brief Publish a message to the job status topic.
 *
 * @param[in] pAgentCtx Agent context which provides the details for the thing, job and mqtt interface.
 * @param[in] pMsg Message to publish.
 * @param[in] status Status of the operation.
 * @param[in] msgSize Size of message to send.
 * @param[in] qos Quality of Service determines the expected response from the server
 * @return OtaErr_t OTA_ERR_NONE if the message is publish is successful.
 */
static OtaErr_t publishStatusMessage( OtaAgentContext_t * pAgentCtx,
                                      const char * pMsg,
                                      uint32_t msgSize );

/**
 * @brief Populate the message buffer with the job status message.
 *
 * @param[in] pMsgBuffer Buffer to populate.
 * @param[in] msgBufferSize Size of the message.
 * @param[in] status Status of the operation.
 * @param[in] pOTAFileCtx File context stores the information about the downloaded blocks and required size.
 * @return uint32_t Size of the message built.
 */
static uint32_t buildStatusMessageReceiving( char * pMsgBuffer,
                                             size_t msgBufferSize,
                                             OtaJobStatus_t status,
                                             const OtaFileContext_t * pOTAFileCtx );

/**
 * @brief Populate the message buffer with the message to indicate device in self-test.
 *
 * @param[in] pMsgBuffer Buffer to populate.
 * @param[in] msgBufferSize Size of the message.
 * @param[in] status Status of the operation.
 * @param[in] reason Reason for job failure (if any).
 * @return uint32_t Size of the message.
 */
static uint32_t prvBuildStatusMessageSelfTest( char * pMsgBuffer,
                                               size_t msgBufferSize,
                                               OtaJobStatus_t status,
                                               int32_t reason );

/**
 * @brief Populate the response message with the status of the job.
 *
 * @param[in] pMsgBuffer Buffer to populate.
 * @param[in] msgBufferSize Size of the message.
 * @param[in] status Status of the operation.
 * @param[in] reason Reason for failure or the new firmware version .
 * @param[in] subReason Error code due to which the operation failed.
 * @return uint32_t Size of the message.
 */
static uint32_t prvBuildStatusMessageFinish( char * pMsgBuffer,
                                             size_t msgBufferSize,
                                             OtaJobStatus_t status,
                                             int32_t reason,
                                             int32_t subReason );

/*
 * Subscribe to the OTA job notification topics.
 */
static OtaErr_t subscribeToJobNotificationTopics( const OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    uint16_t topicLen = 0;
    char pJobTopicGetNext[ OTA_MAX_TOPIC_LEN ];    /*!< Buffer to store the topic generated for requesting next topic. */
    char pJobTopicNotifyNext[ OTA_MAX_TOPIC_LEN ]; /*!< Buffer to store the topic generated for notifying next topic. */

    assert( pAgentCtx != NULL );

    /* Build and subscribe to the first topic. */
    topicLen = ( uint16_t ) snprintf( pJobTopicGetNext,
                                      sizeof( pJobTopicGetNext ),
                                      pOtaJobsGetNextAcceptedTopicTemplate,
                                      pAgentCtx->pThingName );

    /* Buffer size is validated during compile time. */
    assert( topicLen > 0U );

    result = pAgentCtx->pOtaInterface->mqtt.subscribe( pJobTopicGetNext,
                                                       topicLen,
                                                       1,
                                                       pAgentCtx->pOtaInterface->mqtt.jobCallback );

    if( result == OTA_ERR_NONE )
    {
        LogInfo( ( "Subscribed to MQTT topic: "
                   "%s",
                   pJobTopicGetNext ) );
    }
    else
    {
        LogError( ( "Failed to subscribe to MQTT topic: "
                    "subscribe returned error: "
                    "OtaErr_t=%u"
                    ", topic=%s",
                    result,
                    pJobTopicGetNext ) );
    }

    if( result == OTA_ERR_NONE )
    {
        /* Build and subscribe to the second topic. */
        topicLen = ( uint16_t ) snprintf( pJobTopicNotifyNext,
                                          sizeof( pJobTopicNotifyNext ),
                                          pOtaJobsNotifyNextTopicTemplate,
                                          pAgentCtx->pThingName );

        /* Buffer size is validated during compile time. */
        assert( topicLen > 0U );

        result = pAgentCtx->pOtaInterface->mqtt.subscribe( pJobTopicNotifyNext,
                                                           topicLen,
                                                           1,
                                                           pAgentCtx->pOtaInterface->mqtt.jobCallback );

        if( result == OTA_ERR_NONE )
        {
            LogInfo( ( "Subscribed to MQTT topic: %s", pJobTopicNotifyNext ) );
        }
        else
        {
            LogError( ( "Failed to subscribe to MQTT topic: "
                        "subscribe returned error: "
                        "OtaErr_t=%u"
                        ", topic=%s",
                        result,
                        pJobTopicNotifyNext ) );
        }
    }

    return result;
}

/*
 * UnSubscribe from the OTA data stream topic.
 */
static OtaErr_t unsubscribeFromDataStream( const OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;
    char pOtaRxStreamTopic[ OTA_MAX_TOPIC_LEN ];
    uint16_t topicLen = 0;
    const OtaFileContext_t * pFileContext = 0;

    assert( pAgentCtx != NULL );

    pFileContext = &( pAgentCtx->fileContext );

    /* Try to build the dynamic data stream topic and unsubscribe from it. */
    topicLen = ( uint16_t ) snprintf( pOtaRxStreamTopic, /*lint -e586 Intentionally using snprintf. */
                                      sizeof( pOtaRxStreamTopic ),
                                      pOtaStreamDataTopicTemplate,
                                      pAgentCtx->pThingName,
                                      ( const char * ) pFileContext->pStreamName );

    /* Buffer size is validated during compile time. */
    assert( topicLen > 0U );

    result = pAgentCtx->pOtaInterface->mqtt.unsubscribe( pOtaRxStreamTopic,
                                                         topicLen,
                                                         1 );

    if( result == OTA_ERR_NONE )
    {
        LogInfo( ( "Unsubscribed to MQTT topic: %s", pOtaRxStreamTopic ) );
    }
    else
    {
        LogError( ( "Failed to unsubscribe to MQTT topic: "
                    "unsubscribe returned error: "
                    "OtaErr_t=%u"
                    ", topic=%s",
                    result,
                    pOtaRxStreamTopic ) );
    }

    return result;
}

/*
 * Unsubscribe from the OTA job notification topics.
 */
static OtaErr_t unsubscribeFromJobNotificationTopic( const OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;
    char pJobTopic[ OTA_MAX_TOPIC_LEN ];
    uint16_t topicLen = 0;

    assert( pAgentCtx != NULL );

    /* Try to unsubscribe from the first of two job topics. */
    topicLen = ( uint16_t ) snprintf( pJobTopic, /*lint -e586 Intentionally using snprintf. */
                                      sizeof( pJobTopic ),
                                      pOtaJobsNotifyNextTopicTemplate,
                                      pAgentCtx->pThingName );

    /* Buffer size is validated during compile time. */
    assert( topicLen > 0U );

    result = pAgentCtx->pOtaInterface->mqtt.unsubscribe( pJobTopic,
                                                         topicLen,
                                                         0 );

    if( result == OTA_ERR_NONE )
    {
        LogInfo( ( "Unsubscribed to MQTT topic: %s", pJobTopic ) );
    }
    else
    {
        LogError( ( "Failed to unsubscribe to MQTT topic: "
                    "unsubscribe returned error: "
                    "OtaErr_t=%u"
                    ", topic=%s",
                    result,
                    pJobTopic ) );
    }

    if( result == OTA_ERR_NONE )
    {
        /* Try to unsubscribe from the second of two job topics. */
        topicLen = ( uint16_t ) snprintf( pJobTopic, /*lint -e586 Intentionally using snprintf. */
                                          sizeof( pJobTopic ),
                                          pOtaJobsGetNextAcceptedTopicTemplate,
                                          pAgentCtx->pThingName );

        /* Buffer size is validated during compile time. */
        assert( topicLen > 0U );

        result = pAgentCtx->pOtaInterface->mqtt.unsubscribe( pJobTopic,
                                                             topicLen,
                                                             0 );

        if( result == OTA_ERR_NONE )
        {
            LogInfo( ( "Unsubscribed to MQTT topic: %s", pJobTopic ) );
        }
        else
        {
            LogError( ( "Failed to unsubscribe to MQTT topic: "
                        "unsubscribe returned error: "
                        "OtaErr_t=%u"
                        ", topic=%s",
                        result,
                        pJobTopic ) );
        }
    }

    return result;
}

/*
 * Publish a message to the job status topic.
 */
static OtaErr_t publishStatusMessage( OtaAgentContext_t * pAgentCtx,
                                      const char * pMsg,
                                      uint32_t msgSize );
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;
    uint32_t topicLen = 0;
    char pTopicBuffer[ OTA_MAX_TOPIC_LEN ];

    assert( pAgentCtx != NULL );
    /* pMsg is a static buffer of size "OTA_STATUS_MSG_MAX_SIZE". */
    assert( pMsg != NULL );

    /* Build the dynamic job status topic . */
    topicLen = ( uint32_t ) snprintf( pTopicBuffer, /*lint -e586 Intentionally using snprintf. */
                                      sizeof( pTopicBuffer ),
                                      pOtaJobStatusTopicTemplate,
                                      pAgentCtx->pThingName,
                                      pAgentCtx->pOtaSingletonActiveJobName );

    /* Buffer size is validated during compile time. */
    assert( topicLen > 0U );

    /* Publish the status message. */
    LogDebug( ( "Attempting to publish MQTT status message: "
                "message=%s",
                pMsg ) );

    result = pAgentCtx->pOtaInterface->mqtt.publish( pTopicBuffer,
                                                     ( uint16_t ) topicLen,
                                                     &pMsg[ 0 ],
                                                     msgSize,
                                                     1 );

    if( result == OTA_ERR_NONE )
    {
        LogDebug( ( "Published to MQTT topic: "
                    "topic=%s",
                    pTopicBuffer ) );
    }
    else
    {
        LogError( ( "Failed to publish MQTT message: "
                    "publish returned error: "
                    "OtaErr_t=%u"
                    ", topic=%s",
                    result,
                    pTopicBuffer ) );
    }

    return result;
}

static uint32_t buildStatusMessageReceiving( char * pMsgBuffer,
                                             size_t msgBufferSize,
                                             OtaJobStatus_t status,
                                             const OtaFileContext_t * pOTAFileCtx )
{
    uint32_t numBlocks = 0;
    uint32_t received = 0;
    uint32_t msgSize = 0;

    assert( pMsgBuffer != NULL );
    /* This function is only called when a file is received, so it can't be NULL. */
    assert( pOTAFileCtx != NULL );


    numBlocks = ( pOTAFileCtx->fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
    received = numBlocks - pOTAFileCtx->blocksRemaining;

    if( ( received % OTA_UPDATE_STATUS_FREQUENCY ) == 0U ) /* Output a status update once in a while. */
    {
        msgSize = ( uint32_t ) snprintf( pMsgBuffer,       /*lint -e586 Intentionally using snprintf. */
                                         msgBufferSize,
                                         pOtaJobStatusStatusTemplate,
                                         pOtaJobStatusStrings[ status ] );
        /* Buffer size is validated during compile time. */
        assert( msgSize > 0U );

        msgSize += ( uint32_t ) snprintf( &pMsgBuffer[ msgSize ], /*lint -e586 Intentionally using snprintf. */
                                          msgBufferSize - msgSize,
                                          pOtaJobStatusReceiveDetailsTemplate,
                                          pOtaStringReceive,
                                          received,
                                          numBlocks );
        assert( msgSize > 0U );
    }

    return msgSize;
}

static uint32_t prvBuildStatusMessageSelfTest( char * pMsgBuffer,
                                               size_t msgBufferSize,
                                               OtaJobStatus_t status,
                                               int32_t reason )
{
    uint32_t msgSize = 0;
    uint32_t msgTailSize = 0;

    assert( pMsgBuffer != NULL );

    msgSize = ( uint32_t ) snprintf( pMsgBuffer, /*lint -e586 Intentionally using snprintf. */
                                     msgBufferSize,
                                     pOtaJobStatusStatusTemplate,
                                     pOtaJobStatusStrings[ status ] );
    /* Buffer size is validated during compile time. */
    assert( msgSize > 0U );

    msgTailSize = ( uint32_t ) snprintf( &pMsgBuffer[ msgSize ], /*lint -e586 Intentionally using snprintf. */
                                         msgBufferSize - msgSize,
                                         pOtaJobStatusSelfTestDetailsTemplate,
                                         OTA_JSON_SELF_TEST_KEY_ONLY,
                                         pOtaJobReasonStrings[ reason ],
                                         appFirmwareVersion.u.unsignedVersion32 );
    assert( msgTailSize > 0U );
    msgSize += msgTailSize;

    return msgSize;
}

static uint32_t prvBuildStatusMessageFinish( char * pMsgBuffer,
                                             size_t msgBufferSize,
                                             OtaJobStatus_t status,
                                             int32_t reason,
                                             int32_t subReason )
{
    uint32_t msgSize = 0;
    uint32_t msgTailSize = 0;

    assert( pMsgBuffer != NULL );

    msgSize = ( uint32_t ) snprintf( pMsgBuffer, /*lint -e586 Intentionally using snprintf. */
                                     msgBufferSize,
                                     pOtaJobStatusStatusTemplate,
                                     pOtaJobStatusStrings[ status ] );
    /* Buffer size is validated during compile time. */
    assert( msgSize > 0U );

    /* FailedWithVal uses a numeric OTA error code and sub-reason code to cover
     * the case where there may be too many description strings to reasonably
     * include in the code.
     */
    if( status == JobStatusFailedWithVal )
    {
        msgTailSize = ( uint32_t ) snprintf( &pMsgBuffer[ msgSize ], /*lint -e586 Intentionally using snprintf. */
                                             msgBufferSize - msgSize,
                                             pOtaJobStatusReasonValTemplate,
                                             reason,
                                             subReason );
        assert( msgTailSize > 0U );
        msgSize += msgTailSize;
    }

    /* If the status update is for "Succeeded," we are identifying the version
     * of firmware that has been accepted. This makes it easy to find the
     * version associated with each device (Thing) when examining the OTA jobs
     * on the service side via the CLI or possibly with some console tool.
     */
    else if( status == JobStatusSucceeded )
    {
        AppVersion32_t newVersion;

        newVersion.u.unsignedVersion32 = ( uint32_t ) subReason;

        msgTailSize = ( uint32_t ) snprintf( &pMsgBuffer[ msgSize ], /*lint -e586 Intentionally using snprintf. */
                                             msgBufferSize - msgSize,
                                             pOtaJobStatusSucceededStrTemplate,
                                             pOtaJobReasonStrings[ reason ],
                                             newVersion.u.x.major,
                                             newVersion.u.x.minor,
                                             newVersion.u.x.build );
        assert( msgTailSize > 0U );
        msgSize += msgTailSize;
    }

    /* Status updates that are NOT "InProgress" or "Succeeded" or "FailedWithVal" map status and
     * reason codes to a string plus a sub-reason code.
     */
    else
    {
        msgTailSize = ( uint32_t ) snprintf( &pMsgBuffer[ msgSize ], /*lint -e586 Intentionally using snprintf. */
                                             msgBufferSize - msgSize,
                                             pOtaJobStatusReasonStrTemplate,
                                             pOtaJobReasonStrings[ reason ],
                                             subReason );
        assert( msgTailSize > 0U );
        msgSize += msgTailSize;
    }

    return msgSize;
}

/*
 * Check for next available OTA job from the job service by publishing
 * a "get next job" message to the job service.
 */

OtaErr_t requestJob_Mqtt( OtaAgentContext_t * pAgentCtx )
{
    char pJobTopic[ OTA_MAX_TOPIC_LEN ];
    static uint32_t reqCounter = 0;
    OtaErr_t result = OTA_ERR_UNINITIALIZED;
    uint32_t msgSize;
    uint16_t topicLen;

    /* The following buffer is big enough to hold a dynamically constructed $next/get job message.
     * It contains a client token that is used to track how many requests have been made. */
    char pMsg[ CONST_STRLEN( pOtaGetNextJobMsgTemplate ) + U32_MAX_PLACES + otaconfigMAX_THINGNAME_LEN ];

    assert( pAgentCtx != NULL );

    /* Subscribe to the OTA job notification topic. */
    result = subscribeToJobNotificationTopics( pAgentCtx );

    if( result == OTA_ERR_NONE )
    {
        LogDebug( ( "MQTT job request number: counter=%u", reqCounter ) );
        /*lint -e586 Intentionally using snprintf. */
        msgSize = ( uint32_t ) snprintf( pMsg,
                                         sizeof( pMsg ),
                                         pOtaGetNextJobMsgTemplate,
                                         reqCounter,
                                         pAgentCtx->pThingName );
        assert( msgSize > 0U );

        reqCounter++;
        topicLen = ( uint16_t ) snprintf( pJobTopic,
                                          sizeof( pJobTopic ),
                                          pOtaJobsGetNextTopicTemplate,
                                          pAgentCtx->pThingName );

        /* Buffer size is validated during compile time. */
        assert( topicLen > 0U );

        result = pAgentCtx->pOtaInterface->mqtt.publish( pJobTopic, topicLen, pMsg, msgSize, 1 );

        if( result == OTA_ERR_NONE )
        {
            LogDebug( ( "Published MQTT request to get the next job: "
                        "topic=%s",
                        pJobTopic ) );
        }
        else
        {
            LogError( ( "Failed to publish MQTT message:"
                        "publish returned error: "
                        "OtaErr_t=%u",
                        result ) );
            result = OTA_ERR_PUBLISH_FAILED;
        }
    }

    return result;
}


/*
 * Update the job status on the service side with progress or completion info.
 */
OtaErr_t updateJobStatus_Mqtt( OtaAgentContext_t * pAgentCtx,
                               OtaJobStatus_t status,
                               int32_t reason,
                               int32_t subReason )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;
    /* A message size of zero means don't publish anything. */
    uint32_t msgSize = 0;
    /* All job state transitions except streaming progress use QOS 1 since it is required to have status in the job document. */
    char pMsg[ OTA_STATUS_MSG_MAX_SIZE ];
    uint8_t qos = 1;
    const OtaFileContext_t * pFileContext = 0;

    assert( pAgentCtx != NULL );

    /* Get the current file context. */
    pFileContext = &( pAgentCtx->fileContext );

    if( status == JobStatusInProgress )
    {
        if( reason == ( int32_t ) JobReasonReceiving )
        {
            msgSize = buildStatusMessageReceiving( pMsg, sizeof( pMsg ), status, pFileContext );

            /* Downgrade Progress updates to QOS 0 to avoid overloading MQTT buffers during active streaming. */
            qos = 0;
        }
        else
        {
            /* We're no longer receiving but we're still In Progress so we are implicitly in the Self
             * Test phase. Prepare to update the job status with the self_test phase (ready or active). */
            msgSize = prvBuildStatusMessageSelfTest( pMsg, sizeof( pMsg ), status, reason );
        }
    }
    else
    {
        /* The potential values for status are constant at compile time. */
        assert( status < NumJobStatusMappings );
        msgSize = prvBuildStatusMessageFinish( pMsg, sizeof( pMsg ), status, reason, subReason );
    }

    result = publishStatusMessage( pAgentCtx, pMsg, msgSize );

    if( result == OTA_ERR_NONE )
    {
        LogDebug( ( "Published update to the job status." ) );
    }
    else
    {
        LogError( ( "Failed to publish MQTT status message: "
                    "publishStatusMessage returned error: "
                    "OtaErr_t=%u",
                    result ) );
    }

    return result;
}

/*
 * Init file transfer by subscribing to the OTA data stream topic.
 */
OtaErr_t initFileTransfer_Mqtt( OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OTA_ERR_PUBLISH_FAILED;

    char pRxStreamTopic[ OTA_MAX_TOPIC_LEN ]; /*!< Buffer to store the topic generated for requesting data stream. */
    uint16_t topicLen = 0;
    const OtaFileContext_t * pFileContext = 0;

    assert( pAgentCtx != NULL );

    pFileContext = &( pAgentCtx->fileContext );

    topicLen = ( uint16_t ) snprintf( pRxStreamTopic,
                                      sizeof( pRxStreamTopic ),
                                      pOtaStreamDataTopicTemplate,
                                      pAgentCtx->pThingName,
                                      ( const char * ) pFileContext->pStreamName );

    /* Buffer size is validated during compile time. */
    assert( topicLen > 0U );

    result = pAgentCtx->pOtaInterface->mqtt.subscribe( pRxStreamTopic,
                                                       topicLen,
                                                       0,
                                                       pAgentCtx->pOtaInterface->mqtt.dataCallback );

    if( result == OTA_ERR_NONE )
    {
        LogDebug( ( "Subscribed to the OTA data stream topic: "
                    "topic=%s",
                    pRxStreamTopic ) );
    }
    else
    {
        LogError( ( "Failed to subscribe to MQTT topic: "
                    "subscribe returned error: "
                    "OtaErr_t=%u"
                    ", topic=%s",
                    result,
                    pRxStreamTopic ) );
    }

    return result;
}

/*
 * Request file block by publishing to the get stream topic.
 */
OtaErr_t requestFileBlock_Mqtt( OtaAgentContext_t * pAgentCtx )
{
    size_t msgSizeFromStream = 0;
    uint32_t numBlocks = 0;
    uint32_t bitmapLen = 0;
    uint32_t msgSizeToPublish = 0;
    uint32_t topicLen = 0;
    char pMsg[ OTA_REQUEST_MSG_MAX_SIZE ];
    char pTopicBuffer[ OTA_MAX_TOPIC_LEN ];
    OtaErr_t result = OTA_ERR_UNINITIALIZED;
    const OtaFileContext_t * pFileContext = 0;

    assert( pAgentCtx != NULL );

    /* Get the current file context. */
    pFileContext = &( pAgentCtx->fileContext );

    /* Reset number of blocks requested. */
    pAgentCtx->numOfBlocksToReceive = otaconfigMAX_NUM_BLOCKS_REQUEST;

    uint32_t blockSize = OTA_FILE_BLOCK_SIZE & 0x7fffffffU;
    numBlocks = ( pFileContext->fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
    bitmapLen = ( numBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;

    result = OTA_CBOR_Encode_GetStreamRequestMessage( ( uint8_t * ) pMsg,
                                                      sizeof( pMsg ),
                                                      &msgSizeFromStream,
                                                      OTA_CLIENT_TOKEN,
                                                      ( int32_t ) pFileContext->serverFileID,
                                                      ( int32_t ) blockSize,
                                                      0,
                                                      pFileContext->pRxBlockBitmap,
                                                      bitmapLen,
                                                      ( int32_t ) otaconfigMAX_NUM_BLOCKS_REQUEST );

    if( result == OTA_ERR_NONE )
    {
        msgSizeToPublish = ( uint32_t ) msgSizeFromStream;

        /* Try to build the dynamic data REQUEST topic to publish to. */
        topicLen = ( uint32_t ) snprintf( pTopicBuffer, /*lint -e586 Intentionally using snprintf. */
                                          sizeof( pTopicBuffer ),
                                          pOtaGetStreamTopicTemplate,
                                          pAgentCtx->pThingName,
                                          ( const char * ) pFileContext->pStreamName );

        /* Buffer size is validated during compile time. */
        assert( topicLen > 0U );

        result = pAgentCtx->pOtaInterface->mqtt.publish( pTopicBuffer,
                                                         ( uint16_t ) topicLen,
                                                         &pMsg[ 0 ],
                                                         msgSizeToPublish,
                                                         0 );

        if( result == OTA_ERR_NONE )
        {
            LogInfo( ( "Published to MQTT topic to request the next block: "
                       "topic=%s",
                       pTopicBuffer ) );
        }
        else
        {
            LogError( ( "Failed to publish MQTT message: "
                        "publish returned error: "
                        "OtaErr_t=%u",
                        result ) );
        }
    }

    return result;
}

/*
 * Decode a cbor encoded fileblock received from streaming service.
 */
OtaErr_t decodeFileBlock_Mqtt( uint8_t * pMessageBuffer,
                               size_t messageSize,
                               int32_t * pFileId,
                               int32_t * pBlockId,
                               int32_t * pBlockSize,
                               uint8_t ** pPayload,
                               size_t * pPayloadSize )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    /* Decode the CBOR content. */
    result = OTA_CBOR_Decode_GetStreamResponseMessage( pMessageBuffer,
                                                       messageSize,
                                                       pFileId,
                                                       pBlockId,   /*lint !e9087 CBOR requires pointer to int and our block index's never exceed 31 bits. */
                                                       pBlockSize, /*lint !e9087 CBOR requires pointer to int and our block sizes never exceed 31 bits. */
                                                       pPayload,   /* This payload gets malloc'd by OTA_CBOR_Decode_GetStreamResponseMessage(). We must free it. */
                                                       pPayloadSize );

    if( ( result == OTA_ERR_NONE ) && ( pPayload != NULL ) )
    {
        /* pPayloadSize is statically allocated by the caller. */
        assert( pPayloadSize != NULL );

        /* Decode the CBOR content. */
        memcpy( pMessageBuffer, *pPayload, *pPayloadSize );

        /* Free the payload as it is copied in data buffer. */
        free( *pPayload ); /*ToDo */
        *pPayload = pMessageBuffer;
    }
    else
    {
        LogError( ( "Failed to decode MQTT file block: "
                    "OTA_CBOR_Decode_GetStreamResponseMessage returned error: "
                    "OtaErr_t=%d",
                    result ) );
    }

    return result;
}

/*
 * Perform any cleanup operations required for control plane.
 */
OtaErr_t cleanupControl_Mqtt( const OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    assert( pAgentCtx != NULL );

    /* Unsubscribe from job notification topics. */
    result = unsubscribeFromJobNotificationTopic( pAgentCtx );

    if( result != OTA_ERR_NONE )
    {
        LogWarn( ( "Failed cleanup for MQTT control plane: "
                   "unsubscribeFromJobNotificationTopic returned error: "
                   "OtaErr_t=%u",
                   result ) );
    }

    return result;
}

/*
 * Perform any cleanup operations required for data plane.
 */
OtaErr_t cleanupData_Mqtt( const OtaAgentContext_t * pAgentCtx )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    assert( pAgentCtx != NULL );

    /* Unsubscribe from data stream topics. */
    result = unsubscribeFromDataStream( pAgentCtx );

    if( result != OTA_ERR_NONE )
    {
        LogWarn( ( "Failed cleanup for MQTT data plane: "
                   "unsubscribeFromDataStream returned error: "
                   "OtaErr_t=%u",
                   result ) );
    }

    return result;
}
