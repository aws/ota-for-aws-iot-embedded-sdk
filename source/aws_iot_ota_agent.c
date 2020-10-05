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

/* Standard library includes. */
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

/* OTA agent includes. */
#include "aws_iot_ota_agent.h"
#include "aws_ota_agent_config.h"

/* OTA Base64 includes */
#include "aws_ota_base64_private.h"

/* OTA pal includes. */
#include "aws_iot_ota_pal.h"

/* Internal header file for shared OTA definitions. */
#include "aws_iot_ota_agent_private.h"

/* OTA interface includes. */
#include "aws_iot_ota_interface_private.h"
#include "ota_os_posix.h"
#include "ota_os_interface.h"

/* Include firmware version struct definition. */
#include "iot_appversion32.h"
extern const AppVersion32_t appFirmwareVersion;

/* ToDo: Cleanup BaseType_t. */
#define BaseType_t    uint32_t

/* OTA event handler definiton. */

typedef OtaErr_t ( * OtaEventHandler_t )( OtaEventData_t * pEventMsg );

/* OTA Agent state table entry. */

typedef struct OtaStateTableEntry
{
    OtaState_t currentState;
    OtaEvent_t eventId;
    OtaEventHandler_t handler;
    OtaState_t nextState;
} OtaStateTableEntry_t;

/*
 * This union allows us to access document model parameter addresses as their
 * actual type without casting every time we access a parameter.
 */

typedef union MultiParmPtr
{
    const char ** pConstCharPtr;
    uint64_t * pIntPtr;
    uint64_t intVal;
    bool * pBoolPtr;
    Sig256_t ** pSig256Ptr;
    void ** pVoidPtr;
} MultiParmPtr_t;

/* Buffers used to push event data. */

static OtaEventData_t pEventBuffer[ otaconfigMAX_NUM_OTA_DATA_BUFFERS ];

/* OTA control interface. */

static OtaControlInterface_t otaControlInterface;

/* OTA data interface. */

static OtaDataInterface_t otaDataInterface;

/* OTA agent private function prototypes. */


/* Start a timer used for sending data requests. */

static void startRequestTimer( uint32_t periodMS );

/* Stop the data request timer. */

static void stopRequestTimer( void );

/* Data request timer callback. */

static void requestTimerCallback( /*TimerHandle_t T*/ void * pParam );

/* Start the self test timer if in self-test mode. */

static BaseType_t startSelfTestTimer( void );

/* Stop the OTA self test timer if it is running. */

static void stopSelfTestTimer( void );

/* Self-test timer callback, reset the device if this timer expires. */

static void selfTestTimerCallback( /*TimerHandle_t T*/ void * pParam );

/* Called when the OTA agent receives a file data block message. */

static IngestResult_t ingestDataBlock( OtaFileContext_t * pFileContext,
                                       uint8_t * pRawMsg,
                                       uint32_t messageSize,
                                       OtaErr_t * pCloseResult );

/* Called to update the filecontext structure from the job. */

static OtaFileContext_t * getFileContextFromJob( const char * pRawMsg,
                                                 uint32_t messageLength );

/* Get an available OTA file context structure or NULL if none available. */

static OtaFileContext_t * getFreeContext( void );

/* Validate JSON document */

static DocParseErr_t validateJSON( const char * pJson,
                                   uint32_t messageLength );

/* Checks for duplicate entries in the JSON document */

static DocParseErr_t checkDuplicates(   uint32_t * paramsReceivedBitmap, 
                                        uint16_t paramIndex);

/* Store the parameter from the json to the offset specified by the document model*/

static DocParseErr_t extractParameter( JsonDocParam_t docParam,
                                       uint64_t modelContextBase,
                                       uint64_t modelContextSize,
                                       char * pValueInJson,
                                       size_t valueLength );

/* Parse a JSON document using the specified document model. */

static DocParseErr_t parseJSONbyModel( const char * pJson,
                                       uint32_t messageLength,
                                       JsonDocModel_t * pDocModel );

/* Parse the OTA job document, validate and return the populated OTA context if valid. */

static OtaFileContext_t * parseJobDoc( const char * pJson,
                                       uint32_t messageLength,
                                       bool * pUpdateJob );

/* Close an open OTA file context and free it. */

static bool otaClose( OtaFileContext_t * const pFileContext );


/* Internal function to set the image state including an optional reason code. */

static OtaErr_t setImageStateWithReason( OtaImageState_t state,
                                         uint32_t reason );

/* The default OTA callback handler if not provided to OTA_AgentInit(). */

static void defaultOTACompleteCallback( OtaJobEvent_t event );

/* Default Custom Callback handler if not provided to OTA_AgentInit() */

static OtaJobParseErr_t defaultCustomJobCallback( const char * pJson,
                                                  uint32_t messageLength );

/* Default Reset Device handler if not provided to OTA_AgentInit() */

static OtaErr_t palDefaultResetDevice( uint32_t serverFileID );

/* Default Get Platform Image State handler if not provided to OTA_AgentInit() */

static OtaPalImageState_t palDefaultGetPlatformImageState( uint32_t serverFileID );

/* Default Set Platform Image State handler if not provided to OTA_AgentInit() */

static OtaErr_t palDefaultSetPlatformImageState( uint32_t serverFileID,
                                                 OtaImageState_t state );

/* Default Activate New Image handler if not provided to OTA_AgentInit() */

static OtaErr_t palDefaultActivateNewImage( uint32_t serverFileID );

/* A helper function to cleanup resources during OTA agent shutdown. */

static void agentShutdownCleanup( void );

/*
 * Prepare the document model for use by sanity checking the initialization parameters
 * and detecting all required parameters.
 */

static DocParseErr_t initDocModel( JsonDocModel_t * pDocModel,
                                   const JsonDocParam_t * pBodyDef,
                                   uint64_t contextBaseAddr,
                                   uint32_t contextSize,
                                   uint16_t numJobParams );

/* Attempt to force reset the device. Normally called by the agent when a self test rejects the update. */

static OtaErr_t resetDevice( void );

/* Check if the platform is in self-test. */

static bool inSelftest( void );

/* Function to handle events that were unexpected in the current state. */

static void handleUnexpectedEvents( OtaEventMsg_t * pEventMsg );

/* OTA state event handler functions. */

static OtaErr_t startHandler( OtaEventData_t * pEventData );
static OtaErr_t requestJobHandler( OtaEventData_t * pEventData );
static OtaErr_t processJobHandler( OtaEventData_t * pEventData );
static OtaErr_t inSelfTestHandler( OtaEventData_t * pEventData );
static OtaErr_t initFileHandler( OtaEventData_t * pEventData );
static OtaErr_t processDataHandler( OtaEventData_t * pEventData );
static OtaErr_t requestDataHandler( OtaEventData_t * pEventData );
static OtaErr_t shutdownHandler( OtaEventData_t * pEventData );
static OtaErr_t closeFileHandler( OtaEventData_t * pEventData );
static OtaErr_t userAbortHandler( OtaEventData_t * pEventData );
static OtaErr_t suspendHandler( OtaEventData_t * pEventData );
static OtaErr_t resumeHandler( OtaEventData_t * pEventData );
static OtaErr_t jobNotificationHandler( OtaEventData_t * pEventData );

/* OTA default callback initializer. */

#define OTA_JOB_CALLBACK_DEFAULT_INITIALIZER                      \
    {                                                             \
        .abort = prvPAL_Abort,                                    \
        .activateNewImage = palDefaultActivateNewImage,           \
        .closeFile = prvPAL_CloseFile,                            \
        .createFileForRx = prvPAL_CreateFileForRx,                \
        .getPlatformImageState = palDefaultGetPlatformImageState, \
        .resetDevice = palDefaultResetDevice,                     \
        .setPlatformImageState = palDefaultSetPlatformImageState, \
        .writeBlock = prvPAL_WriteBlock,                          \
        .completeCallback = defaultOTACompleteCallback,           \
        .customJobCallback = defaultCustomJobCallback             \
    }

/* This is THE OTA agent context and initialization state. */

static OtaAgentContext_t otaAgent =
{
    .state                      = OtaAgentStateStopped,
    .pThingName                 = { 0 },
    .pConnectionContext         = NULL,
    .pOtaFiles                  = { { 0 } },  /*lint !e910 !e9080 Zero initialization of all members of the single file context structure.*/
    .serverFileID               = 0,
    .pOtaSingletonActiveJobName = NULL,
    .pClientTokenFromJob        = NULL,
    .timestampFromJob           = 0,
    .imageState                 = OtaImageStateUnknown,
    .palCallbacks               = OTA_JOB_CALLBACK_DEFAULT_INITIALIZER,
    .numOfBlocksToReceive       = 1,
    .statistics                 = { 0 },
    .requestMomentum            = 0
};

static OtaStateTableEntry_t otaTransitionTable[] =
{
    /*STATE ,                              EVENT ,                               ACTION ,               NEXT STATE                         */
    { OtaAgentStateReady,               OtaAgentEventStart,               startHandler,           OtaAgentStateRequestingJob       },
    { OtaAgentStateRequestingJob,       OtaAgentEventRequestJobDocument,  requestJobHandler,      OtaAgentStateWaitingForJob       },
    { OtaAgentStateRequestingJob,       OtaAgentEventRequestTimer,        requestJobHandler,      OtaAgentStateWaitingForJob       },
    { OtaAgentStateWaitingForJob,       OtaAgentEventReceivedJobDocument, processJobHandler,      OtaAgentStateCreatingFile        },
    { OtaAgentStateCreatingFile,        OtaAgentEventStartSelfTest,       inSelfTestHandler,      OtaAgentStateWaitingForJob       },
    { OtaAgentStateCreatingFile,        OtaAgentEventCreateFile,          initFileHandler,        OtaAgentStateRequestingFileBlock },
    { OtaAgentStateCreatingFile,        OtaAgentEventRequestTimer,        initFileHandler,        OtaAgentStateRequestingFileBlock },
    { OtaAgentStateRequestingFileBlock, OtaAgentEventRequestFileBlock,    requestDataHandler,     OtaAgentStateWaitingForFileBlock },
    { OtaAgentStateRequestingFileBlock, OtaAgentEventRequestTimer,        requestDataHandler,     OtaAgentStateWaitingForFileBlock },
    { OtaAgentStateWaitingForFileBlock, OtaAgentEventReceivedFileBlock,   processDataHandler,     OtaAgentStateWaitingForFileBlock },
    { OtaAgentStateWaitingForFileBlock, OtaAgentEventRequestTimer,        requestDataHandler,     OtaAgentStateWaitingForFileBlock },
    { OtaAgentStateWaitingForFileBlock, OtaAgentEventRequestFileBlock,    requestDataHandler,     OtaAgentStateWaitingForFileBlock },
    { OtaAgentStateWaitingForFileBlock, OtaAgentEventRequestJobDocument,  requestJobHandler,      OtaAgentStateWaitingForJob       },
    { OtaAgentStateWaitingForFileBlock, OtaAgentEventReceivedJobDocument, jobNotificationHandler, OtaAgentStateRequestingJob       },
    { OtaAgentStateWaitingForFileBlock, OtaAgentEventCloseFile,           closeFileHandler,       OtaAgentStateWaitingForJob       },
    { OtaAgentStateSuspended,           OtaAgentEventResume,              resumeHandler,          OtaAgentStateRequestingJob       },
    { OtaAgentStateAll,                 OtaAgentEventSuspend,             suspendHandler,         OtaAgentStateSuspended           },
    { OtaAgentStateAll,                 OtaAgentEventUserAbort,           userAbortHandler,       OtaAgentStateWaitingForJob       },
    { OtaAgentStateAll,                 OtaAgentEventShutdown,            shutdownHandler,        OtaAgentStateShuttingDown        },
};

static const char * pOtaAgentStateStrings[ OtaAgentStateAll ] =
{
    "Init",
    "Ready",
    "RequestingJob",
    "WaitingForJob",
    "CreatingFile",
    "RequestingFileBlock",
    "WaitingForFileBlock",
    "ClosingFile",
    "Suspended",
    "ShuttingDown",
    "Stopped"
};

static const char * pOtaEventStrings[ OtaAgentEventMax ] =
{
    "Start",
    "StartSelfTest",
    "RequestJobDocument",
    "ReceivedJobDocument",
    "CreateFile",
    "RequestFileBlock",
    "ReceivedFileBlock",
    "RequestTimer",
    "CloseFile",
    "Suspend",
    "Resume",
    "UserAbort",
    "Shutdown"
};

/*
 * This is a private function which checks if the platform is in self-test.
 */
static bool inSelftest( void )
{
    bool selfTest = false;

    /*
     * Get the platform state from the OTA pal layer.
     */
    if( otaAgent.palCallbacks.getPlatformImageState( otaAgent.serverFileID ) == OtaPalImageStatePendingCommit )
    {
        selfTest = true;
    }

    return selfTest;
}

/*
 * If we're in self test mode, start the self test timer. The latest job should
 * also be in the self test state. We must complete the self test and either
 * accept or reject the image before the timer expires or we shall reset the
 * device to initiate a roll back of the MCU firmware bundle. This will catch
 * issues like improper credentials or a device that is connected to a non-
 * production stage of the job service resulting in a different job queue being
 * used.
 */
static BaseType_t startSelfTestTimer( void )
{
    // DEFINE_OTA_METHOD_NAME( "startSelfTestTimer" );

    // static const char pcTimerName[] = "OTA_SelfTest";
    // int32_t xTimerStarted = 0;

    //return xTimerStarted;
}

/* When the self test response timer expires, reset the device since we're likely broken. */

static void selfTestTimerCallback( /*TimerHandle_t T*/ void * pParam )
{
    DEFINE_OTA_METHOD_NAME( "selfTestTimerCallback" );

    OTA_LOG_L1( "[%s] Self test failed to complete within %ums\r\n", OTA_METHOD_NAME, otaconfigSELF_TEST_RESPONSE_WAIT_MS );
   // ( void ) otaAgent.palCallbacks.resetDevice( otaAgent.serverFileID );
}

/* Stop the OTA self test timer if it is running. */

static void stopSelfTestTimer( void )
{
    DEFINE_OTA_METHOD_NAME( "stopSelfTestTimer" );

   // otaAgent.pOTAOSCtx->timer.stop(otaAgent.pOTAOSCtx->timer.PTimerCtx[0]);
}

static OtaErr_t updateJobStatusFromImageState( OtaImageState_t state,
                                               int32_t subReason )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    int32_t reason = 0;

    if( state == OtaImageStateTesting )
    {
        /* We discovered we're ready for test mode, put job status in self_test active. */
        err = otaControlInterface.updateJobStatus( &otaAgent, JobStatusInProgress, JobReasonSelfTestActive, 0 );
    }
    else
    {
        if( state == OtaImageStateAccepted )
        {
            /* Now that we've accepted the firmware update, we can complete the job. */
            stopSelfTestTimer();
            err = otaControlInterface.updateJobStatus( &otaAgent, JobStatusSucceeded, JobReasonAccepted, appFirmwareVersion.u.signedVersion32 );
        }
        else
        {
            /*
             * The firmware update was either rejected or aborted, complete the job as FAILED (Job service
             * doesn't allow us to set REJECTED after the job has been started already).
             */
            reason = ( state == OtaImageStateRejected ) ? JobReasonRejected : JobReasonAborted;
            err = otaControlInterface.updateJobStatus( &otaAgent, JobStatusFailed, reason, subReason );
        }

        /*
         * We don't need the job name memory anymore since we're done with this job.
         */
        free( otaAgent.pOtaSingletonActiveJobName );
        otaAgent.pOtaSingletonActiveJobName = NULL;
    }

    return err;
}

static OtaErr_t setImageStateWithReason( OtaImageState_t state,
                                         uint32_t reason )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    //configASSERT( ( state > OtaImageStateUnknown ) && ( state <= OtaLastImageState ) );

    /* Call the platform specific code to set the image state. */
    err = otaAgent.palCallbacks.setPlatformImageState( otaAgent.serverFileID, state );

    /*
     * If the platform image state couldn't be set correctly, force fail the update by setting the
     * image state to "Rejected" unless it's already in "Aborted".
     */
    if( ( err != OTA_ERR_NONE ) && ( state != OtaImageStateAborted ) )
    {
        state = OtaImageStateRejected; /*lint !e9044 intentionally override state since we failed within this function. */

        /*
         * Capture the failure reason if not already set (and we're not already Aborted as checked above). Otherwise Keep
         * the original reject reason code since it is possible for the PAL to fail to update the image state in some
         * cases (e.g. a reset already caused the bundle rollback and we failed to rollback again).
         */
        if( reason == OTA_ERR_NONE )
        {
            reason = err; /*lint !e9044 intentionally override reason since we failed within this function. */
        }
    }

    /* Now update the image state and job status on service side. */
    otaAgent.imageState = state;

    if( otaAgent.pOtaSingletonActiveJobName != NULL )
    {
        err = updateJobStatusFromImageState( state, ( int32_t ) reason );
    }
    else
    {
        err = OTA_ERR_NO_ACTIVE_JOB;
    }

    return err;
}

static OtaErr_t palDefaultResetDevice( uint32_t serverFileID )
{
    ( void ) serverFileID;
    return prvPAL_ResetDevice();
}

static OtaPalImageState_t palDefaultGetPlatformImageState( uint32_t serverFileID )
{
    ( void ) serverFileID;
    return prvPAL_GetPlatformImageState();
}

static OtaErr_t palDefaultSetPlatformImageState( uint32_t serverFileID,
                                                 OtaImageState_t state )
{
    ( void ) serverFileID;
    ( void ) state;
    return prvPAL_SetPlatformImageState( state );
}

static OtaErr_t palDefaultActivateNewImage( uint32_t serverFileID )
{
    ( void ) serverFileID;
    return prvPAL_ActivateNewImage();
}

/* This is the default OTA callback handler if the user does not provide
 * one. It will do the basic activation and commit of accepted images.
 *
 * The OTA agent has completed the update job or determined we're in self
 * test mode. If the update was accepted, we want to activate the new image
 * by resetting the device to boot the new firmware.  If now is not a good
 * time to reset the device, the user should have registered their own
 * callback function instead of this default callback to allow user level
 * self tests and a user scheduled reset.
 * If the update was rejected, just return without doing anything and we'll
 * wait for another job. If it reported that we're in self test mode, we've
 * already successfully connected to the AWS IoT broker and received the
 * latest job so go ahead and set the image as accepted since there is no
 * additional user level tests to run.
 */
static void defaultOTACompleteCallback( OtaJobEvent_t event )
{
    DEFINE_OTA_METHOD_NAME( "defaultOTACompleteCallback" );

    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    if( event == OtaJobEventActivate )
    {
        OTA_LOG_L1( "[%s] Received OtaJobEventActivate callback from OTA Agent.\r\n", OTA_METHOD_NAME );
        ( void ) OTA_ActivateNewImage();
    }
    else if( event == OtaJobEventFail )
    {
        OTA_LOG_L1( "[%s] Received OtaJobEventFail callback from OTA Agent.\r\n", OTA_METHOD_NAME );
        /* Nothing special to do. The OTA agent handles it. */
    }
    else if( event == OtaJobEventStartTest )
    {
        /* Accept the image since it was a good transfer
         * and networking and services are all working.
         * and networking and services are all working.
         */
        OTA_LOG_L1( "[%s] Received OtaJobEventStartTest callback from OTA Agent.\r\n", OTA_METHOD_NAME );
        err = OTA_SetImageState( OtaImageStateAccepted );

        if( err != OTA_ERR_NONE )
        {
            OTA_LOG_L1( "[%s] Error! Failed to set image state.\r\n", OTA_METHOD_NAME );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Received invalid job event %d from OTA Agent.\r\n", OTA_METHOD_NAME, event );
    }
}

static OtaJobParseErr_t defaultCustomJobCallback( const char * pJson,
                                                  uint32_t messageLength )
{
    DEFINE_OTA_METHOD_NAME( "defaultCustomJobCallback" );
    ( void ) messageLength;
    ( void ) pJson;

    /*
     * The JOB document received is not conforming to AFR OTA job document and it could be a
     * custom OTA job. No applciation callback for handling custom job document is registered so just
     * return error code for non conforming job document from this default handler.
     */
    OTA_LOG_L2( "[%s] Received Custom Job inside OTA Agent which is not supported.\r\n", OTA_METHOD_NAME );

    return OtaJobParseErrNonConformingJobDoc;
}

static void prvSetPALCallbacks( const OtaPalCallbacks_t * pCallbacks )
{
    //configASSERT( pCallbacks != NULL );

    if( pCallbacks->abort != NULL )
    {
        otaAgent.palCallbacks.abort = pCallbacks->abort;
    }
    else
    {
        otaAgent.palCallbacks.abort = prvPAL_Abort;
    }

    if( pCallbacks->activateNewImage != NULL )
    {
        otaAgent.palCallbacks.activateNewImage = pCallbacks->activateNewImage;
    }
    else
    {
        otaAgent.palCallbacks.activateNewImage = palDefaultActivateNewImage;
    }

    if( pCallbacks->closeFile != NULL )
    {
        otaAgent.palCallbacks.closeFile = pCallbacks->closeFile;
    }
    else
    {
        otaAgent.palCallbacks.closeFile = prvPAL_CloseFile;
    }

    if( pCallbacks->createFileForRx != NULL )
    {
        otaAgent.palCallbacks.createFileForRx = pCallbacks->createFileForRx;
    }
    else
    {
        otaAgent.palCallbacks.createFileForRx = prvPAL_CreateFileForRx;
    }

    if( pCallbacks->getPlatformImageState != NULL )
    {
        otaAgent.palCallbacks.getPlatformImageState = pCallbacks->getPlatformImageState;
    }
    else
    {
        otaAgent.palCallbacks.getPlatformImageState = palDefaultGetPlatformImageState;
    }

    if( pCallbacks->resetDevice != NULL )
    {
        otaAgent.palCallbacks.resetDevice = pCallbacks->resetDevice;
    }
    else
    {
        otaAgent.palCallbacks.resetDevice = palDefaultResetDevice;
    }

    if( pCallbacks->setPlatformImageState != NULL )
    {
        otaAgent.palCallbacks.setPlatformImageState = pCallbacks->setPlatformImageState;
    }
    else
    {
        otaAgent.palCallbacks.setPlatformImageState = palDefaultSetPlatformImageState;
    }

    if( pCallbacks->writeBlock != NULL )
    {
        otaAgent.palCallbacks.writeBlock = pCallbacks->writeBlock;
    }
    else
    {
        otaAgent.palCallbacks.writeBlock = prvPAL_WriteBlock;
    }

    if( pCallbacks->completeCallback != NULL )
    {
        otaAgent.palCallbacks.completeCallback = pCallbacks->completeCallback;
    }
    else
    {
        otaAgent.palCallbacks.completeCallback = defaultOTACompleteCallback;
    }

    if( pCallbacks->customJobCallback != NULL )
    {
        otaAgent.palCallbacks.customJobCallback = pCallbacks->customJobCallback;
    }
    else
    {
        otaAgent.palCallbacks.customJobCallback = defaultCustomJobCallback;
    }
}

static OtaErr_t startHandler( OtaEventData_t * pEventData )
{
    DEFINE_OTA_METHOD_NAME( "startHandler" );

    ( void ) pEventData;
    OtaErr_t retVal = OTA_ERR_NONE;
    OtaEventMsg_t eventMsg = { 0 };

    /* Start self-test timer, if platform is in self-test. */
    startSelfTestTimer();

    /* Send event to OTA task to get job document. */
    eventMsg.eventId = OtaAgentEventRequestJobDocument;

    if( !OTA_SignalEvent( &eventMsg ) )
    {
        retVal = OTA_ERR_EVENT_Q_SEND_FAILED;
    }

    return retVal;
}

static OtaErr_t inSelfTestHandler( OtaEventData_t * pEventData )
{
    DEFINE_OTA_METHOD_NAME( "inSelfTestHandler" );

    ( void ) pEventData;

    OTA_LOG_L1( "[%s] inSelfTestHandler, platform is in self-test.\r\n", OTA_METHOD_NAME );

    /* Check the platform's OTA update image state. It should also be in self test. */
    if( inSelftest() == true )
    {
        /* Callback for application specific self-test. */
        otaAgent.palCallbacks.completeCallback( OtaJobEventStartTest );
    }
    else
    {
        /* The job is in self test but the platform image state is not so it could be
         * an attack on the platform image state. Reject the update (this should also
         * cause the image to be erased), aborting the job and reset the device. */
        OTA_LOG_L1( "[%s] Job in self test but platform state is not!\r\n", OTA_METHOD_NAME );
        ( void ) setImageStateWithReason( OtaImageStateRejected, OTA_ERR_IMAGE_STATE_MISMATCH );
        ( void ) resetDevice(); /* Ignore return code since there's nothing we can do if we can't force reset. */
    }

    return OTA_ERR_NONE;
}

static OtaErr_t requestJobHandler( OtaEventData_t * pEventData )
{
    DEFINE_OTA_METHOD_NAME( "requestJobHandler" );

    ( void ) pEventData;
    OtaErr_t retVal = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    /*
     * Check if any pending jobs are available from job service.
     */
    retVal = otaControlInterface.requestJob( &otaAgent );

    if( retVal != OTA_ERR_NONE )
    {
        if( otaAgent.requestMomentum < otaconfigMAX_NUM_REQUEST_MOMENTUM )
        {
            otaAgent.requestMomentum++;

            retVal = OTA_ERR_PUBLISH_FAILED;
        }
        else
        {
            /* Send shutdown event to the OTA Agent task. */
            eventMsg.eventId = OtaAgentEventShutdown;

            if( !OTA_SignalEvent( &eventMsg ) )
            {
                retVal = OTA_ERR_EVENT_Q_SEND_FAILED;
            }
            else
            {
                /*
                 * Too many requests have been sent without a response or too many failures
                 * when trying to publish the request message. Abort. Store attempt count in low bits.
                 */
                retVal = ( uint32_t ) OTA_ERR_MOMENTUM_ABORT | ( otaconfigMAX_NUM_REQUEST_MOMENTUM & ( uint32_t ) OTA_PAL_ERR_MASK );
            }
        }
    }
    else
    {
        /* Reset the request momentum. */
        otaAgent.requestMomentum = 0;
    }

    return retVal;
}

static OtaErr_t processJobHandler( OtaEventData_t * pEventData )
{
    DEFINE_OTA_METHOD_NAME( "processJobHandler" );

    OtaErr_t retVal = OTA_ERR_UNINITIALIZED;
    OtaFileContext_t * pOtaFileContext = NULL;
    OtaEventMsg_t eventMsg = { 0 };

    /*
     * Parse the job document and update file information in the file context.
     */
    pOtaFileContext = getFileContextFromJob( ( const char * ) pEventData->data,
                                             pEventData->dataLength );

    /*
     * A null context here could either mean we didn't receive a valid job or it could
     * signify that we're in the self test phase (where the OTA file transfer is already
     * completed and we've reset the device and are now running the new firmware). We
     * will check the state to determine which case we're in.
     */
    if( pOtaFileContext == NULL )
    {
        /*
         * If the OTA job is in the self_test state, alert the application layer.
         */
        if( OTA_GetImageState() == OtaImageStateTesting )
        {
            /* Send event to OTA task to start self-test. */
            eventMsg.eventId = OtaAgentEventStartSelfTest;

            if( !OTA_SignalEvent( &eventMsg ) )
            {
                retVal = OTA_ERR_EVENT_Q_SEND_FAILED;
            }
            else
            {
                retVal = OTA_ERR_NONE;
            }
        }
        else
        {
            /*
             * If the job context returned NULL and the image state is not in the self_test state,
             * then an error occurred parsing the OTA job message.  Abort the OTA job with a parse error.
             *
             * If there is a valid job id, then a job status update will be sent.
             */
            ( void ) setImageStateWithReason( OtaImageStateAborted, OTA_ERR_JOB_PARSER_ERROR );

            retVal = OTA_ERR_JOB_PARSER_ERROR;
        }
    }
    else
    {
        /*
         * If the platform is not in the self_test state, initiate file download.
         */
        if( inSelftest() == false )
        {
            /* Init data interface routines */
            retVal = setDataInterface( &otaDataInterface, otaAgent.pOtaFiles[ otaAgent.fileIndex ].pProtocols );

            if( retVal == OTA_ERR_NONE )
            {
                OTA_LOG_L1( "[%s] Setting OTA data inerface.\r\n", OTA_METHOD_NAME );

                /* Received a valid context so send event to request file blocks. */
                eventMsg.eventId = OtaAgentEventCreateFile;

                /*Send the event to OTA Agent task. */
                if( !OTA_SignalEvent( &eventMsg ) )
                {
                    retVal = OTA_ERR_EVENT_Q_SEND_FAILED;
                }
            }
            else
            {
                /*
                 * Failed to set the data interface so abort the OTA.If there is a valid job id,
                 * then a job status update will be sent.
                 */
                ( void ) setImageStateWithReason( OtaImageStateAborted, retVal );
            }
        }
        else
        {
            /*
             * Received a job that is not in self-test but platform is, so reboot the device to allow
             * roll back to previous image.
             */
            OTA_LOG_L1( "[%s] Platform is in self-test but job is not, rebooting !  \r\n", OTA_METHOD_NAME );
            ( void ) otaAgent.palCallbacks.resetDevice( otaAgent.serverFileID );
        }
    }

    /*Free the OTA event buffer. */
    otaEventBufferFree( pEventData );

    return retVal;
}

static OtaErr_t initFileHandler( OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    err = otaDataInterface.initFileTransfer( &otaAgent );

    if( err != OTA_ERR_NONE )
    {
        if( otaAgent.requestMomentum < otaconfigMAX_NUM_REQUEST_MOMENTUM )
        {
            otaAgent.requestMomentum++;
            err = OTA_ERR_PUBLISH_FAILED;
        }
        else
        {
            /* Send shutdown event. */
            eventMsg.eventId = OtaAgentEventShutdown;

            if( !OTA_SignalEvent( &eventMsg ) )
            {
                err = OTA_ERR_EVENT_Q_SEND_FAILED;
            }
            else
            {
                /* Too many requests have been sent without a response or too many failures
                 * when trying to publish the request message. Abort. Store attempt count in low bits. */
                err = ( uint32_t ) OTA_ERR_MOMENTUM_ABORT | ( otaconfigMAX_NUM_REQUEST_MOMENTUM & ( uint32_t ) OTA_PAL_ERR_MASK );
            }
        }
    }
    else
    {
        /* Reset the request momentum. */
        otaAgent.requestMomentum = 0;

        eventMsg.eventId = OtaAgentEventRequestFileBlock;

        if( !OTA_SignalEvent( &eventMsg ) )
        {
            err = OTA_ERR_EVENT_Q_SEND_FAILED;
        }
    }

    return err;
}

static OtaErr_t requestDataHandler( OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    if( otaAgent.pOtaFiles[ otaAgent.fileIndex ].blocksRemaining > 0U )
    {
        if( otaAgent.requestMomentum < otaconfigMAX_NUM_REQUEST_MOMENTUM )
        {
            /* Request data blocks. */
            err = otaDataInterface.requestFileBlock( &otaAgent );

            /* Each request increases the momentum until a response is received. Too much momentum is
             * interpreted as a failure to communicate and will cause us to abort the OTA. */
            otaAgent.requestMomentum++;
        }
        else
        {
            /* Failed to send data request abort and close file. */
            ( void ) setImageStateWithReason( OtaImageStateAborted, err );

            /* Send shutdown event. */
            eventMsg.eventId = OtaAgentEventShutdown;

            if( !OTA_SignalEvent( &eventMsg ) )
            {
                err = OTA_ERR_EVENT_Q_SEND_FAILED;
            }
            else
            {
                /* Too many requests have been sent without a response or too many failures
                 * when trying to publish the request message. Abort. Store attempt count in low bits. */
                err = ( uint32_t ) OTA_ERR_MOMENTUM_ABORT | ( otaconfigMAX_NUM_REQUEST_MOMENTUM & ( uint32_t ) OTA_PAL_ERR_MASK );

                /* Reset the request momentum. */
                otaAgent.requestMomentum = 0;
            }
        }
    }

    return err;
}

static OtaErr_t processDataHandler( OtaEventData_t * pEventData )
{
    DEFINE_OTA_METHOD_NAME( "prvProcessDataMessage" );

    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaErr_t closeResult = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    /* Get the file context. */
    OtaFileContext_t * pxFileContext = &otaAgent.pOtaFiles[ otaAgent.fileIndex ];

    /* Ingest data blocks received. */
    IngestResult_t result = ingestDataBlock( pxFileContext,
                                             pEventData->data,
                                             pEventData->dataLength,
                                             &closeResult );

    if( result < IngestResultAccepted_Continue )
    {
        /* Negative result codes mean we should stop the OTA process
         * because we are either done or in an unrecoverable error state.
         * We don't want to hang on to the resources. */

        if( result == IngestResultFileComplete )
        {
            /* File receive is complete and authenticated. Update the job status with the self_test ready identifier. */
            err = otaControlInterface.updateJobStatus( &otaAgent, JobStatusInProgress, JobReasonSigCheckPassed, 0 );

            if( err != OTA_ERR_NONE )
            {
                OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, err );
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Aborting due to IngestResult_t error %d\r\n", OTA_METHOD_NAME, ( int32_t ) result );

            /* Call the platform specific code to reject the image. */
            err = otaAgent.palCallbacks.setPlatformImageState( otaAgent.serverFileID, OtaImageStateRejected );

            if( err != OTA_ERR_NONE )
            {
                OTA_LOG_L2( "[%s] Error trying to set platform image state (0x%08x)\r\n", OTA_METHOD_NAME, ( int32_t ) err );
            }

            /* Update the job status with the with failure code. */
            err = otaControlInterface.updateJobStatus( &otaAgent, JobStatusFailedWithVal, ( int32_t ) closeResult, ( int32_t ) result );

            if( err != OTA_ERR_NONE )
            {
                OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, err );
            }
        }

        /* Send event to close file. */
        eventMsg.eventId = OtaAgentEventCloseFile;

        if( !OTA_SignalEvent( &eventMsg ) )
        {
            OTA_LOG_L2( "[%s] Failed to singal OTA agent to close file.", OTA_METHOD_NAME );
        }

        /* Let main application know of our result. */
        otaAgent.palCallbacks.completeCallback( ( result == IngestResultFileComplete ) ? OtaJobEventActivate : OtaJobEventFail );

        /* Free any remaining string memory holding the job name since this job is done. */
        if( otaAgent.pOtaSingletonActiveJobName != NULL )
        {
            free( otaAgent.pOtaSingletonActiveJobName );
            otaAgent.pOtaSingletonActiveJobName = NULL;
        }
    }
    else
    {
        if( result == IngestResultAccepted_Continue )
        {
            /* We're actively receiving a file so update the job status as needed. */
            /* First reset the momentum counter since we received a good block. */
            otaAgent.requestMomentum = 0;
           // err = otaControlInterface.updateJobStatus( &otaAgent, JobStatusInProgress, JobReasonReceiving, 0 );

         //   if( err != OTA_ERR_NONE )
         //   {
        //        OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, err );
        //    }
        }

        if( otaAgent.numOfBlocksToReceive > 1U )
        {
            otaAgent.numOfBlocksToReceive--;
        }
        else
        {
            eventMsg.eventId = OtaAgentEventRequestFileBlock;

            if( !OTA_SignalEvent( &eventMsg ) )
            {
                OTA_LOG_L2( "[%s] Failed to signal OTA agent to close file.", OTA_METHOD_NAME );
            }
        }
    }

    /* Release the data buffer. */
    otaEventBufferFree( pEventData );

    return OTA_ERR_NONE;
}

static OtaErr_t closeFileHandler( OtaEventData_t * pEventData )
{
    DEFINE_OTA_METHOD_NAME( "closeFileHandler" );

    ( void ) pEventData;

    OTA_LOG_L2( "[%s] Closing File. %d\r\n", OTA_METHOD_NAME );

    ( void ) otaClose( &( otaAgent.pOtaFiles[ otaAgent.fileIndex ] ) );

    return OTA_ERR_NONE;
}

static OtaErr_t userAbortHandler( OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    /* If we have active Job abort it and close the file. */
    if( otaAgent.pOtaSingletonActiveJobName != NULL )
    {
        err = setImageStateWithReason( OtaImageStateAborted, OTA_ERR_USER_ABORT );

        if( err == OTA_ERR_NONE )
        {
            ( void ) otaClose( &( otaAgent.pOtaFiles[ otaAgent.fileIndex ] ) );
        }
    }

    return err;
}

static OtaErr_t shutdownHandler( OtaEventData_t * pEventData )
{
    DEFINE_OTA_METHOD_NAME( "shutdownHandler" );
    ( void ) pEventData;

    OTA_LOG_L2( "[%s] Shutting Down OTA Agent. %d\r\n", OTA_METHOD_NAME );

    /* If we're here, we're shutting down the OTA agent. Free up all resources and quit. */
    agentShutdownCleanup();

    /* Clear the entire agent context. This includes the OTA agent state. */
    ( void ) memset( &otaAgent, 0, sizeof( otaAgent ) );

    otaAgent.state = OtaAgentStateStopped;

    /* Terminate the OTA Agent Thread. */
    pthread_exit( NULL );

    return OTA_ERR_NONE;
}

static OtaErr_t suspendHandler( OtaEventData_t * pEventData )
{
    DEFINE_OTA_METHOD_NAME( "suspendHandler" );

    ( void ) pEventData;
    OtaErr_t err = OTA_ERR_NONE;

    /* Log the state change to suspended state.*/
    OTA_LOG_L1( "[%s] OTA Agent is suspended.\r\n", OTA_METHOD_NAME );

    return err;
}

static OtaErr_t resumeHandler( OtaEventData_t * pEventData )
{
    DEFINE_OTA_METHOD_NAME( "resumeHandler" );

    ( void ) pEventData;

    OtaEventMsg_t eventMsg = { 0 };

    /*
     * Update the connection handle before resuming the OTA process.
     */

    OTA_LOG_L2( "[%s] Updating the connection handle. %d\r\n", OTA_METHOD_NAME );

    otaAgent.pConnectionContext = pEventData;

    /*
     * Send signal to request job document.
     */
    eventMsg.eventId = OtaAgentEventRequestJobDocument;

    return OTA_SignalEvent( &eventMsg ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
}

static OtaErr_t jobNotificationHandler( OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    /* Abort the current job. */
    ( void ) otaAgent.palCallbacks.setPlatformImageState( otaAgent.serverFileID, OtaImageStateAborted );
    ( void ) otaClose( &otaAgent.pOtaFiles[ otaAgent.fileIndex ] );

    /* Free the active job name as its no longer required. */
    if( otaAgent.pOtaSingletonActiveJobName != NULL )
    {
        free( otaAgent.pOtaSingletonActiveJobName );
        otaAgent.pOtaSingletonActiveJobName = NULL;
    }

    /*
     * Send signal to request next OTA job document from service.
     */
    eventMsg.eventId = OtaAgentEventRequestJobDocument;

    return OTA_SignalEvent( &eventMsg ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
}

/*
 * This is a private function only meant to be called by the OTA agent after the
 * currently running image that is in the self test phase rejects the update.
 * It simply calls the platform specific code required to reset the device.
 */
static OtaErr_t resetDevice( void )
{
    DEFINE_OTA_METHOD_NAME( "resetDevice" );

    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    /*
     * Call platform specific code to reset the device. This should not return unless
     * there is a problem within the PAL layer. If it does return, output an error
     * message. The device may need to be reset manually.
     */
    OTA_LOG_L1( "[%s] Attempting forced reset of device...\r\n", OTA_METHOD_NAME );
    err = otaAgent.palCallbacks.resetDevice( otaAgent.serverFileID );

    /*
     * We should not get here, OTA pal call for resetting device failed.
     */
    OTA_LOG_L1( "[%s] Failed to reset the device (0x%08x). Please reset manually.\r\n", OTA_METHOD_NAME, err );

    return err;
}

void otaEventBufferFree( OtaEventData_t * const pBuffer )
{
    DEFINE_OTA_METHOD_NAME( "otaEventBufferFree" );

    /* Release the buffer */
    pBuffer->bufferUsed = false;
}

OtaEventData_t * otaEventBufferGet( void )
{
    DEFINE_OTA_METHOD_NAME( "otaEventBufferGet" );

    uint32_t index = 0;
    OtaEventData_t * pOtaFreeMsg = NULL;

    for( index = 0; index < otaconfigMAX_NUM_OTA_DATA_BUFFERS; index++ )
    {
        if( pEventBuffer[ index ].bufferUsed == false )
        {
            pEventBuffer[ index ].bufferUsed = true;
            pOtaFreeMsg = &pEventBuffer[ index ];
            break;
        }
    }

    return pOtaFreeMsg;
}

static void prvOTA_FreeContext( OtaFileContext_t * const pFileContext )
{
    if( pFileContext != NULL )
    {
        if( pFileContext->pStreamName != NULL )
        {
            free( pFileContext->pStreamName ); /* Free any previously allocated stream name memory. */
            pFileContext->pStreamName = NULL;
        }

        if( pFileContext->pJobName != NULL )
        {
            free( pFileContext->pJobName ); /* Free the job name memory. */
            pFileContext->pJobName = NULL;
        }

        if( pFileContext->pRxBlockBitmap != NULL )
        {
            free( pFileContext->pRxBlockBitmap ); /* Free the previously allocated block bitmap. */
            pFileContext->pRxBlockBitmap = NULL;
        }

        if( pFileContext->pSignature != NULL )
        {
            free( pFileContext->pSignature ); /* Free the image signature memory. */
            pFileContext->pSignature = NULL;
        }

        if( pFileContext->pFilePath != NULL )
        {
            free( pFileContext->pFilePath ); /* Free the file path name string memory. */
            pFileContext->pFilePath = NULL;
        }

        if( pFileContext->pCertFilepath != NULL )
        {
            free( pFileContext->pCertFilepath ); /* Free the certificate path name string memory. */
            pFileContext->pCertFilepath = NULL;
        }

        if( pFileContext->pUpdateUrlPath != NULL )
        {
            free( pFileContext->pUpdateUrlPath ); /* Free the url path name string memory. */
            pFileContext->pUpdateUrlPath = NULL;
        }

        if( pFileContext->pAuthScheme != NULL )
        {
            free( pFileContext->pAuthScheme ); /* Free the pAuthScheme name string memory. */
            pFileContext->pAuthScheme = NULL;
        }

        if( pFileContext->pProtocols != NULL )
        {
            free( pFileContext->pProtocols ); /* Free the pProtocols string memory. */
            pFileContext->pProtocols = NULL;
        }
    }
}

/* Close an existing OTA context and free its resources. */

static bool otaClose( OtaFileContext_t * const pFileContext )
{
    DEFINE_OTA_METHOD_NAME( "otaClose" );

    bool result = false;

    OTA_LOG_L2( "[%s] Context->0x%p\r\n", OTA_METHOD_NAME, pFileContext );

    /* Cleanup related to selected protocol. */
    if( otaDataInterface.cleanup != NULL )
    {
        ( void ) otaDataInterface.cleanup( &otaAgent );
    }

    if( pFileContext != NULL )
    {
        /*
         * Abort any active file access and release the file resource, if needed.
         */
        ( void ) otaAgent.palCallbacks.abort( pFileContext );

        /* Free the resources. */
        prvOTA_FreeContext( pFileContext );

        /* Clear the entire structure now that it is free. */
        ( void ) memset( pFileContext, 0, sizeof( OtaFileContext_t ) );

        result = true;
    }

    return result;
}


/* Find an available OTA transfer context structure. */

static OtaFileContext_t * getFreeContext( void )
{
    uint32_t index = 0U;
    OtaFileContext_t * pFileContext = NULL;

    while( ( index < OTA_MAX_FILES ) && ( otaAgent.pOtaFiles[ index ].pFilePath != NULL ) )
    {
        index++;
    }

    if( index != OTA_MAX_FILES )
    {
        ( void ) memset( &otaAgent.pOtaFiles[ index ], 0, sizeof( OtaFileContext_t ) );
        pFileContext = &otaAgent.pOtaFiles[ index ];
        otaAgent.fileIndex = index;
    }
    else
    {
        /* Not able to support this request so we'll return NULL. */
    }

    return pFileContext;
}

/* Validate JSON document and the DocModel*/
static DocParseErr_t validateJSON( const char * pJson,
                                   uint32_t messageLength )
{
    DEFINE_OTA_METHOD_NAME( "validateJSON" );

    DocParseErr_t err = DocParseErrNone;
    JSONStatus_t result;

    /* Check JSON document pointer is valid.*/
    if( pJson == NULL )
    {
        OTA_LOG_L1( "[%s] JSON document pointer is NULL!\r\n", OTA_METHOD_NAME );
        err = DocParseErrNullDocPointer;
    }

    /* Check if the JSON document is valid*/
    if( err == DocParseErrNone )
    {
        result = JSON_Validate( pJson, ( size_t ) messageLength );

        if( result != JSONSuccess )
        {
            OTA_LOG_L1( "[%s] Invalid JSON document \r\n", OTA_METHOD_NAME );
            err = DocParseErr_InvalidJSONBuffer;
        }
    }

    return err;
}

/* Store the parameter from the json to the offset specified by the document model*/

static DocParseErr_t extractParameter( JsonDocParam_t docParam,
                                       uint64_t modelContextBase,
                                       uint64_t modelContextSize,
                                       char * pValueInJson,
                                       size_t valueLength )
{
    DEFINE_OTA_METHOD_NAME( "extractParameter" );

    MultiParmPtr_t paramAddr; /*lint !e9018 We intentionally use this union to cast the parameter address to the proper type. */
    DocParseErr_t err = DocParseErrNone;

    /* Get destination offset to parameter storage location. */

    /* If it's within the models context structure, add in the context instance base address. */
    if( docParam.destOffset < modelContextSize )
    {
        paramAddr.intVal = modelContextBase + docParam.destOffset;
    }
    else
    {
        /* It's a raw pointer so keep it as is. */
        paramAddr.intVal = docParam.destOffset;
    }

    if( ( ModelParamTypeStringCopy == docParam.modelParamType ) || ( ModelParamTypeArrayCopy == docParam.modelParamType ) )
    {
        /* Malloc memory for a copy of the value string plus a zero terminator. */
        void * pvStringCopy = malloc( valueLength + 1U );

        if( pvStringCopy != NULL )
        {
            *paramAddr.pVoidPtr = pvStringCopy;
            char * pcStringCopy = ( char * ) pvStringCopy;
            /* Copy parameter string into newly allocated memory. */
            ( void ) memcpy( pvStringCopy, pValueInJson, valueLength );
            /* Zero terminate the new string. */
            pcStringCopy[ valueLength ] = '\0';
            OTA_LOG_L1( "[%s] New Extracted parameter [ %s: %s]\r\n",
                        OTA_METHOD_NAME,
                        docParam.pSrcKey,
                        pcStringCopy );
        }
        else
        { /* Stop processing on error. */
            err = DocParseErrOutOfMemory;
        }
    }
    else if( ModelParamTypeStringInDoc == docParam.modelParamType )
    {
        /* Copy pointer to source string instead of duplicating the string. */
        const char * pcStringInDoc = pValueInJson;
        *paramAddr.pConstCharPtr = pcStringInDoc;
        OTA_LOG_L1( "[%s] New Extracted parameter [ %s: %.*s ]\r\n",
                    OTA_METHOD_NAME,
                    docParam.pSrcKey,
                    valueLength, pcStringInDoc );
    }
    else if( ModelParamTypeUInt32 == docParam.modelParamType )
    {
        char * pEnd;
        const char * pStart = pValueInJson;
        *paramAddr.pIntPtr = strtoul( pStart, &pEnd, 0 );

        if( pEnd == &pValueInJson[ valueLength ] )
        {
            OTA_LOG_L1( "[%s] New Extracted parameter [ %s: %lu ]\r\n",
                        OTA_METHOD_NAME,
                        docParam.pSrcKey,
                        *paramAddr.pIntPtr );
        }
        else
        {
            err = DocParseErrInvalidNumChar;
        }
    }
    else if( ModelParamTypeSigBase64 == docParam.modelParamType )
    {
        /* Allocate space for and decode the base64 signature. */
        void * pvSignature = malloc( sizeof( Sig256_t ) );

        if( pvSignature != NULL )
        {
            size_t xActualLen = 0;
            *paramAddr.pVoidPtr = pvSignature;
            Sig256_t * pxSig256 = *paramAddr.pSig256Ptr;
            /* Allocate space for and decode the base64 signature. */
            void * pvSignature = malloc( sizeof( Sig256_t ) );

            if( pvSignature != NULL )
            {
                size_t xActualLen = 0;
                *paramAddr.pVoidPtr = pvSignature;
                Sig256_t * pxSig256 = *paramAddr.pSig256Ptr;

                if( base64Decode( pxSig256->data, sizeof( pxSig256->data ), &xActualLen,
                                            ( const uint8_t * ) pValueInJson, valueLength ) != 0 )
                { /* Stop processing on error. */
                    OTA_LOG_L1( "[%s] base64Decode failed.\r\n", OTA_METHOD_NAME );
                    err = DocParseErrBase64Decode;
                }
                else
                {
                    pxSig256->size = ( uint16_t ) xActualLen;
                    OTA_LOG_L1( "[%s] New Extracted parameter [ %s: %.32s... ]\r\n",
                                OTA_METHOD_NAME,
                                docParam.pSrcKey,
                                pValueInJson );
                }
            }
            else
            {
                /* We failed to allocate needed memory. Everything will be freed below upon failure. */
                err = DocParseErrOutOfMemory;
            }

        }
        else
        {
            /* We failed to allocate needed memory. Everything will be freed below upon failure. */
            err = DocParseErrOutOfMemory;
        }
    }
    else if( ModelParamTypeIdent == docParam.modelParamType )
    {
        OTA_LOG_L1( "[%s] New Identified parameter [ %s ]\r\n",
                    OTA_METHOD_NAME,
                    docParam.pSrcKey );
        *paramAddr.pBoolPtr = true;
    }
    else
    {
        /* Ignore if invalid type */
    }

    return err;
}

/* Checks for duplicate entries in the JSON document*/
static DocParseErr_t checkDuplicates(uint32_t * paramsReceivedBitmap, uint16_t paramIndex)
{
    DocParseErr_t err = DocParseErrNone;
    // TODO need to change this implementation because duplicates are not searched properly
    /* Check for duplicates of the token*/
    if( (* paramsReceivedBitmap & ( ( uint32_t ) 1U << paramIndex ) ) != 0U )             /*lint !e9032 paramIndex will never be greater than kDocModel_MaxParams, which is the the size of the bitmap. */
    {
        err = DocParseErrDuplicatesNotAllowed;
    }
    else
    {
        /* Mark parameter as received in the bitmap. */
        * paramsReceivedBitmap |= ( ( uint32_t ) 1U << paramIndex );             /*lint !e9032 paramIndex will never be greater than kDocModel_MaxParams, which is the the size of the bitmap. */
    }

    return err;
}

/* Extract the desired fields from the JSON document based on the specified document model. */

static DocParseErr_t parseJSONbyModel( const char * pJson,
                                       uint32_t messageLength,
                                       JsonDocModel_t * pDocModel )
{
    DEFINE_OTA_METHOD_NAME( "parseJSONbyModel" );

    const JsonDocParam_t * pModelParam = NULL;
    uint16_t modelParamIndex = 0;
    uint32_t scanIndex = 0;
    DocParseErr_t err;
    JSONStatus_t result;
    uint16_t paramIndex;
    char * pFileParams = NULL;
    uint32_t fileParamsLength;

    /* Check the validity of the JSON document */
    err = validateJSON( pJson, messageLength );

    /* Check if any tokens specified in the docModel are present in the JSON */
    if( err == DocParseErrNone )
    {
        /* Fetch the model parameters from the DocModel*/
        pModelParam = pDocModel->pBodyDef;
        /* char pJsonCopy[messageLength]; */
        /* strcpy(pJsonCopy, pJson); */
        /* pJsonCopy[messageLength] = '\0'; */
        OTA_LOG_L1( "[%s] JSON(%d) : %s \r \n", OTA_METHOD_NAME, messageLength, pJson );

        /* Traverse the docModel and search the JSON if it containg the Source Key specified*/
        for( paramIndex = 0; paramIndex < pDocModel->numModelParams; paramIndex++ )
        {
            char * pQueryKey = pDocModel->pBodyDef[ paramIndex ].pSrcKey;
            size_t queryKeyLength = strlen( pQueryKey );
            char * pValueInJson;
            size_t valueLength;
            result = JSON_Search( pJson, messageLength, pQueryKey, queryKeyLength, OTA_JSON_SEPARATOR[ 0 ], &pValueInJson, &valueLength ); /*TODO check if we need to use a copy of pJson */
            OTA_LOG_L1( "[%s]Searching for Token in pJson: %s. Status: %d\r\n", OTA_METHOD_NAME, pQueryKey, result );

            /* If not found in pJSon search for the key in FileParameters JSON*/
            if( ( result != JSONSuccess ) && ( pFileParams != NULL ) )
            {
                result = JSON_Search( pFileParams, fileParamsLength, pQueryKey, queryKeyLength, OTA_JSON_SEPARATOR[ 0 ], &pValueInJson, &valueLength );
                OTA_LOG_L1( "[%s]Searching for Token in file json: %s. Status: %d\r\n", OTA_METHOD_NAME, pQueryKey, result );
            }

            if( result == JSONSuccess )
            {
                err = checkDuplicates(&(pDocModel->paramsReceivedBitmap), paramIndex);

                if( OTA_DONT_STORE_PARAM == pModelParam[ paramIndex ].destOffset )
                {
                   /* Do nothing if we don't need to store the parameter */
                   continue;
                }
                else if( OTA_STORE_NESTED_JSON == pModelParam[ paramIndex ].destOffset )
                {
                    pFileParams = pValueInJson+1;
                    fileParamsLength = valueLength-2U;
                    OTA_LOG_L1( "File JSON(%d) : %.*s \r \n", fileParamsLength, fileParamsLength, pFileParams);
                }
                else
                {
                    err = extractParameter( pModelParam[ paramIndex ], pDocModel->contextBase, pDocModel->contextSize, pValueInJson, valueLength );
                }
            }
        }
    }

     if( err == DocParseErrNone ) 
     { 
         uint32_t ulMissingParams = ( pDocModel->paramsReceivedBitmap & pDocModel->paramsRequiredBitmap ) 
                                    ^ pDocModel->paramsRequiredBitmap;
         if( ulMissingParams != 0U ) 
         { 
             /* The job document did not have all required document model parameters. */
             for( scanIndex = 0UL; scanIndex < pDocModel->numModelParams; scanIndex++ ) 
             { 
                 if( ( ulMissingParams & ( 1UL << scanIndex ) ) != 0UL ) 
                 {
                     OTA_LOG_L1( "[%s] parameter not present: %s\r\n",
                                 OTA_METHOD_NAME, 
                                 pModelParam[ scanIndex ].pSrcKey );
                 }
             } 
             err = DocParseErrMalformedDoc;
         } 
     } 
     else 
     { 
         OTA_LOG_L1( "[%s] Error (%d) parsing JSON document.\r\n", OTA_METHOD_NAME, ( int32_t ) err );
     } 

    /*configASSERT( err != DocParseErrUnknown ); */
    return err;
}

/* Prepare the document model for use by sanity checking the initialization parameters
 * and detecting all required parameters. */

static DocParseErr_t initDocModel( JsonDocModel_t * pDocModel,
                                   const JsonDocParam_t * pBodyDef,
                                   uint64_t contextBaseAddr,
                                   uint32_t contextSize,
                                   uint16_t numJobParams )
{
    DEFINE_OTA_METHOD_NAME( "initDocModel" );

    DocParseErr_t err = DocParseErrUnknown;
    uint32_t scanIndex;

    /* Sanity check the model pointers and parameter count. Exclude the context base address and size since
     * it is technically possible to create a model that writes entirely into absolute memory locations.
     */
    if( pDocModel == NULL )
    {
        OTA_LOG_L1( "[%s] The pointer to the document model is NULL.\r\n", OTA_METHOD_NAME );
        err = DocParseErrNullModelPointer;
    }
    else if( pBodyDef == NULL )
    {
        OTA_LOG_L1( "[%s] Document model %p body pointer is NULL.\r\n", OTA_METHOD_NAME, pDocModel );
        err = DocParseErrNullBodyPointer;
    }
    else if( numJobParams > OTA_DOC_MODEL_MAX_PARAMS )
    {
        OTA_LOG_L1( "[%s] Model has too many parameters (%u).\r\n", OTA_METHOD_NAME, pDocModel->numModelParams );
        err = DocParseErrTooManyParams;
    }
    else
    {
        pDocModel->contextBase = contextBaseAddr;
        pDocModel->contextSize = contextSize;
        pDocModel->pBodyDef = pBodyDef;
        pDocModel->numModelParams = numJobParams;
        pDocModel->paramsReceivedBitmap = 0;
        pDocModel->paramsRequiredBitmap = 0;

        /* Scan the model and detect all required parameters (i.e. not optional). */
        for( scanIndex = 0; scanIndex < pDocModel->numModelParams; scanIndex++ )
        {
            if( pDocModel->pBodyDef[ scanIndex ].required )
            {
                /* Add parameter to the required bitmap. */
                pDocModel->paramsRequiredBitmap |= ( 1UL << scanIndex );
            }
        }

        err = DocParseErrNone;
    }

    return err;
}

/*
 * Validate the version of the update received.
 */
static OtaErr_t prvValidateUpdateVersion( OtaFileContext_t * pFileContext )
{
    DEFINE_OTA_METHOD_NAME( "prvValidateUpdateVersion" );

    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    /* Only check for versions if the target is self */
    if( otaAgent.serverFileID == 0 )
    {
        /* Check if update version received is newer than current version.*/
        if( pFileContext->updaterVersion < appFirmwareVersion.u.unsignedVersion32 )
        {
            OTA_LOG_L1( "[%s] The update version is newer than the version on device.\r\n", OTA_METHOD_NAME );

            err = OTA_ERR_NONE;
        }
        /* Check if update version received is older than current version.*/
        else if( pFileContext->updaterVersion > appFirmwareVersion.u.unsignedVersion32 )
        {
            OTA_LOG_L1( "[%s] The update version is older than the version on device.\r\n", OTA_METHOD_NAME );

            err = OTA_ERR_DOWNGRADE_NOT_ALLOWED;
        }
        /* Check if version reported is the same as the running version. */
        else if( pFileContext->updaterVersion == appFirmwareVersion.u.unsignedVersion32 )
        {
            /* The version is the same so either we're not actually the new firmware or
             * someone messed up and sent firmware with the same version. In either case,
             * this is a failure of the OTA update so reject the job.
             */
            OTA_LOG_L1( "[%s] We rebooted and the version is still the same.\r\n", OTA_METHOD_NAME );

            err = OTA_ERR_SAME_FIRMWARE_VERSION;
        }
    }
    else
    {
        /* For any other serverFileID.*/
        err = OTA_ERR_NONE;
    }

    return err;
}

#define OFFSET_OF( t, e )    ( ( uint32_t ) ( &( ( t * ) 0x10000UL )->e ) & 0xffffUL )

/* Parse the OTA job document and validate. Return the populated
 * OTA context if valid otherwise return NULL.
 */

static OtaFileContext_t * parseJobDoc( const char * pJson,
                                       uint32_t messageLength,
                                       bool * pUpdateJob )
{
    DEFINE_OTA_METHOD_NAME( "parseJobDoc" );

    /* This is the OTA job document model describing the parameters, their types, destination and how to extract. */
    /*lint -e{708} We intentionally do some things lint warns about but produce the proper model. */
    /* Namely union initialization and pointers converted to values. */
    static const JsonDocParam_t otaJobDocModelParamStructure[ OTA_NUM_JOB_PARAMS ] =
    {
        { OTA_JSON_CLIENT_TOKEN_KEY,    OTA_JOB_PARAM_OPTIONAL, { OTA_DONT_STORE_PARAM }, ModelParamTypeStringInDoc },                          /*lint !e9078 !e923 Get address of token as value. */
        { OTA_JSON_TIMESTAMP_KEY,       OTA_JOB_PARAM_OPTIONAL, { OTA_DONT_STORE_PARAM }, ModelParamTypeUInt32 },
        { OTA_JSON_EXECUTION_KEY,       OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM }, ModelParamTypeObject },
        { OTA_JSON_JOB_ID_KEY,          OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pJobName )}, ModelParamTypeStringCopy },
        { OTA_JSON_STATUS_DETAILS_KEY,  OTA_JOB_PARAM_OPTIONAL, { OTA_DONT_STORE_PARAM }, ModelParamTypeObject},
        { OTA_JSON_SELF_TEST_KEY,       OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, isInSelfTest )}, ModelParamTypeIdent },
        { OTA_JSON_UPDATED_BY_KEY,      OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, updaterVersion )}, ModelParamTypeUInt32 },
        { OTA_JSON_JOB_DOC_KEY,         OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM }, ModelParamTypeObject },
        { OTA_JSON_OTA_UNIT_KEY,        OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM }, ModelParamTypeObject },
        { OTA_JSON_STREAM_NAME_KEY,     OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, pStreamName )}, ModelParamTypeStringCopy },
        { OTA_JSON_PROTOCOLS_KEY,       OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pProtocols )}, ModelParamTypeArrayCopy },
        { OTA_JSON_FILE_GROUP_KEY,      OTA_JOB_PARAM_REQUIRED, { OTA_STORE_NESTED_JSON }, ModelParamTypeArray },
        { OTA_JSON_FILE_PATH_KEY,       OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pFilePath )}, ModelParamTypeStringCopy },
        { OTA_JSON_FILE_SIZE_KEY,       OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, fileSize )}, ModelParamTypeUInt32 },
        { OTA_JSON_FILE_ID_KEY,         OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, serverFileID )}, ModelParamTypeUInt32 },
        { OTA_JSON_FILE_CERT_NAME_KEY,  OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pCertFilepath )}, ModelParamTypeStringCopy },
        { OTA_JSON_UPDATE_DATA_URL_KEY, OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, pUpdateUrlPath )}, ModelParamTypeStringCopy },
        { OTA_JSON_AUTH_SCHEME_KEY,     OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, pAuthScheme )}, ModelParamTypeStringCopy },
        { OTA_JsonFileSignatureKey,     OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pSignature )}, ModelParamTypeSigBase64 },
        { OTA_JSON_FILE_ATTRIBUTE_KEY,  OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, fileAttributes )}, ModelParamTypeUInt32 },
    };

    OtaErr_t otaErr = OTA_ERR_NONE;
    OtaJobParseErr_t err = OtaJobParseErrUnknown;
    OtaFileContext_t * pFinalFile = NULL;
    OtaFileContext_t fileContext = { 0 };
    OtaFileContext_t * pFileContext = &fileContext;
    OtaErr_t errVersionCheck = OTA_ERR_UNINITIALIZED;

    JsonDocModel_t otaJobDocModel;

    if( initDocModel( &otaJobDocModel,
                      otaJobDocModelParamStructure,
                      ( uint64_t ) pFileContext,    /*lint !e9078 !e923 Intentionally casting context pointer to a value for initDocModel. */
                      sizeof( OtaFileContext_t ),
                      OTA_NUM_JOB_PARAMS ) != DocParseErrNone )
    {
        err = OtaJobParseErrBadModelInitParams;
    }
    else if( parseJSONbyModel( pJson, messageLength, &otaJobDocModel ) == DocParseErrNone )
    { /* Validate the job document parameters. */
        err = OtaJobParseErrNone;

        if( pFileContext->fileSize == 0U )
        {
            OTA_LOG_L1( "[%s] Zero file size is not allowed!\r\n", OTA_METHOD_NAME );
            err = OtaJobParseErrZeroFileSize;
        }
        /* If there's an active job, verify that it's the same as what's being reported now. */
        /* We already checked for missing parameters so we SHOULD have a job name in the context. */
        else if( otaAgent.pOtaSingletonActiveJobName != NULL )
        {
            if( pFileContext->pJobName != NULL )
            {
                /* pFileContext->pJobName is guaranteed to be zero terminated. */
                if( strcmp( ( char * ) otaAgent.pOtaSingletonActiveJobName, ( char * ) pFileContext->pJobName ) != 0 )
                {
                    OTA_LOG_L1( "[%s] New job document received,aborting current job.\r\n", OTA_METHOD_NAME );

                    /* Abort the current job. */
                    ( void ) otaAgent.palCallbacks.setPlatformImageState( otaAgent.serverFileID, OtaImageStateAborted );
                    ( void ) otaClose( &otaAgent.pOtaFiles[ otaAgent.fileIndex ] );

                    /* Set new active job name. */
                    free( otaAgent.pOtaSingletonActiveJobName );
                    otaAgent.pOtaSingletonActiveJobName = pFileContext->pJobName;
                    pFileContext->pJobName = NULL;

                    err = OtaJobParseErrNone;
                }
                else
                { /* The same job is being reported so update the url. */
                    OTA_LOG_L1( "[%s] Job received is current active job.\r\n", OTA_METHOD_NAME );

                    if( otaAgent.pOtaFiles[ otaAgent.fileIndex ].pUpdateUrlPath != NULL )
                    {
                        free( otaAgent.pOtaFiles[ otaAgent.fileIndex ].pUpdateUrlPath );
                        otaAgent.pOtaFiles[ otaAgent.fileIndex ].pUpdateUrlPath = pFileContext->pUpdateUrlPath;
                        pFileContext->pUpdateUrlPath = NULL;
                    }

                    prvOTA_FreeContext( pFileContext );

                    pFinalFile = &otaAgent.pOtaFiles[ otaAgent.fileIndex ];
                    *pUpdateJob = true;

                    err = OtaJobParseErrUpdateCurrentJob;
                }
            }
            else
            {
                OTA_LOG_L1( "[%s] Null job reported while busy. Ignoring.\r\n", OTA_METHOD_NAME );
                err = OtaJobParseErrNullJob;
            }
        }
        else
        { /* Assume control of the job name from the context. */
            otaAgent.pOtaSingletonActiveJobName = pFileContext->pJobName;
            pFileContext->pJobName = NULL;
        }

        /* Store the File ID received in the job */
        otaAgent.serverFileID = pFileContext->serverFileID;

        if( err == OtaJobParseErrNone )
        {
            /* If the job is in self test mode, don't start an
             * OTA update but instead do the following:
             *
             * If the firmware that performed the update was older
             * than the currently running firmware, set the image
             * state to "Testing." This is the success path.
             *
             * If it's the same or newer, reject the job since
             * either the firmware wasn't accepted during self
             * test or an incorrect image was sent by the OTA
             * operator.
             */
            if( pFileContext->isInSelfTest )
            {
                OTA_LOG_L1( "[%s] In self test mode.\r\n", OTA_METHOD_NAME );

                /* Validate version of the update received.*/
                errVersionCheck = prvValidateUpdateVersion( pFileContext );

                if( otaconfigAllowDowngrade || ( errVersionCheck == OTA_ERR_NONE ) )
                {
                    /* The running firmware version is newer than the firmware that performed
                     * the update or downgrade is allowed so this means we're ready to start
                     * the self test phase.
                     *
                     * Set image state accordingly and update job status with self test identifier.
                     */
                    OTA_LOG_L1( "[%s] Setting image state to Testing for file ID %d\r\n", OTA_METHOD_NAME, otaAgent.serverFileID );

                    ( void ) setImageStateWithReason( OtaImageStateTesting, errVersionCheck );
                }
                else
                {
                    OTA_LOG_L1( "[%s] Downgrade or same version not allowed, rejecting the update & rebooting.\r\n", OTA_METHOD_NAME );
                    ( void ) setImageStateWithReason( OtaImageStateRejected, errVersionCheck );

                    /* All reject cases must reset the device. */
                    ( void ) resetDevice(); /* Ignore return code since there's nothing we can do if we can't force reset. */
                }
            }
            else
            {
                pFinalFile = getFreeContext();

                if( pFinalFile == NULL )
                {
                    OTA_LOG_L1( "[%s] Job parsing successful but no file context available, aborting.\r\n", OTA_METHOD_NAME );
                }
                else
                {
                    *pFinalFile = *pFileContext;

                    /* Everything looks OK. Set final context structure to start OTA. */
                    OTA_LOG_L1( "[%s] Job was accepted. Attempting to start transfer.\r\n", OTA_METHOD_NAME );
                }
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Error %d parsing job document.\r\n", OTA_METHOD_NAME, err );
        }
    }
    else
    { /* We have an unknown job parser error. Check to see if we can pass control to a callback for parsing */
        err = otaAgent.palCallbacks.customJobCallback( pJson, messageLength );

        if( err == OtaJobParseErrNone )
        {
            /* Custom job was parsed by external callback successfully. Grab the job name from the file
             *  context and save that in the ota agent */
            if( pFileContext->pJobName != NULL )
            {
                otaAgent.pOtaSingletonActiveJobName = pFileContext->pJobName;
                pFileContext->pJobName = NULL;
                otaErr = otaControlInterface.updateJobStatus( &otaAgent,
                                                              JobStatusSucceeded,
                                                              JobReasonAccepted,
                                                              0 );

                if( otaErr != OTA_ERR_NONE )
                {
                    OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, otaErr );
                }

                /* We don't need the job name memory anymore since we're done with this job. */
                free( otaAgent.pOtaSingletonActiveJobName );
                otaAgent.pOtaSingletonActiveJobName = NULL;
            }
            else
            {
                /* Job is malformed - return an error */
                OTA_LOG_L1( "[%s] Job does not have context or has no ID but has been processed\r\n", OTA_METHOD_NAME );
                err = OtaJobParseErrNonConformingJobDoc;
            }
        }
        else
        {
            /*Check if we received a timestamp and client token but no job ID.*/
            if( ( otaAgent.pClientTokenFromJob != NULL ) && ( otaAgent.timestampFromJob != 0 ) && ( pFileContext->pJobName == NULL ) )
            {
                /* Received job docuement with no execution so no active job is available.*/
                OTA_LOG_L1( "[%s] No active jobs available in the service for execution.\r\n", OTA_METHOD_NAME );
                err = OtaJobParseErrNoActiveJobs;
            }
            else
            {
                /* Job is malformed - return an error */
                err = OtaJobParseErrNonConformingJobDoc;
            }
        }
    }

    //assert( err != OtaJobParseErrUnknown );

    if( err != OtaJobParseErrNone )
    {
        /* If job parsing failed AND there's a job ID, update the job state to FAILED with
         * a reason code.  Without a job ID, we can't update the status in the job service. */
        if( pFileContext->pJobName != NULL )
        {
            OTA_LOG_L1( "[%s] Rejecting job due to OtaJobParseErr_t %d, JobName: %s\r\n", OTA_METHOD_NAME, err , ( char * ) pFileContext->pJobName);

            /* Assume control of the job name from the context. */
            otaAgent.pOtaSingletonActiveJobName = pFileContext->pJobName;
            pFileContext->pJobName = NULL;
            otaErr = otaControlInterface.updateJobStatus( &otaAgent,
                                                          JobStatusFailedWithVal,
                                                          ( int32_t ) OTA_ERR_JOB_PARSER_ERROR,
                                                          ( int32_t ) err );

            if( otaErr != OTA_ERR_NONE )
            {
                OTA_LOG_L2( "[%s] Failed to update job status %d\r\n", OTA_METHOD_NAME, otaErr );
            }

            /* We don't need the job name memory anymore since we're done with this job. */
            free( otaAgent.pOtaSingletonActiveJobName );
            otaAgent.pOtaSingletonActiveJobName = NULL;
        }
        else
        {
            OTA_LOG_L1( "[%s] Ignoring job without ID.\r\n", OTA_METHOD_NAME );
        }
    }

    /* If we failed, close the open files. */
    if( pFinalFile == NULL )
    {
        /* Free the current reserved file context. */
        prvOTA_FreeContext( pFileContext );

        /* Close any open files. */
        ( void ) otaClose( &otaAgent.pOtaFiles[ otaAgent.fileIndex ] );
    }

    /* Return pointer to populated file context or NULL if it failed. */
    return pFinalFile;
}


/* getFileContextFromJob
 *
 * We received an OTA update job message from the job service so process
 * the message and update the file context.
 */

static OtaFileContext_t * getFileContextFromJob( const char * pRawMsg,
                                                 uint32_t messageLength )
{
    DEFINE_OTA_METHOD_NAME( "getFileContextFromJob" );

    uint32_t index;
    uint32_t numBlocks;             /* How many data pages are in the expected update image. */
    uint32_t bitmapLen;             /* Length of the file block bitmap in bytes. */
    OtaFileContext_t * pUpdateFile; /* Pointer to an OTA update context. */
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    bool updateJob = false;

    /* Populate an OTA file context from the OTA job document. */

    pUpdateFile = parseJobDoc( pRawMsg, messageLength, &updateJob );

    if( updateJob )
    {
        OTA_LOG_L1( "[%s] We receive a job update.\r\n", OTA_METHOD_NAME );
    }

    if( ( updateJob == false ) && ( pUpdateFile != NULL ) && ( inSelftest() == false ) )
    {
        if( pUpdateFile->pRxBlockBitmap != NULL )
        {
            free( pUpdateFile->pRxBlockBitmap ); /* Free any previously allocated bitmap. */
            pUpdateFile->pRxBlockBitmap = NULL;
        }

        /* Calculate how many bytes we need in our bitmap for tracking received blocks.
         * The below calculation requires power of 2 page sizes. */

        numBlocks = ( pUpdateFile->fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
        bitmapLen = ( numBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;
        pUpdateFile->pRxBlockBitmap = ( uint8_t * ) malloc( bitmapLen ); /*lint !e9079 FreeRTOS malloc port returns void*. */

        if( pUpdateFile->pRxBlockBitmap != NULL )
        {
            /* Set all bits in the bitmap to the erased state (we use 1 for erased just like flash memory). */
            ( void ) memset( pUpdateFile->pRxBlockBitmap, ( int32_t ) OTA_ERASED_BLOCKS_VAL, bitmapLen );

            /* Mark as used any pages in the bitmap that are out of range, based on the file size.
             * This keeps us from requesting those pages during retry processing or if using a windowed
             * block request. It also avoids erroneously accepting an out of range data block should it
             * get past any safety checks.
             * Files aren't always a multiple of 8 pages (8 bits/pages per byte) so some bits of the
             * last byte may be out of range and those are the bits we want to clear. */

            uint8_t bit = 1U << ( BITS_PER_BYTE - 1U );
            uint32_t numOutOfRange = ( bitmapLen * BITS_PER_BYTE ) - numBlocks;

            for( index = 0U; index < numOutOfRange; index++ )
            {
                pUpdateFile->pRxBlockBitmap[ bitmapLen - 1U ] &= ~bit;
                bit >>= 1U;
            }

            pUpdateFile->blocksRemaining = numBlocks; /* Initialize our blocks remaining counter. */

            /* Create/Open the OTA file on the file system. */
            err = otaAgent.palCallbacks.createFileForRx( pUpdateFile );

            if( err != OTA_ERR_NONE )
            {
                ( void ) setImageStateWithReason( OtaImageStateAborted, err );
                ( void ) otaClose( pUpdateFile ); /* Ignore false result since we're setting the pointer to null on the next line. */
                pUpdateFile = NULL;
            }
        }
        else
        {
            /* Can't receive the image without enough memory. */
            ( void ) otaClose( pUpdateFile );
            pUpdateFile = NULL;
        }
    }

    return pUpdateFile; /* Return the OTA file context. */
}

/*
 * prvValidateDataBlock
 *
 * Validate the block index and size. If it is NOT the last block, it MUST be equal to a full block size.
 * If it IS the last block, it MUST be equal to the expected remainder. If the block ID is out of range,
 * that's an error.
 */
static bool prvValidateDataBlock( const OtaFileContext_t * pFileContext,
                                  uint32_t blockIndex,
                                  uint32_t blockSize )
{
    bool ret = false;
    uint32_t lastBlock = 0;

    lastBlock = ( ( pFileContext->fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE ) - 1U;

    if( ( ( blockIndex < lastBlock ) && ( blockSize == OTA_FILE_BLOCK_SIZE ) ) ||
        ( ( blockIndex == lastBlock ) && ( blockSize == ( pFileContext->fileSize - ( lastBlock * OTA_FILE_BLOCK_SIZE ) ) ) ) )
    {
        ret = true;
    }

    return ret;
}

/*
 * ingestDataBlock
 *
 * A block of file data was received by the application via some configured communication protocol.
 * If it looks like it is in range, write it to persistent storage. If it's the last block we're
 * expecting, close the file and perform the final signature check on it. If the close and signature
 * check are OK, let the caller know so it can be used by the system. Firmware updates generally
 * reboot the system and perform a self test phase. If the close or signature check fails, abort
 * the file transfer and return the result and any available details to the caller.
 */
static IngestResult_t ingestDataBlock( OtaFileContext_t * pFileContext,
                                       uint8_t * pRawMsg,
                                       uint32_t messageSize,
                                       OtaErr_t * pCloseResult )
{
    DEFINE_OTA_METHOD_NAME( "ingestDataBlock" );

    IngestResult_t eIngestResult = IngestResultUninitialized;
    int32_t lFileId = 0;
    int32_t sBlockSize = 0;
    int32_t sBlockIndex = 0;
    uint32_t uBlockSize = 0;
    uint32_t uBlockIndex = 0;
    uint8_t * pPayload = NULL;
    size_t payloadSize = 0;
    uint32_t byte = 0;
    uint8_t bitMask = 0;

    /* Check if the file context is NULL. */
    if( pFileContext == NULL )
    {
        eIngestResult = IngestResultNullContext;
    }

    /* Check if the result pointer is NULL. */
    if( eIngestResult == IngestResultUninitialized )
    {
        if( pCloseResult == NULL )
        {
            eIngestResult = IngestResultNullResultPointer;
        }
        else
        {
            /* Default to a generic ingest function error until we prove success. */
            *pCloseResult = OTA_ERR_GENERIC_INGEST_ERROR;
        }
    }

    /* Decode the received data block. */
    if( eIngestResult == IngestResultUninitialized )
    {
        /* If we have a block bitmap available then process the message. */
        if( ( pFileContext->pRxBlockBitmap != NULL ) && ( pFileContext->blocksRemaining > 0U ) )
        {
            /* Decode the file block received. */
            if( OTA_ERR_NONE != otaDataInterface.decodeFileBlock(
                    pRawMsg,
                    messageSize,
                    &lFileId,
                    &sBlockIndex,
                    &sBlockSize,
                    &pPayload,
                    &payloadSize ) )
            {
                eIngestResult = IngestResultBadData;
            }
            else
            {
                uBlockIndex = ( uint32_t ) sBlockIndex;
                uBlockSize = ( uint32_t ) sBlockSize;
            }
        }
        else
        {
            eIngestResult = IngestResultUnexpectedBlock;
        }
    }

    /* Validate the received data block.*/
    if( eIngestResult == IngestResultUninitialized )
    {
        if( prvValidateDataBlock( pFileContext, uBlockIndex, uBlockSize ) )
        {
            OTA_LOG_L1( "[%s] Received file block %u, size %u\r\n", OTA_METHOD_NAME, uBlockIndex, uBlockSize );

            /* Create bit mask for use in our bitmap. */
            bitMask = 1U << ( uBlockIndex % BITS_PER_BYTE ); /*lint !e9031 The composite expression will never be greater than BITS_PER_BYTE(8). */

            /* Calculate byte offset into bitmap. */
            byte = uBlockIndex >> LOG2_BITS_PER_BYTE;

            /* Check if we've already received this block. */
            if( ( ( pFileContext->pRxBlockBitmap[ byte ] ) & bitMask ) == 0U )
            {
                OTA_LOG_L1( "[%s] block %u is a DUPLICATE. %u blocks remaining.\r\n", OTA_METHOD_NAME,
                            uBlockIndex,
                            pFileContext->blocksRemaining );

                eIngestResult = IngestResultDuplicate_Continue;
                *pCloseResult = OTA_ERR_NONE; /* This is a success path. */
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Error! Block %u out of expected range! Size %u\r\n", OTA_METHOD_NAME, uBlockIndex, uBlockSize );
            eIngestResult = IngestResultBlockOutOfRange;
        }
    }

    /* Process the received data block. */
    if( eIngestResult == IngestResultUninitialized )
    {
        if( pFileContext->pFile != NULL )
        {
            int32_t iBytesWritten = otaAgent.palCallbacks.writeBlock( pFileContext, ( uBlockIndex * OTA_FILE_BLOCK_SIZE ), pPayload, uBlockSize );

            if( iBytesWritten < 0 )
            {
                OTA_LOG_L1( "[%s] Error (%d) writing file block\r\n", OTA_METHOD_NAME, iBytesWritten );
                eIngestResult = IngestResultWriteBlockFailed;
            }
            else
            {
                pFileContext->pRxBlockBitmap[ byte ] &= ~bitMask; /* Mark this block as received in our bitmap. */
                pFileContext->blocksRemaining--;
                eIngestResult = IngestResultAccepted_Continue;
                *pCloseResult = OTA_ERR_NONE;
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Error: Unable to write block, file handle is NULL.\r\n", OTA_METHOD_NAME );
            eIngestResult = IngestResultBadFileHandle;
        }
    }

    /* Close the file and cleanup.*/
    if( eIngestResult == IngestResultAccepted_Continue )
    {
        if( pFileContext->blocksRemaining == 0U )
        {
            OTA_LOG_L1( "[%s] Received final expected block of file.\r\n", OTA_METHOD_NAME );

            free( pFileContext->pRxBlockBitmap ); /* Free the bitmap now that we're done with the download. */
            pFileContext->pRxBlockBitmap = NULL;

            if( pFileContext->pFile != NULL )
            {
                *pCloseResult = otaAgent.palCallbacks.closeFile( pFileContext );

                if( *pCloseResult == OTA_ERR_NONE )
                {
                    OTA_LOG_L1( "[%s] File receive complete and signature is valid.\r\n", OTA_METHOD_NAME );
                    eIngestResult = IngestResultFileComplete;
                }
                else
                {
                    uint32_t closeResult = ( uint32_t ) *pCloseResult;

                    OTA_LOG_L1( "[%s] Error (%u:0x%06x) closing OTA file.\r\n",
                                OTA_METHOD_NAME,
                                closeResult >> OTA_MAIN_ERR_SHIFT_DOWN_BITS,
                                closeResult & ( uint32_t ) OTA_PAL_ERR_MASK );

                    if( ( ( closeResult ) & ( OTA_MAIN_ERR_MASK ) ) == OTA_ERR_SIGNATURE_CHECK_FAILED )
                    {
                        eIngestResult = IngestResultSigCheckFail;
                    }
                    else
                    {
                        eIngestResult = IngestResultFileCloseFail;
                    }
                }

                pFileContext->pFile = NULL; /* File is now closed so clear the file handle in the context. */
            }
            else
            {
                OTA_LOG_L1( "[%s] Error: File handle is NULL after last block received.\r\n", OTA_METHOD_NAME );
                eIngestResult = IngestResultBadFileHandle;
            }
        }
        else
        {
            OTA_LOG_L1( "[%s] Remaining: %u\r\n", OTA_METHOD_NAME, pFileContext->blocksRemaining );
        }
    }

    return eIngestResult;
}

/*
 * Clean up after the OTA process is done. Possibly free memory for re-use.
 */
static void agentShutdownCleanup( void )
{
    DEFINE_OTA_METHOD_NAME( "agentShutdownCleanup" );

    uint32_t index;

    otaAgent.state = OtaAgentStateShuttingDown;

    /*
     * Stop and delete any existing self test timer.
     */
    /*if( otaAgent.pvSelfTestTimer != NULL )
    {
        ( void ) xTimerStop( otaAgent.pvSelfTestTimer, 0 );
        ( void ) xTimerDelete( otaAgent.pvSelfTestTimer, 0 );
        otaAgent.pvSelfTestTimer = NULL;
    }*/

    /*
     * Stop and delete any existing transfer request timer.
     */
    /*if( otaAgent.xRequestTimer != NULL )
    {
        ( void ) xTimerStop( otaAgent.xRequestTimer, 0 );
        ( void ) xTimerDelete( otaAgent.xRequestTimer, 0 );
        otaAgent.xRequestTimer = NULL;
    }*/

    /* Cleanup related to selected protocol. */
    if( otaDataInterface.cleanup != NULL )
    {
        ( void ) otaDataInterface.cleanup( &otaAgent );
    }

    /*
     * Close any open OTA transfers.
     */
    for( index = 0; index < OTA_MAX_FILES; index++ )
    {
        ( void ) otaClose( &otaAgent.pOtaFiles[ index ] );
    }

    /*
     * Free any remaining string memory holding the job name.
     */
    if( otaAgent.pOtaSingletonActiveJobName != NULL )
    {
        free( otaAgent.pOtaSingletonActiveJobName );
        otaAgent.pOtaSingletonActiveJobName = NULL;
    }

    /* Delete the OTA Agent Queue.*/
   /* if( otaAgent.xOTA_EventQueue != NULL )
    {
        vQueueDelete( otaAgent.xOTA_EventQueue );
    }*/

    /*
     * Free OTA event buffers.
     */
    for( index = 0; index < otaconfigMAX_NUM_OTA_DATA_BUFFERS; index++ )
    {
        pEventBuffer[ index ].bufferUsed = false;
    }

    /* Delete the semaphore.*/
    /*if( otaAgent.xOTA_ThreadSafetyMutex != NULL )
    {
        sem_destroy(&otaAgent.otaBufferSem);
    }*/
}

/*
 * Handle any events that were unexpected in the current state.
 */
static void handleUnexpectedEvents( OtaEventMsg_t * pEventMsg )
{
    DEFINE_OTA_METHOD_NAME( "handleUnexpectedEvents" );

    //configASSERT( pEventMsg );

    OTA_LOG_L1( "[%s] Unexpected Event. Current State [%s] Received Event  [%s] \n",
                OTA_METHOD_NAME,
                pOtaAgentStateStrings[ otaAgent.state ],
                pOtaEventStrings[ pEventMsg->eventId ] );

    /* Perform any cleanup operations required for specifc unhandled events.*/
    switch( pEventMsg->eventId )
    {
        case OtaAgentEventReceivedJobDocument:

            /* Received job event is not handled , release the buffer.*/
            otaEventBufferFree( pEventMsg->pEventData );

            break;

        case OtaAgentEventReceivedFileBlock:

            /* Received file data event is not handled , release the buffer.*/
            otaEventBufferFree( pEventMsg->pEventData );

            break;

        default:

            /* Nothing to do here.*/
            break;
    }
}

/*
 * Execute the handler for selected index from the transition table.
 */
static void executeHandler( uint32_t index,
                            const OtaEventMsg_t * const pEventMsg )
{
    DEFINE_OTA_METHOD_NAME( "executeHandler" );

    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    if( otaTransitionTable[ index ].handler )
    {
        err = otaTransitionTable[ index ].handler( pEventMsg->pEventData );

        if( err == OTA_ERR_NONE )
        {
            OTA_LOG_L1( "[%s] Called handler. Current State [%s] Event [%s] New state [%s] \n",
                        OTA_METHOD_NAME,
                        pOtaAgentStateStrings[ otaAgent.state ],
                        pOtaEventStrings[ pEventMsg->eventId ],
                        pOtaAgentStateStrings[ otaTransitionTable[ index ].nextState ] );

            /*
             * Update the current state in OTA agent context.
             */
            otaAgent.state = otaTransitionTable[ index ].nextState;
        }
        else
        {
            OTA_LOG_L1( "[%s] Handler failed. Current State [%s] Event  [%s] Error Code [%d] \n",
                        OTA_METHOD_NAME,
                        pOtaAgentStateStrings[ otaAgent.state ],
                        pOtaEventStrings[ pEventMsg->eventId ],
                        err );
        }
    }
}

void otaAgentTask( void * pUnused )
{
    DEFINE_OTA_METHOD_NAME( "otaAgentTask" );

    ( void ) pUnused;

    OtaEventMsg_t eventMsg = { 0 };
    uint32_t transitionTableLen = sizeof( otaTransitionTable ) / sizeof( otaTransitionTable[ 0 ] );
    uint32_t i = 0;

    /*
     * OTA Agent is ready to receive and process events so update the state to ready.
     */
    otaAgent.state = OtaAgentStateReady;

    for( ; ; )
    {
        /*
         * Receive the next event form the OTA event queue to process.
         */
        if( otaAgent.pOTAOSCtx->event.recv( otaAgent.pOTAOSCtx->event.pContext, &eventMsg, 0 )  == OTA_ERR_NONE )
        {
            /*
             * Search for the state and event from the table.
             */
            for( i = 0; i < transitionTableLen; i++ )
            {
                if( ( ( otaTransitionTable[ i ].currentState == otaAgent.state ) ||
                      ( otaTransitionTable[ i ].currentState == OtaAgentStateAll ) ) &&
                    ( otaTransitionTable[ i ].eventId == eventMsg.eventId ) )
                {
                    OTA_LOG_L3( "[%s] , State matched [%s],  Event matched  [%s]\n",
                                OTA_METHOD_NAME,
                                pOtaAgentStateStrings[ i ]
                                pOtaEventStrings[ i ] );

                    /*
                     * Execute the handler function.
                     */
                    executeHandler( i, &eventMsg );
                    break;
                }
            }

            if( i == transitionTableLen )
            {
                /*
                 * Handle unexpected events.
                 */
                handleUnexpectedEvents( &eventMsg );
            }
        }
    }
}

static BaseType_t startOTAAgentTask( void * pConnectionContext,
                                     void * pOTAOSCtx,
                                     void * pOtaMqttInterface,
                                     uint32_t ticksToWait )
{
    BaseType_t retVal = 0;
    uint32_t index = 0;
    int ret = 0;

    /*
     * The actual OTA Task and queue control structure. Only created once.
     */
    pthread_t otaThreadHandle;

    /*
     * The current OTA image state as set by the OTA agent.
     */
    otaAgent.imageState = OtaImageStateUnknown;

    /*
     * Save the current connection context provided by the user.
     */
    otaAgent.pConnectionContext = pConnectionContext;

    otaAgent.pOTAOSCtx = ( OtaOSInterface_t * ) pOTAOSCtx;

    otaAgent.pOTAOSCtx->event.init( otaAgent.pOTAOSCtx->event.pContext );

    otaAgent.pOTAMqttInterface = pOtaMqttInterface;

    /*
     * Initialize all file paths to NULL.
     */
    for( index = 0; index < OTA_MAX_FILES; index++ )
    {
        otaAgent.pOtaFiles[ index ].pFilePath = NULL;
    }

    /*
     * Make sure OTA event buffers are clear.
     */
    for( index = 0; index < otaconfigMAX_NUM_OTA_DATA_BUFFERS; index++ )
    {
        pEventBuffer[ index ].bufferUsed = false;
    }

    return retVal;
}

bool OTA_SignalEvent( const OtaEventMsg_t * const pEventMsg )
{
    DEFINE_OTA_METHOD_NAME( "OTA_SignalEvent" );

    bool retVal = false;
    BaseType_t err = 0;

    /*
     * Send event to back of the queue.
     */
    {
        err = otaAgent.pOTAOSCtx->event.send( otaAgent.pOTAOSCtx->event.pContext,
                                              pEventMsg,
                                              0 );
    }

    if( err == 0 )
    {
        retVal = true;
        OTA_LOG_L3( "Success: Pushed event message to queue.\r\n" );
    }
    else
    {
        retVal = false;
        OTA_LOG_L1( "Error: Could not push event message to queue.\r\n" );
    }

    return retVal;
}

/*
 * Public API to initialize the OTA Agent.
 *
 * If the Application calls OTA_AgentInit() after it is already initialized, we will
 * only reset the statistics counters and set the job complete callback but will not
 * modify the existing OTA agent context. You must first call OTA_AgentShutdown()
 * successfully.
 */
OtaState_t OTA_AgentInit( void * pConnectionContext,
                          void * pOtaOSCtx,
                          void * pOtaMqttInterface,
                          const uint8_t * pThingName,
                          OtaCompleteCallback_t completeCallback,
                          uint32_t ticksToWait )
{
    OtaState_t state;

    if( otaAgent.state == OtaAgentStateStopped )
    {
        /* Init default OTA pal callbacks. */
        OtaPalCallbacks_t palCallbacks = OTA_JOB_CALLBACK_DEFAULT_INITIALIZER;

        /* Set the OTA complete callback. */
        palCallbacks.completeCallback = completeCallback;

        state = OTA_AgentInit_internal( pConnectionContext, pOtaOSCtx, pOtaMqttInterface  , pThingName, &palCallbacks, ticksToWait );
    }
    /* If OTA agent is already running, just update the CompleteCallback and reset the statistics. */
    else
    {
        if( completeCallback != NULL )
        {
            otaAgent.palCallbacks.completeCallback = completeCallback;
        }

        ( void ) memset( &otaAgent.statistics, 0, sizeof( otaAgent.statistics ) );
        state = otaAgent.state;
    }

    return state;
}

OtaState_t OTA_AgentInit_internal( void * pConnectionContext,
                                   void * pOtaOSCtx,
                                   void * pOtaMqttInterface,
                                   const uint8_t * pThingName,
                                   const OtaPalCallbacks_t * pCallbacks,
                                   uint32_t ticksToWait )
{
    DEFINE_OTA_METHOD_NAME( "OTA_AgentInit_internal" );

    BaseType_t retVal = 0;
    OtaEventMsg_t eventMsg = { 0 };

    /*
     * OTA Task is not running yet so update the state to init direclty in OTA context.
     */
    otaAgent.state = OtaAgentStateInit;

    /*
     * Check all the callbacks for null values and initialize the values in the ota agent context.
     * The OTA agent context is initialized with the prvPAL values. So, if null is passed in, don't
     * do anything and just use the defaults in the OTA structure.
     */
    prvSetPALCallbacks( pCallbacks );

    /*
     * Initialize the OTA control interface based on the application protocol
     * selected.
     */
    setControlInterface( &otaControlInterface );

    /*
     * Reset all the statistics counters.
     */
    otaAgent.statistics.otaPacketsReceived = 0;
    otaAgent.statistics.otaPacketsDropped = 0;
    otaAgent.statistics.otaPacketsQueued = 0;
    otaAgent.statistics.otaPacketsProcessed = 0;

    if( pThingName == NULL )
    {
        OTA_LOG_L1( "[%s]Error: Thing name is NULL.\r\n", OTA_METHOD_NAME );
    }
    else
    {
        uint32_t strLength = strlen( ( const char * ) pThingName );

        if( strLength <= otaconfigMAX_THINGNAME_LEN )
        {
            /*
             * Store the Thing name to be used for topics later.
             */
            ( void ) memcpy( otaAgent.pThingName, pThingName, strLength + 1UL ); /* Include zero terminator when saving the Thing name. */
        }

        retVal = startOTAAgentTask( pConnectionContext, pOtaOSCtx, pOtaMqttInterface, ticksToWait );
    }

    if( otaAgent.state == OtaAgentStateReady )
    {
        OTA_LOG_L1( "[%s] OTA Task is Ready.\r\n", OTA_METHOD_NAME );

        /*
         * OTA agent is ready so send event to start update process.
         */
        eventMsg.eventId = OtaAgentEventStart;

        /* Send signal to OTA task. */
        if( !OTA_SignalEvent( &eventMsg ) )
        {
            OTA_LOG_L1( "[%s] Failed to signal the OTA agent to start.", OTA_METHOD_NAME );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Failed to start the OTA Task, Error Code :%08x\r\n", OTA_METHOD_NAME, retVal );

        otaAgent.state = OtaAgentStateStopped;
    }

    /* Return status of agent. */
    return otaAgent.state;
}

/*
 * Public API to shutdown the OTA Agent.
 */
OtaState_t OTA_AgentShutdown( uint32_t ticksToWait )
{
    DEFINE_OTA_METHOD_NAME( "OTA_AgentShutdown" );

    OtaEventMsg_t eventMsg = { 0 };

    OTA_LOG_L2( "[%s] Start: %u ticks\r\n", OTA_METHOD_NAME, ticksToWait );

    if( ( otaAgent.state != OtaAgentStateStopped ) && ( otaAgent.state != OtaAgentStateShuttingDown ) )
    {
        /*
         * Send shutdown signal to OTA Agent task.
         */
        eventMsg.eventId = OtaAgentEventShutdown;

        /* Send signal to OTA task. */
        if( !OTA_SignalEvent( &eventMsg ) )
        {
            OTA_LOG_L1( "[%s] Failed to signal the OTA agent to shutdown.", OTA_METHOD_NAME );
        }
        else
        {
            /*
             * Wait for the OTA agent to complete shutdown, if requested.
             */
            while( ( ticksToWait > 0U ) && ( otaAgent.state != OtaAgentStateStopped ) )
            {
                //vTaskDelay( 1 );
                ticksToWait--;
            }
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Nothing to do: Already in state [%s]\r\n", OTA_METHOD_NAME, pOtaAgentStateStrings[ otaAgent.state ] );
    }

    OTA_LOG_L2( "[%s] End: %u ticks\r\n", OTA_METHOD_NAME, ticksToWait );

    return otaAgent.state;
}

/*
 * Return the current state of the OTA agent.
 */
OtaState_t OTA_GetAgentState( void )
{
    return otaAgent.state;
}

/*
 * Return the number of packets dropped.
 */
uint32_t OTA_GetPacketsDropped( void )
{
    return otaAgent.statistics.otaPacketsDropped;
}

/*
 * Return the number of packets queued.
 */
uint32_t OTA_GetPacketsQueued( void )
{
    return otaAgent.statistics.otaPacketsQueued;
}

/*
 * Return the number of packets processed.
 */
uint32_t OTA_GetPacketsProcessed( void )
{
    return otaAgent.statistics.otaPacketsProcessed;
}

/*
 * Return the number of packets received.
 */
uint32_t OTA_GetPacketsReceived( void )
{
    return otaAgent.statistics.otaPacketsReceived;
}

OtaErr_t OTA_CheckForUpdate( void )
{
    DEFINE_OTA_METHOD_NAME( "OTA_CheckForUpdate" );

    OtaErr_t retVal = OTA_ERR_NONE;
    OtaEventMsg_t eventMsg = { 0 };

    OTA_LOG_L1( "[%s] Sending event to check for update.\r\n", OTA_METHOD_NAME );

    /*
     * Send event to get OTA job document.
     */
    eventMsg.eventId = OtaAgentEventRequestJobDocument;

    if( !OTA_SignalEvent( &eventMsg ) )
    {
        retVal = OTA_ERR_EVENT_Q_SEND_FAILED;
    }

    /*
     * The event will be processed later so return OTA_ERR_NONE.
     */
    return retVal;
}

/*
 * This should be called by the user application or the default OTA callback handler
 * after an OTA update is considered accepted. It simply calls the platform specific
 * code required to activate the received OTA update (usually just a device reset).
 */
OtaErr_t OTA_ActivateNewImage( void )
{
    DEFINE_OTA_METHOD_NAME( "OTA_ActivateNewImage" );

    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    /*
     * Call platform specific code to activate the image. This should reset the device
     * and not return unless there is a problem within the PAL layer. If it does return,
     * output an error message. The device may need to be reset manually.
     */
    if( otaAgent.palCallbacks.activateNewImage != NULL )
    {
        err = otaAgent.palCallbacks.activateNewImage( otaAgent.serverFileID );
    }

    OTA_LOG_L1( "[%s] Error: Failed to activate new image, Error code - (0x%08x). Please reset manually.\r\n", OTA_METHOD_NAME, err );

    return err;
}

/*
 * Accept, reject or abort the OTA image transfer.
 *
 * If accepting or rejecting an image transfer, this API
 * will set the OTA image state and update the job status
 * appropriately.
 * If aborting a transfer, it will trigger the OTA task to
 * abort via an RTOS event asynchronously and therefore do
 * not set the image state here.
 *
 * NOTE: This call may block due to the status update message.
 */

OtaErr_t OTA_SetImageState( OtaImageState_t eState )
{
    DEFINE_OTA_METHOD_NAME( "OTA_SetImageState" );

    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    switch( eState )
    {
        case OtaImageStateAborted:

            if( 1 /*otaAgent.xOTA_EventQueue != NULL*/ )
            {
                eventMsg.eventId = OtaAgentEventUserAbort;

                /*
                 * Send the event, otaAgent.imageState will be set later when the event is processed.
                 */
                err = OTA_SignalEvent( &eventMsg ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
            }
            else
            {
                OTA_LOG_L1( "[%s] Error: OTA event queue is not initialized.\r\n", OTA_METHOD_NAME );

                err = OTA_ERR_PANIC;
            }

            break;

        case OtaImageStateRejected:

            /*
             * Set the image state as rejected.
             */
            err = setImageStateWithReason( eState, 0 );

            break;

        case OtaImageStateAccepted:

            /*
             * Set the image state as accepted.
             */
            err = setImageStateWithReason( eState, 0 );

            break;

        default:

            /*lint -e788 Keep lint quiet about the obvious unused states we're catching here. */
            err = OTA_ERR_BAD_IMAGE_STATE;

            break;
    }

    return err;
}

OtaImageState_t OTA_GetImageState( void )
{
    /*
     * Return the current OTA image state.
     */
    return otaAgent.imageState;
}

/*
 * Suspend OTA Agent task.
 */
OtaErr_t OTA_Suspend( void )
{
    DEFINE_OTA_METHOD_NAME( "OTA_Suspend" );

    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    /* Check if OTA Agent is running. */
    if( otaAgent.state != OtaAgentStateStopped )
    {
        /*
         * Send event to OTA agent task.
         */
        eventMsg.eventId = OtaAgentEventSuspend;
        err = OTA_SignalEvent( &eventMsg ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
    }
    else
    {
        OTA_LOG_L1( "[%s] Error: OTA Agent is not running, cannot suspend.\r\n", OTA_METHOD_NAME );

        err = OTA_ERR_OTA_AGENT_STOPPED;
    }

    return err;
}

/*
 * Resume OTA Agent task.
 */
OtaErr_t OTA_Resume( void * pConnection )
{
    DEFINE_OTA_METHOD_NAME( "OTA_Resume" );

    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    eventMsg.pEventData = pConnection;

    /* Check if OTA Agent is running. */
    if( otaAgent.state != OtaAgentStateStopped )
    {
        /*
         * Send event to OTA agent task.
         */
        eventMsg.eventId = OtaAgentEventResume;
        err = OTA_SignalEvent( &eventMsg ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
    }
    else
    {
        OTA_LOG_L1( "[%s] Error: OTA Agent is not running, cannot resume.\r\n", OTA_METHOD_NAME );

        err = OTA_ERR_OTA_AGENT_STOPPED;
    }

    return err;
}

/*-----------------------------------------------------------*/
