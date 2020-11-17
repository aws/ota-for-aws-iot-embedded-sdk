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
#include <errno.h>

/* OTA agent includes. */
#include "ota.h"

/* OTA_DO_NOT_USE_CUSTOM_CONFIG allows building the OTA library
 * without a custom config. If a custom config is provided, the
 * OTA_DO_NOT_USE_CUSTOM_CONFIG macro should not be defined. */
#ifndef OTA_DO_NOT_USE_CUSTOM_CONFIG
    #include "ota_config.h"
#endif

/* Include config defaults header to get default values of configs not defined
 * in ota_config.h file. */
#include "ota_config_defaults.h"

/* OTA Base64 includes */
#include "ota_base64_private.h"

/* OTA pal includes. */
#include "ota_platform_interface.h"

/* Internal header file for shared OTA definitions. */
#include "ota_private.h"

/* OTA interface includes. */
#include "ota_interface_private.h"

/* OTA OS interface. */
#include "ota_os_interface.h"

/* Core JSON include */
#include "core_json.h"

/* Include firmware version struct definition. */
#include "ota_appversion32.h"

/* ToDo: Cleanup BaseType_t. */
#define BaseType_t    uint32_t

/* OTA event handler definition. */

typedef OtaErr_t ( * OtaEventHandler_t )( OtaEventData_t * pEventMsg );

/**
 * @ingroup ota_datatypes_structs
 * @brief OTA Agent state table entry.
 * */

typedef struct OtaStateTableEntry
{
    OtaState_t currentState;   /**< Current state of the agent. */
    OtaEvent_t eventId;        /**< Event corresponding to the action. */
    OtaEventHandler_t handler; /**< Handler to invoke the next action. */
    OtaState_t nextState;      /**< New state to be triggered*/
} OtaStateTableEntry_t;

/* OTA control interface. */

static OtaControlInterface_t otaControlInterface;

/* OTA data interface. */

static OtaDataInterface_t otaDataInterface;

/* OTA agent private function prototypes. */

/* Called when the OTA agent receives a file data block message. */

static IngestResult_t ingestDataBlock( OtaFileContext_t * pFileContext,
                                       uint8_t * pRawMsg,
                                       uint32_t messageSize,
                                       OtaErr_t * pCloseResult );

/* Validate the incoming data block and store it in the file context. */

static IngestResult_t processDataBlock( OtaFileContext_t * pFileContext,
                                        uint32_t uBlockIndex,
                                        uint32_t uBlockSize,
                                        OtaErr_t * pCloseResult,
                                        uint8_t * pPayload );

/* Free the resources allocated for data ingestion and close the file handle. */

static IngestResult_t ingestDataBlockCleanup( OtaFileContext_t * pFileContext,
                                              OtaErr_t * pCloseResult );

/* Called to update the filecontext structure from the job. */

static OtaFileContext_t * getFileContextFromJob( const char * pRawMsg,
                                                 uint32_t messageLength );

/* Get an available OTA file context structure or NULL if none available. */

static OtaFileContext_t * getFreeContext( void );

/* Validate JSON document */

static DocParseErr_t validateJSON( const char * pJson,
                                   uint32_t messageLength );

/* Checks for duplicate entries in the JSON document. */

static DocParseErr_t checkDuplicates( uint32_t * paramsReceivedBitmap,
                                      uint16_t paramIndex );

/* Store the parameter from the json to the offset specified by the document model. */

static DocParseErr_t extractParameter( JsonDocParam_t docParam,
                                       void * modelContextBase,
                                       char * pValueInJson,
                                       size_t valueLength );

/* Parse a JSON document using the specified document model. */

static DocParseErr_t parseJSONbyModel( const char * pJson,
                                       uint32_t messageLength,
                                       JsonDocModel_t * pDocModel );

/* Decode the signature key from the job document and store it.*/

static DocParseErr_t decodeAndStoreKey( char * pValueInJson,
                                        size_t valueLength,
                                        void ** ppvParamAdd );

/* Check if all the required parameters for the job are present in the JSON. */

static DocParseErr_t verifyRequiredParamsExtracted( const JsonDocParam_t * pModelParam,
                                                    const JsonDocModel_t * pDocModel );

/* Validate the version of the update received. */
static OtaErr_t validateUpdateVersion( const OtaFileContext_t * pFileContext );

/* Check if the JSON can be parsed through a custom callback if initial parsing fails. */

static OtaJobParseErr_t parseJobDocFromCustomCallback( const char * pJson,
                                                       uint32_t messageLength,
                                                       OtaFileContext_t * pFileContext );

/* Check if the incoming job document is not conflicting with current job status. */

static OtaJobParseErr_t verifyActiveJobStatus( OtaFileContext_t * pFileContext,
                                               OtaFileContext_t ** pFinalFile,
                                               bool * pUpdateJob );

/* Check if all the file context params are valid and initialize resources for the job transfer */

static OtaJobParseErr_t validateAndStartJob( OtaFileContext_t * pFileContext,
                                             OtaFileContext_t ** pFinalFile,
                                             bool * pUpdateJob );

/* Parse the OTA job document, validate and return the populated OTA context if valid. */

static OtaFileContext_t * parseJobDoc( const char * pJson,
                                       uint32_t messageLength,
                                       bool * pUpdateJob );

/* Close an open OTA file context and free it. */

static bool otaClose( OtaFileContext_t * const pFileContext );


/* Internal function to set the image state including an optional reason code. */

static OtaErr_t setImageStateWithReason( OtaImageState_t stateToSet,
                                         uint32_t reasonToSet );

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
                                   void * contextBaseAddr,
                                   uint32_t contextSize,
                                   uint16_t numJobParams );

/* Check if the platform is in self-test. */

static bool inSelftest( void );

/* Function to handle events that were unexpected in the current state. */

static void handleUnexpectedEvents( const OtaEventMsg_t * pEventMsg );

/* OTA state event handler functions. */

static OtaErr_t startHandler( const OtaEventData_t * pEventData );
static OtaErr_t requestJobHandler( const OtaEventData_t * pEventData );
static OtaErr_t processJobHandler( OtaEventData_t * pEventData );
static OtaErr_t inSelfTestHandler( const OtaEventData_t * pEventData );
static OtaErr_t initFileHandler( const OtaEventData_t * pEventData );
static OtaErr_t processDataHandler( OtaEventData_t * pEventData );
static OtaErr_t requestDataHandler( const OtaEventData_t * pEventData );
static OtaErr_t shutdownHandler( const OtaEventData_t * pEventData );
static OtaErr_t closeFileHandler( const OtaEventData_t * pEventData );
static OtaErr_t userAbortHandler( const OtaEventData_t * pEventData );
static OtaErr_t suspendHandler( const OtaEventData_t * pEventData );
static OtaErr_t resumeHandler( OtaEventData_t * pEventData );
static OtaErr_t jobNotificationHandler( const OtaEventData_t * pEventData );

/* OTA default callback initializer. */

#define OTA_JOB_CALLBACK_DEFAULT_INITIALIZER                      \
    {                                                             \
        .abortUpdate = prvPAL_Abort,                              \
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
    .fileContext                = { 0 },  /*lint !e910 !e9080 Zero initialization of all members of the single file context structure.*/
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

static void otaTimerCallback( OtaTimerId_t otaTimerId )
{
    if( otaTimerId == OtaRequestTimer )
    {
        OtaEventMsg_t xEventMsg = { 0 };

        LogDebug( ( "Self-test expired within %ums\r\n",
                    otaconfigFILE_REQUEST_WAIT_MS ) );

        xEventMsg.eventId = OtaAgentEventRequestTimer;

        /* Send job document received event. */
        OTA_SignalEvent( &xEventMsg );
    }
    else if( otaTimerId == OtaSelfTestTimer )
    {
        LogError( ( "Self test failed to complete within %ums\r\n",
                    otaconfigSELF_TEST_RESPONSE_WAIT_MS ) );

        ( void ) otaAgent.palCallbacks.resetDevice( otaAgent.serverFileID );
    }
    else
    {
        LogWarn( ( "Invalid ota timer id: "
                   "otaTimerId=%u",
                   otaTimerId ) );
    }
}

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

static OtaErr_t updateJobStatusFromImageState( OtaImageState_t state,
                                               int32_t subReason )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    int32_t reason = 0;

    if( state == OtaImageStateTesting )
    {
        /* We discovered we're ready for test mode, put job status in self_test active. */
        err = otaControlInterface.updateJobStatus( &otaAgent,
                                                   JobStatusInProgress,
                                                   JobReasonSelfTestActive,
                                                   0 );
    }
    else
    {
        if( state == OtaImageStateAccepted )
        {
            /* Now that we have accepted the firmware update, we can complete the job. */
            err = otaControlInterface.updateJobStatus( &otaAgent,
                                                       JobStatusSucceeded,
                                                       JobReasonAccepted,
                                                       appFirmwareVersion.u.signedVersion32 );
        }
        else
        {
            /*
             * The firmware update was either rejected or aborted, complete the job as FAILED (Job service
             * will not allow us to set REJECTED after the job has been started already).
             */
            reason = ( state == OtaImageStateRejected ) ? JobReasonRejected : JobReasonAborted;
            err = otaControlInterface.updateJobStatus( &otaAgent,
                                                       JobStatusFailed,
                                                       reason,
                                                       subReason );
        }

        /*
         * We don't need the job name memory anymore since we're done with this job.
         */
        otaAgent.pOtaInterface->os.mem.free( otaAgent.pOtaSingletonActiveJobName );
        otaAgent.pOtaSingletonActiveJobName = NULL;
    }

    return err;
}

static OtaErr_t setImageStateWithReason( OtaImageState_t stateToSet,
                                         uint32_t reasonToSet )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaImageState_t state = stateToSet;
    uint32_t reason = reasonToSet;

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

    if( err != OTA_ERR_NONE )
    {
        LogWarn( ( "Failed to set image state with reason: "
                   "OtaErr_t=%u"
                   ", state=%d"
                   ", reason=%d",
                   err,
                   stateToSet,
                   reasonToSet ) );
    }

    return err;
}

static OtaErr_t palDefaultResetDevice( uint32_t serverFileID )
{
    ( void ) serverFileID;
    return prvPAL_ResetDevice( &(otaAgent.fileContext) );
}

static OtaPalImageState_t palDefaultGetPlatformImageState( uint32_t serverFileID )
{
    ( void ) serverFileID;
    return prvPAL_GetPlatformImageState( &(otaAgent.fileContext) );
}

static OtaErr_t palDefaultSetPlatformImageState( uint32_t serverFileID,
                                                 OtaImageState_t state )
{
    ( void ) serverFileID;
    ( void ) state;
    return prvPAL_SetPlatformImageState( &(otaAgent.fileContext) , state );
}

static OtaErr_t palDefaultActivateNewImage( uint32_t serverFileID )
{
    ( void ) serverFileID;
    return prvPAL_ActivateNewImage( &(otaAgent.fileContext) );
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
 * If the update was rejected, just return without doing anything and agent will
 * wait for another job. If it reported that we're in self test mode, we have
 * already successfully connected to the AWS IoT broker and received the
 * latest job so go ahead and set the image as accepted since there is no
 * additional user level tests to run.
 */
static void defaultOTACompleteCallback( OtaJobEvent_t event )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    if( event == OtaJobEventActivate )
    {
        LogInfo( ( "New image has been received and authenticated."
                   " Activating image. " ) );

        err = OTA_ActivateNewImage();

        if( err != OTA_ERR_NONE )
        {
            LogError( ( "Failed to activate new image: "
                        "OTA_ActivateNewImage returned error: "
                        "OtaErr_t=%u",
                        err ) );
        }
    }
    else if( event == OtaJobEventFail )
    {
        LogWarn( ( "Unable to complete the OTA job: "
                   "Received OTA job event OTAJobEventFail" ) );
        /* Nothing special to do. The OTA agent handles it. */
    }
    else if( event == OtaJobEventStartTest )
    {
        /* Accept the image since it was a good transfer
         * and networking and services are all working.
         */
        LogInfo( ( "New image has been activated. Beginning self test." ) );
        err = OTA_SetImageState( OtaImageStateAccepted );

        if( err != OTA_ERR_NONE )
        {
            LogError( ( "Failed to set image state: "
                        "OtaErr_t=%u"
                        ", state=%d",
                        err,
                        OtaImageStateAccepted ) );
        }
    }
    else
    {
        LogWarn( ( "Received invalid job event: "
                   "event=%d",
                   event ) );
    }
}

static OtaJobParseErr_t defaultCustomJobCallback( const char * pJson,
                                                  uint32_t messageLength )
{
    ( void ) messageLength;
    ( void ) pJson;

    /*
     * The JOB document received is not conforming to AFR OTA job document and it could be a
     * custom OTA job. No application callback for handling custom job document is registered so just
     * return error code for non conforming job document from this default handler.
     */
    LogWarn( ( "Received unsupported custom job document: "
               "Missing custom job callback for handling the job document." ) );

    return OtaJobParseErrNonConformingJobDoc;
}

static void setPALCallbacks( const OtaPalCallbacks_t * pCallbacks )
{
    if( pCallbacks->abortUpdate != NULL )
    {
        otaAgent.palCallbacks.abortUpdate = pCallbacks->abortUpdate;
    }
    else
    {
        otaAgent.palCallbacks.abortUpdate = prvPAL_Abort;
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

static OtaErr_t startHandler( const OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaErr_t retVal = OTA_ERR_NONE;
    OtaEventMsg_t eventMsg = { 0 };

    /* Start self-test timer, if platform is in self-test. */
    if( inSelftest() == true )
    {
        otaAgent.pOtaInterface->os.timer.start( OtaSelfTestTimer,
                                                "OtaSelfTestTimer",
                                                otaconfigSELF_TEST_RESPONSE_WAIT_MS,
                                                otaTimerCallback );
    }

    /* Send event to OTA task to get job document. */
    eventMsg.eventId = OtaAgentEventRequestJobDocument;

    if( OTA_SignalEvent( &eventMsg ) == false )
    {
        retVal = OTA_ERR_EVENT_Q_SEND_FAILED;
    }

    return retVal;
}

static OtaErr_t inSelfTestHandler( const OtaEventData_t * pEventData )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    ( void ) pEventData;

    LogInfo( ( "Beginning self-test." ) );

    /* Check the platform's OTA update image state. It should also be in self test. */
    if( inSelftest() == true )
    {
        /* Callback for application specific self-test. */
        err = OTA_ERR_NONE;
        otaAgent.palCallbacks.completeCallback( OtaJobEventStartTest );
    }
    else
    {
        /* The job is in self test but the platform image state is not so it could be
         * an attack on the platform image state. Reject the update (this should also
         * cause the image to be erased), aborting the job and reset the device. */
        LogWarn( ( "Rejecting new image and rebooting:"
                   "The job is in the self-test state while the platform is not." ) );

        err = setImageStateWithReason( OtaImageStateRejected, OTA_ERR_IMAGE_STATE_MISMATCH );
        ( void ) otaAgent.palCallbacks.resetDevice( otaAgent.serverFileID );
    }

    if( err != OTA_ERR_NONE )
    {
        LogError( ( "Failed to start self-test: "
                    "OtaErr_t=%d",
                    err ) );
    }

    return OTA_ERR_NONE;
}

static OtaErr_t requestJobHandler( const OtaEventData_t * pEventData )
{
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
            /* Start the request timer. */
            retVal = otaAgent.pOtaInterface->os.timer.start( OtaRequestTimer,
                                                             "OtaRequestTimer",
                                                             otaconfigFILE_REQUEST_WAIT_MS,
                                                             otaTimerCallback );

            if( retVal != OTA_ERR_NONE )
            {
                LogError( ( "Failed to start request timer: "
                            "OtaErr_t=%d",
                            retVal ) );
            }
            else
            {
                otaAgent.requestMomentum++;
            }

            retVal = OTA_ERR_PUBLISH_FAILED;
        }
        else
        {
            /* Stop the request timer. */
            otaAgent.pOtaInterface->os.timer.stop( OtaRequestTimer );

            /* Send shutdown event to the OTA Agent task. */
            eventMsg.eventId = OtaAgentEventShutdown;

            if( OTA_SignalEvent( &eventMsg ) == false )
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
        /* Stop the request timer. */
        otaAgent.pOtaInterface->os.timer.stop( OtaRequestTimer );

        /* Reset the request momentum. */
        otaAgent.requestMomentum = 0;
    }

    return retVal;
}

static OtaErr_t processJobHandler( OtaEventData_t * pEventData )
{
    OtaErr_t retVal = OTA_ERR_UNINITIALIZED;
    OtaErr_t err = OTA_ERR_NONE;
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
     * completed and we have reset the device and are now running the new firmware). We
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

            if( OTA_SignalEvent( &eventMsg ) == false )
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
            err = setImageStateWithReason( OtaImageStateAborted, OTA_ERR_JOB_PARSER_ERROR );

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
            retVal = setDataInterface( &otaDataInterface, otaAgent.fileContext.pProtocols );

            if( retVal == OTA_ERR_NONE )
            {
                LogInfo( ( "Setting OTA data interface." ) );

                /* Received a valid context so send event to request file blocks. */
                eventMsg.eventId = OtaAgentEventCreateFile;

                /*Send the event to OTA Agent task. */
                if( OTA_SignalEvent( &eventMsg ) == false )
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
                err = setImageStateWithReason( OtaImageStateAborted, retVal );
            }
        }
        else
        {
            /*
             * Received a job that is not in self-test but platform is, so reboot the device to allow
             * roll back to previous image.
             */
            LogWarn( ( "Rejecting new image and rebooting:"
                       "The platform is in the self-test state while the job is not." ) );
            ( void ) otaAgent.palCallbacks.resetDevice( otaAgent.serverFileID );
        }
    }

    if( err != OTA_ERR_NONE )
    {
        LogDebug( ( "Failed to process job document: "
                    "OtaErr_t=%u",
                    err ) );
    }

    return retVal;
}

static OtaErr_t initFileHandler( const OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    err = otaDataInterface.initFileTransfer( &otaAgent );

    if( err != OTA_ERR_NONE )
    {
        if( otaAgent.requestMomentum < otaconfigMAX_NUM_REQUEST_MOMENTUM )
        {
            /* Start the request timer. */
            err = otaAgent.pOtaInterface->os.timer.start( OtaRequestTimer,
                                                          "OtaRequestTimer",
                                                          otaconfigFILE_REQUEST_WAIT_MS,
                                                          otaTimerCallback );

            if( err != OTA_ERR_NONE )
            {
                LogError( ( "Failed to start request timer: "
                            "OtaErr_t=%d",
                            err ) );
            }
            else
            {
                otaAgent.requestMomentum++;
            }

            err = OTA_ERR_PUBLISH_FAILED;
        }
        else
        {
            /* Stop the request timer. */
            otaAgent.pOtaInterface->os.timer.stop( OtaRequestTimer );

            /* Send shutdown event. */
            eventMsg.eventId = OtaAgentEventShutdown;

            if( OTA_SignalEvent( &eventMsg ) == false )
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

        if( OTA_SignalEvent( &eventMsg ) == false )
        {
            err = OTA_ERR_EVENT_Q_SEND_FAILED;
        }
    }

    return err;
}

static OtaErr_t requestDataHandler( const OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };
    uint32_t reason = 0;

    if( otaAgent.fileContext.blocksRemaining > 0U )
    {
        /* Start the request timer. */
        err = otaAgent.pOtaInterface->os.timer.start( OtaRequestTimer,
                                                      "OtaRequestTimer",
                                                      otaconfigFILE_REQUEST_WAIT_MS,
                                                      otaTimerCallback );

        if( ( err == OTA_ERR_NONE ) && ( otaAgent.requestMomentum < otaconfigMAX_NUM_REQUEST_MOMENTUM ) )
        {
            /* Request data blocks. */
            err = otaDataInterface.requestFileBlock( &otaAgent );

            /* Each request increases the momentum until a response is received. Too much momentum is
             * interpreted as a failure to communicate and will cause us to abort the OTA. */
            otaAgent.requestMomentum++;
        }
        else
        {
            /* Stop the request timer. */
            otaAgent.pOtaInterface->os.timer.stop( OtaRequestTimer );

            /* Failed to send data request abort and close file. */
            reason = err;
            err = setImageStateWithReason( OtaImageStateAborted, reason );

            if( err != OTA_ERR_NONE )
            {
                LogWarn( ( "Failed to set image state with reason: "
                           "OtaErr_t=%u"
                           ", state=%d"
                           ", reason=%d",
                           err,
                           OtaImageStateAborted,
                           reason ) );
            }

            /* Send shutdown event. */
            eventMsg.eventId = OtaAgentEventShutdown;

            if( OTA_SignalEvent( &eventMsg ) == false )
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
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaErr_t closeResult = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    /* Get the file context. */
    OtaFileContext_t * pFileContext = &( otaAgent.fileContext );

    /* Ingest data blocks received. */
    IngestResult_t result = ingestDataBlock( pFileContext,
                                             pEventData->data,
                                             pEventData->dataLength,
                                             &closeResult );

    if( result < IngestResultAccepted_Continue )
    {
        /* Stop the request timer. */
        otaAgent.pOtaInterface->os.timer.stop( OtaRequestTimer );

        /* Negative result codes mean we should stop the OTA process
         * because we are either done or in an unrecoverable error state.
         * We don't want to hang on to the resources. */

        if( result == IngestResultFileComplete )
        {
            /* File receive is complete and authenticated. Update the job status with the self_test ready identifier. */
            err = otaControlInterface.updateJobStatus( &otaAgent, JobStatusInProgress, JobReasonSigCheckPassed, 0 );

            if( err != OTA_ERR_NONE )
            {
                LogError( ( "Failed to update job status: "
                            "updateJobStatus returned error: "
                            "OtaErr_t=%u",
                            err ) );
            }
        }
        else
        {
            LogError( ( "Failed to ingest data block, rejecting image: "
                        "ingestDataBlock returned error: "
                        "OtaErr_t=%d",
                        result ) );

            /* Call the platform specific code to reject the image. */
            err = otaAgent.palCallbacks.setPlatformImageState( otaAgent.serverFileID, OtaImageStateRejected );

            if( err != OTA_ERR_NONE )
            {
                LogError( ( "Failed to set image state: "
                            "OtaErr_t=%u"
                            ", state=%d",
                            err,
                            OtaImageStateRejected ) );
            }

            /* Update the job status with the with failure code. */
            err = otaControlInterface.updateJobStatus( &otaAgent, JobStatusFailedWithVal, ( int32_t ) closeResult, ( int32_t ) result );

            if( err != OTA_ERR_NONE )
            {
                LogError( ( "Failed to update job status: "
                            "updateJobStatus returned error: "
                            "OtaErr_t=%u",
                            err ) );
            }
        }

        /* Send event to close file. */
        eventMsg.eventId = OtaAgentEventCloseFile;

        if( OTA_SignalEvent( &eventMsg ) == false )
        {
            LogWarn( ( "Failed to trigger closing file: "
                       "Unable to signal event: "
                       "event=%d",
                       eventMsg.eventId ) );
        }

        /* Let main application know of our result. */
        otaAgent.palCallbacks.completeCallback( ( result == IngestResultFileComplete ) ? OtaJobEventActivate : OtaJobEventFail );

        /* Free any remaining string memory holding the job name since this job is done. */
        if( otaAgent.pOtaSingletonActiveJobName != NULL )
        {
            otaAgent.pOtaInterface->os.mem.free( otaAgent.pOtaSingletonActiveJobName );
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
        }

        if( otaAgent.numOfBlocksToReceive > 1U )
        {
            otaAgent.numOfBlocksToReceive--;
        }
        else
        {
            /* Start the request timer. */
            otaAgent.pOtaInterface->os.timer.start( OtaRequestTimer,
                                                    "OtaRequestTimer",
                                                    otaconfigFILE_REQUEST_WAIT_MS,
                                                    otaTimerCallback );

            eventMsg.eventId = OtaAgentEventRequestFileBlock;

            if( OTA_SignalEvent( &eventMsg ) == false )
            {
                LogWarn( ( "Failed to trigger requesting the next block: "
                           "Unable to signal event: "
                           "event=%d",
                           eventMsg.eventId ) );
            }
        }
    }

    return OTA_ERR_NONE;
}

static OtaErr_t closeFileHandler( const OtaEventData_t * pEventData )
{
    ( void ) pEventData;

    LogInfo( ( "Closing file: "
               "file index=%u",
               otaAgent.fileIndex ) );

    ( void ) otaClose( &( otaAgent.fileContext ) );

    return OTA_ERR_NONE;
}

static OtaErr_t userAbortHandler( const OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    /* If we have active Job abort it and close the file. */
    if( otaAgent.pOtaSingletonActiveJobName != NULL )
    {
        err = setImageStateWithReason( OtaImageStateAborted, OTA_ERR_USER_ABORT );

        if( err == OTA_ERR_NONE )
        {
            ( void ) otaClose( &( otaAgent.fileContext ) );
        }
    }

    return err;
}

static OtaErr_t shutdownHandler( const OtaEventData_t * pEventData )
{
    ( void ) pEventData;

    LogInfo( ( "OTA Agent is shutting down." ) );

    /* If we're here, we're shutting down the OTA agent. Free up all resources and quit. */
    agentShutdownCleanup();

    /* Clear the entire agent context. This includes the OTA agent state. */
    ( void ) memset( &otaAgent, 0, sizeof( otaAgent ) );

    otaAgent.state = OtaAgentStateStopped;

    /* Terminate the OTA Agent Thread. */
    pthread_exit( NULL );

    return OTA_ERR_NONE;
}

static OtaErr_t suspendHandler( const OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaErr_t err = OTA_ERR_NONE;

    /* Log the state change to suspended state.*/
    LogInfo( ( "OTA Agent is suspended." ) );

    return err;
}

static OtaErr_t resumeHandler( OtaEventData_t * pEventData )
{
    ( void ) pEventData;

    OtaEventMsg_t eventMsg = { 0 };

    /*
     * Send signal to request job document.
     */
    eventMsg.eventId = OtaAgentEventRequestJobDocument;

    return ( OTA_SignalEvent( &eventMsg ) == true ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
}

static OtaErr_t jobNotificationHandler( const OtaEventData_t * pEventData )
{
    ( void ) pEventData;
    OtaEventMsg_t eventMsg = { 0 };

    /* Stop the request timer. */
    otaAgent.pOtaInterface->os.timer.stop( OtaRequestTimer );

    /* Abort the current job. */
    ( void ) otaAgent.palCallbacks.setPlatformImageState( otaAgent.serverFileID, OtaImageStateAborted );
    ( void ) otaClose( &( otaAgent.fileContext ) );

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

    return ( OTA_SignalEvent( &eventMsg ) == true ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
}

/* Close an existing OTA file context and free its resources. */

static bool otaClose( OtaFileContext_t * const pFileContext )
{
    bool result = false;

    LogDebug( ( "Attempting to close OTA file context: "
                "file context address=0x%p",
                pFileContext ) );

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
        ( void ) otaAgent.palCallbacks.abortUpdate( pFileContext );

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

    while( ( index < OTA_MAX_FILES ) && ( otaAgent.fileContext.pFilePath != NULL ) )
    {
        index++;
    }

    if( index != OTA_MAX_FILES )
    {
        ( void ) memset( &( otaAgent.fileContext ), 0, sizeof( OtaFileContext_t ) );
        pFileContext = &( otaAgent.fileContext );
        otaAgent.fileIndex = index;
    }
    else
    {
        /* Not able to support this request so return NULL. */
    }

    return pFileContext;
}

/* Validate JSON document and the DocModel*/
static DocParseErr_t validateJSON( const char * pJson,
                                   uint32_t messageLength )
{
    DocParseErr_t err = DocParseErrNone;
    JSONStatus_t result;

    /* Check JSON document pointer is valid.*/
    if( pJson == NULL )
    {
        LogError( ( "Parameter check failed: pJson is NULL." ) );
        err = DocParseErrNullDocPointer;
    }

    /* Check if the JSON document is valid*/
    if( err == DocParseErrNone )
    {
        result = JSON_Validate( pJson, ( size_t ) messageLength );

        if( result != JSONSuccess )
        {
            LogError( ( "Invalid JSON document: "
                        "JSON_Validate returned error: "
                        "JSONStatus_t=%d",
                        result ) );
            err = DocParseErr_InvalidJSONBuffer;
        }
    }

    return err;
}

/* Decode the base64 encoded file signature key from the job document and store it in file context*/

static DocParseErr_t decodeAndStoreKey( char * pValueInJson,
                                        size_t valueLength,
                                        void ** ppvParamAdd )
{
    DocParseErr_t err = DocParseErrNone;

    /* Allocate space for and decode the base64 signature. */
    void * pSignature = otaAgent.pOtaInterface->os.mem.malloc( sizeof( Sig256_t ) );

    if( pSignature != NULL )
    {
        size_t actualLen = 0;
        int base64Status = 0;

        *ppvParamAdd = pSignature;
        Sig256_t * pSig256 = *ppvParamAdd;

        base64Status = base64Decode( pSig256->data,
                                     sizeof( pSig256->data ),
                                     &actualLen,
                                     ( const uint8_t * ) pValueInJson,
                                     valueLength );

        if( base64Status != 0 )
        {
            /* Stop processing on error. */
            LogError( ( "Failed to decode Base64 data: "
                        "base64Decode returned error: "
                        "error=%d",
                        base64Status ) );
            err = DocParseErrBase64Decode;
        }
        else
        {
            pSig256->size = ( uint16_t ) actualLen;
            LogInfo( ( "Extracted parameter [ %s: %.32s... ]",
                       OTA_JsonFileSignatureKey,
                       pValueInJson ) );
        }
    }
    else
    {
        /* We failed to allocate needed memory. Everything will be freed below upon failure. */
        err = DocParseErrOutOfMemory;
    }

    return err;
}

/* Store the parameter from the json to the offset specified by the document model. */

static DocParseErr_t extractParameter( JsonDocParam_t docParam,
                                       void * pContextBase,
                                       char * pValueInJson,
                                       size_t valueLength )
{
    void ** ppvParamAdd;
    uint32_t * pParamSizeAdd;
    DocParseErr_t err = DocParseErrNone;

    /* Get destination offset to parameter storage location.*/
    ppvParamAdd = pContextBase + docParam.pDestOffset;

    /* Get destination buffer size to parameter storage location. */
    pParamSizeAdd = pContextBase + docParam.pDestSizeOffset;

    char * pStringCopy = NULL;

    if( ( ModelParamTypeStringCopy == docParam.modelParamType ) || ( ModelParamTypeArrayCopy == docParam.modelParamType ) )
    {
        if( *ppvParamAdd == NULL )
        {
            /* Malloc memory for a copy of the value string plus a zero terminator. */
            pStringCopy = otaAgent.pOtaInterface->os.mem.malloc( valueLength + 1U );

            if( pStringCopy != NULL )
            {
                *ppvParamAdd = pStringCopy;
            }
            else
            {
                /* Stop processing on error. */
                err = DocParseErrOutOfMemory;

                LogError( ( "Memory allocation failed "
                            "[key: valueLength]=[%s: %s]",
                            docParam.pSrcKey,
                            valueLength ) );
            }
        }
        else
        {
            if( *pParamSizeAdd < ( valueLength + 1U ) )
            {
                err = DocParseErrUserBufferInsuffcient;

                LogError( ( "Insufficient user memory: "
                            "[key: valueLength]=[%s: %s]",
                            docParam.pSrcKey,
                            valueLength ) );
            }
            else
            {
                pStringCopy = *ppvParamAdd;
                err = DocParseErrNone;
            }
        }

        if( err == DocParseErrNone )
        {
            /* Copy parameter string into newly allocated memory. */
            ( void ) memcpy( ( *ppvParamAdd ), pValueInJson, valueLength );

            /* Zero terminate the new string. */
            pStringCopy[ valueLength ] = '\0';

            LogInfo( ( "Extracted parameter: "
                       "[key: value]=[%s: %s]",
                       docParam.pSrcKey,
                       pStringCopy ) );
        }
    }
    else if( ModelParamTypeStringInDoc == docParam.modelParamType )
    {
        /* Copy pointer to source string instead of duplicating the string. */
        char * pStringInDoc = pValueInJson;
        *ppvParamAdd = pStringInDoc;

        LogInfo( ( "Extracted parameter: "
                   "[key: value]=[%s: %.*s]",
                   docParam.pSrcKey,
                   ( int16_t ) valueLength,
                   pStringInDoc ) );
    }
    else if( ModelParamTypeUInt32 == docParam.modelParamType )
    {
        char * pEnd;
        const char * pStart = pValueInJson;
        errno = 0;
        uint32_t * puint32 = ( uint32_t * ) ppvParamAdd;

        *puint32 = ( uint32_t ) strtoul( pStart, &pEnd, 0 );

        if( ( errno == 0 ) && ( pEnd == &pValueInJson[ valueLength ] ) )
        {
            LogInfo( ( "Extracted parameter: "
                       "[key: value]=[%s: %u]",
                       docParam.pSrcKey,
                       *puint32 ) );
        }
        else
        {
            err = DocParseErrInvalidNumChar;
        }
    }
    else if( ModelParamTypeSigBase64 == docParam.modelParamType )
    {
        err = decodeAndStoreKey( pValueInJson, valueLength, ppvParamAdd );
    }
    else if( ModelParamTypeIdent == docParam.modelParamType )
    {
        LogDebug( ( "Identified parameter: [ %s ]",
                    docParam.pSrcKey ) );

        *ppvParamAdd = true;
    }
    else
    {
        /* Ignore if invalid type */
    }

    if( err != DocParseErrNone )
    {
        LogError( ( "Failed to extract document parameter: "
                    "error=%d"
                    ", paramter key=%s",
                    err,
                    docParam.pSrcKey ) );
    }

    return err;
}

/* Checks for duplicate entries in the JSON document. */

static DocParseErr_t checkDuplicates( uint32_t * paramsReceivedBitmap,
                                      uint16_t paramIndex )
{
    DocParseErr_t err = DocParseErrNone;

    /* TODO need to change this implementation because duplicates are not searched properly */
    /* Check for duplicates of the token*/
    if( ( *paramsReceivedBitmap & ( ( uint32_t ) 1U << paramIndex ) ) != 0U ) /*lint !e9032 paramIndex will never be greater than kDocModel_MaxParams, which is the the size of the bitmap. */
    {
        err = DocParseErrDuplicatesNotAllowed;
    }
    else
    {
        /* Mark parameter as received in the bitmap. */
        *paramsReceivedBitmap |= ( ( uint32_t ) 1U << paramIndex ); /*lint !e9032 paramIndex will never be greater than kDocModel_MaxParams, which is the the size of the bitmap. */
    }

    return err;
}

/* Check if all the required parameters for job document are extracted from the JSON */

static DocParseErr_t verifyRequiredParamsExtracted( const JsonDocParam_t * pModelParam,
                                                    const JsonDocModel_t * pDocModel )
{
    uint32_t scanIndex = 0;
    DocParseErr_t err = DocParseErrNone;
    uint32_t missingParams = ( pDocModel->paramsReceivedBitmap & pDocModel->paramsRequiredBitmap )
                             ^ pDocModel->paramsRequiredBitmap;

    if( missingParams != 0U )
    {
        /* The job document did not have all required document model parameters. */
        for( scanIndex = 0U; scanIndex < pDocModel->numModelParams; scanIndex++ )
        {
            if( ( missingParams & ( ( uint32_t ) 1U << scanIndex ) ) != 0U )
            {
                LogDebug( ( "Failed job document content check: "
                            "Required job document parameter was not extracted: "
                            "parameter=%s",
                            pModelParam[ scanIndex ].pSrcKey ) );
            }
        }

        err = DocParseErrMalformedDoc;
    }

    return err;
}

/* Extract the desired fields from the JSON document based on the specified document model. */

static DocParseErr_t parseJSONbyModel( const char * pJson,
                                       uint32_t messageLength,
                                       JsonDocModel_t * pDocModel )
{
    const JsonDocParam_t * pModelParam = NULL;
    DocParseErr_t err;
    JSONStatus_t result;
    uint16_t paramIndex;
    char * pFileParams = NULL;
    uint32_t fileParamsLength;

    /* Fetch the model parameters from the DocModel*/
    pModelParam = pDocModel->pBodyDef;

    /* Check the validity of the JSON document */
    err = validateJSON( pJson, messageLength );

    /* Traverse the docModel and search the JSON if it containing the Source Key specified*/
    for( paramIndex = 0; ( paramIndex < pDocModel->numModelParams ) && ( err == DocParseErrNone ); paramIndex++ )
    {
        const char * pQueryKey = pDocModel->pBodyDef[ paramIndex ].pSrcKey;
        size_t queryKeyLength = strlen( pQueryKey );
        char * pValueInJson;
        size_t valueLength;
        result = JSON_Search( pJson, messageLength, pQueryKey, queryKeyLength, &pValueInJson, &valueLength );

        /* If not found in pJSon search for the key in FileParameters JSON*/
        if( ( result != JSONSuccess ) && ( pFileParams != NULL ) )
        {
            result = JSON_Search( pFileParams, fileParamsLength, pQueryKey, queryKeyLength, &pValueInJson, &valueLength );
        }

        if( result == JSONSuccess )
        {
            err = checkDuplicates( &( pDocModel->paramsReceivedBitmap ), paramIndex );

            if( ( void * ) OTA_DONT_STORE_PARAM == pModelParam[ paramIndex ].pDestOffset )
            {
                /* Do nothing if we don't need to store the parameter */
                continue;
            }
            else if( ( void * ) OTA_STORE_NESTED_JSON == pModelParam[ paramIndex ].pDestOffset )
            {
                pFileParams = pValueInJson + 1;
                fileParamsLength = ( uint32_t ) valueLength - 2U;
            }
            else
            {
                err = extractParameter( pModelParam[ paramIndex ],
                                        ( void * ) pDocModel->contextBase,
                                        pValueInJson,
                                        valueLength );
            }
        }
    }

    if( err == DocParseErrNone )
    {
        err = verifyRequiredParamsExtracted( pModelParam, pDocModel );
    }

    if( err != DocParseErrNone )
    {
        LogError( ( "Failed to parse JSON document: "
                    "DocParseErr_t=%d",
                    err ) );
    }

    return err;
}

/* Prepare the document model for use by sanity checking the initialization parameters
 * and detecting all required parameters. */

static DocParseErr_t initDocModel( JsonDocModel_t * pDocModel,
                                   const JsonDocParam_t * pBodyDef,
                                   void * contextBaseAddr,
                                   uint32_t contextSize,
                                   uint16_t numJobParams )
{
    DocParseErr_t err = DocParseErrUnknown;
    uint32_t scanIndex;

    /* Sanity check the model pointers and parameter count. Exclude the context base address and size since
     * it is technically possible to create a model that writes entirely into absolute memory locations.
     */
    if( pDocModel == NULL )
    {
        LogError( ( "Parameter check failed: pDocModel is NULL." ) );
        err = DocParseErrNullModelPointer;
    }
    else if( pBodyDef == NULL )
    {
        LogError( ( "Parameter check failed: pBodyDef is NULL." ) );
        err = DocParseErrNullBodyPointer;
    }
    else if( numJobParams > OTA_DOC_MODEL_MAX_PARAMS )
    {
        LogError( ( "Parameter check failed: "
                    "Document model has %u parameters: "
                    "Document model should have <= %u parameters.",
                    numJobParams,
                    OTA_DOC_MODEL_MAX_PARAMS ) );
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
            if( pDocModel->pBodyDef[ scanIndex ].required == true )
            {
                /* Add parameter to the required bitmap. */
                pDocModel->paramsRequiredBitmap |= ( ( uint32_t ) 1U << scanIndex );
            }
        }

        err = DocParseErrNone;
    }

    if( err != DocParseErrNone )
    {
        LogError( ( "Failed to initialize document model: "
                    "DocParseErr_t=%d", err ) );
    }

    return err;
}

/*
 * Validate the version of the update received.
 */
static OtaErr_t validateUpdateVersion( const OtaFileContext_t * pFileContext )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    /* Only check for versions if the target is self */
    if( otaAgent.serverFileID == 0U )
    {
        /* Check if version reported is the same as the running version. */
        if( pFileContext->updaterVersion == appFirmwareVersion.u.unsignedVersion32 )
        {
            /* The version is the same so either we're not actually the new firmware or
             * someone messed up and sent firmware with the same version. In either case,
             * this is a failure of the OTA update so reject the job.
             */
            LogWarn( ( "Application version of the new image is identical to the current image: "
                       "New images are expected to have a higher version number: " ) );

            err = OTA_ERR_SAME_FIRMWARE_VERSION;
        }
        /* Check if update version received is older than current version.*/
        else if( pFileContext->updaterVersion > appFirmwareVersion.u.unsignedVersion32 )
        {
            LogWarn( ( "Application version of the new image is lower than the current image: "
                       "New images are expected to have a higher version number." ) );
            err = OTA_ERR_DOWNGRADE_NOT_ALLOWED;
        }

        /* pFileContext->updaterVersion < appFirmwareVersion.u.unsignedVersion32 is true.
         * Update version received is newer than current version. */
        else
        {
            LogInfo( ( "New image has a higher version number than the current image: "
                       "Old image version=%u"
                       ", New image version=%u",
                       appFirmwareVersion.u.unsignedVersion32,
                       pFileContext->updaterVersion ) );

            err = OTA_ERR_NONE;
        }
    }
    else
    {
        /* For any other serverFileID.*/
        err = OTA_ERR_NONE;
    }

    return err;
}

/* If there is an error is parsing the json check if it can be handled by external callback. */

static OtaJobParseErr_t parseJobDocFromCustomCallback( const char * pJson,
                                                       uint32_t messageLength,
                                                       OtaFileContext_t * pFileContext )
{
    OtaErr_t otaErr = OTA_ERR_NONE;

    /* We have an unknown job parser error. Check to see if we can pass control to a callback for parsing */
    OtaJobParseErr_t err = otaAgent.palCallbacks.customJobCallback( pJson, messageLength );

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
                LogError( ( "Failed to update job status: "
                            "updateJobStatus returned error: "
                            "OtaErr_t=%d",
                            otaErr ) );
            }

            /* We don't need the job name memory anymore since we're done with this job. */
            free( otaAgent.pOtaSingletonActiveJobName );
            otaAgent.pOtaSingletonActiveJobName = NULL;
        }
        else
        {
            /* Job is malformed - return an error */
            err = OtaJobParseErrNonConformingJobDoc;

            LogError( ( "Custom job document was parsed, but the job name is NULL: "
                        "OtaJobParseErr_t=%i",
                        err ) );
        }
    }
    else
    {
        /*Check if we received a timestamp and client token but no job ID.*/
        if( ( otaAgent.pClientTokenFromJob != NULL ) && ( otaAgent.timestampFromJob != 0U ) && ( pFileContext->pJobName == NULL ) )
        {
            /* Received job document with no execution so no active job is available.*/
            LogWarn( ( "No active jobs available for execution." ) );
            err = OtaJobParseErrNoActiveJobs;
        }
        else
        {
            /* Job is malformed - return an error */
            err = OtaJobParseErrNonConformingJobDoc;
        }
    }

    return err;
}

/* Check if the incoming job document is not conflicting with current job status. */

static OtaJobParseErr_t verifyActiveJobStatus( OtaFileContext_t * pFileContext,
                                               OtaFileContext_t ** pFinalFile,
                                               bool * pUpdateJob )
{
    OtaJobParseErr_t err = OtaJobParseErrNone;

    if( pFileContext->pJobName != NULL )
    {
        /* pFileContext->pJobName is guaranteed to be zero terminated. */
        if( strcmp( ( char * ) otaAgent.pOtaSingletonActiveJobName, ( char * ) pFileContext->pJobName ) != 0 )
        {
            LogInfo( ( "New job document received, aborting current job." ) );

            /* Abort the current job. */
            ( void ) otaAgent.palCallbacks.setPlatformImageState( otaAgent.serverFileID, OtaImageStateAborted );
            ( void ) otaClose( &( otaAgent.fileContext ) );

            /* Set new active job name. */
            free( otaAgent.pOtaSingletonActiveJobName );
            otaAgent.pOtaSingletonActiveJobName = pFileContext->pJobName;
            pFileContext->pJobName = NULL;

            err = OtaJobParseErrNone;
        }
        else
        {   /* The same job is being reported so update the url. */
            LogInfo( ( "New job document ID is identical to the current job: "
                       "Updating the URL based on the new job document." ) );

            if( otaAgent.fileContext.pUpdateUrlPath != NULL )
            {
                free( otaAgent.fileContext.pUpdateUrlPath );
                otaAgent.fileContext.pUpdateUrlPath = pFileContext->pUpdateUrlPath;
                pFileContext->pUpdateUrlPath = NULL;
            }

            *pFinalFile = &( otaAgent.fileContext );
            *pUpdateJob = true;

            err = OtaJobParseErrUpdateCurrentJob;
        }
    }
    else
    {
        LogWarn( ( "Parameter check failed: "
                   "pJobName is NULL while the OTA Agent is busy: "
                   "Ignoring parameter check failure." ) );
        err = OtaJobParseErrNullJob;
    }

    return err;
}

/* Check if all the file context params are valid and initialize resources for the job transfer */

static OtaJobParseErr_t validateAndStartJob( OtaFileContext_t * pFileContext,
                                             OtaFileContext_t ** pFinalFile,
                                             bool * pUpdateJob )
{
    OtaErr_t errVersionCheck = OTA_ERR_UNINITIALIZED;
    OtaJobParseErr_t err = OtaJobParseErrNone;

    /* Validate the job document parameters. */
    if( pFileContext->fileSize == 0U )
    {
        LogError( ( "Parameter check failed: "
                    "pFileContext->fileSize is 0: "
                    "File size should be > 0." ) );
        err = OtaJobParseErrZeroFileSize;
    }
    /* If there's an active job, verify that it's the same as what's being reported now. */
    /* We already checked for missing parameters so we SHOULD have a job name in the context. */
    else if( otaAgent.pOtaSingletonActiveJobName != NULL )
    {
        err = verifyActiveJobStatus( pFileContext, pFinalFile, pUpdateJob );
    }
    else
    {   /* Assume control of the job name from the context. */
        otaAgent.pOtaSingletonActiveJobName = pFileContext->pJobName;
        pFileContext->pJobName = NULL;
    }

    /* Store the File ID received in the job. */
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
         * either the firmware was not accepted during self
         * test or an incorrect image was sent by the OTA
         * operator.
         */
        if( pFileContext->isInSelfTest == true )
        {
            LogInfo( ( "In self test mode." ) );

            /* Validate version of the update received.*/
            errVersionCheck = validateUpdateVersion( pFileContext );

            if( ( otaconfigAllowDowngrade == 1U ) || ( errVersionCheck == OTA_ERR_NONE ) )
            {
                /* The running firmware version is newer than the firmware that performed
                 * the update or downgrade is allowed so this means we're ready to start
                 * the self test phase.
                 *
                 * Set image state accordingly and update job status with self test identifier.
                 */
                LogInfo( ( "Image version is valid: "
                           "Begin testing file: "
                           "File ID=%d",
                           otaAgent.serverFileID ) );

                ( void ) setImageStateWithReason( OtaImageStateTesting, errVersionCheck );
            }
            else
            {
                LogWarn( ( "New image is being rejected: "
                           "Application version of the new image is invalid: "
                           "OtaErr_t=%u",
                           errVersionCheck ) );
                ( void ) setImageStateWithReason( OtaImageStateRejected, errVersionCheck );

                /* All reject cases must reset the device. */
                ( void ) otaAgent.palCallbacks.resetDevice( otaAgent.serverFileID );
            }
        }
        else
        {
            *pFinalFile = pFileContext;

            if( *pFinalFile == NULL )
            {
                LogError( ( "Job succesfully parsed, but there is no file context available." ) );
            }
            else
            {
                **pFinalFile = *pFileContext;

                /* Everything looks OK. Set final context structure to start OTA. */
                LogInfo( ( "Job document was accepted. Attempting to begin the update." ) );
            }
        }
    }
    else
    {
        LogError( ( "Failed to validate and start the job: "
                    "OtaJobParseErr_t=%d",
                    err ) );
    }

    return err;
}

/* This is the OTA job document model describing the parameters, their types, destination and how to extract. */
/*lint -e{708} We intentionally do some things lint warns about but produce the proper model. */
/* Namely union initialization and pointers converted to values. */

static const JsonDocParam_t otaJobDocModelParamStructure[ OTA_NUM_JOB_PARAMS ] =
{
    { OTA_JSON_CLIENT_TOKEN_KEY,    OTA_JOB_PARAM_OPTIONAL, ( void * ) OTA_DONT_STORE_PARAM,       ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeStringInDoc },
    { OTA_JSON_TIMESTAMP_KEY,       OTA_JOB_PARAM_OPTIONAL, ( void * ) OTA_DONT_STORE_PARAM,       ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeUInt32      },
    { OTA_JSON_EXECUTION_KEY,       OTA_JOB_PARAM_REQUIRED, ( void * ) OTA_DONT_STORE_PARAM,       ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeObject      },
    { OTA_JSON_JOB_ID_KEY,          OTA_JOB_PARAM_REQUIRED, ( void * ) offsetof( OtaFileContext_t, pJobName ),                      ( void * ) offsetof( OtaFileContext_t, jobNameMaxSize ), ModelParamTypeStringCopy},
    { OTA_JSON_STATUS_DETAILS_KEY,  OTA_JOB_PARAM_OPTIONAL, ( void * ) OTA_DONT_STORE_PARAM,       ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeObject      },
    { OTA_JSON_SELF_TEST_KEY,       OTA_JOB_PARAM_OPTIONAL, ( void * ) offsetof( OtaFileContext_t, isInSelfTest ),                  ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeIdent},
    { OTA_JSON_UPDATED_BY_KEY,      OTA_JOB_PARAM_OPTIONAL, ( void * ) offsetof( OtaFileContext_t, updaterVersion ),                ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeUInt32},
    { OTA_JSON_JOB_DOC_KEY,         OTA_JOB_PARAM_REQUIRED, ( void * ) OTA_DONT_STORE_PARAM,       ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeObject      },
    { OTA_JSON_OTA_UNIT_KEY,        OTA_JOB_PARAM_REQUIRED, ( void * ) OTA_DONT_STORE_PARAM,       ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeObject      },
    { OTA_JSON_STREAM_NAME_KEY,     OTA_JOB_PARAM_OPTIONAL, ( void * ) offsetof( OtaFileContext_t, pStreamName ),                   ( void * ) offsetof( OtaFileContext_t, streamNameMaxSize ), ModelParamTypeStringCopy},
    { OTA_JSON_PROTOCOLS_KEY,       OTA_JOB_PARAM_REQUIRED, ( void * ) offsetof( OtaFileContext_t, pProtocols ),                    ( void * ) offsetof( OtaFileContext_t, protocolMaxSize ), ModelParamTypeArrayCopy},
    { OTA_JSON_FILE_GROUP_KEY,      OTA_JOB_PARAM_REQUIRED, ( void * ) OTA_STORE_NESTED_JSON,      ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeArray       },
    { OTA_JSON_FILE_PATH_KEY,       OTA_JOB_PARAM_REQUIRED, ( void * ) offsetof( OtaFileContext_t, pFilePath ),                     ( void * ) offsetof( OtaFileContext_t, filePathMaxSize ), ModelParamTypeStringCopy},
    { OTA_JSON_FILE_SIZE_KEY,       OTA_JOB_PARAM_REQUIRED, ( void * ) offsetof( OtaFileContext_t, fileSize ),                      ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeUInt32},
    { OTA_JSON_FILE_ID_KEY,         OTA_JOB_PARAM_REQUIRED, ( void * ) offsetof( OtaFileContext_t, serverFileID ),                  ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeUInt32},
    { OTA_JSON_FILE_CERT_NAME_KEY,  OTA_JOB_PARAM_REQUIRED, ( void * ) offsetof( OtaFileContext_t, pCertFilepath ),                 ( void * ) offsetof( OtaFileContext_t, certFilePathMaxSize ), ModelParamTypeStringCopy},
    { OTA_JSON_UPDATE_DATA_URL_KEY, OTA_JOB_PARAM_OPTIONAL, ( void * ) offsetof( OtaFileContext_t, pUpdateUrlPath ),                ( void * ) offsetof( OtaFileContext_t, updateUrlMaxSize ), ModelParamTypeStringCopy},
    { OTA_JSON_AUTH_SCHEME_KEY,     OTA_JOB_PARAM_OPTIONAL, ( void * ) offsetof( OtaFileContext_t, pAuthScheme ),                   ( void * ) offsetof( OtaFileContext_t, authSchemeMaxSize ), ModelParamTypeStringCopy},
    { OTA_JsonFileSignatureKey,     OTA_JOB_PARAM_REQUIRED, ( void * ) offsetof( OtaFileContext_t, pSignature ),                    ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeSigBase64},
    { OTA_JSON_FILE_ATTRIBUTE_KEY,  OTA_JOB_PARAM_OPTIONAL, ( void * ) offsetof( OtaFileContext_t, fileAttributes ),                ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeUInt32},
    { OTA_JSON_FILETYPE_KEY,        OTA_JOB_PARAM_OPTIONAL, ( void * ) offsetof( OtaFileContext_t, fileType ),                      ( void * ) OTA_DONT_STORE_PARAM, ModelParamTypeUInt32}
};

/* Parse the OTA job document and validate. Return the populated
 * OTA context if valid otherwise return NULL.
 */

static OtaFileContext_t * parseJobDoc( const char * pJson,
                                       uint32_t messageLength,
                                       bool * pUpdateJob )
{
    OtaErr_t otaErr = OTA_ERR_NONE;
    OtaJobParseErr_t err = OtaJobParseErrUnknown;
    DocParseErr_t parseError = DocParseErrNone;
    OtaFileContext_t * pFinalFile = NULL;
    OtaFileContext_t * pFileContext = &( otaAgent.fileContext );
    JsonDocModel_t otaJobDocModel;

    parseError = initDocModel( &otaJobDocModel,
                               otaJobDocModelParamStructure,
                               ( void * ) pFileContext, /*lint !e9078 !e923 Intentionally casting context pointer to a value for initDocModel. */
                               ( uint32_t ) sizeof( OtaFileContext_t ),
                               OTA_NUM_JOB_PARAMS );
    printf("%s\n",pJson);

    if( parseError != DocParseErrNone )
    {
        err = OtaJobParseErrBadModelInitParams;
    }
    else
    {
        parseError = parseJSONbyModel( pJson, messageLength, &otaJobDocModel );

        if( parseError == DocParseErrNone )
        {
            err = validateAndStartJob( pFileContext, &pFinalFile, pUpdateJob );
        }
        else
        {
            err = parseJobDocFromCustomCallback( pJson, messageLength, pFileContext );
        }
    }

    if( err != OtaJobParseErrNone )
    {
        /* If job parsing failed AND there's a job ID, update the job state to FAILED with
         * a reason code.  Without a job ID, we can't update the status in the job service. */
        if( pFileContext->pJobName != NULL )
        {
            LogError( ( "Failed to parse the job document after parsing the job name: "
                        "OtaJobParseErr_t=%d"
                        ", Job name=",
                        err,
                        ( char * ) pFileContext->pJobName ) );

            /* Assume control of the job name from the context. */
            otaAgent.pOtaSingletonActiveJobName = pFileContext->pJobName;
            pFileContext->pJobName = NULL;
            otaErr = otaControlInterface.updateJobStatus( &otaAgent,
                                                          JobStatusFailedWithVal,
                                                          ( int32_t ) OTA_ERR_JOB_PARSER_ERROR,
                                                          ( int32_t ) err );

            if( otaErr != OTA_ERR_NONE )
            {
                LogError( ( "Failed to update job status: "
                            "updateJobStatus returned error: "
                            "OtaErr_t=%d",
                            err ) );
            }

            /* We don't need the job name memory anymore since we're done with this job. */
            free( otaAgent.pOtaSingletonActiveJobName );
            otaAgent.pOtaSingletonActiveJobName = NULL;
        }
        else
        {
            LogError( ( "Failed to parse job document: "
                        "OtaJobParseErr_t=%d",
                        err ) );
        }
    }

    /* If we failed, close the open files. */
    if( pFinalFile == NULL )
    {
        /* Close any open files. */
        ( void ) otaClose( &( otaAgent.fileContext ) );
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
    uint32_t index;
    uint32_t numBlocks;             /* How many data pages are in the expected update image. */
    uint32_t bitmapLen;             /* Length of the file block bitmap in bytes. */
    OtaFileContext_t * pUpdateFile; /* Pointer to an OTA update context. */
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    bool updateJob = false;

    /* Populate an OTA file context from the OTA job document. */

    pUpdateFile = parseJobDoc( pRawMsg, messageLength, &updateJob );

    if( updateJob == true )
    {
        LogInfo( ( "Job document for receiving an update received." ) );
    }

    if( ( updateJob == false ) && ( pUpdateFile != NULL ) && ( inSelftest() == false ) )
    {
        if( pUpdateFile->pRxBlockBitmap != NULL )
        {
            /* Free any previously allocated bitmap. */
            free( pUpdateFile->pRxBlockBitmap );
            pUpdateFile->pRxBlockBitmap = NULL;
        }

        /* Calculate how many bytes we need in our bitmap for tracking received blocks.
         * The below calculation requires power of 2 page sizes. */

        numBlocks = ( pUpdateFile->fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
        bitmapLen = ( numBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;
        pUpdateFile->pRxBlockBitmap = ( uint8_t * ) otaAgent.pOtaInterface->os.mem.malloc( bitmapLen ); /*lint !e9079 FreeRTOS malloc port returns void*. */

        if( pUpdateFile->pRxBlockBitmap != NULL )
        {
            /* Set all bits in the bitmap to the erased state (we use 1 for erased just like flash memory). */
            ( void ) memset( pUpdateFile->pRxBlockBitmap, ( int32_t ) OTA_ERASED_BLOCKS_VAL, bitmapLen );

            /* Mark as used any pages in the bitmap that are out of range, based on the file size.
             * This keeps us from requesting those pages during retry processing or if using a windowed
             * block request. It also avoids erroneously accepting an out of range data block should it
             * get past any safety checks.
             * Files are not always a multiple of 8 pages (8 bits/pages per byte) so some bits of the
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
                err = setImageStateWithReason( OtaImageStateAborted, err );
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

    if( err != OTA_ERR_NONE )
    {
        LogDebug( ( "Failed to parse the file context from the job document: "
                    "OtaErr_t=%d",
                    err ) );
    }

    return pUpdateFile; /* Return the OTA file context. */
}

/*
 * validateDataBlock
 *
 * Validate the block index and size. If it is NOT the last block, it MUST be equal to a full block size.
 * If it IS the last block, it MUST be equal to the expected remainder. If the block ID is out of range,
 * that's an error.
 */
static bool validateDataBlock( const OtaFileContext_t * pFileContext,
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

/* Validate the incoming data block and store it in the file context. */

static IngestResult_t processDataBlock( OtaFileContext_t * pFileContext,
                                        uint32_t uBlockIndex,
                                        uint32_t uBlockSize,
                                        OtaErr_t * pCloseResult,
                                        uint8_t * pPayload )
{
    IngestResult_t eIngestResult = IngestResultUninitialized;
    uint32_t byte = 0;
    uint8_t bitMask = 0;

    if( validateDataBlock( pFileContext, uBlockIndex, uBlockSize ) == true )
    {
        LogInfo( ( "Received valid file block: "
                   "Block index=%u"
                   ", Size=%u",
                   uBlockIndex,
                   uBlockSize ) );

        /* Create bit mask for use in our bitmap. */
        bitMask = 1U << ( uBlockIndex % BITS_PER_BYTE ); /*lint !e9031 The composite expression will never be greater than BITS_PER_BYTE(8). */

        /* Calculate byte offset into bitmap. */
        byte = uBlockIndex >> LOG2_BITS_PER_BYTE;

        /* Check if we have already received this block. */
        if( ( ( pFileContext->pRxBlockBitmap[ byte ] ) & bitMask ) == 0U )
        {
            LogWarn( ( "Received a duplicate block: "
                       "Block index=%u"
                       ", Block size=%u",
                       uBlockIndex,
                       uBlockSize ) );
            LogDebug( ( "Number of blocks remaining: %u",
                        pFileContext->blocksRemaining ) );

            eIngestResult = IngestResultDuplicate_Continue;
            *pCloseResult = OTA_ERR_NONE; /* This is a success path. */
        }
    }
    else
    {
        LogError( ( "Block range check failed: "
                    "Received a block outside of the expected range: "
                    "Block index=%u"
                    ", Block size=%u",
                    uBlockIndex,
                    uBlockSize ) );
        eIngestResult = IngestResultBlockOutOfRange;
    }

    /* Process the received data block. */
    if( eIngestResult == IngestResultUninitialized )
    {
        if( pFileContext->pFile != NULL )
        {
            int32_t iBytesWritten = otaAgent.palCallbacks.writeBlock( pFileContext,
                                                                      ( uBlockIndex * OTA_FILE_BLOCK_SIZE ),
                                                                      pPayload,
                                                                      uBlockSize );

            if( iBytesWritten < 0 )
            {
                eIngestResult = IngestResultWriteBlockFailed;
                LogError( ( "Failed to ingest received block: "
                            "IngestResult_t=%d",
                            eIngestResult ) );
            }
            else
            {
                /* Mark this block as received in our bitmap. */
                pFileContext->pRxBlockBitmap[ byte ] &= ~bitMask;
                pFileContext->blocksRemaining--;
                eIngestResult = IngestResultAccepted_Continue;
                *pCloseResult = OTA_ERR_NONE;
            }
        }
        else
        {
            LogError( ( "Parameter check failed: "
                        "pFileContext->pFile is NULL." ) );
            eIngestResult = IngestResultBadFileHandle;
        }
    }

    return eIngestResult;
}

/* Free the resources allocated for data ingestion and close the file handle. */

static IngestResult_t ingestDataBlockCleanup( OtaFileContext_t * pFileContext,
                                              OtaErr_t * pCloseResult )
{
    IngestResult_t eIngestResult = IngestResultAccepted_Continue;

    if( pFileContext->blocksRemaining == 0U )
    {
        LogInfo( ( "Received final block of the update." ) ); \

        /* Stop the request timer. */
        otaAgent.pOtaInterface->os.timer.stop( OtaRequestTimer );

        /* Free the bitmap now that we're done with the download. */
        otaAgent.pOtaInterface->os.mem.free( pFileContext->pRxBlockBitmap );
        pFileContext->pRxBlockBitmap = NULL;

        if( pFileContext->pFile != NULL )
        {
            *pCloseResult = otaAgent.palCallbacks.closeFile( pFileContext );

            if( *pCloseResult == OTA_ERR_NONE )
            {
                LogInfo( ( "Received entire update and validated the signature." ) );
                eIngestResult = IngestResultFileComplete;
            }
            else
            {
                uint32_t closeResult = ( uint32_t ) *pCloseResult;

                LogError( ( "Failed to close the OTA file: "
                            "Error=(%u:0x%06x)",
                            closeResult >> OTA_MAIN_ERR_SHIFT_DOWN_BITS,
                            closeResult & ( uint32_t ) OTA_PAL_ERR_MASK ) );

                if( ( ( closeResult ) & ( OTA_MAIN_ERR_MASK ) ) == OTA_ERR_SIGNATURE_CHECK_FAILED )
                {
                    eIngestResult = IngestResultSigCheckFail;
                }
                else
                {
                    eIngestResult = IngestResultFileCloseFail;
                }
            }

            /* File is now closed so clear the file handle in the context. */
            pFileContext->pFile = NULL;
        }
        else
        {
            LogError( ( "Parameter check failed: "
                        "pFileContext->pFile is NULL." ) );
            eIngestResult = IngestResultBadFileHandle;
        }
    }
    else
    {
        LogInfo( ( "Number of blocks remaining: %u",
                   pFileContext->blocksRemaining ) );
    }

    return eIngestResult;
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
    IngestResult_t eIngestResult = IngestResultUninitialized;
    int32_t lFileId = 0;
    int32_t sBlockSize = 0;
    int32_t sBlockIndex = 0;
    uint32_t uBlockSize = 0;
    uint32_t uBlockIndex = 0;
    uint8_t * pPayload = NULL;
    size_t payloadSize = 0;

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
            otaAgent.pOtaInterface->os.timer.start( OtaRequestTimer,
                                                    "OtaRequestTimer",
                                                    otaconfigFILE_REQUEST_WAIT_MS,
                                                    otaTimerCallback ); /*ToDo */

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

    /* Validate the data block and process it to store the information.*/
    if( eIngestResult == IngestResultUninitialized )
    {
        eIngestResult = processDataBlock( pFileContext, uBlockIndex, uBlockSize, pCloseResult, pPayload );
    }

    /* If the ingestion is complete close the file and cleanup.*/
    if( eIngestResult == IngestResultAccepted_Continue )
    {
        eIngestResult = ingestDataBlockCleanup( pFileContext, pCloseResult );
    }

    return eIngestResult;
}

/*
 * Clean up after the OTA process is done. Possibly free memory for re-use.
 */
static void agentShutdownCleanup( void )
{
    uint32_t index;

    otaAgent.state = OtaAgentStateShuttingDown;

    /* Control plane cleanup related to selected protocol. */
    if( otaControlInterface.cleanup != NULL )
    {
        ( void ) otaControlInterface.cleanup( &otaAgent );
    }

    /* Data plane cleanup related to selected protocol. */
    if( otaDataInterface.cleanup != NULL )
    {
        ( void ) otaDataInterface.cleanup( &otaAgent );
    }

    /*
     * Close any open OTA transfers.
     */
    for( index = 0; index < OTA_MAX_FILES; index++ )
    {
        ( void ) otaClose( &( otaAgent.fileContext ) );
    }

    /*
     * Free any remaining string memory holding the job name.
     */
    if( otaAgent.pOtaSingletonActiveJobName != NULL )
    {
        otaAgent.pOtaInterface->os.mem.free( otaAgent.pOtaSingletonActiveJobName );
        otaAgent.pOtaSingletonActiveJobName = NULL;
    }
}

/*
 * Handle any events that were unexpected in the current state.
 */
static void handleUnexpectedEvents( const OtaEventMsg_t * pEventMsg )
{
    LogError( ( "Received unexpected event: "
                "Current state=[%s]"
                ", Event received=[%s]",
                pOtaAgentStateStrings[ otaAgent.state ],
                pOtaEventStrings[ pEventMsg->eventId ] ) );
}

/*
 * Execute the handler for selected index from the transition table.
 */
static void executeHandler( uint32_t index,
                            const OtaEventMsg_t * const pEventMsg )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    if( otaTransitionTable[ index ].handler )
    {
        err = otaTransitionTable[ index ].handler( pEventMsg->pEventData );

        if( err == OTA_ERR_NONE )
        {
            LogDebug( ( "Executing handler for state transition: "
                        "Current State=[%s]"
                        ", Event=[%s]"
                        ", New state=[%s]",
                        pOtaAgentStateStrings[ otaAgent.state ],
                        pOtaEventStrings[ pEventMsg->eventId ],
                        pOtaAgentStateStrings[ otaTransitionTable[ index ].nextState ] ) );

            /*
             * Update the current state in OTA agent context.
             */
            otaAgent.state = otaTransitionTable[ index ].nextState;
        }
        else
        {
            LogError( ( "Failed to execute state transition handler: "
                        "Handler returned error: "
                        "OtaErr_t=%d",
                        err ) );
            LogDebug( ( "Current State=[%s]"
                        ", Event=[%s]"
                        ", New state=[%s]",
                        pOtaAgentStateStrings[ otaAgent.state ],
                        pOtaEventStrings[ pEventMsg->eventId ],
                        pOtaAgentStateStrings[ otaTransitionTable[ index ].nextState ] ) );
        }
    }
}

static uint32_t searchTransition( const OtaEventMsg_t * pEventMsg )
{
    uint32_t transitionTableLen = ( uint32_t ) ( sizeof( otaTransitionTable ) / sizeof( otaTransitionTable[ 0 ] ) );
    uint32_t i = 0;

    for( i = 0; i < transitionTableLen; i++ )
    {
        if( ( ( otaTransitionTable[ i ].currentState == otaAgent.state ) ||
              ( otaTransitionTable[ i ].currentState == OtaAgentStateAll ) ) &&
            ( otaTransitionTable[ i ].eventId == pEventMsg->eventId ) )
        {
            break;
        }
    }

    return i;
}

void otaAgentTask( const void * pUnused )
{
    ( void ) pUnused;

    OtaEventMsg_t eventMsg = { 0 };
    uint32_t i = 0;
    uint32_t transitionTableLen = ( uint32_t ) ( sizeof( otaTransitionTable ) / sizeof( otaTransitionTable[ 0 ] ) );

    /*
     * OTA Agent is ready to receive and process events so update the state to ready.
     */
    otaAgent.state = OtaAgentStateReady;

    for( ; ; )
    {
        /*
         * Receive the next event form the OTA event queue to process.
         */
        if( otaAgent.pOtaInterface->os.event.recv( NULL, &eventMsg, 0 ) == OTA_ERR_NONE )
        {
            /*
             * Search transition index if available in the table.
             */
            i = searchTransition( &eventMsg );

            if( i < transitionTableLen )
            {
                LogDebug( ( "Found valid event handler for state transition: "
                            "State=[%s], "
                            "Event=[%s]",
                            pOtaAgentStateStrings[ i ],
                            pOtaEventStrings[ i ] ) );

                /*
                 * Execute the handler function.
                 */
                executeHandler( i, &eventMsg );
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

bool OTA_SignalEvent( const OtaEventMsg_t * const pEventMsg )
{
    bool retVal = false;
    OtaErr_t err = OTA_ERR_NONE;

    /*
     * Send event to back of the queue.
     */
    err = otaAgent.pOtaInterface->os.event.send( NULL, pEventMsg, 0 );

    if( err == OTA_ERR_NONE )
    {
        retVal = true;
        LogDebug( ( "Added event message to OTA event queue." ) );
    }
    else
    {
        retVal = false;
        LogError( ( "Failed to add even message to OTA event queue: "
                    "send returned error: "
                    "OtaErr_t=%d",
                    err ) );
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
OtaErr_t OTA_AgentInit( OtaAppBuffer_t * pOtaBuffer,
                        OtaInterfaces_t * pOtaInterfaces,
                        const uint8_t * pThingName,
                        OtaCompleteCallback_t completeCallback )
{
    /* Return value from this function */
    OtaErr_t returnStatus = OTA_ERR_UNINITIALIZED;

    /* If OTA agent is stopped then start running. */
    if( otaAgent.state == OtaAgentStateStopped )
    {
        /*
         * Check all the callbacks for null values and initialize the values in the ota agent context.
         * The OTA agent context is initialized with the prvPAL values. So, if null is passed in, don't
         * do anything and just use the defaults in the OTA structure.
         */

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

        /*
         * Initialize the OTA interfaces.
         */
        otaAgent.pOtaInterface = pOtaInterfaces;

        /* Initialize update file path buffer from application buffer.*/
        if( pOtaBuffer->pUpdateFilePath != NULL )
        {
            otaAgent.fileContext.pFilePath = pOtaBuffer->pUpdateFilePath;
            otaAgent.fileContext.filePathMaxSize = pOtaBuffer->updateFilePathsize;
        }
        else
        {
            otaAgent.fileContext.filePathMaxSize = -1;
        }

        /* Initialize certificate file path buffer from application buffer.*/
        if( pOtaBuffer->pCertFilePath != NULL )
        {
            otaAgent.fileContext.pCertFilepath = pOtaBuffer->pCertFilePath;
            otaAgent.fileContext.certFilePathMaxSize = pOtaBuffer->certFilePathSize;
        }
        else
        {
            otaAgent.fileContext.certFilePathMaxSize = -1;
        }

        /* Initialize stream name buffer from application buffer.*/
        if( pOtaBuffer->pStreamName != NULL )
        {
            otaAgent.fileContext.pStreamName = pOtaBuffer->pStreamName;
            otaAgent.fileContext.streamNameMaxSize = pOtaBuffer->streamNameSize;
        }
        else
        {
            otaAgent.fileContext.streamNameMaxSize = -1;
        }

        /* Initialize file bitmap buffer from application buffer.*/
        if( pOtaBuffer->pFileBitmap != NULL )
        {
            otaAgent.fileContext.pRxBlockBitmap = pOtaBuffer->pFileBitmap;
            otaAgent.fileContext.blockBitmapMaxSize = pOtaBuffer->fileBitmapSize;
        }
        else
        {
            otaAgent.fileContext.blockBitmapMaxSize = -1;
        }

        /* Initialize url buffer from application buffer.*/
        if( pOtaBuffer->pUrl != NULL )
        {
            otaAgent.fileContext.pUpdateUrlPath = pOtaBuffer->pUrl;
            otaAgent.fileContext.updateUrlMaxSize = pOtaBuffer->urlSize;
        }
        else
        {
            otaAgent.fileContext.updateUrlMaxSize = -1;
        }

        /* Initialize auth scheme buffer from application buffer.*/
        if( pOtaBuffer->pAuthScheme != NULL )
        {
            otaAgent.fileContext.pAuthScheme = pOtaBuffer->pAuthScheme;
            otaAgent.fileContext.authSchemeMaxSize = pOtaBuffer->authSchemeSize;
        }
        else
        {
            otaAgent.fileContext.authSchemeMaxSize = -1;
        }

        /* Initialize ota complete callback.*/
        otaAgent.palCallbacks.completeCallback = completeCallback;

        /*
         * The current OTA image state as set by the OTA agent.
         */
        otaAgent.imageState = OtaImageStateUnknown;

        /*
         * Initialize OTA event interface.
         */
        otaAgent.pOtaInterface->os.event.init( NULL );

        if( pThingName == NULL )
        {
            LogError( ( "Error: Thing name is NULL.\r\n" ) );
        }
        else
        {
            uint32_t strLength = ( uint32_t ) ( strlen( ( const char * ) pThingName ) );

            if( strLength <= otaconfigMAX_THINGNAME_LEN )
            {
                /*
                 * Store the Thing name to be used for topics later. Include zero terminator
                 * when saving the Thing name.
                 */
                ( void ) memcpy( otaAgent.pThingName, pThingName, strLength + 1UL );
                returnStatus = OTA_ERR_NONE;
            }
            else
            {
                LogError( ( "Error: Thing name is too long.\r\n" ) );
            }
        }

        if( returnStatus == OTA_ERR_NONE )
        {
            /* OTA Task is not running yet so update the state to init directly in OTA context. */
            otaAgent.state = OtaAgentStateInit;
        }
    }
    /* If OTA agent is already running, just reset the statistics. */
    else
    {
        ( void ) memset( &otaAgent.statistics, 0, sizeof( otaAgent.statistics ) );
        returnStatus = OTA_ERR_NONE;
    }

    return returnStatus;
}

/*
 * Public API to shutdown the OTA Agent.
 */
OtaState_t OTA_AgentShutdown( uint32_t ticksToWait )
{
    OtaEventMsg_t eventMsg = { 0 };
    uint32_t ticks = ticksToWait;

    LogDebug( ( "Number of ticks to idle while the OTA Agent shuts down: "
                "ticks=%u",
                ticks ) );

    if( ( otaAgent.state != OtaAgentStateStopped ) && ( otaAgent.state != OtaAgentStateShuttingDown ) )
    {
        /*
         * Send shutdown signal to OTA Agent task.
         */
        eventMsg.eventId = OtaAgentEventShutdown;

        /* Send signal to OTA task. */
        if( OTA_SignalEvent( &eventMsg ) == false )
        {
            LogError( ( "Failed to signal the OTA Agent to shutdown: "
                        "OTA_SignalEvent returned false." ) );
        }
        else
        {
            /*
             * Wait for the OTA agent to complete shutdown, if requested.
             */
            while( ( ticks > 0U ) && ( otaAgent.state != OtaAgentStateStopped ) )
            {
                ticks--;
            }
        }
    }
    else
    {
        LogDebug( ( "Ignoring request to shutdown OTA Agent: "
                    "OTA Agent is already in state [%s]",
                    pOtaAgentStateStrings[ otaAgent.state ] ) );
    }

    LogDebug( ( "Number of ticks remaining when OTA Agent shutdown: "
                "ticks=%u",
                ticks ) );

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
    OtaErr_t retVal = OTA_ERR_NONE;
    OtaEventMsg_t eventMsg = { 0 };

    LogInfo( ( "Sending event to trigger checking for and update." ) );

    /*
     * Send event to get OTA job document.
     */
    eventMsg.eventId = OtaAgentEventRequestJobDocument;

    if( OTA_SignalEvent( &eventMsg ) == false )
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

    LogError( ( "Failed to activate new image: "
                "activateNewImage returned error: "
                "Manual reset required: "
                "OtaErr_t=%d",
                err ) );

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

OtaErr_t OTA_SetImageState( OtaImageState_t state )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    switch( state )
    {
        case OtaImageStateAborted:

            if( 1 /*otaAgent.xOTA_EventQueue != NULL*/ )
            {
                eventMsg.eventId = OtaAgentEventUserAbort;

                /*
                 * Send the event, otaAgent.imageState will be set later when the event is processed.
                 */
                err = ( OTA_SignalEvent( &eventMsg ) == true ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
            }
            else
            {
                err = OTA_ERR_PANIC;

                LogError( ( "Failed to send OTA event: "
                            "OTA event queue is not initialized." ) );
            }

            break;

        case OtaImageStateRejected:

            /*
             * Set the image state as rejected.
             */
            err = setImageStateWithReason( state, 0 );

            break;

        case OtaImageStateAccepted:

            /*
             * Set the image state as accepted.
             */
            err = setImageStateWithReason( state, 0 );

            break;

        default:

            /*lint -e788 Keep lint quiet about the obvious unused states we're catching here. */
            err = OTA_ERR_BAD_IMAGE_STATE;

            break;
    }

    if( err != OTA_ERR_NONE )
    {
        LogDebug( ( "Failed to update the image state: "
                    "OtaErr_t=%d",
                    err ) );
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
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    /* Stop the request timer. */
    otaAgent.pOtaInterface->os.timer.stop( OtaRequestTimer );

    /* Check if OTA Agent is running. */
    if( otaAgent.state != OtaAgentStateStopped )
    {
        /*
         * Send event to OTA agent task.
         */
        eventMsg.eventId = OtaAgentEventSuspend;
        err = ( OTA_SignalEvent( &eventMsg ) == true ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
    }
    else
    {
        err = OTA_ERR_OTA_AGENT_STOPPED;

        LogWarn( ( "Failed to suspend OTA Agent: "
                   "OTA Agent is stopped: "
                   "OtaErr_t=%d",
                   err ) );
    }

    return err;
}

/*
 * Resume OTA Agent task.
 */
OtaErr_t OTA_Resume( void * pConnection )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;
    OtaEventMsg_t eventMsg = { 0 };

    /* Check if OTA Agent is running. */
    if( otaAgent.state != OtaAgentStateStopped )
    {
        /*
         * Send event to OTA agent task.
         */
        eventMsg.eventId = OtaAgentEventResume;
        err = ( OTA_SignalEvent( &eventMsg ) == true ) ? OTA_ERR_NONE : OTA_ERR_EVENT_Q_SEND_FAILED;
    }
    else
    {
        err = OTA_ERR_OTA_AGENT_STOPPED;

        LogWarn( ( "Failed to resume OTA Agent: "
                   "OTA Agent is stopped: "
                   "OtaErr_t=%d",
                   err ) );
    }

    return err;
}

/*-----------------------------------------------------------*/
