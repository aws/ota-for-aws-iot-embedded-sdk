/*
 * AWS IoT Over-the-air Update v2.0.0 (Release Candidate)
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
 */

/**
 * @file ota.h
 * @brief OTA Agent Interface
 */

#ifndef OTA_H
#define OTA_H

/* Standard includes. */
/* For FILE type in OtaFileContext_t.*/
#include <stdio.h>
#include <stdint.h>

/* OTA Library Interface include. */
#include "ota_private.h"
#include "ota_os_interface.h"
#include "ota_mqtt_interface.h"
#include "ota_http_interface.h"
#include "ota_platform_interface.h"

/**
 * @ingroup ota_helpers
 * @brief Evaluates to the length of a constant string defined like 'static const char str[]= "xyz";
 */
#define CONST_STRLEN( s )    ( ( ( uint32_t ) sizeof( s ) ) - 1UL )


#define OTA_FILE_SIG_KEY_STR_MAX_LENGTH    32 /*!< Maximum length of the file signature key. */


/**
 * @ingroup ota_helpers
 * @brief The OTA signature algorithm string is specified by the PAL.
 *
 */

/* MISRA rule 8.6 requires identifier with external linkage to have exact one external definition.
 * However, this variable is defined in OTA platform abstraction layer implementation, which is
 * not in this repository but in C-SDK and amazon-freertos repo, so it's a false positive. */
/* coverity[misra_c_2012_rule_8_6_violation] */
extern const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ];

/*-------------------------- OTA enumerated types --------------------------*/

/**
 * @ingroup ota_enum_types
 * @brief The OTA API return status.
 * OTA agent error codes are in the upper 8 bits of the 32 bit OTA error word, OtaErr_t.
 */
typedef enum OtaErr
{
    OtaErrNone = 0,               /*!< @brief No error occurred during the operation. */
    OtaErrUninitialized,          /*!< @brief The error code has not yet been set by a logic path. */
    OtaErrPanic,                  /*!< @brief Unrecoverable Firmware error. Probably should log error and reboot. */
    OtaErrInvalidArg,             /*!< @brief API called with invalid argument. */
    OtaErrAgentStopped,           /*!< @brief Returned when operations are performed that requires OTA Agent running & its stopped. */
    OtaErrSignalEventFailed,      /*!< @brief Failed to send event to OTA state machine. */
    OtaErrRequestJobFailed,       /*!< @brief Failed to request the job document. */
    OtaErrInitFileTransferFailed, /*!< @brief Failed to update the OTA job status. */
    OtaErrRequestFileBlockFailed, /*!< @brief Failed to request file block. */
    OtaErrCleanupControlFailed,   /*!< @brief Failed to clean up the control plane. */
    OtaErrCleanupDataFailed,      /*!< @brief Failed to clean up the data plane. */
    OtaErrUpdateJobStatusFailed,  /*!< @brief Failed to update the OTA job status. */
    OtaErrJobParserError,         /*!< @brief An error occurred during job document parsing. See reason sub-code. */
    OtaErrInvalidDataProtocol,    /*!< @brief Job does not have a valid protocol for data transfer. */
    OtaErrMomentumAbort,          /*!< @brief Too many OTA stream requests without any response. */
    OtaErrDowngradeNotAllowed,    /*!< @brief Firmware version is older than the previous version. */
    OtaErrSameFirmwareVersion,    /*!< @brief Firmware version is the same as previous. New firmware could have failed to commit. */
    OtaErrImageStateMismatch,     /*!< @brief The OTA job was in Self Test but the platform image state was not. Possible tampering. */
    OtaErrNoActiveJob,            /*!< @brief Attempt to set final image state without an active job. */
    OtaErrUserAbort,              /*!< @brief User aborted the active OTA. */
    OtaErrFailedToEncodeCbor,     /*!< @brief Failed to encode CBOR object for requesting data block from streaming service. */
    OtaErrFailedToDecodeCbor,     /*!< @brief Failed to decode CBOR object from streaming service response. */
    OtaErrActivateFailed          /*!< @brief Failed to activate the new image. */
} OtaErr_t;

/**
 * @ingroup ota_enum_types
 * @brief OTA Agent states.
 *
 * The current state of the OTA Task (OTA Agent).
 *
 * @note There is currently support only for a single OTA context.
 */
typedef enum OtaState
{
    OtaAgentStateNoTransition = -1,
    OtaAgentStateInit = 0,
    OtaAgentStateReady,
    OtaAgentStateRequestingJob,
    OtaAgentStateWaitingForJob,
    OtaAgentStateCreatingFile,
    OtaAgentStateRequestingFileBlock,
    OtaAgentStateWaitingForFileBlock,
    OtaAgentStateClosingFile,
    OtaAgentStateSuspended,
    OtaAgentStateShuttingDown,
    OtaAgentStateStopped,
    OtaAgentStateAll
} OtaState_t;

/**
 * @ingroup ota_enum_types
 * @brief OTA job document parser error codes.
 */
typedef enum OtaJobParseErr
{
    OtaJobParseErrUnknown = -1,        /* @brief The error code has not yet been set by a logic path. */
    OtaJobParseErrNone = 0,            /* @brief Signifies no error has occurred. */
    OtaJobParseErrBusyWithExistingJob, /* @brief We're busy with a job but received a new job document. */
    OtaJobParseErrNullJob,             /* @brief A null job was reported (no job ID). */
    OtaJobParseErrUpdateCurrentJob,    /* @brief We're already busy with the reported job ID. */
    OtaJobParseErrZeroFileSize,        /* @brief Job document specified a zero sized file. This is not allowed. */
    OtaJobParseErrNonConformingJobDoc, /* @brief The job document failed to fulfill the model requirements. */
    OtaJobParseErrBadModelInitParams,  /* @brief There was an invalid initialization parameter used in the document model. */
    OtaJobParseErrNoContextAvailable,  /* @brief There was not an OTA context available. */
    OtaJobParseErrNoActiveJobs         /* @brief No active jobs are available in the service. */
} OtaJobParseErr_t;

/**
 * @ingroup ota_enum_types
 * @brief OTA Job callback events.
 *
 * After an OTA update image is received and authenticated, the agent calls the user
 * callback (set with the @ref OTA_Init API) with the value OtaJobEventActivate to
 * signal that the device must be rebooted to activate the new image. When the device
 * boots, if the OTA job status is in self test mode, the agent calls the user callback
 * with the value OtaJobEventStartTest, signaling that any additional self tests
 * should be performed.
 *
 * If the OTA receive fails for any reason, the agent calls the user callback with
 * the value OtaJobEventFail instead to allow the user to log the failure and take
 * any action deemed appropriate by the user code.
 *
 * See the OtaImageState_t type for more information.
 */
typedef enum OtaJobEvent
{
    OtaJobEventActivate = 0,       /*!< @brief OTA receive is authenticated and ready to activate. */
    OtaJobEventFail = 1,           /*!< @brief OTA receive failed. Unable to use this update. */
    OtaJobEventStartTest = 2,      /*!< @brief OTA job is now in self test, perform user tests. */
    OtaJobEventProcessed = 3,      /*!< @brief OTA event queued by OTA_SignalEvent is processed. */
    OtaJobEventSelfTestFailed = 4, /*!< @brief OTA self-test failed for current job. */
    OtaJobEventParseCustomJob = 5, /*!< @brief OTA event for parsing custom job document. */
    OtaLastJobEvent = OtaJobEventStartTest
} OtaJobEvent_t;

/**
 * @ingroup ota_enum_types
 * @brief Gives the status of the job operation.
 *
 */
typedef enum
{
    JobStatusInProgress = 0,
    JobStatusFailed,
    JobStatusSucceeded,
    JobStatusRejected,      /* Not possible today using the "get next job" feature. FUTURE! */
    JobStatusFailedWithVal, /* This shows 2 numeric reason codes. */
    NumJobStatusMappings
} OtaJobStatus_t;

/**
 * @ingroup ota_struct_types
 * @brief OTA Job document.
 *
 * Structure representing OTA job document.
 */
typedef struct OtaJobDocument
{
    uint8_t * pJobDocJson;     /*!< @brief Job document in JSON format. */
    uint32_t jobDocLength;     /*!< @brief Job document length in bytes. */
    uint8_t * pJobId;          /*!< @brief Job document in JSON format. */
    OtaJobParseErr_t parseErr; /*!< @brief Job parsing error. */
    OtaJobStatus_t status;     /*!< @brief Job status. */
    int32_t reason;            /*!< @brief Job status reason. */
    int32_t subReason;         /*!< @brief Job status subreason. */
} OtaJobDocument_t;

/*------------------------- OTA callbacks --------------------------*/

/**
 * @ingroup ota_callback_types
 * @brief OTA update complete callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback is used to notify the main application when the OTA update job is complete.
 * Typically, it is used to reset the device after a successful update by calling
 * @ref OTA_ActivateNewImage and may also be used to kick off user specified self tests
 * during the Self Test phase. If the user does not supply a custom callback function,
 * a default callback handler is used that automatically calls @ref OTA_ActivateNewImage
 * after a successful update.
 *
 * The callback function is called with one of the following arguments:
 *
 *      OtaJobEventActivate      OTA update is authenticated and ready to activate.
 *      OtaJobEventFail          OTA update failed. Unable to use this update.
 *      OtaJobEventStartTest     OTA job is now ready for optional user self tests.
 *
 * When OtaJobEventActivate is received, the job status details have been updated with
 * the state as ready for Self Test. After reboot, the new firmware will (normally) be
 * notified that it is in the Self Test phase via the callback and the application may
 * then optionally run its own tests before committing the new image.
 *
 * If the callback function is called with a result of OtaJobEventFail, the OTA update
 * job has failed in some way and should be rejected.
 *
 * @param[in] eEvent An OTA update event from the OtaJobEvent_t enum.
 *
 * @param[in] pData Optional data related to the event.
 */
typedef void (* OtaAppCallback_t)( OtaJobEvent_t eEvent,
                                   const void * pData );

/**
 * @ingroup ota_callback_types
 * @brief Custom Job callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback will be called when the OTA agent cannot parse a job document.
 *
 * @param[in] pcJSON Pointer to the json document received by the OTA agent.
 * @param[in] ulMsgLen Length of the json document received by the agent.
 */
typedef OtaJobParseErr_t (* OtaCustomJobCallback_t)( const char * pcJSON,
                                                     uint32_t ulMsgLen );

/*--------------------------- OTA structs ----------------------------*/


/**
 * @ingroup ota_struct_types
 * @brief OTA Interface for referencing different components.
 *
 * Information about the different interfaces used to initialize
 * the OTA agent with references to components.
 */
typedef struct OtaInterface
{
    OtaOSInterface_t os;     /*!< @brief OS interface to store event, timers and memory operations. */
    OtaMqttInterface_t mqtt; /*!< @brief MQTT interface that references the publish subscribe methods and callbacks. */
    OtaHttpInterface_t http; /*!< @brief HTTP interface to request data. */
    OtaPalInterface_t pal;   /*!< @brief OTA PAL callback structure. */
} OtaInterfaces_t;

/**
 * @ingroup ota_struct_types
 * @brief OTA Application Buffer size information.
 *
 * File key signature information to verify the authenticity of the incoming file
 */
typedef struct OtaAppBuffer
{
    uint8_t * pUpdateFilePath;   /*!< @brief Path to store the files. */
    uint16_t updateFilePathsize; /*!< @brief Maximum size of the file path. */
    uint8_t * pCertFilePath;     /*!< @brief Path to certificate file. */
    uint16_t certFilePathSize;   /*!< @brief Maximum size of the certificate file path. */
    uint8_t * pStreamName;       /*!< @brief Name of stream to download the files. */
    uint16_t streamNameSize;     /*!< @brief Maximum size of the stream name. */
    uint8_t * pDecodeMemory;     /*!< @brief Place to store the decoded files. */
    uint32_t decodeMemorySize;   /*!< @brief Maximum size of the decoded files buffer. */
    uint8_t * pFileBitmap;       /*!< @brief Bitmap of the parameters received. */
    uint16_t fileBitmapSize;     /*!< @brief Maximum size of the bitmap. */
    uint8_t * pUrl;              /*!< @brief Presigned url to download files from S3. */
    uint16_t urlSize;            /*!< @brief Maximum size of the URL. */
    uint8_t * pAuthScheme;       /*!< @brief Authentication scheme used to validate download. */
    uint16_t authSchemeSize;     /*!< @brief Maximum size of the auth scheme. */
} OtaAppBuffer_t;

/**
 * @ingroup ota_private_struct_types
 * @brief  The OTA agent is a singleton today. The structure keeps it nice and organized.
 */

typedef struct OtaAgentContext
{
    OtaState_t state;                                      /*!< State of the OTA agent. */
    uint8_t pThingName[ otaconfigMAX_THINGNAME_LEN + 1U ]; /*!< Thing name + zero terminator. */
    OtaFileContext_t fileContext;                          /*!< Static array of OTA file structures. */
    uint32_t fileIndex;                                    /*!< Index of current file in the array. */
    uint32_t serverFileID;                                 /*!< Variable to store current file ID passed down */
    uint8_t pActiveJobName[ OTA_JOB_ID_MAX_SIZE ];         /*!< The currently active job name. We only allow one at a time. */
    uint8_t * pClientTokenFromJob;                         /*!< The clientToken field from the latest update job. */
    uint32_t timestampFromJob;                             /*!< Timestamp received from the latest job document. */
    OtaImageState_t imageState;                            /*!< The current application image state. */
    uint32_t numOfBlocksToReceive;                         /*!< Number of data blocks to receive per data request. */
    OtaAgentStatistics_t statistics;                       /*!< The OTA agent statistics block. */
    uint32_t requestMomentum;                              /*!< The number of requests sent before a response was received. */
    OtaInterfaces_t * pOtaInterface;                       /*!< Collection of all interfaces used by the agent. */
    OtaAppCallback_t OtaAppCallback;                       /*!< OTA App callback. */
    OtaCustomJobCallback_t customJobCallback;              /*!< Custom job callback. */
    uint8_t unsubscribeOnShutdown;                         /*!< Flag to indicate if unsubscribe from job topics should be done at shutdown. */
} OtaAgentContext_t;

/*------------------------- OTA Public API --------------------------*/

/**
 * @brief OTA Agent initialization function.
 *
 * Initialize the OTA engine by starting the OTA Agent ("OTA Task") in the system. This function must
 * be called with the connection client context before calling @ref OTA_CheckForUpdate. Only one
 * OTA Agent may exist.
 *
 * @param[in] pOtaBuffer Buffers used by the agent to store different params.
 * @param[in] pOtaInterfaces A pointer to the OS context.
 * @param[in] pThingName A pointer to a C string holding the Thing name.
 * @param[in] OtaAppCallback Static callback function for when an OTA job is complete. This function will have
 * input of the state of the OTA image after download and during self-test.
 * @return OtaErr_t The state of the OTA Agent upon return from the OtaState_t enum.
 * If the agent was successfully initialized and ready to operate, the state will be
 * OtaAgentStateReady. Otherwise, it will be one of the other OtaState_t enum values.
 */
/* @[declare_ota_init] */
OtaErr_t OTA_Init( OtaAppBuffer_t * pOtaBuffer,
                   OtaInterfaces_t * pOtaInterfaces,
                   const uint8_t * pThingName,
                   OtaAppCallback_t OtaAppCallback );
/* @[declare_ota_init] */

/**
 * @brief Signal to the OTA Agent to shut down.
 *
 * Signals the OTA agent task to shut down. The OTA agent will unsubscribe from all MQTT job
 * notification topics, stop in progress OTA jobs, if any, and clear all resources.
 *
 * @param[in] ticksToWait The number of ticks to wait for the OTA Agent to complete the shutdown process.
 * If this is set to zero, the function will return immediately without waiting. The actual state is
 * returned to the caller.
 *
 * @param[in] unsubscribeFlag Flag to indicate if unsubscribe operations should be performed from the job topics when
 * shutdown is called. If the flag is 0 then unsubscribe operations are not called for job topics If application
 * requires it to be unsubscribed from the job topics then flag must be set to 1 when calling OTA_Shutdown.
 *
 * @return One of the OTA agent states from the OtaState_t enum.
 * A normal shutdown will return OtaAgentStateNotReady. Otherwise, refer to the OtaState_t enum for details.
 */
/* @[declare_ota_shutdown] */
OtaState_t OTA_Shutdown( uint32_t ticksToWait,
                         uint8_t unsubscribeFlag );
/* @[declare_ota_shutdown] */

/**
 * @brief Get the current state of the OTA agent.
 *
 * @return The current state of the OTA agent.
 */
/* @[declare_ota_getstate] */
OtaState_t OTA_GetState( void );
/* @[declare_ota_getstate] */

/**
 * @brief Activate the newest MCU image received via OTA.
 *
 * This function should reset the MCU and cause a reboot of the system to execute the newly updated
 * firmware. It should be called by the user code sometime after the OtaJobEventActivate event
 * is passed to the users application via the OTA Job Complete Callback mechanism. Refer to the
 * @ref OTA_Init function for more information about configuring the callback.
 *
 * @return OtaErrNone if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
/* @[declare_ota_activatenewimage] */
OtaErr_t OTA_ActivateNewImage( void );
/* @[declare_ota_activatenewimage] */

/**
 * @brief Set the state of the current MCU image.
 *
 * The states are OtaImageStateTesting, OtaImageStateAccepted, OtaImageStateAborted or
 * OtaImageStateRejected; see OtaImageState_t documentation. This will update the status of the
 * current image and publish to the active job status topic.
 *
 * @param[in] state The state to set of the OTA image.
 *
 * @return OtaErrNone if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
/* @[declare_ota_setimagestate] */
OtaErr_t OTA_SetImageState( OtaImageState_t state );
/* @[declare_ota_setimagestate] */

/**
 * @brief Get the state of the currently running MCU image.
 *
 * The states are OtaImageStateTesting, OtaImageStateAccepted, OtaImageStateAborted or
 * OtaImageStateRejected; see OtaImageState_t documentation.
 *
 * @return The state of the current context's OTA image.
 */
/* @[declare_ota_getimagestate] */
OtaImageState_t OTA_GetImageState( void );
/* @[declare_ota_getimagestate] */

/**
 * @brief Request for the next available OTA job from the job service.
 *
 * @return OtaErrNone if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
/* @[declare_ota_checkforupdate] */
OtaErr_t OTA_CheckForUpdate( void );
/* @[declare_ota_checkforupdate] */

/**
 * @brief Suspend OTA agent operations .
 *
 * @return OtaErrNone if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
/* @[declare_ota_suspend] */
OtaErr_t OTA_Suspend( void );
/* @[declare_ota_suspend] */

/**
 * @brief Resume OTA agent operations .
 *
 * @return OtaErrNone if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
/* @[declare_ota_resume] */
OtaErr_t OTA_Resume( void );
/* @[declare_ota_resume] */

/**
 * @brief OTA agent event processing loop.
 *
 * This is the main event loop to handle events for OTA update and needs to be called by
 * the application task. This loop will continue to handle and execute events received for
 * OTA Update until this tasks is terminated by the application.
 *
 * @param[in] pUnused Can be used to pass down functionality to the agent task, Unused for now.
 * This can be a function pointer that executes as the first routine when the
 * event loop starts.
 */
/* @[declare_ota_eventprocessingtask] */
void OTA_EventProcessingTask( void * pUnused );
/* @[declare_ota_eventprocessingtask] */


/**
 * @brief Signal event to the OTA Agent task.
 *
 * This function adds the event to the back of event queue and used
 * by internal OTA modules to signal agent task.
 *
 * @param[in] pEventMsg Event to be added to the queue
 * @return true If operation is successful, false If the event can not be added
 */
/* @[declare_ota_signalevent] */
bool OTA_SignalEvent( const OtaEventMsg_t * const pEventMsg );
/* @[declare_ota_signalevent] */

/*---------------------------------------------------------------------------*/
/*							Statistics API									 */
/*---------------------------------------------------------------------------*/

/**
 * @brief Get the statistics of OTA message packets.
 *
 * Packet statistics are:
 * <ul>
 *  <li> Received: The number of OTA packets that have been received
 *  but not necessarily queued for processing by the OTA agent.
 *  <li> Queued: The number of OTA packets that have been queued for
 *  processing. This implies there was a free message queue entry so
 *  it can be passed to the agent for processing.
 *  <li> Processed: The number of OTA packets that have actually been
 *  processed.
 *  <li> Dropped: The number of OTA packets that have been dropped
 *  because of either no queue or at shutdown cleanup.
 *</ul>
 * @note Calling @ref OTA_Init will reset this statistic.
 *
 * @return OtaErrNone if the statistics can be received successfully.
 */
/* @[declare_ota_getstatistics] */
OtaErr_t OTA_GetStatistics( OtaAgentStatistics_t * pStatistics );
/* @[declare_ota_getstatistics] */

/**
 * @brief Error code to string conversion for OTA errors.
 *
 * @param[in] err The error to convert to a string.
 *
 * @return The string representation of the error.
 */
/* @[declare_ota_err_strerror] */
const char * OTA_Err_strerror( OtaErr_t err );
/* @[declare_ota_err_strerror] */

/**
 * @brief Error code to string conversion for OTA Job Parsing errors.
 *
 * @param[in] err The error to convert to a string.
 *
 * @return The string representation of the error.
 */
/* @[declare_ota_jobparse_strerror] */
const char * OTA_JobParse_strerror( OtaJobParseErr_t err );
/* @[declare_ota_jobparse_strerror] */

/**
 * @brief Status code to string conversion for OTA PAL status.
 *
 * @param[in] status The status to convert to a string.
 *
 * @return The string representation of the status.
 */
/* @[declare_ota_palstatus_strerror] */
const char * OTA_PalStatus_strerror( OtaPalMainStatus_t status );
/* @[declare_ota_palstatus_strerror] */

/**
 * @brief Status code to string conversion for OTA OS status.
 *
 * @param[in] status The status to convert to a string.
 *
 * @return The string representation of the status.
 */
/* @[declare_ota_osstatus_strerror] */
const char * OTA_OsStatus_strerror( OtaOsStatus_t status );
/* @[declare_ota_osstatus_strerror] */

#endif /* ifndef OTA_H */
