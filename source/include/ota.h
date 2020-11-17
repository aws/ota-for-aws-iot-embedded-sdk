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
 * @file ota.h
 * @brief OTA Agent Interface
 */

#ifndef _AWS_IOT_OTA_AGENT_H_
#define _AWS_IOT_OTA_AGENT_H_

/* Standard includes. */
/* For FILE type in OtaFileContext_t.*/
#include <stdio.h>
#include <stdint.h>

/* OTA Library Interface include. */
#include "ota_os_interface.h"
#include "ota_mqtt_interface.h"
#include "ota_http_interface.h"

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 */

/* bool is defined in only C99+. */
#if defined( __cplusplus ) || ( defined( __STDC_VERSION__ ) && ( __STDC_VERSION__ >= 199901L ) )
    #include <stdbool.h>
#elif !defined( bool )
    #define bool     int8_t
    #define false    ( int8_t ) 0
    #define true     ( int8_t ) 1
#endif
/** @endcond */

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
extern const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ];

/*-------------------------- OTA enumerated types --------------------------*/

/**
 * @enums{ota,OTA library}
 */

/**
 * @ingroup ota_datatypes_enums
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
 * @ingroup ota_datatypes_enums
 * @brief OTA Agent Events.
 *
 * The events sent to OTA agent.
 */
typedef enum OtaEvent
{
    OtaAgentEventStart = 0,
    OtaAgentEventStartSelfTest,
    OtaAgentEventRequestJobDocument,
    OtaAgentEventReceivedJobDocument,
    OtaAgentEventCreateFile,
    OtaAgentEventRequestFileBlock,
    OtaAgentEventReceivedFileBlock,
    OtaAgentEventRequestTimer,
    OtaAgentEventCloseFile,
    OtaAgentEventSuspend,
    OtaAgentEventResume,
    OtaAgentEventUserAbort,
    OtaAgentEventShutdown,
    OtaAgentEventMax
} OtaEvent_t;

/**
 * @ingroup ota_datatypes_enums
 * @brief OTA Platform Image State.
 *
 * The image state set by platform implementation.
 */
typedef enum OtaPalImageState
{
    OtaPalImageStateUnknown = 0,
    OtaPalImageStatePendingCommit,
    OtaPalImageStateValid,
    OtaPalImageStateInvalid,
} OtaPalImageState_t;

/**
 * @ingroup ota_datatypes_enums
 * @brief OTA job document parser error codes.
 */
typedef enum OtaJobParseErr
{
    OtaJobParseErrUnknown = -1,        /* The error code has not yet been set by a logic path. */
    OtaJobParseErrNone = 0,            /* Signifies no error has occurred. */
    OtaJobParseErrBusyWithExistingJob, /* We're busy with a job but received a new job document. */
    OtaJobParseErrNullJob,             /* A null job was reported (no job ID). */
    OtaJobParseErrUpdateCurrentJob,    /* We're already busy with the reported job ID. */
    OtaJobParseErrZeroFileSize,        /* Job document specified a zero sized file. This is not allowed. */
    OtaJobParseErrNonConformingJobDoc, /* The job document failed to fulfill the model requirements. */
    OtaJobParseErrBadModelInitParams,  /* There was an invalid initialization parameter used in the document model. */
    OtaJobParseErrNoContextAvailable,  /* There was not an OTA context available. */
    OtaJobParseErrNoActiveJobs,        /* No active jobs are available in the service. */
} OtaJobParseErr_t;


/**
 * @ingroup ota_datatypes_enums
 * @brief OTA Job callback events.
 *
 * After an OTA update image is received and authenticated, the agent calls the user
 * callback (set with the @ref OTA_AgentInit API) with the value OtaJobEventActivate to
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
    OtaJobEventActivate = 0,  /*!< OTA receive is authenticated and ready to activate. */
    OtaJobEventFail = 1,      /*!< OTA receive failed. Unable to use this update. */
    OtaJobEventStartTest = 2, /*!< OTA job is now in self test, perform user tests. */
    OtaLastJobEvent = OtaJobEventStartTest
} OtaJobEvent_t;


/**
 * @ingroup ota_datatypes_enums
 * @brief OTA Image states.
 *
 * After an OTA update image is received and authenticated, it is logically moved to
 * the Self Test state by the OTA agent pending final acceptance. After the image is
 * activated and tested by your user code, you should put it into either the Accepted
 * or Rejected state by calling @ref OTA_SetImageState ( OtaImageStateAccepted ) or
 * @ref OTA_SetImageState ( OtaImageStateRejected ). If the image is accepted, it becomes
 * the main firmware image to be booted from then on. If it is rejected, the image is
 * no longer valid and shall not be used, reverting to the last known good image.
 *
 * If you want to abort an active OTA transfer, you may do so by calling the API
 * @ref OTA_SetImageState ( OtaImageStateAborted ).
 */
typedef enum OtaImageState
{
    OtaImageStateUnknown = 0,  /*!< The initial state of the OTA MCU Image. */
    OtaImageStateTesting = 1,  /*!< The state of the OTA MCU Image post successful download and reboot. */
    OtaImageStateAccepted = 2, /*!< The state of the OTA MCU Image post successful download and successful self_test. */
    OtaImageStateRejected = 3, /*!< The state of the OTA MCU Image when the job has been rejected. */
    OtaImageStateAborted = 4,  /*!< The state of the OTA MCU Image after a timeout publish to the stream request fails.
                                *   Also if the OTA MCU image is aborted in the middle of a stream. */
    OtaLastImageState = OtaImageStateAborted
} OtaImageState_t;


/*------------------------- OTA callbacks --------------------------*/

/**
 * @functionpointers{ota,OTA library}
 */

/* Forward declaration of OtaFileContext_t. */
typedef struct OtaFileContext   OtaFileContext_t;

/**
 * @brief OTA Error type.
 */
typedef uint32_t                OtaErr_t;

/**
 * @ingroup ota_datatypes_functionpointers
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
 */
typedef void (* OtaCompleteCallback_t)( OtaJobEvent_t eEvent );

/**
 * @ingroup ota_datatypes_functionpointers
 * @brief OTA abort callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback is used to override the behavior of how a job is aborted.
 *
 * @param[in] C File context of the job being aborted
 */
typedef OtaErr_t (* OtaPALAbortCallback_t)( OtaFileContext_t * const C );

/**
 * @ingroup ota_datatypes_functionpointers
 * @brief OTA new image received callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback is used to override the behavior of what happens when a new image is
 * activated.
 *
 * @param[in] serverFileID File ID of the image received
 */
typedef OtaErr_t (* OtaPALActivateNewImageCallback_t)( uint32_t serverFileID );

/**
 * @ingroup ota_datatypes_functionpointers
 * @brief OTA close file callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback is used to override the behavior of what happens when a file is closed.
 *
 * @param[in] C File context of the job being aborted
 */
typedef OtaErr_t (* OtaPALCloseFileCallback_t)( OtaFileContext_t * const C );

/**
 * @ingroup ota_datatypes_functionpointers
 * @brief OTA create file to store received data callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback is used to override the behavior of how a new file is created.
 *
 * @param[in] C File context of the job being aborted
 */
typedef OtaErr_t (* OtaPALCreateFileForRxCallback_t)( OtaFileContext_t * const C );

/**
 * @ingroup ota_datatypes_functionpointers
 * @brief OTA Get Platform Image State callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback is used to override the behavior of returning the platform image state.
 *
 * @param[in] serverFileID File ID of the image received
 */
typedef OtaPalImageState_t (* OtaPALGetPlatformImageStateCallback_t)( uint32_t serverFileID );

/**
 * @ingroup ota_datatypes_functionpointers
 * @brief OTA Reset Device callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback is used to override the behavior of what happens when the OTA agent resets the device.
 *
 * @param[in] serverFileID File ID of the image received
 */
typedef OtaErr_t (* OtaPALResetDeviceCallback_t)( uint32_t serverFileID );

/**
 * @ingroup ota_datatypes_functionpointers
 * @brief OTA Set Platform Image State callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback is used to override the behavior of how a platform image state is stored.
 *
 * @param[in] serverFileID File ID of the image received
 * @param[in] eState Platform Image State to be state
 */
typedef OtaErr_t (* OtaPALSetPlatformImageStateCallback_t)( uint32_t serverFileID,
                                                            OtaImageState_t eState );

/**
 * @ingroup ota_datatypes_functionpointers
 * @brief OTA Write Block callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback is used to override the behavior of how a block is written to a file.
 *
 * @param[in] C File context of the job being aborted
 * @param[in] iOffset Offset into the file to write the data
 * @param[in] pacData Data to be written at the offset
 * @param[in] iBlocksize Block size of the data to be written
 */
typedef int16_t (* OtaPALWriteBlockCallback_t)( OtaFileContext_t * const C,
                                                uint32_t iOffset,
                                                uint8_t * const pacData,
                                                uint32_t iBlockSize );

/**
 * @ingroup ota_datatypes_functionpointers
 * @brief Custom Job callback function typedef.
 *
 * The user may register a callback function when initializing the OTA Agent. This
 * callback will be called when the OTA agent cannot parse a job document.
 *
 * @param[in] pcJSON Pointer to the json document received by the OTA agent
 * @param[in] ulMsgLen Length of the json document received by the agent
 */
typedef OtaJobParseErr_t (* OtaCustomJobCallback_t)( const char * pcJSON,
                                                     uint32_t ulMsgLen );


/*--------------------------- OTA structs ----------------------------*/

/**
 * @structs{ota,OTA library}
 */

/**
 * @ingroup ota_datatypes_structs
 * @brief OTA PAL callback structure
 */
typedef struct
{
    OtaPALAbortCallback_t abortUpdate;                           /*!< OTA Abort callback pointer */
    OtaPALActivateNewImageCallback_t activateNewImage;           /*!< OTA Activate New Image callback pointer */
    OtaPALCloseFileCallback_t closeFile;                         /*!< OTA Close File callback pointer */
    OtaPALCreateFileForRxCallback_t createFileForRx;             /*!< OTA Create File for Receive callback pointer */
    OtaPALGetPlatformImageStateCallback_t getPlatformImageState; /*!< OTA Get Platform Image State callback pointer */
    OtaPALResetDeviceCallback_t resetDevice;                     /*!< OTA Reset Device callback pointer */
    OtaPALSetPlatformImageStateCallback_t setPlatformImageState; /*!< OTA Set Platform Image State callback pointer */
    OtaPALWriteBlockCallback_t writeBlock;                       /*!< OTA Write Block callback pointer */
    OtaCompleteCallback_t completeCallback;                      /*!< OTA Job Completed callback pointer */
    OtaCustomJobCallback_t customJobCallback;                    /*!< OTA Custom Job callback pointer */
} OtaPalCallbacks_t;

/**
 * @ingroup ota_datatypes_struct_constants
 * @brief A composite cryptographic signature structure able to hold our largest supported signature.
 */

#define kOTA_MaxSignatureSize    256        /* Max bytes supported for a file signature (2048 bit RSA is 256 bytes). */

/**
 * @ingroup ota_datatypes_structs
 * @brief OTA File Signature info.
 *
 * File key signature information to verify the authenticity of the incoming file
 */
typedef struct
{
    uint16_t size;                         /*!< Size, in bytes, of the signature. */
    uint8_t data[ kOTA_MaxSignatureSize ]; /*!< The binary signature data. */
} Sig256_t;

/**
 * @ingroup ota_datatypes_structs
 * @brief OTA Interface for referencing different components.
 *
 * Information about the different interfaces used to initialize
 * the OTA agent with references to components.
 */
typedef struct OtaInterface
{
    OtaOSInterface_t os;     /*!< OS interface to store event, timers and memory operations. */
    OtaMqttInterface_t mqtt; /*!< MQTT interface that references the publish subscribe methods and callbacks. */
    OtaHttpInterface_t http; /*!< HTTP interface to request data. */
    OtaPalCallbacks_t pal;   /*!< OTA PAL callback structure. */
} OtaInterfaces_t;

/**
 * @ingroup ota_datatypes_structs
 * @brief OTA Application Buffer size information.
 *
 * File key signature information to verify the authenticity of the incoming file
 */
typedef struct OtaAppBuffer
{
    uint8_t * pUpdateFilePath;   /*!< Path to store the files. */
    uint16_t updateFilePathsize; /*!< Maximum size of the file path. */
    uint8_t * pCertFilePath;     /*!< Path to certificate file. */
    uint16_t certFilePathSize;   /*!< Maximum size of the certificate file path. */
    uint8_t * pStreamName;       /*!< Name of stream to download the files. */
    uint16_t streamNameSize;     /*!< Maximum size of the stream name. */
    uint8_t * pDecodeMemory;     /*!< Place to store the decoded files. */
    uint32_t decodeMemorySize;   /*!< Maximum size of the decoded files buffer. */
    uint8_t * pFileBitmap;       /*!< Bitmap of the parameters received. */
    uint16_t fileBitmapSize;     /*!< Maximum size of the bitmap. */
    uint8_t * pUrl;              /*!< Presigned url to download files from S3. */
    uint16_t urlSize;            /*!< Maximum size of the URL. */
    uint8_t * pAuthScheme;       /*!< Authentication scheme used to validate download. */
    uint16_t authSchemeSize;     /*!< Maximum size of the auth scheme. */
} OtaAppBuffer_t;

/**
 * @ingroup ota_datatypes_structs
 * @brief OTA File Context Information.
 *
 * Information about an OTA Update file that is to be streamed. This structure is filled in from a
 * job notification MQTT message. Currently only one file context can be streamed at time.
 */
struct OtaFileContext
{
    uint8_t * pFilePath;         /*!< Update file pathname. */
    int16_t filePathMaxSize;     /*!< Maximum size of the update file path */
    #if defined( WIN32 ) || defined( __linux__ )
        FILE * pFile;            /*!< File type is stdio FILE structure after file is open for write. */
    #else
        uint8_t * pFile;         /*!< File type is RAM/Flash image pointer after file is open for write. */
    #endif
    uint32_t fileSize;           /*!< The size of the file in bytes. */
    uint32_t blocksRemaining;    /*!< How many blocks remain to be received (a code optimization). */
    uint32_t fileAttributes;     /*!< Flags specific to the file being received (e.g. secure, bundle, archive). */
    uint32_t serverFileID;       /*!< The file is referenced by this numeric ID in the OTA job. */
    uint8_t * pJobName;          /*!< The job name associated with this file from the job service. */
    int16_t jobNameMaxSize;      /*!< Maximum size of the job name. */
    uint8_t * pStreamName;       /*!< The stream associated with this file from the OTA service. */
    int16_t streamNameMaxSize;   /*!< Maximum size of the stream name. */
    uint8_t * pRxBlockBitmap;    /*!< Bitmap of blocks received (for deduplicating and missing block request). */
    int16_t blockBitmapMaxSize;  /*!< Maximum size of the block bitmap. */
    uint8_t * pCertFilepath;     /*!< Pathname of the certificate file used to validate the receive file. */
    int16_t certFilePathMaxSize; /*!< Maximum certificate path size. */
    uint8_t * pUpdateUrlPath;    /*!< Url for the file. */
    int8_t updateUrlMaxSize;     /*!< Maximum size of the url. */
    uint8_t * pAuthScheme;       /*!< Authorization scheme. */
    int8_t authSchemeMaxSize;    /*!< Maximum size of the auth scheme. */
    uint32_t updaterVersion;     /*!< Used by OTA self-test detection, the version of Firmware that did the update. */
    bool isInSelfTest;           /*!< True if the job is in self test mode. */
    uint8_t * pProtocols;        /*!< Authorization scheme. */
    int16_t protocolMaxSize;     /*!< Maximum size of the  supported protocols string. */
    uint32_t fileType;           /*!< The file type id set when creating the OTA job. */
    Sig256_t * pSignature;       /*!< Pointer to the file's signature structure. */
};

/*------------------------- OTA defined constants --------------------------*/

/**
 * @constantspage{ota,OTA library}
 *
 * @section ota_constants_err_codes OTA Error Codes
 * @brief OTA Agent error codes returned by OTA agent API.
 *
 * @snippet this define_ota_err_codes
 *
 * OTA agent error codes are in the upper 8 bits of the 32 bit OTA error word, OtaErr_t.
 *
 * @section ota_constants_err_code_helpers OTA Error Code Helper constants
 * @brief OTA Error code helper constant for extracting the error code from the OTA error returned.
 *
 * @snippet this define_ota_err_code_helpers
 *
 * OTA error codes consist of an agent code in the upper 8 bits of a 32 bit word and sometimes
 * merged with a platform specific code in the lower 24 bits. You must refer to the platform PAL
 * layer in use to determine the meaning of the lower 24 bits.
 */

/* @[define_ota_err_codes] */
#define OTA_ERR_PANIC                        0xfe000000U /*!< Unrecoverable Firmware error. Probably should log error and reboot. */
#define OTA_ERR_UNINITIALIZED                0xff000000U /*!< The error code has not yet been set by a logic path. */
#define OTA_ERR_NONE                         0x00000000U /*!< No error occurred during the operation. */
#define OTA_ERR_SIGNATURE_CHECK_FAILED       0x01000000U /*!< The signature check failed for the specified file. */
#define OTA_ERR_BAD_SIGNER_CERT              0x02000000U /*!< The signer certificate was not readable or zero length. */
#define OTA_ERR_OUT_OF_MEMORY                0x03000000U /*!< General out of memory error. */
#define OTA_ERR_ACTIVATE_FAILED              0x04000000U /*!< The activation of the new OTA image failed. */
#define OTA_ERR_COMMIT_FAILED                0x05000000U /*!< The acceptance commit of the new OTA image failed. */
#define OTA_ERR_REJECT_FAILED                0x06000000U /*!< Error trying to reject the OTA image. */
#define OTA_ERR_ABORT_FAILED                 0x07000000U /*!< Error trying to abort the OTA. */
#define OTA_ERR_PUBLISH_FAILED               0x08000000U /*!< Attempt to publish a MQTT message failed. */
#define OTA_ERR_BAD_IMAGE_STATE              0x09000000U /*!< The specified OTA image state was out of range. */
#define OTA_ERR_NO_ACTIVE_JOB                0x0a000000U /*!< Attempt to set final image state without an active job. */
#define OTA_ERR_NO_FREE_CONTEXT              0x0b000000U /*!< There was not an OTA file context available for processing. */
#define OTA_ERR_HTTP_INIT_FAILED             0x0c000000U /*!< Error initializing the HTTP connection. */
#define OTA_ERR_HTTP_REQUEST_FAILED          0x0d000000U /*!< Error sending the HTTP request. */
#define OTA_ERR_FILE_ABORT                   0x10000000U /*!< Error in low level file abort. */
#define OTA_ERR_FILE_CLOSE                   0x11000000U /*!< Error in low level file close. */
#define OTA_ERR_RX_FILE_CREATE_FAILED        0x12000000U /*!< The PAL failed to create the OTA receive file. */
#define OTA_ERR_BOOT_INFO_CREATE_FAILED      0x13000000U /*!< The PAL failed to create the OTA boot info file. */
#define OTA_ERR_RX_FILE_TOO_LARGE            0x14000000U /*!< The OTA receive file is too big for the platform to support. */
#define OTA_ERR_NULL_FILE_PTR                0x20000000U /*!< Attempt to use a null file pointer. */
#define OTA_ERR_MOMENTUM_ABORT               0x21000000U /*!< Too many OTA stream requests without any response. */
#define OTA_ERR_DOWNGRADE_NOT_ALLOWED        0x22000000U /*!< Firmware version is older than the previous version. */
#define OTA_ERR_SAME_FIRMWARE_VERSION        0x23000000U /*!< Firmware version is the same as previous. New firmware could have failed to commit. */
#define OTA_ERR_JOB_PARSER_ERROR             0x24000000U /*!< An error occurred during job document parsing. See reason sub-code. */
#define OTA_ERR_FAILED_TO_ENCODE_CBOR        0x25000000U /*!< Failed to encode CBOR object. */
#define OTA_ERR_IMAGE_STATE_MISMATCH         0x26000000U /*!< The OTA job was in Self Test but the platform image state was not. Possible tampering. */
#define OTA_ERR_GENERIC_INGEST_ERROR         0x27000000U /*!< A failure in block ingestion not caused by the PAL. See the error sub code. */
#define OTA_ERR_USER_ABORT                   0x28000000U /*!< User aborted the active OTA. */
#define OTA_ERR_RESET_NOT_SUPPORTED          0x29000000U /*!< We tried to reset the device but the device does not support it. */
#define OTA_ERR_TOPIC_TOO_LARGE              0x2a000000U /*!< Attempt to build a topic string larger than the supplied buffer. */
#define OTA_ERR_SELF_TEST_TIMER_FAILED       0x2b000000U /*!< Attempt to start self-test timer failed. */
#define OTA_ERR_EVENT_Q_SEND_FAILED          0x2c000000U /*!< Posting event message to the event queue failed. */
#define OTA_ERR_INVALID_DATA_PROTOCOL        0x2d000000U /*!< Job does not have a valid protocol for data transfer. */
#define OTA_ERR_OTA_AGENT_STOPPED            0x2e000000U /*!< Returned when operations are performed that requires OTA Agent running & its stopped. */
#define OTA_ERR_EVENT_Q_CREATE_FAILED        0x2f000000U /*!< Failed to create the event queue. */
#define OTA_ERR_EVENT_Q_RECEIVE_FAILED       0x30000000U /*!< Failed to receive from the event queue. */
#define OTA_ERR_EVENT_Q_DELETE_FAILED        0x31000000U /*!< Failed to delete the event queue. */
#define OTA_ERR_EVENT_TIMER_CREATE_FAILED    0x32000000U /*!< Failed to create the timer. */
#define OTA_ERR_EVENT_TIMER_START_FAILED     0x33000000U /*!< Failed to create the timer. */
#define OTA_ERR_EVENT_TIMER_STOP_FAILED      0x34000000U /*!< Failed to stop the timer. */
#define OTA_ERR_EVENT_TIMER_DELETE_FAILED    0x35000000U /*!< Failed to delete the timer. */
#define OTA_ERR_SUBSCRIBE_FAILED             0x40000000U /*!< Failed to subscribe to a topic. */
#define OTA_ERR_UNSUBSCRIBE_FAILED           0x41000000U /*!< Failed to unsubscribe from a topic. */
#define OTA_ERR_FAILED_TO_DECODE_CBOR        0x42000000U /*!< Failed to decode CBOR object. */

/* @[define_ota_err_codes] */

/* @[define_ota_err_code_helpers] */
#define OTA_PAL_ERR_MASK                0xffffffUL    /*!< The PAL layer uses the signed low 24 bits of the OTA error code. */
#define OTA_MAIN_ERR_MASK               0xff000000UL  /*!< Mask out all but the OTA Agent error code (high 8 bits). */
#define OTA_MAIN_ERR_SHIFT_DOWN_BITS    24U           /*!< The OTA Agent error code is the highest 8 bits of the word. */
/* @[define_ota_err_code_helpers] */


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
 * @param[in] completeCallback Static callback function for when an OTA job is complete. This function will have
 * input of the state of the OTA image after download and during self-test.
 * @return OtaErr_t The state of the OTA Agent upon return from the OtaState_t enum.
 * If the agent was successfully initialized and ready to operate, the state will be
 * OtaAgentStateReady. Otherwise, it will be one of the other OtaState_t enum values.
 */
OtaErr_t OTA_AgentInit( OtaAppBuffer_t * pOtaBuffer,
                        OtaInterfaces_t * pOtaInterfaces,
                        const uint8_t * pThingName,
                        OtaCompleteCallback_t completeCallback );

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
 * @return One of the OTA agent states from the OtaState_t enum.
 * A normal shutdown will return OtaAgentStateNotReady. Otherwise, refer to the OtaState_t enum for details.
 */
OtaState_t OTA_AgentShutdown( uint32_t ticksToWait );

/**
 * @brief Get the current state of the OTA agent.
 *
 * @return The current state of the OTA agent.
 */
OtaState_t OTA_GetAgentState( void );

/**
 * @brief Activate the newest MCU image received via OTA.
 *
 * This function should reset the MCU and cause a reboot of the system to execute the newly updated
 * firmware. It should be called by the user code sometime after the OtaJobEventActivate event
 * is passed to the users application via the OTA Job Complete Callback mechanism. Refer to the
 * @ref OTA_AgentInit function for more information about configuring the callback.
 *
 * @return OTA_ERR_NONE if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
OtaErr_t OTA_ActivateNewImage( void );

/**
 * @brief Set the state of the current MCU image.
 *
 * The states are OtaImageStateTesting, OtaImageStateAccepted, OtaImageStateAborted or
 * OtaImageStateRejected; see OtaImageState_t documentation. This will update the status of the
 * current image and publish to the active job status topic.
 *
 * @param[in] state The state to set of the OTA image.
 *
 * @return OTA_ERR_NONE if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
OtaErr_t OTA_SetImageState( OtaImageState_t state );

/**
 * @brief Get the state of the currently running MCU image.
 *
 * The states are OtaImageStateTesting, OtaImageStateAccepted, OtaImageStateAborted or
 * OtaImageStateRejected; see OtaImageState_t documentation.
 *
 * @return The state of the current context's OTA image.
 */
OtaImageState_t OTA_GetImageState( void );

/**
 * @brief Request for the next available OTA job from the job service.
 *
 * @return OTA_ERR_NONE if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
OtaErr_t OTA_CheckForUpdate( void );

/**
 * @brief Suspend OTA agent operations .
 *
 * @return OTA_ERR_NONE if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
OtaErr_t OTA_Suspend( void );

/**
 * @brief Resume OTA agent operations .
 *
 * @param[in] pConnection Update connection context.
 *
 * @return OTA_ERR_NONE if successful, otherwise an error code prefixed with 'kOTA_Err_' from the
 * list above.
 */
OtaErr_t OTA_Resume( void * pConnection );

/**
 * @brief OTA agent task function.
 *
 * @param[in] pUnused Can be used to pass down functionality to the agent task, Unused for now.
 */
void otaAgentTask( const void * pUnused );

/*---------------------------------------------------------------------------*/
/*							Statistics API									 */
/*---------------------------------------------------------------------------*/

/**
 * @brief Get the number of OTA message packets received by the OTA agent.
 *
 * @note Calling @ref OTA_AgentInit will reset this statistic.
 *
 * @return The number of OTA packets that have been received but not
 * necessarily queued for processing by the OTA agent.
 */
uint32_t OTA_GetPacketsReceived( void );

/**
 * @brief Get the number of OTA message packets queued by the OTA agent.
 *
 * @note Calling @ref OTA_AgentInit will reset this statistic.
 *
 * @return The number of OTA packets that have been queued for processing.
 * This implies there was a free message queue entry so it can be passed
 * to the agent for processing.
 */
uint32_t OTA_GetPacketsQueued( void );

/**
 * @brief Get the number of OTA message packets processed by the OTA agent.
 *
 * @note Calling @ref OTA_AgentInit will reset this statistic.
 *
 * @return the number of OTA packets that have actually been processed.
 *
 */
uint32_t OTA_GetPacketsProcessed( void );

/**
 * @brief Get the number of OTA message packets dropped by the OTA agent.
 *
 * @note Calling @ref OTA_AgentInit will reset this statistic.
 *
 * @return the number of OTA packets that have been dropped because
 * of either no queue or at shutdown cleanup.
 */
uint32_t OTA_GetPacketsDropped( void );

#endif /* ifndef _AWS_IOT_OTA_AGENT_H_ */
