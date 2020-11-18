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
 * @file ota_utest.c
 * @brief Unit tests for functions in OTA agent.
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>

/* 3rdparty includes. */
#include <unistd.h>
#include <pthread.h>
#include "unity.h"

/* For accessing OTA private functions. */
#include "ota_appversion32.h"
#include "ota.h"
#include "ota_private.h"

/* Mock OTA PAL. */
#include "mock_ota_platform_interface.h"

/* test includes. */
#include "utest_helpers.h"

/* Job document for testing. */
#define OTA_TEST_FILE_SIZE          10240
#define OTA_TEST_FILE_SIZE_STR      "10240"
#define JOB_DOC_A                   "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_A_LENGTH            ( sizeof( JOB_DOC_A ) - 1 )
#define JOB_DOC_B                   "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob21\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_B_LENGTH            ( sizeof( JOB_DOC_B ) - 1 )
#define JOB_DOC_SELF_TEST           "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"IN_PROGRESS\",\"statusDetails\":{\"self_test\":\"ready\",\"updatedBy\":\"0x1000000\"},\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_SELF_TEST_LENGTH    ( sizeof( JOB_DOC_SELF_TEST ) - 1 )
#define JOB_DOC_INVALID             "not a json"
#define JOB_DOC_INVALID_LENGTH      ( sizeof( JOB_DOC_INVALID ) - 1 )

/* Firmware version. */
const AppVersion32_t appFirmwareVersion =
{
    .u.x.major = 1,
    .u.x.minor = 0,
    .u.x.build = 1,
};

/* OTA code signing signature algorithm. */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

/* OTA client name. */
static const char * pOtaDefaultClientId = "ota_utest";

/* OTA interface. */
static OtaInterfaces_t otaInterfaces;

/* OTA application buffer. */
static OtaAppBuffer_t pOtaAppBuffer;
static uint8_t pUserBuffer[ 300 ];

/* OTA Event. */
static OtaEventMsg_t otaEvent;
static OtaEventData_t eventBuffer;
static pthread_mutex_t eventLock;
static bool eventIgnore;

/* OTA File handle and buffer. */
static FILE * pOtaFileHandle = NULL;
static uint8_t pOtaFileBuffer[ OTA_TEST_FILE_SIZE ];

/* Default wait time for OTA state machine transition. */
static const int otaDefaultWait = 1000;

/* ========================================================================== */

OtaErr_t mockOtaPalCreateFileForRx( OtaFileContext_t * pOtaFileCtx,
                                    int numCalls )
{
    pOtaFileHandle = ( FILE * ) pOtaFileBuffer;
    pOtaFileCtx->pFile = pOtaFileHandle;
    return OTA_ERR_NONE;
}

int16_t mockOtaPalWriteFileBlock( OtaFileContext_t * const pOtaFileCtx,
                                  uint32_t offset,
                                  uint8_t * const pData,
                                  uint32_t blockSize,
                                  int numCalls )
{
    if( offset >= OTA_TEST_FILE_SIZE )
    {
        TEST_ASSERT_TRUE_MESSAGE( false, "Offset is bigger than test file buffer." );
    }

    memcpy( pOtaFileBuffer + offset, pData, blockSize );
    return blockSize;
}

static OtaErr_t mockOSEventReset( OtaEventContext_t * unused )
{
    otaEvent.eventId = OtaAgentEventMax;
    otaEvent.pEventData = NULL;
    eventIgnore = false;

    return OTA_ERR_NONE;
}

/* Allow an event to be sent only once, after that ignore all incoming event. Useful to make sure
 * internal OTA handler are not able to send any event. */
static OtaErr_t mockOSEventSendThenStop( OtaEventContext_t * unused_1,
                                         const void * pEventMsg,
                                         uint32_t unused_2 )
{
    pthread_mutex_lock( &eventLock );

    if( !eventIgnore )
    {
        const OtaEventMsg_t * pOtaEvent = pEventMsg;

        otaEvent.eventId = pOtaEvent->eventId;
        otaEvent.pEventData = pOtaEvent->pEventData;

        eventIgnore = true;
    }

    pthread_mutex_unlock( &eventLock );

    return OTA_ERR_NONE;
}

/* A variant of mockOSEventSendThenStop, but return failure after first event sent. */
static OtaErr_t mockOSEventSendThenFail( OtaEventContext_t * unused_1,
                                         const void * pEventMsg,
                                         uint32_t unused_2 )
{
    OtaErr_t err = OTA_ERR_NONE;

    if( eventIgnore )
    {
        err = OTA_ERR_EVENT_Q_SEND_FAILED;
    }
    else
    {
        err = mockOSEventSendThenStop( unused_1, pEventMsg, unused_2 );
    }

    return err;
}

/* Allow events to be sent any number of times. */
static OtaErr_t mockOSEventSend( OtaEventContext_t * unused_1,
                                 const void * pEventMsg,
                                 uint32_t unused_2 )
{
    const OtaEventMsg_t * pOtaEvent = pEventMsg;

    otaEvent.eventId = pOtaEvent->eventId;
    otaEvent.pEventData = pOtaEvent->pEventData;

    return OTA_ERR_NONE;
}

/* Ignore all incoming events and return fail. */
static OtaErr_t mockOSEventSendAlwaysFail( OtaEventContext_t * unused_1,
                                           const void * pEventMsg,
                                           uint32_t unused_2 )
{
    return OTA_ERR_PANIC;
}

static OtaErr_t mockOSEventReceive( OtaEventContext_t * unused_1,
                                    void * pEventMsg,
                                    uint32_t unused_2 )
{
    OtaErr_t err = OTA_ERR_NONE;
    OtaEventMsg_t * pOtaEvent = pEventMsg;

    if( otaEvent.eventId != OtaAgentEventMax )
    {
        pOtaEvent->eventId = otaEvent.eventId;
        pOtaEvent->pEventData = otaEvent.pEventData;
        otaEvent.eventId = OtaAgentEventMax;
        otaEvent.pEventData = NULL;
    }
    else
    {
        usleep( 1000 );
        err = OTA_ERR_EVENT_Q_RECEIVE_FAILED;
    }

    return err;
}

static OtaErr_t stubOSTimerStart( OtaTimerId_t timerId,
                                  const char * const pTimerName,
                                  const uint32_t timeout,
                                  OtaTimerCallback_t callback )
{
    return OTA_ERR_NONE;
}

static OtaErr_t stubOSTimerStop( OtaTimerId_t timerId )
{
    return OTA_ERR_NONE;
}

static OtaErr_t stubOSTimerDelete( OtaTimerId_t timerId )
{
    return OTA_ERR_NONE;
}

static OtaErr_t stubMqttSubscribe( const char * unused_1,
                                   uint16_t unused_2,
                                   uint8_t unused_3,
                                   OtaMqttCallback_t unused_4 )
{
    return OTA_ERR_NONE;
}

static OtaErr_t stubMqttPublish( const char * const unused_1,
                                 uint16_t unused_2,
                                 const char * unused_3,
                                 uint32_t unused_4,
                                 uint8_t unused_5 )
{
    return OTA_ERR_NONE;
}

static OtaErr_t stubMqttUnsubscribe( const char * unused_1,
                                     uint16_t unused_2,
                                     uint8_t unused_3 )
{
    return OTA_ERR_NONE;
}

static void stubMqttJobCallback( void * unused )
{
}

static void stubMqttDataCallback( void * unused )
{
}

static void stubCompleteCallback( OtaJobEvent_t event )
{
}

/* Set default OTA OS interface to mockOSEventSendThenStop. This allows us to easily control the
 * state machine transition by blocking any event in OTA internal handlers. */
static void otaInterfaceDefault()
{
    otaInterfaces.os.event.init = mockOSEventReset;
    otaInterfaces.os.event.send = mockOSEventSendThenStop;
    otaInterfaces.os.event.recv = mockOSEventReceive;
    otaInterfaces.os.event.deinit = mockOSEventReset;

    otaInterfaces.os.timer.start = stubOSTimerStart;
    otaInterfaces.os.timer.stop = stubOSTimerStop;
    otaInterfaces.os.timer.delete = stubOSTimerDelete;

    otaInterfaces.os.mem.malloc = malloc;
    otaInterfaces.os.mem.free = free;

    otaInterfaces.mqtt.subscribe = stubMqttSubscribe;
    otaInterfaces.mqtt.publish = stubMqttPublish;
    otaInterfaces.mqtt.unsubscribe = stubMqttUnsubscribe;
    otaInterfaces.mqtt.jobCallback = stubMqttJobCallback;
    otaInterfaces.mqtt.dataCallback = stubMqttDataCallback;
}

static void otaInit( const char * pClientID,
                     OtaCompleteCallback_t completeCallback )
{
    pOtaAppBuffer.pUpdateFilePath = pUserBuffer;
    pOtaAppBuffer.updateFilePathsize = 100;
    pOtaAppBuffer.pCertFilePath = pOtaAppBuffer.pUpdateFilePath + pOtaAppBuffer.updateFilePathsize;
    pOtaAppBuffer.certFilePathSize = 100;
    pOtaAppBuffer.pStreamName = pOtaAppBuffer.pCertFilePath + pOtaAppBuffer.certFilePathSize;
    pOtaAppBuffer.streamNameSize = 50;
    OTA_AgentInit( &pOtaAppBuffer,
                   &otaInterfaces,
                   ( const uint8_t * ) pClientID,
                   completeCallback );
}

static void otaInitDefault()
{
    otaInit( pOtaDefaultClientId, stubCompleteCallback );
}

static void otaDeinit()
{
    prvPAL_Abort_IgnoreAndReturn( OTA_ERR_NONE );
    mockOSEventReset( NULL );
    OTA_AgentShutdown( 1 );
}

static void otaStartAgentTask()
{
    pthread_t otaThread;

    if( OtaAgentStateInit == OTA_GetAgentState() )
    {
        pthread_create( &otaThread, NULL, otaAgentTask, NULL );
    }
}

static void otaWaitForStateWithTimeout( OtaState_t state,
                                        int milliseconds )
{
    while( milliseconds > 0 && state != OTA_GetAgentState() )
    {
        usleep( 1000 );
        milliseconds--;
    }
}

static void otaWaitForState( OtaState_t state )
{
    otaWaitForStateWithTimeout( state, otaDefaultWait );
}


static void otaWaitForEmptyEventWithTimeout( int milliseconds )
{
    while( milliseconds > 0 && otaEvent.eventId != OtaAgentEventMax )
    {
        usleep( 1000 );
        milliseconds--;
    }
}

static void otaWaitForEmptyEvent()
{
    otaWaitForEmptyEventWithTimeout( otaDefaultWait );
}

static void otaGoToStateWithTimeout( OtaState_t state,
                                     int timeout_ms )
{
    OtaEventMsg_t otaEvent = { 0 };

    if( state == OTA_GetAgentState() )
    {
        return;
    }

    if( OtaAgentStateStopped == OTA_GetAgentState() )
    {
        otaInitDefault();
    }

    switch( state )
    {
        case OtaAgentStateInit:

            /* Nothing needs to be done here since we should either be in init state already or
             * we are in other running states. */
            break;

        case OtaAgentStateReady:
            otaStartAgentTask();
            break;

        case OtaAgentStateRequestingJob:
            /* Let the PAL says it's not in self test.*/
            prvPAL_GetPlatformImageState_IgnoreAndReturn( OtaPalImageStateValid );
            otaGoToStateWithTimeout( OtaAgentStateReady, timeout_ms );
            otaEvent.eventId = OtaAgentEventStart;
            OTA_SignalEvent( &otaEvent );
            break;

        case OtaAgentStateWaitingForJob:
            otaGoToStateWithTimeout( OtaAgentStateRequestingJob, timeout_ms );
            otaEvent.eventId = OtaAgentEventRequestJobDocument;
            OTA_SignalEvent( &otaEvent );
            break;

        case OtaAgentStateCreatingFile:
            otaGoToStateWithTimeout( OtaAgentStateWaitingForJob, timeout_ms );
            /* Let the PAL says it's not in self test.*/
            prvPAL_GetPlatformImageState_IgnoreAndReturn( OtaPalImageStateValid );
            /* Parse success would create the file, let it invoke our mock when creating file. */
            prvPAL_CreateFileForRx_Stub( mockOtaPalCreateFileForRx );
            otaEvent.eventId = OtaAgentEventReceivedJobDocument;
            otaEvent.pEventData = &eventBuffer;
            memcpy( otaEvent.pEventData->data, JOB_DOC_A, JOB_DOC_A_LENGTH );
            otaEvent.pEventData->dataLength = JOB_DOC_A_LENGTH;
            OTA_SignalEvent( &otaEvent );
            break;

        case OtaAgentStateRequestingFileBlock:
            otaGoToStateWithTimeout( OtaAgentStateCreatingFile, timeout_ms );
            otaEvent.eventId = OtaAgentEventCreateFile;
            OTA_SignalEvent( &otaEvent );
            break;

        case OtaAgentStateWaitingForFileBlock:
            otaGoToStateWithTimeout( OtaAgentStateRequestingFileBlock, timeout_ms );
            otaEvent.eventId = OtaAgentEventRequestFileBlock;
            OTA_SignalEvent( &otaEvent );
            break;

        case OtaAgentStateSuspended:
            otaGoToStateWithTimeout( OtaAgentStateReady, timeout_ms );
            OTA_Suspend();
            break;

        default:
            break;
    }

    otaWaitForState( state );
    mockOSEventReset( NULL );
}

static void otaGoToState( OtaState_t state )
{
    otaGoToStateWithTimeout( state, otaDefaultWait );
}

void setUp()
{
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
    otaInterfaceDefault();
}

void tearDown()
{
    pOtaFileHandle = NULL;
    memset( pOtaFileBuffer, 0, OTA_TEST_FILE_SIZE );
    otaInterfaceDefault();
    otaDeinit();
    otaWaitForState( OtaAgentStateStopped );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_InitWhenStopped()
{
    otaGoToState( OtaAgentStateInit );
    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetAgentState() );

    /* TODO, fix the bug. Once OTA agent is initialized. It has to be start first before calling
     * shutdown. There's no way to shutdown when it's in init state.*/
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_InitWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Calling init again should remain in ready state. */
    otaInitDefault();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Explicitly test NULL client name and NULL complete callback. */
    otaInit( NULL, NULL );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_InitWithNullName()
{
    /* Explicitly test NULL client name. OTA agent should remain in stopped state. */
    otaInit( NULL, stubCompleteCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_InitWithNameTooLong()
{
    /* OTA does not accept name longer than 64. Explicitly test long client name. */
    char long_name[ 100 ] = { 0 };

    memset( long_name, 1, sizeof( long_name ) - 1 );
    otaInit( long_name, stubCompleteCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_ShutdownWhenStopped()
{
    /* Calling shutdown when already stopped should have no effect. */
    OTA_AgentShutdown( otaDefaultWait );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_ShutdownFailToSendEvent()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    /* Shutdown should now fail and OTA agent should remain in ready state. */
    OTA_AgentShutdown( otaDefaultWait );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_StartWhenReady()
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Let the PAL says it's not in self test.*/
    prvPAL_GetPlatformImageState_IgnoreAndReturn( OtaPalImageStateValid );

    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    otaEvent.eventId = OtaAgentEventStart;
    OTA_SignalEvent( &otaEvent );
    otaWaitForState( OtaAgentStateRequestingJob );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetAgentState() );
}

void test_OTA_StartFailedWhenReady()
{
    OtaEventMsg_t otaEvent = { 0 };

    /* Let the PAL says it's not in self test.*/
    prvPAL_GetPlatformImageState_IgnoreAndReturn( OtaPalImageStateValid );

    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Set the event send interface to a mock function that fails after first event sent. */
    otaInterfaces.os.event.send = mockOSEventSendThenFail;

    /* The event handler should fail, so OTA agent should remain in OtaAgentStateReady state. */
    otaEvent.eventId = OtaAgentEventStart;
    OTA_SignalEvent( &otaEvent );
    otaWaitForEmptyEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_SuspendWhenStopped()
{
    /* Calling suspend when stopped should return an error. */
    TEST_ASSERT_NOT_EQUAL( OTA_ERR_NONE, OTA_Suspend() );

    /* OTA agent should remain in stopped state. */
    otaWaitForEmptyEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_SuspendWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    TEST_ASSERT_EQUAL( OTA_ERR_NONE, OTA_Suspend() );
    otaWaitForState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetAgentState() );
}

void test_OTA_SuspendFailedWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    /* Suspend should fail and OTA agent should remain in ready state. */
    TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_SEND_FAILED, OTA_Suspend() );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_ResumeWhenStopped()
{
    /* Calling resume when stopped should return an error. */
    TEST_ASSERT_NOT_EQUAL( OTA_ERR_NONE, OTA_Resume( NULL ) );

    /* OTA agent should remain in stopped state. */
    otaWaitForEmptyEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_ResumeWhenSuspended()
{
    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetAgentState() );

    TEST_ASSERT_EQUAL( OTA_ERR_NONE, OTA_Resume( NULL ) );
    otaWaitForState( OtaAgentStateRequestingJob );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetAgentState() );
}

void test_OTA_ResumeWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Calling resume when OTA agent is not suspend state. This should be an unexpected event and
     * the agent should remain in ready state. */
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, OTA_Resume( NULL ) );
    otaWaitForEmptyEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_ResumeFailedWhenSuspended()
{
    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetAgentState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    /* Resume should fail and OTA agent should remain in suspend state. */
    TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_SEND_FAILED, OTA_Resume( NULL ) );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetAgentState() );
}

void test_OTA_Statistics()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    TEST_ASSERT_EQUAL( 0, OTA_GetPacketsDropped() );
    TEST_ASSERT_EQUAL( 0, OTA_GetPacketsQueued() );
    TEST_ASSERT_EQUAL( 0, OTA_GetPacketsProcessed() );
    TEST_ASSERT_EQUAL( 0, OTA_GetPacketsReceived() );
}

void test_OTA_CheckForUpdate()
{
    otaGoToState( OtaAgentStateRequestingJob );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetAgentState() );

    TEST_ASSERT_EQUAL( OTA_ERR_NONE, OTA_CheckForUpdate() );
    otaWaitForState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );
}

void test_OTA_CheckForUpdateFailToSendEvent()
{
    otaGoToState( OtaAgentStateRequestingJob );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetAgentState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    /* Check for update should fail and OTA agent should remain in requesting job state. */
    TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_SEND_FAILED, OTA_CheckForUpdate() );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetAgentState() );
}

void test_OTA_ActivateNewImage()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Activate image simply calls the PAL implementation and return its return value. */
    prvPAL_ActivateNewImage_IgnoreAndReturn( OTA_ERR_NONE );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, OTA_ActivateNewImage() );

    prvPAL_ActivateNewImage_IgnoreAndReturn( OTA_ERR_ACTIVATE_FAILED );
    TEST_ASSERT_EQUAL( OTA_ERR_ACTIVATE_FAILED, OTA_ActivateNewImage() );
}

/* OTA pal function pointers should be NULL when OTA agent stopped. Calling OTA_ActivateNewImage
 * should fail. */
void test_OTA_ActivateNewImageWhenStopped()
{
    prvPAL_ActivateNewImage_IgnoreAndReturn( OTA_ERR_NONE );
    TEST_ASSERT_NOT_EQUAL( OTA_ERR_NONE, OTA_ActivateNewImage() );
}

void test_OTA_ImageStateAbortWithActiveJob()
{
    /* TODO. */
}

void test_OTA_ImageStateAbortWithNoJob()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously
     * since setting image state to abort would send an user abort event in the handler. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Calling abort without an active job would fail. OTA agent should remain in ready state. */
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, OTA_SetImageState( OtaImageStateAborted ) );
    otaWaitForEmptyEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_ImageStateAbortFailToSendEvent()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Set the event send interface to a mock function that always fail. */
    otaInterfaces.os.event.send = mockOSEventSendAlwaysFail;

    TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_SEND_FAILED, OTA_SetImageState( OtaImageStateAborted ) );
    otaWaitForEmptyEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_ImageStateRjectWithActiveJob()
{
    /* TODO. */
}

void test_OTA_ImageStateRjectWithNoJob()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    prvPAL_SetPlatformImageState_IgnoreAndReturn( OTA_ERR_NONE );
    TEST_ASSERT_EQUAL( OTA_ERR_NO_ACTIVE_JOB, OTA_SetImageState( OtaImageStateRejected ) );
    TEST_ASSERT_EQUAL( OtaImageStateRejected, OTA_GetImageState() );
}

void test_OTA_ImageStateAcceptWithActiveJob()
{
    /* TODO. */
}

void test_OTA_ImageStateAcceptWithNoJob()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    prvPAL_SetPlatformImageState_IgnoreAndReturn( OTA_ERR_NONE );
    TEST_ASSERT_EQUAL( OTA_ERR_NO_ACTIVE_JOB, OTA_SetImageState( OtaImageStateAccepted ) );
    TEST_ASSERT_EQUAL( OtaImageStateAccepted, OTA_GetImageState() );
}

void test_OTA_ImageStateInvalidState()
{
    TEST_ASSERT_EQUAL( OTA_ERR_BAD_IMAGE_STATE, OTA_SetImageState( -1 ) );
}

void test_OTA_ProcessJobDocumentInvalidJson()
{
    OtaEventMsg_t otaEvent = { 0 };
    const char * pJobDoc = JOB_DOC_INVALID;

    /* Parse failure would abort the update. */
    prvPAL_SetPlatformImageState_IgnoreAndReturn( OTA_ERR_NONE );
    prvPAL_Abort_IgnoreAndReturn( OTA_ERR_NONE );

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );

    otaEvent.eventId = OtaAgentEventReceivedJobDocument;
    otaEvent.pEventData = &eventBuffer;
    memcpy( otaEvent.pEventData->data, pJobDoc, JOB_DOC_INVALID_LENGTH );
    otaEvent.pEventData->dataLength = JOB_DOC_INVALID_LENGTH;
    OTA_SignalEvent( &otaEvent );
    otaWaitForEmptyEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );
}

void test_OTA_ProcessJobDocumentValidJson()
{
    OtaEventMsg_t otaEvent = { 0 };
    const char * pJobDoc = JOB_DOC_A;

    /* Let the PAL says it's not in self test.*/
    prvPAL_GetPlatformImageState_IgnoreAndReturn( OtaPalImageStateValid );

    /* Parse success would create the file, let PAL return success. */
    prvPAL_CreateFileForRx_IgnoreAndReturn( OTA_ERR_NONE );

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );

    otaEvent.eventId = OtaAgentEventReceivedJobDocument;
    otaEvent.pEventData = &eventBuffer;
    memcpy( otaEvent.pEventData->data, pJobDoc, JOB_DOC_A_LENGTH );
    otaEvent.pEventData->dataLength = JOB_DOC_A_LENGTH;
    OTA_SignalEvent( &otaEvent );
    otaWaitForState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetAgentState() );
}

void test_OTA_InitFileTransfer()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetAgentState() );

    otaEvent.eventId = OtaAgentEventCreateFile;
    OTA_SignalEvent( &otaEvent );
    otaWaitForState( OtaAgentStateRequestingFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetAgentState() );
}

void test_OTA_RequestFileBlock()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateRequestingFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetAgentState() );

    otaEvent.eventId = OtaAgentEventRequestFileBlock;
    OTA_SignalEvent( &otaEvent );
    otaWaitForState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetAgentState() );
}

void test_OTA_ReceiveFileBlockEmpty()
{
    OtaEventMsg_t otaEvent = { 0 };

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetAgentState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously.
     * This is required because decode failure would cause OtaAgentEventCloseFile event to be sent
     * within the OTA event handler and we want it to be processed. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Decode failure would reject this the update. */
    prvPAL_SetPlatformImageState_IgnoreAndReturn( OTA_ERR_NONE );
    prvPAL_Abort_IgnoreAndReturn( OTA_ERR_NONE );

    otaEvent.eventId = OtaAgentEventReceivedFileBlock;
    otaEvent.pEventData = &eventBuffer;
    otaEvent.pEventData->dataLength = 0;
    OTA_SignalEvent( &otaEvent );
    otaWaitForState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );
}

void test_OTA_ReceiveFileBlockComplete()
{
    OtaEventMsg_t otaEvent = { NULL, OtaAgentEventReceivedFileBlock };
    uint8_t pFileBlock[ OTA_FILE_BLOCK_SIZE ] = { 0 };
    uint8_t pStreamingMessage[ OTA_FILE_BLOCK_SIZE * 2 ] = { 0 };
    size_t streamingMessageSize = 0;
    int remainingBlocks = OTA_TEST_FILE_SIZE;
    int idx = 0;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetAgentState() );

    /* Set the event send interface to a mock function that allows events to be sent continuously
     * because we're receiving multiple blocks in this test. */
    otaInterfaces.os.event.send = mockOSEventSend;

    /* Set up mock to write file block to our buffer. */
    prvPAL_WriteBlock_Stub( mockOtaPalWriteFileBlock );

    /* By pass signature validation and ignore the final activate and abort call. */
    prvPAL_CloseFile_IgnoreAndReturn( OTA_ERR_NONE );
    prvPAL_Abort_IgnoreAndReturn( OTA_ERR_NONE );
    prvPAL_ActivateNewImage_IgnoreAndReturn( OTA_ERR_NONE );

    /* Fill the file block. */
    for( idx = 0; idx < sizeof( pFileBlock ); idx++ )
    {
        pFileBlock[ idx ] = idx % UINT8_MAX;
    }

    /* Send blocks. */
    idx = 0;

    while( remainingBlocks > OTA_FILE_BLOCK_SIZE )
    {
        /* Construct a AWS IoT streaming message. */
        createOtaStreammingMessage(
            pStreamingMessage,
            sizeof( pStreamingMessage ),
            idx++,
            pFileBlock,
            OTA_FILE_BLOCK_SIZE,
            &streamingMessageSize );
        otaEvent.pEventData = &eventBuffer;
        memcpy( otaEvent.pEventData->data, pStreamingMessage, streamingMessageSize );
        otaEvent.pEventData->dataLength = streamingMessageSize;

        OTA_SignalEvent( &otaEvent );
        otaWaitForEmptyEvent();
        TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetAgentState() );

        /* TODO, statistics is now broken. Need to fix it to test OTA_GetPacketsReceived
         * OTA_GetPacketsProcessed, and OTA_GetPacketsDropped . */
        remainingBlocks -= OTA_FILE_BLOCK_SIZE;
    }

    /* Send last block. */
    createOtaStreammingMessage(
        pStreamingMessage,
        sizeof( pStreamingMessage ),
        idx,
        pFileBlock,
        remainingBlocks,
        &streamingMessageSize );
    otaEvent.pEventData = &eventBuffer;
    memcpy( otaEvent.pEventData->data, pStreamingMessage, streamingMessageSize );
    otaEvent.pEventData->dataLength = streamingMessageSize;

    /* OTA agent should complete the update and go back to waiting for job state. */
    OTA_SignalEvent( &otaEvent );
    otaWaitForEmptyEvent();
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );
}

void test_OTA_SelfTest()
{
    OtaEventMsg_t otaEvent = { 0 };
    const char * pJobDoc = JOB_DOC_SELF_TEST;

    /* Set the event send interface to a mock function that allows events to be sent continuously.
     * This is to complete the self test process. */
    otaInterfaces.os.event.send = mockOSEventSend;
    /* Use default complete callback. */
    otaInit( pOtaDefaultClientId, NULL );

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );

    /* Let the PAL says it's in self test and bypass setting platform image state. */
    prvPAL_GetPlatformImageState_IgnoreAndReturn( OtaPalImageStatePendingCommit );
    prvPAL_SetPlatformImageState_IgnoreAndReturn( OTA_ERR_NONE );
    prvPAL_Abort_IgnoreAndReturn( OTA_ERR_NONE );

    otaEvent.eventId = OtaAgentEventReceivedJobDocument;
    otaEvent.pEventData = &eventBuffer;
    memcpy( otaEvent.pEventData->data, pJobDoc, JOB_DOC_SELF_TEST_LENGTH );
    otaEvent.pEventData->dataLength = JOB_DOC_SELF_TEST_LENGTH;
    OTA_SignalEvent( &otaEvent );
    otaWaitForState( OtaAgentStateCreatingFile );
    otaWaitForState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );
    TEST_ASSERT_EQUAL( OtaImageStateAccepted, OTA_GetImageState() );
}

void test_OTA_ReceiveNewJobDocWhileInProgress()
{
    OtaEventMsg_t otaEvent = { 0 };
    const char * pJobDoc = JOB_DOC_B;

    otaGoToState( OtaAgentStateWaitingForFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetAgentState() );

    /* Reset the event queue so that we can send the next event. */
    mockOSEventReset( NULL );

    /* Let abort pass. */
    prvPAL_SetPlatformImageState_IgnoreAndReturn( OTA_ERR_NONE );
    prvPAL_Abort_IgnoreAndReturn( OTA_ERR_NONE );

    /* Sending another job document should cause OTA agent to abort current update. */
    otaEvent.eventId = OtaAgentEventReceivedJobDocument;
    otaEvent.pEventData = &eventBuffer;
    memcpy( otaEvent.pEventData->data, pJobDoc, JOB_DOC_B_LENGTH );
    otaEvent.pEventData->dataLength = JOB_DOC_B_LENGTH;
    OTA_SignalEvent( &otaEvent );
    otaWaitForState( OtaAgentStateRequestingJob );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingJob, OTA_GetAgentState() );
}

// void test_OTA_RefreshWithSameJobDoc()
// {
//     OtaEventMsg_t otaEvent = { 0 };
//     const char * pJobDoc = JOB_DOC_A;

//     otaGoToState( OtaAgentStateWaitingForFileBlock );
//     TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetAgentState() );

//     /* Set the event send interface to a mock function that allows events to be sent continuously.
//      * We need this to go through the process of refreshing job doc. */
//     otaInterfaces.os.event.send = mockOSEventSend;

//     /* First send request job doc event while we're in progress, this should make OTA agent to
//      * to request job doc again and transit to waiting for job state. */
//     otaEvent.eventId = OtaAgentEventRequestJobDocument;
//     OTA_SignalEvent( &otaEvent );
//     otaWaitForState( OtaAgentStateWaitingForJob );
//     TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );

//     /* Now send the same job doc, OTA agent should resume the download. */
//     otaEvent.eventId = OtaAgentEventReceivedJobDocument;
//     otaEvent.pEventData = &eventBuffer;
//     memcpy( otaEvent.pEventData->data, pJobDoc, JOB_DOC_A_LENGTH );
//     otaEvent.pEventData->dataLength = JOB_DOC_A_LENGTH;
//     OTA_SignalEvent( &otaEvent );
//     otaWaitForState( OtaAgentStateWaitingForFileBlock );
//     TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetAgentState() );
// }

// void test_OTA_RefreshWithDifferentJobDoc()
// {
//     OtaEventMsg_t otaEvent = { 0 };
//     const char * pJobDoc = JOB_DOC_B;

//     otaGoToState( OtaAgentStateWaitingForFileBlock );
//     TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetAgentState() );

//     /* Set the event send interface to a mock function that allows events to be sent continuously.
//      * We need this to go through the process of refreshing job doc. */
//     otaInterfaces.os.event.send = mockOSEventSend;

//     /* Let abort pass. */
//     prvPAL_SetPlatformImageState_IgnoreAndReturn( OTA_ERR_NONE );
//     prvPAL_Abort_IgnoreAndReturn( OTA_ERR_NONE );

//     /* First send request job doc event while we're in progress, this should make OTA agent to
//      * to request job doc again and transit to waiting for job state. */
//     otaEvent.eventId = OtaAgentEventRequestJobDocument;
//     OTA_SignalEvent( &otaEvent );
//     otaWaitForState( OtaAgentStateWaitingForJob );
//     TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );

//     /* Now send a different job doc, OTA agent should abort current and job and start the new job. */
//     otaEvent.eventId = OtaAgentEventReceivedJobDocument;
//     otaEvent.pEventData = &eventBuffer;
//     memcpy( otaEvent.pEventData->data, pJobDoc, JOB_DOC_B_LENGTH );
//     otaEvent.pEventData->dataLength = JOB_DOC_B_LENGTH;
//     OTA_SignalEvent( &otaEvent );
//     otaWaitForState( OtaAgentStateWaitingForFileBlock );
//     TEST_ASSERT_EQUAL( OtaAgentStateWaitingForFileBlock, OTA_GetAgentState() );
// }
