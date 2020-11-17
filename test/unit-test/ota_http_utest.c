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
 * @file ota_http_utest.c
 * @brief Unit tests for http component
 */
/* Standard includes. */
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
#include "ota_http_private.h"
#include "ota_interface_private.h"

/* Mock OTA PAL. */
#include "mock_ota_platform_interface.h"

/* test includes. */
#include "utest_helpers.h"

/* Testing parameters */
#define OTA_TEST_FILE_SIZE          10240
#define OTA_TEST_FILE_SIZE_STR      "10240"
#define configENABLED_DATA_PROTOCOLS    ( OTA_DATA_OVER_HTTP )
#define configOTA_PRIMARY_DATA_PROTOCOL    ( OTA_DATA_OVER_HTTP )
#define JOB_DOC_A                   "small"//{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":" OTA_TEST_FILE_SIZE_STR ",\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_DOC_A_LENGTH            ( sizeof( JOB_DOC_A ) - 1 )

/* Firmware version. */
const AppVersion32_t appFirmwareVersion =
{
    .u.x.major = 1,
    .u.x.minor = 0,
    .u.x.build = 0,
};

/* OTA code signing signature algorithm. */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

/* OTA client name. */
static const char * pOtaDefaultClientId = "ota_utest";

/* OTA OS and MQTT interface. */
static OtaOSInterface_t otaOSInterface;
static OtaMqttInterface_t otaMqttInterface;
static OtaHttpInterface_t otaHttpInterface;

/* OTA Event. */
static OtaEventMsg_t otaEvent;
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

static OtaErr_t stubMqttSubscribe( const char * unused_1,
                                   uint16_t unused_2,
                                   uint8_t unused_3,
                                   void * unused_4 )
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

static OtaErr_t stubHttpInit( char * url)
{
    return OTA_ERR_NONE;
}

static OtaErr_t stubHttpRequest( uint32_t rangeStart,
                              uint32_t rangeEnd )
{
    return OTA_ERR_NONE;
}

static OtaErr_t stubHttpDeinit( )
{
    return OTA_ERR_NONE;
}
/* Set default OTA OS interface to mockOSEventSendThenStop. This allows us to easily control the
 * state machine transition by blocking any event in OTA internal handlers. */
static void otaInterfaceDefault()
{
    otaOSInterface.event.init = mockOSEventReset;
    otaOSInterface.event.send = mockOSEventSendThenStop;
    otaOSInterface.event.recv = mockOSEventReceive;
    otaOSInterface.event.deinit = mockOSEventReset;

    otaMqttInterface.subscribe = stubMqttSubscribe;
    otaMqttInterface.publish = stubMqttPublish;
    otaMqttInterface.unsubscribe = stubMqttUnsubscribe;
    otaMqttInterface.jobCallback = stubMqttJobCallback;
    otaMqttInterface.dataCallback = stubMqttDataCallback;

    otaHttpInterface.init = stubHttpInit;
    otaHttpInterface.request = stubHttpRequest;
    otaHttpInterface.deinit = stubHttpDeinit;
}

static void otaInit( const char * pClientID,
                     OtaCompleteCallback_t completeCallback )
{
    OTA_AgentInit( &otaOSInterface,
                   &otaMqttInterface,
                   &otaHttpInterface,
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
            otaEvent.pEventData = otaEventBufferGet();
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

/* ============================   UNITY FIXTURES ============================ */

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
/* ========================================================================== */


void test_OTA_HTTP_InitFileTransfer()
{
    OtaEventMsg_t otaEvent = { 0 };

    prvPAL_SetPlatformImageState_IgnoreAndReturn( OTA_ERR_NONE );
    //TEST_ASSERT_EQUAL("a", "b");
    otaGoToState( OtaAgentStateCreatingFile );
    
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetAgentState() );
    
    otaEvent.eventId = OtaAgentEventCreateFile;
    OTA_SignalEvent( &otaEvent );
    otaWaitForState( OtaAgentStateRequestingFileBlock );
    TEST_ASSERT_EQUAL( OtaAgentStateRequestingFileBlock, OTA_GetAgentState() );
}