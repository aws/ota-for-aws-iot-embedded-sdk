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
 * @file aws_ota_utest.c
 * @brief Unit tests for functions in OTA agent.
 */
#include <string.h>
#include <stdbool.h>

#include <unistd.h>
#include <pthread.h>

#include "unity.h"

/* For accessing OTA private functions. */
#include "iot_appversion32.h"
#include "aws_iot_ota_agent.h"
#include "aws_iot_ota_agent_private.h"

/* Mock OTA PAL. */
#include "mock_aws_iot_ota_pal.h"

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

/* OTA Event. */
static OtaEventMsg_t otaEvent;
static pthread_mutex_t eventLock;
static bool eventIgnore;

/* Default wait time for OTA state machine transition. */
static const int otaDefaultWait = 1000;

/* ========================================================================== */

static OtaErr_t mockOSEventReset( OtaEventContext_t * unused )
{
    otaEvent.eventId = OtaAgentEventMax;
    otaEvent.pEventData = NULL;
    eventIgnore = false;

    return OTA_ERR_NONE;
}

/* Allow an event to be sent only once, after that ignore all incoming event.
* Useful to make sure internal OTA handler are not able to send any event. */
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
}

static void otaInit( const char * pClientID,
                     OtaCompleteCallback_t completeCallback )
{
    OTA_AgentInit( NULL,
                   &otaOSInterface,
                   &otaMqttInterface,
                   ( const uint8_t * ) pClientID,
                   completeCallback,
                   ( uint32_t ) ~0 );
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
        otaInterfaceDefault();
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
}

void tearDown()
{
    otaDeinit();
    otaWaitForState( OtaAgentStateStopped );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_InitWhenStopped()
{
    otaGoToState( OtaAgentStateInit );
    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetAgentState() );

    /* TODO, fix the bug. Once OTA agent is initialized. It has to be start first before calling
     * shutdown. There's no way to deinit when it's in init state.*/
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_InitWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Explicitly test OTA_AgentInit. */
    otaInitDefault();
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Explicitly test NULL client name and NULL complete callback. */
    otaInit( NULL, NULL );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_InitWithNullName()
{
    /* Explicitly test NULL client name. */
    otaInit( NULL, stubCompleteCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_InitWithNameTooLong()
{
    /* OTA doesn't accept name longer than 64. Explicitly test long client name. */
    char long_name[ 100 ] = { 0 };

    memset( long_name, 1, sizeof( long_name ) - 1 );
    otaInit( long_name, stubCompleteCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_ShutdownWhenStopped()
{
    OTA_AgentShutdown( 0 );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_ShutdownFailToSendEvent()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Call OTA init to set the event send interface to a mock function that always fail. */
    ota_SendEvent_t prev_send = otaOSInterface.event.send;
    otaOSInterface.event.send = mockOSEventSendAlwaysFail;
    otaInitDefault();

    if( TEST_PROTECT() )
    {
        OTA_AgentShutdown( 0 );
    }

    otaOSInterface.event.send = prev_send;
}

void test_OTA_StartWhenReady()
{
    OtaEventMsg_t otaEvent = { 0 };

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

    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Call OTA init to set the event send interface to a mock function that fails after first
     * event sent. */
    ota_SendEvent_t prev_send = otaOSInterface.event.send;
    otaOSInterface.event.send = mockOSEventSendThenFail;
    otaInitDefault();

    if( TEST_PROTECT() )
    {
        /* The event handler should fail, so we should remain in OtaAgentStateReady state. */
        otaEvent.eventId = OtaAgentEventStart;
        OTA_SignalEvent( &otaEvent );
        otaWaitForEmptyEvent( otaDefaultWait );
        TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
    }

    otaOSInterface.event.send = prev_send;
}

void test_OTA_SuspendWhenStopped()
{
    TEST_ASSERT_EQUAL( OTA_ERR_OTA_AGENT_STOPPED, OTA_Suspend() );
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

    /* Call OTA init to set the event send interface to a mock function that always fail. */
    ota_SendEvent_t prev_send = otaOSInterface.event.send;
    otaOSInterface.event.send = mockOSEventSendAlwaysFail;
    otaInitDefault();

    if( TEST_PROTECT() )
    {
        TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_SEND_FAILED, OTA_Suspend() );
    }

    otaOSInterface.event.send = prev_send;
}

void test_OTA_ResumeWhenStopped()
{
    TEST_ASSERT_EQUAL( OTA_ERR_OTA_AGENT_STOPPED, OTA_Resume( NULL ) );
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
    otaWaitForEmptyEvent( otaDefaultWait );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_ResumeFailedWhenSuspended()
{
    otaGoToState( OtaAgentStateSuspended );
    TEST_ASSERT_EQUAL( OtaAgentStateSuspended, OTA_GetAgentState() );

    /* Call OTA init to set the event send interface to a mock function that always fail. */
    ota_SendEvent_t prev_send = otaOSInterface.event.send;
    otaOSInterface.event.send = mockOSEventSendAlwaysFail;
    otaInitDefault();

    if( TEST_PROTECT() )
    {
        TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_SEND_FAILED, OTA_Resume( NULL ) );
    }

    otaOSInterface.event.send = prev_send;
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

    /* Call OTA init to set the event send interface to a mock function that always fail. */
    ota_SendEvent_t prev_send = otaOSInterface.event.send;
    otaOSInterface.event.send = mockOSEventSendAlwaysFail;
    otaInitDefault();

    if( TEST_PROTECT() )
    {
        TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_SEND_FAILED, OTA_CheckForUpdate() );
    }

    otaOSInterface.event.send = prev_send;
}

void test_OTA_ActivateNewImage()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    prvPAL_ActivateNewImage_IgnoreAndReturn( OTA_ERR_NONE );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, OTA_ActivateNewImage() );
}

/* OTA pal function pointers should be NULL when OTA agent is not started. */
void test_OTA_ActivateNewImageWhenStopped()
{
    TEST_ASSERT_EQUAL( OTA_ERR_UNINITIALIZED, OTA_ActivateNewImage() );
}

void test_OTA_ImageStateAbortWithActiveJob()
{
    /* TODO. */
}

void test_OTA_ImageStateAbortWithNoJob()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    TEST_ASSERT_EQUAL( OTA_ERR_NONE, OTA_SetImageState( OtaImageStateAborted ) );
    otaWaitForEmptyEvent( otaDefaultWait );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_ImageStateAbortFailToSendEvent()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Call OTA init to set the event send interface to a mock function that always fail. */
    ota_SendEvent_t prev_send = otaOSInterface.event.send;
    otaOSInterface.event.send = mockOSEventSendAlwaysFail;
    otaInitDefault();

    if( TEST_PROTECT() )
    {
        TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_SEND_FAILED, OTA_SetImageState( OtaImageStateAborted ) );
    }

    otaOSInterface.event.send = prev_send;
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
    const char job_doc[] = "not a json";

    /* Parse failuire would abort the update. */
    prvPAL_SetPlatformImageState_IgnoreAndReturn( OTA_ERR_NONE );
    prvPAL_Abort_IgnoreAndReturn( OTA_ERR_NONE );

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );

    otaEvent.eventId = OtaAgentEventReceivedJobDocument;
    otaEvent.pEventData = otaEventBufferGet();
    memcpy( otaEvent.pEventData->data, job_doc, sizeof( job_doc ) );
    otaEvent.pEventData->dataLength = sizeof( job_doc );
    OTA_SignalEvent( &otaEvent );
    otaWaitForEmptyEvent( otaDefaultWait );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );
}

void test_OTA_ProcessJobDocumentValidJson()
{
    OtaEventMsg_t otaEvent = { 0 };
    const char job_doc[] = "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":180568,\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}";

    /* Let the PAL says it's not in self test.*/
    prvPAL_GetPlatformImageState_IgnoreAndReturn( OtaPalImageStateValid );

    /* Parse success would create the file, let PAL return success. */
    prvPAL_CreateFileForRx_IgnoreAndReturn( OTA_ERR_NONE );

    otaGoToState( OtaAgentStateWaitingForJob );
    TEST_ASSERT_EQUAL( OtaAgentStateWaitingForJob, OTA_GetAgentState() );

    otaEvent.eventId = OtaAgentEventReceivedJobDocument;
    otaEvent.pEventData = otaEventBufferGet();
    memcpy( otaEvent.pEventData->data, job_doc, strlen( job_doc ) );
    otaEvent.pEventData->dataLength = strlen( job_doc );
    OTA_SignalEvent( &otaEvent );
    otaWaitForState( OtaAgentStateCreatingFile );
    TEST_ASSERT_EQUAL( OtaAgentStateCreatingFile, OTA_GetAgentState() );
}
