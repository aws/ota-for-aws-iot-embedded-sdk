/*
 * coreMQTT v1.0.0
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
static OtaErr_t mockOSEventSendAndStop( OtaEventContext_t * unused_1,
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
static OtaErr_t mockOSEventSendAndFail( OtaEventContext_t * unused_1,
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
        usleep( 10 );
        err = OTA_ERR_EVENT_Q_RECEIVE_FAILED;
    }

    return err;
}

static OtaErr_t stubMqttSubscribe( const char * unused_1,
                                   uint16_t unused_2,
                                   uint8_t unused_3,
                                   void * unused_4 )
{
}
static OtaErr_t stubMqttPublish( const char * const unused_1,
                                 uint16_t unused_2,
                                 const char * unused_3,
                                 uint32_t unused_4,
                                 uint8_t unused_5 )
{
}
static OtaErr_t stubMqttUnsubscribe( const char * unused_1,
                                     uint16_t unused_2,
                                     uint8_t unused_3 )
{
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

/* Set default OTA OS interface to mockOSEventSendAndStop. This allows us to easily control the
 * state machine transition by blocking any event in OTA internal handlers. */
static void otaInterfaceDefault()
{
    otaOSInterface.event.init = mockOSEventReset;
    otaOSInterface.event.send = mockOSEventSendAndStop;
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
    OTA_AgentShutdown( 0 );
}

static void otaStartAgentTask()
{
    pthread_t otaThread;

    if( OtaAgentStateInit == OTA_GetAgentState() )
    {
        pthread_create( &otaThread, NULL, otaAgentTask, NULL );
    }
}

static void otaWaitForState( OtaState_t state,
                             int milliseconds )
{
    while( milliseconds > 0 && state != OTA_GetAgentState() )
    {
        usleep( 1 );
        milliseconds--;
    }
}

static void otaGoToStateWithTimeout( OtaState_t state,
                                     int timeout_ms )
{
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
            otaWaitForState( state, otaDefaultWait );
            break;

        default:
            break;
    }
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
    otaWaitForState( OtaAgentStateStopped, otaDefaultWait );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_InitWhenStopped()
{
    otaGoToState( OtaAgentStateInit );
    TEST_ASSERT_EQUAL( OtaAgentStateInit, OTA_GetAgentState() );

    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_InitWhenReady()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    otaGoToState( OtaAgentStateInit );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    /* Explicitly test NULL client name and NULL complete callback. */
    otaInit( NULL, NULL );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_InitWithNullName()
{
    /* Explicitly test NULL client name. */
    otaInterfaceDefault();
    otaInit( NULL, stubCompleteCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );

    otaInitDefault();
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_InitWithNameTooLong()
{
    /* OTA doesn't accept name longer than 64. Explicitly test long client name. */
    char long_name[ 100 ] = { 0 };

    memset( long_name, 1, sizeof( long_name ) - 1 );
    otaInterfaceDefault();
    otaInit( long_name, stubCompleteCallback );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );

    otaInitDefault();
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );
}

void test_OTA_ShutdownWhenStopped()
{
    otaDeinit();
    otaWaitForState( OtaAgentStateStopped, otaDefaultWait );
    TEST_ASSERT_EQUAL( OtaAgentStateStopped, OTA_GetAgentState() );
}

void test_OTA_SuspendWhenStopped( void )
{
    TEST_ASSERT_EQUAL( OTA_Suspend(), OTA_ERR_OTA_AGENT_STOPPED );
}

void test_OTA_SuspendWhenReady( void )
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    TEST_ASSERT_EQUAL( OTA_Suspend(), OTA_ERR_NONE );

    /* Call OTA init again to set the event send interface to a mock function that always fail. */
    ota_SendEvent_t prev_send = otaOSInterface.event.send;
    otaOSInterface.event.send = mockOSEventSendAndFail;
    otaInitDefault();
    TEST_ASSERT_EQUAL( OTA_Suspend(), OTA_ERR_EVENT_Q_SEND_FAILED );
    otaOSInterface.event.send = prev_send;
}

void test_OTAStatistics()
{
    otaGoToState( OtaAgentStateReady );
    TEST_ASSERT_EQUAL( OtaAgentStateReady, OTA_GetAgentState() );

    TEST_ASSERT_EQUAL( OTA_GetPacketsDropped(), 0 );
    TEST_ASSERT_EQUAL( OTA_GetPacketsQueued(), 0 );
    TEST_ASSERT_EQUAL( OTA_GetPacketsProcessed(), 0 );
    TEST_ASSERT_EQUAL( OTA_GetPacketsReceived(), 0 );
}
