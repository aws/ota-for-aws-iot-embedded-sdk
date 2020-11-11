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
 * @file ota_os_posix_utest.c
 * @brief Unit tests for functions in ota_os_posix.c
 */

#include <string.h>
#include <mqueue.h>
#include <time.h>
#include "unity.h"

/* For accessing OTA private functions and error codes. */
#include "ota_os_posix.h"
#include "ota_private.h"


/* Testing constants. */
#define MAX_MESSAGES           10
#define TIMER_NAME             "dummy_name"
#define OTA_DEFAULT_TIMEOUT    10000

/* Timer used in os_posix.c */
extern timer_t otaTimer;

/* Interfaces for Timer and Event. */
static OtaTimerInterface_t timer;
static OtaEventInterface_t event;
static OtaTimerContext_t * pTimerContext = NULL;
static OtaEventContext_t * pEventContext = NULL;

/**
 * @brief Get the Time elapsed from the timer.
 *
 * This is used to ensure that the timer has started successfully.
 *
 * @return long time elapsed in nano seconds.
 */
static long getTime_Posix()
{
    struct itimerspec timerAttr;
    long retVal = 0;

    if( timer_gettime( otaTimer, &timerAttr ) == 0 )
    {
        retVal = timerAttr.it_value.tv_nsec;
    }

    return retVal;
}
/* ============================   UNITY FIXTURES ============================ */

void setUp( void )
{
    timer.start = Posix_OtaStartTimer;
    timer.delete = Posix_OtaDeleteTimer;
    timer.stop = Posix_OtaStopTimer;
    timer.PTimerCtx = pTimerContext;

    event.init = Posix_OtaInitEvent;
    event.send = Posix_OtaSendEvent;
    event.recv = Posix_OtaReceiveEvent;
    event.deinit = Posix_OtaDeinitEvent;
    event.pEventContext = pEventContext;
}

void tearDown( void )
{
}

/* ========================================================================== */

/**
 * @brief Test that the event queue gets populated with the messages.
 */
void test_OTA_posix_SendAndRecvEvent( void )
{
    OtaEventMsg_t otaEventToSend = { 0 };
    OtaEventMsg_t otaEventToRecv = { 0 };
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    otaEventToSend.eventId = OtaAgentEventStart;
    result = event.init( event.pEventContext );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    result = event.send( event.pEventContext, &otaEventToSend, 0 );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );
    result = event.recv( event.pEventContext, &otaEventToRecv, 0 );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );
    TEST_ASSERT_EQUAL( otaEventToSend.eventId, otaEventToRecv.eventId );

    result = event.deinit( event.pEventContext );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );
}

/**
 * @brief Test that the event queue operations do not succeed for invalid operations.
 *
 * TODO: 1. need to use timed send or O_NONBLOCK to test event recv failure
 * 2. Since the queue is unlinked and other params are not variable, can not test init fail
 * 3. Need to set O_NONBLOCK flag for testing send failure
 */
void test_OTA_posix_InvalidEventQueue( void )
{
    OtaEventMsg_t otaEventToSend = { 0 };
    OtaEventMsg_t otaEventToRecv = { 0 };
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    otaEventToSend.eventId = OtaAgentEventStart;

    /* Try to perform recv on non-existing queue.
     * result = Posix_OtaReceiveEvent(pEventCtx, &otaEventToRecv, 0);
     * TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_RECEIVE_FAILED, result );
     */

    result = event.init( event.pEventContext );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* Publish more than allowed messages to the event queue.
     * for ( uint8_t counter = 0; counter <= MAX_MESSAGES; counter++)
     * {
     *  result = Posix_OtaSendEvent(pEventCtx, &otaEventToSend, 0);
     * }
     * TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_SEND_FAILED, result );
     */

    result = event.deinit( event.pEventContext );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* Try to deinitialize a non-existing queue. */
    result = event.deinit( event.pEventContext );
    TEST_ASSERT_EQUAL( OTA_ERR_EVENT_Q_DELETE_FAILED, result );
}

/**
 * @brief Test invalid operations on timers.
 */
void test_OTA_posix_TimerCreateAndStop( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    result = timer.start( timer.PTimerCtx, TIMER_NAME, OTA_DEFAULT_TIMEOUT, NULL );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    TEST_ASSERT_NOT_EQUAL( 0, getTime_Posix() );

    result = timer.stop( timer.PTimerCtx );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    result = timer.delete( timer.PTimerCtx );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );
}

/**
 * @brief Test timers are initialized, stopped and deleted successfully.
 */
void test_OTA_posix_InvalidTimerOperations( void )
{
    OtaErr_t result = OTA_ERR_UNINITIALIZED;

    result = timer.start( timer.PTimerCtx, TIMER_NAME, OTA_DEFAULT_TIMEOUT, NULL );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* Set the timeout to 0 and stop the timer*/
    result = timer.start( timer.PTimerCtx, TIMER_NAME, 0, NULL );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    result = timer.stop( timer.PTimerCtx );
    TEST_ASSERT_NOT_EQUAL( OTA_ERR_NONE, result );

    result = timer.delete( timer.PTimerCtx );
    TEST_ASSERT_EQUAL( OTA_ERR_NONE, result );

    /* Delete a timer that has been deleted. */
    result = timer.delete( timer.PTimerCtx );
    TEST_ASSERT_NOT_EQUAL( OTA_ERR_NONE, result );
}

/**
 * @brief Test memory allocation and free.
 */
void test_OTA_posix_MemoryAllocAndFree( void )
{
    uint8_t * buffer = NULL;

    buffer = ( uint8_t * ) STDC_Malloc( sizeof( uint8_t ) );
    TEST_ASSERT_NOT_NULL( buffer );

    /* Test that we can access and assign a value in the buffer. */
    buffer[ 0 ] = MAX_MESSAGES;
    TEST_ASSERT_EQUAL( MAX_MESSAGES, buffer[ 0 ] );

    /* Free the buffer and check if the contents are cleared. */
    STDC_Free( buffer );
    TEST_ASSERT_EQUAL( 0, buffer[ 0 ] );
}
