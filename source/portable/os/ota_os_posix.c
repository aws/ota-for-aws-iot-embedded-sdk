/*
 * FreeRTOS OTA V2.0.0
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

/* Standard Includes.*/
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* MISRA rule 21.5 prohibits use of signal.h on embedded system. But this implementation is on linux.
 * So it's a false positive. */
/* coverity[misra_c_2012_rule_21_5_violation] */
#include <signal.h>
#include <errno.h>

/* Posix includes. */
#include <sys/types.h>
#include <mqueue.h>

/* OTA OS POSIX Interface Includes.*/
#include "ota_os_posix.h"

/* OTA Library include. */
#include "ota.h"
#include "ota_private.h"

/* OTA Event queue attributes.*/
#define OTA_QUEUE_NAME    "/otaqueue"
#define MAX_MESSAGES      10
#define MAX_MSG_SIZE      sizeof( OtaEventMsg_t )

static void requestTimerCallback( union sigval arg );
static void selfTestTimerCallback( union sigval arg );

static OtaTimerCallback_t otaTimerCallback;

/* OTA Event queue attributes.*/
static mqd_t otaEventQueue;

/* OTA Timer handles.*/
static timer_t otaTimers[ OtaNumOfTimers ];
static timer_t * pOtaTimers[ OtaNumOfTimers ] = { 0 };

/* OTA Timer callbacks.*/
static void ( * timerCallback[ OtaNumOfTimers ] )( union sigval arg ) = { requestTimerCallback, selfTestTimerCallback };

OtaErr_t Posix_OtaInitEvent( OtaEventContext_t * pEventCtx )
{
    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;
    struct mq_attr attr;

    ( void ) pEventCtx;

    /* Unlink the event queue.*/
    ( void ) mq_unlink( OTA_QUEUE_NAME );

    /* Initialize queue attributes.*/
    attr.mq_flags = 0;
    attr.mq_maxmsg = MAX_MESSAGES;
    attr.mq_msgsize = ( long ) MAX_MSG_SIZE;
    attr.mq_curmsgs = 0;

    /* Open the event queue.*/
    errno = 0;

    /* MISRA rule 10.1 requires bitwise operand to be unsigned type. However, O_CREAT and O_RDWR
     * flags are from standard linux header, and this is the normal way of using them. Hence we
     * silence the warning here. */
    /* coverity[misra_c_2012_rule_10_1_violation] */
    otaEventQueue = mq_open( OTA_QUEUE_NAME, O_CREAT | O_RDWR, S_IRWXU, &attr );

    if( otaEventQueue == -1 )
    {
        otaErrRet = OTA_ERR_EVENT_Q_CREATE_FAILED;

        LogError( ( "Failed to create OTA Event Queue: "
                    "mq_open returned error: "
                    "otaErrRet=%i "
                    ",errno=%s",
                    otaErrRet,
                    strerror( errno ) ) );
    }
    else
    {
        LogDebug( ( "OTA Event Queue created." ) );

        otaErrRet = OTA_ERR_NONE;
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaSendEvent( OtaEventContext_t * pEventCtx,
                             const void * pEventMsg,
                             unsigned int timeout )
{
    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

    ( void ) pEventCtx;
    ( void ) timeout;

    /* Send the event to OTA event queue.*/
    errno = 0;

    if( mq_send( otaEventQueue, pEventMsg, MAX_MSG_SIZE, 0 ) == -1 )
    {
        otaErrRet = OTA_ERR_EVENT_Q_SEND_FAILED;

        LogError( ( "Failed to send event to OTA Event Queue: "
                    "mq_send returned error: "
                    "otaErrRet=%i "
                    ",errno=%s",
                    otaErrRet,
                    strerror( errno ) ) );
    }
    else
    {
        LogDebug( ( "OTA Event Sent." ) );

        otaErrRet = OTA_ERR_NONE;
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaReceiveEvent( OtaEventContext_t * pEventCtx,
                                void * pEventMsg,
                                uint32_t timeout )
{
    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;
    char * pDst = pEventMsg;
    char buff[ MAX_MSG_SIZE ];

    ( void ) pEventCtx;
    ( void ) timeout;

    /* Receive the next event from OTA event queue.*/
    errno = 0;

    if( mq_receive( otaEventQueue, buff, sizeof( buff ), NULL ) == -1 )
    {
        otaErrRet = OTA_ERR_EVENT_Q_RECEIVE_FAILED;

        LogError( ( "Failed to receive OTA Event: "
                    "mq_reqeive returned error: "
                    "otaErrRet=%i "
                    ",errno=%s",
                    otaErrRet,
                    strerror( errno ) ) );
    }
    else
    {
        LogDebug( ( "OTA Event received." ) );

        /* copy the data from local buffer.*/
        ( void ) memcpy( pDst, buff, MAX_MSG_SIZE );

        otaErrRet = OTA_ERR_NONE;
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaDeinitEvent( OtaEventContext_t * pEventCtx )
{
    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

    ( void ) pEventCtx;

    /* Remove the event queue.*/
    errno = 0;

    if( mq_unlink( OTA_QUEUE_NAME ) == -1 )
    {
        otaErrRet = OTA_ERR_EVENT_Q_DELETE_FAILED;

        LogError( ( "Failed to delete OTA Event queue: "
                    "mq_unlink returned error: "
                    "otaErrRet=%i "
                    ",errno=%s",
                    otaErrRet,
                    strerror( errno ) ) );
    }
    else
    {
        LogDebug( ( "OTA Event queue deleted." ) );

        otaErrRet = OTA_ERR_NONE;
    }

    return otaErrRet;
}

static void selfTestTimerCallback( union sigval arg )
{
    ( void ) arg;

    LogDebug( ( "Self-test expired within %ums\r\n",
                otaconfigSELF_TEST_RESPONSE_WAIT_MS ) );

    if( otaTimerCallback != NULL )
    {
        otaTimerCallback( OtaSelfTestTimer );
    }
    else
    {
        LogWarn( ( "Self-test timer event unhandled.\r\n" ) );
    }
}

static void requestTimerCallback( union sigval arg )
{
    ( void ) arg;

    LogDebug( ( "Request timer expired in %ums \r\n",
                otaconfigFILE_REQUEST_WAIT_MS ) );

    if( otaTimerCallback != NULL )
    {
        otaTimerCallback( OtaRequestTimer );
    }
    else
    {
        LogWarn( ( "Request timer event unhandled.\r\n" ) );
    }
}

OtaErr_t Posix_OtaStartTimer( OtaTimerId_t otaTimerId,
                              const char * const pTimerName,
                              const uint32_t timeout,
                              OtaTimerCallback_t callback )
{
    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

    /* Create the timer structures. */
    struct sigevent sgEvent;
    struct itimerspec timerAttr;

    ( void ) pTimerName;

    /* clear everything in the structures. */
    ( void ) memset( &sgEvent, 0, sizeof( struct sigevent ) );
    ( void ) memset( &timerAttr, 0, sizeof( struct itimerspec ) );

    /* Set attributes. */
    sgEvent.sigev_notify = SIGEV_THREAD;
    sgEvent.sigev_value.sival_ptr = otaTimers[ otaTimerId ];
    sgEvent.sigev_notify_function = timerCallback[ otaTimerId ];

    /* Set OTA lib callback. */
    otaTimerCallback = callback;

    /* Set timeout attributes.*/
    timerAttr.it_value.tv_sec = ( time_t ) timeout / 1000;

    /* Create timer if required.*/
    if( pOtaTimers[ otaTimerId ] == NULL )
    {
        errno = 0;

        if( timer_create( CLOCK_REALTIME, &sgEvent, &otaTimers[ otaTimerId ] ) == -1 )
        {
            otaErrRet = OTA_ERR_EVENT_TIMER_CREATE_FAILED;

            LogError( ( "Failed to create OTA timer: "
                        "timer_create returned error: "
                        "otaErrRet=%i "
                        ",errno=%s",
                        otaErrRet,
                        strerror( errno ) ) );
        }
        else
        {
            pOtaTimers[ otaTimerId ] = &otaTimers[ otaTimerId ];
        }
    }

    /* Set timeout.*/
    if( pOtaTimers[ otaTimerId ] != NULL )
    {
        errno = 0;

        if( timer_settime( otaTimers[ otaTimerId ], 0, &timerAttr, NULL ) == -1 )
        {
            otaErrRet = OTA_ERR_EVENT_TIMER_START_FAILED;

            LogError( ( "Failed to set OTA timer timeout: "
                        "timer_settime returned error: "
                        "otaErrRet=%i "
                        ",errno=%s",
                        otaErrRet,
                        strerror( errno ) ) );
        }
        else
        {
            LogDebug( ( "OTA Timer started." ) );
            otaErrRet = OTA_ERR_NONE;
        }
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaStopTimer( OtaTimerId_t otaTimerId )
{
    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

    /* Create the timer structures. */
    struct itimerspec timerAttr;

    /* clear everything in the structures. */
    ( void ) memset( &timerAttr, 0, sizeof( struct itimerspec ) );

    /* Clear the timeout. */
    timerAttr.it_value.tv_sec = 0;

    if( pOtaTimers[ otaTimerId ] != NULL )
    {
        /* Stop the timer*/
        errno = 0;

        if( timer_settime( otaTimers[ otaTimerId ], 0, &timerAttr, NULL ) == -1 )
        {
            otaErrRet = OTA_ERR_EVENT_TIMER_STOP_FAILED;

            LogError( ( "Failed to stop OTA timer: "
                        "timer_settime returned error: "
                        "otaErrRet=%i "
                        ",errno=%s",
                        otaErrRet,
                        strerror( errno ) ) );
        }
        else
        {
            LogDebug( ( "OTA Timer Stopped for Timerid=%i.", otaTimerId ) );

            otaErrRet = OTA_ERR_NONE;
        }
    }
    else
    {
        LogWarn( ( "OTA Timer handle NULL for Timerid=%i, can't stop.", otaTimerId ) );

        otaErrRet = OTA_ERR_EVENT_TIMER_STOP_FAILED;
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaDeleteTimer( OtaTimerId_t otaTimerId )
{
    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

    if( pOtaTimers[ otaTimerId ] != NULL )
    {
        /* Delete the timer*/
        errno = 0;

        if( timer_delete( otaTimers[ otaTimerId ] ) == -1 )
        {
            otaErrRet = OTA_ERR_EVENT_TIMER_DELETE_FAILED;

            LogError( ( "Failed to delete OTA timer: "
                        "timer_delete returned error: "
                        "otaErrRet=%i "
                        ",errno=%s",
                        otaErrRet,
                        strerror( errno ) ) );
        }
        else
        {
            LogDebug( ( "OTA Timer deleted." ) );

            pOtaTimers[ otaTimerId ] = NULL;
            otaErrRet = OTA_ERR_NONE;
        }
    }
    else
    {
        LogWarn( ( "OTA Timer handle NULL for Timerid=%i, can't delete.", otaTimerId ) );

        otaErrRet = OTA_ERR_EVENT_TIMER_DELETE_FAILED;
    }

    return otaErrRet;
}

void * STDC_Malloc( size_t size )
{
    /* Use standard C malloc.*/

    /* MISRA rule 21.3 prohibits the use of malloc and free from stdlib.h. But this implementation
     * is on linux, so it's a false positive. */
    /* coverity[misra_c_2012_rule_21_3_violation]. */
    return malloc( size );
}

void STDC_Free( void * ptr )
{
    /* Use standard C free.*/

    /* MISRA rule 21.3 prohibits the use of malloc and free from stdlib.h. But this implementation
     * is on linux, so it's a false positive. */
    /* coverity[misra_c_2012_rule_21_3_violation]. */
    free( ptr );
}
