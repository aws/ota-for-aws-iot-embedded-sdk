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

/* Linkage for error reporting. */
extern int errno;

static void requestTimerCallback( union sigval arg );
static void selfTestTimerCallback( union sigval arg );

static OtaTimerCallback_t otaTimerCallback;

/* OTA Event queue attributes.*/
static mqd_t otaEventQueue;

/* OTA Timer handles.*/
static timer_t otaTimer[ OtaNumOfTimers ];

/* OTA Timer callbacks.*/
void ( * timerCallback[ OtaNumOfTimers ] )( union sigval arg ) = { requestTimerCallback, selfTestTimerCallback };

OtaErr_t Posix_OtaInitEvent( OtaEventContext_t * pEventCtx )
{
    ( void ) pEventCtx;

    OtaErr_t otaErrRet = OtaErrorUnInitialized;
    struct mq_attr attr;

    /* Unlink the event queue.*/
    mq_unlink( OTA_QUEUE_NAME );

    /* Initialize queue attributes.*/
    attr.mq_flags = 0;
    attr.mq_maxmsg = MAX_MESSAGES;
    attr.mq_msgsize = MAX_MSG_SIZE;
    attr.mq_curmsgs = 0;

    /* Open the event queue.*/
    otaEventQueue = mq_open( OTA_QUEUE_NAME, O_CREAT | O_RDWR, S_IRWXU, &attr );

    if( otaEventQueue == -1 )
    {
        otaErrRet = OtaErrorEventQCreateFailed;

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

        otaErrRet = OtaErrorNone;
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaSendEvent( OtaEventContext_t * pEventCtx,
                             const void * pEventMsg,
                             unsigned int timeout )
{
    ( void ) pEventCtx;
    ( void ) timeout;

    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    /* Send the event to OTA event queue.*/
    if( mq_send( otaEventQueue, pEventMsg, MAX_MSG_SIZE, 0 ) == -1 )
    {
        otaErrRet = OtaErrorEventQSendFailed;

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

        otaErrRet = OtaErrorNone;
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaReceiveEvent( OtaEventContext_t * pContext,
                                void * pEventMsg,
                                uint32_t timeout )
{
    ( void ) pContext;
    ( void ) timeout;

    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    char * pDst = pEventMsg;
    char buff[ MAX_MSG_SIZE ];

    /* Receive the next event from OTA event queue.*/
    if( mq_receive( otaEventQueue, buff, sizeof( buff ), NULL ) == -1 )
    {
        otaErrRet = OtaErrorEventQReceiveFailed;

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
        memcpy( pDst, buff, MAX_MSG_SIZE );

        otaErrRet = OtaErrorNone;
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaDeinitEvent( OtaEventContext_t * pContext )
{
    ( void ) pContext;

    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    /* Remove the event queue.*/
    if( mq_unlink( OTA_QUEUE_NAME ) == -1 )
    {
        otaErrRet = OtaErrorEventQDeleteFailed;

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

        otaErrRet = OtaErrorNone;
    }

    return otaErrRet;
}

static void selfTestTimerCallback( union sigval arg )
{
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
    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    /* Create the timer structures. */
    struct sigevent sgEvent;
    struct itimerspec timerAttr;

    /* clear everything in the structures. */
    memset( &sgEvent, 0, sizeof( struct sigevent ) );
    memset( &timerAttr, 0, sizeof( struct itimerspec ) );

    /* Set attributes. */
    sgEvent.sigev_notify = SIGEV_THREAD;
    sgEvent.sigev_value.sival_ptr = otaTimer[ otaTimerId ];
    sgEvent.sigev_notify_function = timerCallback[ otaTimerId ];

    /* Set OTA lib callback. */
    otaTimerCallback = callback;

    /* Set timeout attributes.*/
    timerAttr.it_value.tv_sec = timeout / 1000;

    /* Create timer if required.*/
    if( otaTimer[ otaTimerId ] == NULL )
    {
        if( timer_create( CLOCK_REALTIME, &sgEvent, &otaTimer[ otaTimerId ] ) == -1 )
        {
            otaErrRet = OtaErrorEventTimerCreateFailed;

            LogError( ( "Failed to create OTA timer: "
                        "timer_create returned error: "
                        "otaErrRet=%i "
                        ",errno=%s",
                        otaErrRet,
                        strerror( errno ) ) );
        }
    }

    /* Set timeout.*/
    if( otaTimer[ otaTimerId ] != NULL )
    {
        if( timer_settime( otaTimer[ otaTimerId ], 0, &timerAttr, NULL ) == -1 )
        {
            otaErrRet = OtaErrorEventTimerCreateFailed;

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
            otaErrRet = OtaErrorNone;
        }
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaStopTimer( OtaTimerId_t otaTimerId )
{
    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    /* Create the timer structures. */
    struct itimerspec timerAttr;

    /* clear everything in the structures. */
    memset( &timerAttr, 0, sizeof( struct itimerspec ) );

    /* Clear the timeout. */
    timerAttr.it_value.tv_sec = 0;

    if( otaTimer[ otaTimerId ] != NULL )
    {
        /* Stop the timer*/
        if( timer_settime( otaTimer[ otaTimerId ], 0, &timerAttr, NULL ) == -1 )
        {
            otaErrRet = OtaErrorEventTimerStopFailed;

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

            otaErrRet = OtaErrorNone;
        }
    }
    else
    {
        LogWarn( ( "OTA Timer handle NULL for Timerid=%i, can't stop.", otaTimerId ) );

        otaErrRet = OtaErrorNone;
    }

    return otaErrRet;
}

OtaErr_t Posix_OtaDeleteTimer( OtaTimerId_t otaTimerId )
{
    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    if( otaTimer[ otaTimerId ] != NULL )
    {
        /* Delete the timer*/
        if( timer_delete( otaTimer[ otaTimerId ] ) == -1 )
        {
            otaErrRet = OtaErrorEventTimerDeleteFailed;

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

            otaErrRet = OtaErrorNone;
        }
    }
    else
    {
        LogWarn( ( "OTA Timer handle NULL for Timerid=%i, can't delete.", otaTimerId ) );

        otaErrRet = OtaErrorNone;
    }

    return otaErrRet;
}

void * STDC_Malloc( size_t size )
{
    /* Use standard C malloc.*/
    return malloc( size );
}

void STDC_Free( void * ptr )
{
    /* Use standard C free.*/
    free( ptr );
}
