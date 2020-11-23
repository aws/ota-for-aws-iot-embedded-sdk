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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "timers.h"
#include "queue.h"

/* OTA OS POSIX Interface Includes.*/
#include "ota_os_freertos.h"

/* OTA Event queue attributes.*/
#define MAX_MESSAGES    10
#define MAX_MSG_SIZE    sizeof( OtaEventMsg_t )

/* Array containing pointer to the OTA event structures used to send events to the OTA task. */
static OtaEventMsg_t queueData[ MAX_MESSAGES ];

/* The queue control structure.  .*/
static StaticQueue_t staticQueue;

/* The queue control handle.  .*/
static QueueHandle_t otaEventQueue;

/* OTA App Timer callback.*/
static OtaTimerCallback_t otaTimerCallback;

/* OTA Timer handles.*/
static TimerHandle_t otaTimer[ OtaNumOfTimers ];

/* OTA Timer callbacks.*/
static void requestTimerCallback( union sigval arg );
static void selfTestTimerCallback( union sigval arg );
void ( * timerCallback[ OtaNumOfTimers ] )( TimerHandle_t T ) = { requestTimerCallback, selfTestTimerCallback };

OtaErr_t OtaInitEvent_FreeRTOS( OtaEventContext_t * pEventCtx )
{
    ( void ) pContext;

    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    otaEventQueue = xQueueCreateStatic( ( UBaseType_t ) OTA_NUM_MSG_Q_ENTRIES,
                                        ( UBaseType_t ) MAX_MSG_SIZE,
                                        ( uint8_t * ) queueData,
                                        &staticQueue );

    if( otaEventQueue == NULL )
    {
        otaErrRet = OtaErrorEventQCreateFailed;

        LogError( ( "Failed to create OTA Event Queue: "
                    "xQueueCreateStatic returned error: "
                    "otaErrRet=%i ",
                    otaErrRet ) );
    }
    else
    {
        otaErrRet = OtaErrorNone;

        LogDebug( ( "OTA Event Queue created." ) );
    }

    return otaErrRet;
}

OtaErr_t OtaSendEvent_FreeRTOS( OtaEventContext_t * pContext,
                                const void * pEventMsg,
                                unsigned int timeout )
{
    ( void ) pContext;
    ( void ) timeout;

    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    BaseType_t retVal = pdFALSE;

    /* Send the event to OTA event queue.*/
    retVal = xQueueSendToBack( otaEventQueue, pxEventMsg, ( TickType_t ) 0 );

    if( retVal == pdTRUE )
    {
        otaErrRet = OtaErrorNone;

        LogDebug( ( "OTA Event Sent." ) );
    }
    else
    {
        otaErrRet = OtaErrorEventQSendFailed;

        LogError( ( "Failed to send event to OTA Event Queue: "
                    "xQueueSendToBack returned error: "
                    "otaErrRet=%i ",
                    otaErrRet ) );
    }

    return otaErrRet;
}

OtaErr_t OtaReceiveEvent_FreeRTOS( OtaEventContext_t * pContext,
                                   void * pEventMsg,
                                   uint32_t timeout )
{
    ( void ) pContext;

    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    BaseType_t retVal = pdFALSE;

    /* Temp buffer.*/
    char buff[ MAX_MSG_SIZE ];

    retVal = xQueueReceive( otaEventQueue, &buff, portMAX_DELAY );

    if( retVal == pdTRUE )
    {
        /* copy the data from local buffer.*/
        memcpy( pEventMsg, buff, MAX_MSG_SIZE );

        otaErrRet = OtaErrorNone;

        LogDebug( ( "OTA Event received" ) );
    }
    else
    {
        otaErrRet = OtaErrorEventQReceiveFailed;

        LogError( ( "Failed to receive event from OTA Event Queue: "
                    "xQueueReceive returned error: "
                    "otaErrRet=%i ",
                    otaErrRet ) );
    }

    return otaErrRet;
}

void OtaDeinitEvent_FreeRTOS( OtaEventContext_t * pContext )
{
    ( void ) pContext;

    /* Remove the event queue.*/
    if( otaEventQueue != NULL )
    {
        vQueueDelete( otaEventQueue );

        LogDebug( ( "OTA Event Queue Deleted." ) );
    }
}

static void selfTestTimerCallback( TimerHandle_t T )
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

static void requestTimerCallback( TimerHandle_t T )
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

OtaErr_t OtaStartTimer_FreeRTOS( OtaTimerId_t otaTimerId,
                                 const char * const pTimerName,
                                 const uint32_t timeout,
                                 OtaTimerCallback_t callback )
{
    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    BaseType_t retVal = pdFALSE;

    assert( callback != NULL );

    /* If timer is not created.*/
    if( otaTimer[ otaTimerId ] == NULL )
    {
        /* Create the timer. */
        otaTimer[ otaTimerId ] = xTimerCreate( pTimerName,
                                               pdMS_TO_TICKS( timeout ),
                                               pdFALSE,
                                               NULL,
                                               timerCallback[ otaTimerId ] );

        if( otaTimer[ otaTimerId ] == NULL )
        {
            otaErrRet = OtaErrorEventTimerCreateFailed;

            LogError( ( "Failed to create OTA timer: "
                        "timerCreate returned NULL "
                        "otaErrRet=%i "
                        otaErrRet ) );
        }
        else
        {
            otaErrRet = OtaErrorNone;

            LogDebug( ( "OTA Timer created." ) );

            /* Start the timer. */
            retVal = xTimerStart( otaTimer[ otaTimerId ], portMAX_DELAY );

            if( retVal == pdTRUE )
            {
                otaErrRet = OtaErrorNone;

                LogDebug( ( "OTA Timer started." ) );
            }
            else
            {
                otaErrRet = OtaErrorEventTimerStartFailed;

                LogError( ( "Failed to start OTA timer: "
                            "timerStart returned error." ) );
            }
        }
    }
    else
    {
        /* Reset the timer. */
        retVal = xTimerReset( otaTimer[ otaTimerId ], portMAX_DELAY );

        if( retVal == pdTRUE )
        {
            otaErrRet = OtaErrorNone;

            LogDebug( ( "OTA Timer restarted." ) );
        }
        else
        {
            otaErrRet = OtaErrorEventTimerRestartFailed;

            LogError( ( "Failed to set OTA timer timeout: "
                        "timer_settime returned error: "
                        "otaErrRet=%i ",
                        otaErrRet ) );
        }
    }

    return otaErrRet;
}

OtaErr_t OtaStopTimer_FreeRTOS( OtaTimerId_t otaTimerId )
{
    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    if( otaTimer[ otaTimerId ] != NULL )
    {
        /* Stop the timer. */
        retVal = xTimerStop( otaTimer[ otaTimerId ], portMAX_DELAY );

        if( retVal == pdTRUE )
        {
            LogDebug( ( "OTA Timer Stopped for Timerid=%i.", otaTimerId ) );

            otaErrRet = OtaErrorNone;
        }
        else
        {
            LogError( ( "Failed to stop OTA timer: "
                        "timer_settime returned error: "
                        "otaErrRet=%i ",
                        otaErrRet ) );

            otaErrRet = OtaErrorEventTimerStopFailed;
        }
    }
    else
    {
        LogWarn( ( "OTA Timer handle NULL for Timerid=%i, can't stop.", otaTimerId ) );

        otaErrRet = OtaErrorNone;
    }

    return otaErrRet;
}

OtaErr_t ota_DeleteTimer( OtaTimerId_t otaTimerId )
{
    OtaErr_t otaErrRet = OtaErrorUnInitialized;

    if( otaTimer[ otaTimerId ] != NULL )
    {
        /* Stop the timer. */
        retVal = xTimerDelete( otaTimer[ otaTimerId ], portMAX_DELAY );

        if( retVal == pdTRUE )
        {
            otaErrRet = OtaErrorNone;

            otaTimer[ otaTimerId ] == NULL;

            LogDebug( ( "OTA Timer deleted." ) );
        }
        else
        {
            otaErrRet = OtaErrorEventTimerDeleteFailed;

            LogError( ( "Failed to delete OTA timer: "
                        "timer_delete returned error: "
                        "otaErrRet=%i ",
                        otaErrRet ) );
        }
    }
    else
    {
        otaErrRet = OtaErrorEventTimerDeleteFailed;

        LogWarn( ( "OTA Timer handle NULL for Timerid=%i, can't delete.", otaTimerId ) );
    }

    return otaErrRet;
}

void * Malloc_FreeRTOS( size_t size )
{
    return vPortMalloc( size );
}

void Malloc_Free( void * ptr )
{
    vPortFree( ptr );
}
