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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "timers.h"
#include "queue.h"

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* OTA OS Interface Includes.*/
#include "ota_os_interface.h"

/* OTA OS POSIX Interface Includes.*/
#include "ota_os_freertos.h"

/* OTA Event queue attributes.*/
#define MAX_MESSAGES    10
#define MAX_MSG_SIZE    12

/* Array containing pointer to the OTA event structures used to send events to the OTA task. */
static OTA_EventMsg_t xQueueData[ MAX_MESSAGES ];

/* The queue control structure.  .*/
static StaticQueue_t xStaticQueue;

/* The queue control handle.  .*/
QueueHandle_t xOtaEventQueue;

/* OTA Timer.*/


int32_t ota_InitEvent( OtaEventContext_t * pContext )
{
    ( void ) pContext;

    xOtaEventQueue = xQueueCreateStatic( ( UBaseType_t ) OTA_NUM_MSG_Q_ENTRIES,
                                         ( UBaseType_t ) MAX_MSG_SIZE,
                                         ( uint8_t * ) xQueueData,
                                         &xStaticQueue );

    if( xOtaEventQueue == NULL )
    {
        return 0;
    }

    return 1;
}

int32_t ota_SendEvent( OtaEventContext_t * pContext,
                       const void * pEventMsg,
                       unsigned int timeout )
{
    ( void ) pContext;
    ( void ) timeout;

    /* Send the event to OTA event queue.*/
    if( xQueueSendToBack( xOtaEventQueue, pxEventMsg, ( TickType_t ) 0 ) )
    {
        LogInfo( ( "OTA Event Sent." ) );
        return 1;
    }
    else
    {
        LogDebug( ( "OTA Event send failed" ) );
        return 0;
    }
}

int32_t ota_ReceiveEvent( OtaEventContext_t * pContext,
                          void * pEventMsg,
                          uint32_t timeout )
{
    ( void ) pContext;
    ( void ) timeout;

    char buff[ MAX_MSG_SIZE ];

    if( xQueueReceive( xOtaEventQueue, &buff, portMAX_DELAY ) == pdTRUE )
    {
        LogInfo( ( "OTA Event receive failed." ) );
    }
    else
    {
        LogInfo( ( "OTA Event received" ) );

        /* copy the data from local buffer.*/
        memcpy( pEventMsg, buff, MAX_MSG_SIZE );
        return 1;
    }

    return 0;
}

void ota_DeinitEvent( OtaEventContext_t * pContext )
{
    ( void ) pContext;

    /* Remove the event queue.*/
    if( xOtaEventQueue != NULL )
    {
        vQueueDelete( xOtaEventQueue );
    }
}
