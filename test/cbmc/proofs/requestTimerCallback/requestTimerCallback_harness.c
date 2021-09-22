/*
 * AWS IoT Over-the-air Update v3.0.0
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
 * @file requestTimerCallback_harness.c
 * @brief Implements the proof harness for requestTimerCallback function.
 */
/*  FreeRTOS includes for OTA library. */
#include "ota_os_freertos.h"
#include "FreeRTOS.h"
#include "timers.h"
#include "ota_private.h"

/* Declaration of the mangled name function created by CBMC for static functions.*/
void __CPROVER_file_local_ota_os_freertos_c_requestTimerCallback(TimerHandle_t timer);

void otaTimerCallback( OtaTimerId_t otaTimerId )
{
    assert( ( otaTimerId == OtaRequestTimer ) || ( otaTimerId == OtaSelfTestTimer ) );

    if( otaTimerId == OtaRequestTimer )
    {
        OtaEventMsg_t xEventMsg = { 0 };

        LogDebug( ( "Self-test expired within %ums",
                    otaconfigFILE_REQUEST_WAIT_MS ) );

        xEventMsg.eventId = OtaAgentEventRequestTimer;

        /* Send request timer event. */
        if( OTA_SignalEvent( &xEventMsg ) == false )
        {
            LogError( ( "Failed to signal the OTA Agent to start request timer" ) );
        }
    }
    else /* ( otaTimerId == OtaSelfTestTimer ) */
    {
        LogError( ( "Self test failed to complete within %ums",
                    otaconfigSELF_TEST_RESPONSE_WAIT_MS ) );

    }
}

bool OTA_SignalEvent( const OtaEventMsg_t * const pEventMsg )
{
    bool status;
    return status;
}

void requestTimerCallback_harness()
{
    TimerHandle_t timer;
    OtaTimerId_t otaTimerId;
    char * pTimerName;
    uint32_t timeout;

    __CPROVER_assume(otaTimerId >= 0 && otaTimerId < 2);

    __CPROVER_assume(timeout < UINT32_MAX / 1000);
    
    OtaStartTimer_FreeRTOS( otaTimerId,
                                 pTimerName,
                                    timeout,
                                      otaTimerCallback );

    __CPROVER_file_local_ota_os_freertos_c_requestTimerCallback(timer);
}