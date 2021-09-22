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
 * @file OtaStartTimer_FreeRTOS_harness.c
 * @brief Implements the proof harness for OtaStartTimer_FreeRTOS function.
 */
/*  FreeRTOS includes for OTA library. */
#include "ota_os_freertos.h"
#include "FreeRTOS.h"
#include "timers.h"

/* Stub for creating the timer. */
TimerHandle_t xTimerCreate(const char* const pTimerName, TickType_t xTimerperiod
, UBaseType_t uxAutoReload, void* pvTimerId,
TimerCallbackFunction_t pxCallbackFunction)
{
    TimerHandle_t timer;
    return timer;
}

/* Stub to start the timer. */
BaseType_t xTimerStart(TimerHandle_t xTimer, TickType_t xBlockTime){
    BaseType_t status;
    return status;
}

/* Stub to reset the timer. */
BaseType_t xTimerReset(TimerHandle_t xTimer, TickType_t xBlockTime){
    BaseType_t status;
    return status;
}

void OtaStartTimer_FreeRTOS_harness()
{
    OtaTimerId_t otaTimerId;
    char* pTimerName;
    uint32_t timeout; 
    OtaTimerCallback_t callback;

    /* The valid range of values for OtaTimerId_t enum is [0,2) */
    __CPROVER_assume(otaTimerId >= 0 && otaTimerId < 2);

    OtaStartTimer_FreeRTOS(otaTimerId, pTimerName, timeout, callback);
}

