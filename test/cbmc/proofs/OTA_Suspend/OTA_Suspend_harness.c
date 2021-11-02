/*
 * AWS IoT Over-the-air Update v3.1.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file OTA_Suspend_harness.c
 * @brief Implements the proof harness for OTA_Suspend function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "otaAgentStubs.c"

extern OtaAgentContext_t otaAgent;

void OTA_Suspend_harness()
{
    OtaState_t state;
    OtaErr_t err;
    OtaInterfaces_t otaInterface;

    otaInterface.os.timer.stop = timerStop;

    otaAgent.state = state;
    otaAgent.pOtaInterface = &otaInterface;

    /* OtaInterface in the otaAgent is always checked in OTA_Init to be non-NULL. */
    __CPROVER_assume( otaAgent.pOtaInterface != NULL );

    /* otaAgent.state must always have values of OtaState_t enum type. */
    __CPROVER_assume( ( otaAgent.state >= OtaAgentStateNoTransition ) && ( otaAgent.state <= OtaAgentStateAll ) );

    err = OTA_Suspend();

    __CPROVER_assert( ( err == OtaErrNone ) || ( err == OtaErrAgentStopped ) ||
                      ( err == OtaErrSignalEventFailed ), "Invalid return value from OTA_Suspend: Expected OtaErrNone, OtaErrAgentStopped or OtaErrSignalEventFailed." );
}
