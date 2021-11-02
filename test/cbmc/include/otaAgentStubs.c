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
 * @file otaAgentStubs.c
 * @brief Adds stubs required for the CBMC proofs of OTA Agent functions.
 */
/*  Ota Agent includes. */
#include "ota.h"

/* Stub for stop function in os.timer interface. */
OtaOsStatus_t timerStop( OtaTimerId_t otaTimerId )
{
    OtaOsStatus_t status;

    __CPROVER_assume( ( status >= OtaOsSuccess ) && ( status <= OtaOsTimerDeleteFailed ) );

    return status;
}

/* Stub to activate pal interface. */
OtaPalStatus_t palActivate( OtaFileContext_t * const pFileContext )
{
    OtaPalStatus_t status;

    return status;
}
