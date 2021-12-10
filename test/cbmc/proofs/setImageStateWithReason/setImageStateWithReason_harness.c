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
 * @file setImageStateWithReason_harness.c
 * @brief Implements the proof harness for setImageStateWithReason function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include <string.h>

extern OtaAgentContext_t otaAgent;
extern OtaErr_t setImageStateWithReason( OtaImageState_t stateToSet,
                                         uint32_t reasonToSet );

OtaPalStatus_t setPlatformImageStateStub( OtaFileContext_t * const pFileContext,
                                          OtaImageState_t eState )
{
    OtaPalStatus_t status;

    /* status must have values of OtaPalStatus_t. */
    __CPROVER_assume( status <= INT32_MAX );

    __CPROVER_assert( pFileContext != NULL,
                      "Error: pFileContext in the otaAgent is statically initialized and hence cannot be NULL." );

    return status;
}

void setImageStateWithReason_harness()
{
    OtaImageState_t stateToSet;
    OtaInterfaces_t otaInterface;
    uint32_t reasonToSet;
    size_t activeJobNameSize;

    __CPROVER_havoc_object(&otaAgent);

    __CPROVER_assume(activeJobNameSize < OTA_JOB_ID_MAX_SIZE);

    otaInterface.pal.setPlatformImageState = setPlatformImageStateStub;

    otaAgent.pOtaInterface = &otaInterface;

    memset(otaAgent.pActiveJobName, 'a', activeJobNameSize);
    otaAgent.pActiveJobName[activeJobNameSize] = '\0';

    setImageStateWithReason(stateToSet,reasonToSet);
}
