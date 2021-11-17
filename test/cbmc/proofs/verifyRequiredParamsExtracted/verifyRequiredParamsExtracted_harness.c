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
 * @file verifyRequiredParamsExtracted_harness.c
 * @brief Implements the proof harness for verifyRequiredParamsExtracted function.
 */
/*  Ota Agent includes. */
#include "ota.h"

extern OtaAgentContext_t otaAgent;
extern DocParseErr_t verifyRequiredParamsExtracted( const JsonDocParam_t * pModelParam,
                                                    const JsonDocModel_t * pDocModel );

void verifyRequiredParamsExtracted_harness()
{
    /* docModel cannot be NULL as it is statically initialized in parseJobDoc function
     * before being passed to verifyRequiredParamsExtracted function.*/
    JsonDocModel_t docModel;
    JsonDocParam_t modelParams;
    DocParseErr_t err;

    uint32_t paramsReceivedBitmap;
    uint32_t paramsRequiredBitmap;
    uint32_t numModelParams;

    /* The number of parameters in the jsonDoc are defined by OTA_NUM_JOB_PARAMS. */
    __CPROVER_assume( numModelParams <= OTA_NUM_JOB_PARAMS + 1 );

    /* CBMC preconditions. */
    docModel.paramsReceivedBitmap = paramsReceivedBitmap;
    docModel.paramsRequiredBitmap = paramsRequiredBitmap;
    docModel.numModelParams = numModelParams;

    err = verifyRequiredParamsExtracted( &modelParams, &docModel );

    __CPROVER_assert( ( err == DocParseErrNone ) || ( err == DocParseErrMalformedDoc ),
                      "Error: Expected return value to be either DocParseErrNone or DocParseErrMalformedDoc" );
}
