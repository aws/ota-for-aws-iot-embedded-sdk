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
 * @file requestDataBlock_Http_harness.c
 * @brief Implements the proof harness for requestDataBlock_Http function.
 */
/* Http interface includes. */
#include "ota_http_private.h"

/* Stub required for the proof. */
OtaHttpStatus_t request( uint32_t rangeStart,
                         uint32_t rangeEnd )
{
    OtaHttpStatus_t status;

    return status;
}
/*-----------------------------------------------------------*/

void requestDataBlock_Http_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaFileContext_t fileContext;
    OtaHttpInterface_t http;
    OtaInterfaces_t interface;
    OtaErr_t err;

    /* Allocating memory to the agent context. */
    pAgentCtx = ( OtaAgentContext_t * ) malloc( sizeof( OtaAgentContext_t ) );

    /* The Agent context cannot point to NULL. If it does, then the assert
     *  in the source file is triggered. */
    __CPROVER_assume( pAgentCtx != NULL );

    /* Initialize the file context field in the Agent context. */
    pAgentCtx->fileContext = fileContext;
    http.request = request;
    interface.http = http;

    /* The file size in the file context should have a non-zero value. */
    __CPROVER_assume( pAgentCtx->fileContext.fileSize != 0 );

    /* Initialize the interface in the Agent Context. */
    pAgentCtx->pOtaInterface = &interface;

    /* Call to the function under test. */
    err = requestDataBlock_Http( pAgentCtx );

    /*Assert to check if the return from the function is of expected values. */
    __CPROVER_assert( ( err == OtaErrNone ) || ( err == OtaErrRequestFileBlockFailed ),
                      "The function return should be either of these values" );
}
