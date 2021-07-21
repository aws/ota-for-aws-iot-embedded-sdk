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
 * @file initFileTransfer_Http_harness.c
 * @brief Implements the proof harness for initFileTransfer_Http function.
 */
/* Http interface includes. */
#include "ota_http_private.h"

/* Stub required for the proof. */
OtaHttpStatus_t init( char * pUrl )
{
    OtaHttpStatus_t status;

    return status;
}

void initFileTransfer_Http_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaFileContext_t fileContext;
    OtaHttpInterface_t http;
    OtaHttpStatus_t status;
    OtaInterfaces_t interface;

    pAgentCtx = ( OtaAgentContext_t * ) malloc( sizeof( OtaAgentContext_t ) );

    /* The function requires Agent and the interface to be initialized and
     *  thus they can't be NULL. If they are, they will hit an assert in the function. */
    __CPROVER_assume( pAgentCtx != NULL );

    /* Initialize the file context from the Agent context. */
    pAgentCtx->fileContext = fileContext;

    /* Updating the function pointer in Http to the stub. */
    http.init = init;

    /* Update the interface and the Agent. */
    interface.http = http;
    pAgentCtx->pOtaInterface = &interface;

    /* Call function under test. */
    status = initFileTransfer_Http( pAgentCtx );

    /* The function should either return OtaErrNone or OtaErrCleanupDataFailed. */
    __CPROVER_assert( ( status == OtaErrNone ) ||
                      ( status == OtaErrInitFileTransferFailed ),
                      "The function return should be either OtaErrNone or OtaErrCleanupDataFailed" );
}
