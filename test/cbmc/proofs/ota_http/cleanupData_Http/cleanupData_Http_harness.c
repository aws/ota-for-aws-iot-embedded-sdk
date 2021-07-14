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
 * @file cleanupData_Http_harness.c
 * @brief Implements the proof harness for cleanupData_Http function.
 */

#include "ota.h"
#include "ota_http_private.h"

OtaHttpStatus_t deinit()
{
    OtaHttpStatus_t status;

    return status;
}

void cleanupData_Http_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaHttpInterface_t http;
    OtaInterfaces_t * interfaces;

    pAgentCtx = ( OtaAgentContext_t * ) malloc( sizeof( OtaAgentContext_t ) );
    interfaces = ( OtaInterfaces_t * ) malloc( sizeof( OtaInterfaces_t ) );

    http.deinit = deinit;

    __CPROVER_assume( pAgentCtx != NULL && interfaces != NULL );

    interfaces->http = http;

    pAgentCtx->pOtaInterface = interfaces;

    cleanupData_Http( pAgentCtx );
}