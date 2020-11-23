/*
 * FreeRTOS OTA V2.0.0
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

/**
 * @file ota_http.c
 * @brief Data transfer over HTTP routines.
 */

/* Standard library include. */
#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

/* OTA includes. */
#include "ota.h"
#include "ota_private.h"
#include "ota_http_private.h"

/**
 * @brief Track the current block for HTTP requests
 *
 */
static uint32_t currBlock;

/*
 * Init file transfer by initializing the http module with the pre-signed url.
 */
OtaErr_t initFileTransfer_Http( OtaAgentContext_t * pAgentCtx )
{
    LogInfo( ( "Invoking initFileTransfer_Http" ) );

    assert( pAgentCtx != NULL && pAgentCtx->pOtaInterface != NULL );

    /* Return status. */
    OtaErr_t status = OtaErrorUnInitialized;

    /* Pre-signed URL. */
    char * pURL = NULL;

    /* File context from OTA agent. */
    OtaFileContext_t * fileContext = &( pAgentCtx->fileContext );

    /* Get pre-signed URL from pAgentCtx. */
    pURL = fileContext->pUpdateUrlPath;

    /* Connect to the HTTP server and initialize download information. */
    status = pAgentCtx->pOtaInterface->http.init( pURL );

    return status;
}

/*
 * Check for next available OTA job from the job service.
 */
OtaErr_t requestDataBlock_Http( OtaAgentContext_t * pAgentCtx )
{
    LogInfo( ( "Invoking requestDataBlock_Http" ) );

    assert( pAgentCtx != NULL && pAgentCtx->pOtaInterface != NULL );

    /* Return status. */
    OtaErr_t status = OtaErrorUnInitialized;

    /* Values for the "Range" field in HTTP header. */
    uint32_t rangeStart = 0;
    uint32_t rangeEnd = 0;

    /* File context from OTA agent. */
    OtaFileContext_t * fileContext = &( pAgentCtx->fileContext );

    /* Calculate ranges. */
    rangeStart = currBlock * OTA_FILE_BLOCK_SIZE;

    if( fileContext->blocksRemaining == 1 )
    {
        rangeEnd = fileContext->fileSize - 1;
    }
    else
    {
        rangeEnd = rangeStart + OTA_FILE_BLOCK_SIZE - 1;
    }

    /* Request file data over HTTP using the rangeStart and rangeEnd. */
    status = pAgentCtx->pOtaInterface->http.request( rangeStart, rangeEnd );

    return status;
}

/*
 * Decode a cbor encoded fileblock received from streaming service.
 */
OtaErr_t decodeFileBlock_Http( uint8_t * pMessageBuffer,
                               size_t messageSize,
                               int32_t * pFileId,
                               int32_t * pBlockId,
                               int32_t * pBlockSize,
                               uint8_t ** pPayload,
                               size_t * pPayloadSize )
{
    assert( pMessageBuffer != NULL && pFileId != NULL && pBlockId != NULL &&
            pBlockSize != NULL && pPayload != NULL && pPayloadSize != NULL );

    /* Unused parameters. */
    ( void ) messageSize;

    /* The data received over HTTP does not require any decoding. */
    *pPayload = pMessageBuffer;
    *pFileId = 0;
    *pBlockId = currBlock;
    *pBlockSize = messageSize;
    *pPayloadSize = messageSize;

    /* Current block is processed, set the file block to next. */
    currBlock += 1;

    return OtaErrorNone;
}

/*
 * Perform any cleanup operations required for data plane.
 */
OtaErr_t cleanupData_Http( OtaAgentContext_t * pAgentCtx )
{
    assert( pAgentCtx != NULL && pAgentCtx->pOtaInterface != NULL );

    /* Call HTTP deinit to cleanup */
    OtaErr_t status = pAgentCtx->pOtaInterface->http.deinit();

    /* Reset currBlock. */
    currBlock = 0;

    return status;
}
