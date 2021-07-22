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
 * @file decodeFileBlock_Http_harness.c
 * @brief Implements the proof harness for decodeFileBlock_Http function.
 */
/* Http interface includes. */
#include "ota_http_private.h"


void decodeFileBlock_Http_harness()
{
    OtaErr_t err;

    uint8_t * pMessageBuffer;
    size_t messageSize;
    int32_t * pFileId;
    int32_t * pBlockId;
    int32_t * pBlockSize;
    uint8_t ** pPayload;
    size_t * pPayloadSize;

    int32_t fileId;
    int32_t blockId;
    int32_t blockSize;
    size_t payloadSize;

    /* Initializing the unconstrained variables. */
    pFileId = &fileId;
    pBlockId = &blockId;
    pBlockSize = &blockSize;

    /* Allocate memory for the payload and the buffer to store the message. */
    char * size = ( char * ) malloc( messageSize );
    pMessageBuffer = ( uint8_t * ) malloc( messageSize );

    /* size is used to store the content from the message buffer and should
     *  not point to a NULL address. */
    __CPROVER_assume( size != NULL );

    /* Initializing the variable. */
    pPayload = &size;
    pPayloadSize = &payloadSize;

    /* pMessageBuffer stores the message from the FIle and should point to a NULL
     *  address. */
    __CPROVER_assume( pMessageBuffer != NULL );

    /* pFileId is required to point to a FILE and cannot point to a NULL address. */
    __CPROVER_assume( pFileId != NULL );

    /* BlockId is pointer to the block inside the file and should not point to a NULL
     * address. */
    __CPROVER_assume( pBlockId != NULL );

    /* pBlockSize is a pointer to store the size of the current block and should not
     *  point to a NULL address. */
    __CPROVER_assume( pBlockSize != NULL );

    /* pPayloadSize is the pointer to a variable which stores the size of the Payload
     *  and should not be point to NULL address. */
    __CPROVER_assume( pPayloadSize != NULL );

    err = decodeFileBlock_Http( pMessageBuffer, messageSize, pFileId,
                                pBlockId, pBlockSize, pPayload, pPayloadSize );

    /* Assert because the function cannot return values other OtaErrNone and OtaErrInvalidArg. */
    __CPROVER_assert( ( ( err == OtaErrNone ) || ( err == OtaErrInvalidArg ) ),
                      "Function return should be either None or invalid argument" );

    /* Free allocated memory. */
    free( size );
    free( pMessageBuffer );
}
