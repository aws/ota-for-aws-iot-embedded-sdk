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
/* Http interface inclues. */
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

    char * size = ( char * ) malloc( messageSize );
    pMessageBuffer = ( uint8_t * ) malloc( messageSize );

    /* The size of the message buffer cannot be null. */
    __CPROVER_assume( size != NULL );

    /* Intializing the variable. */
    pPayload = &size;
    pPayloadSize = &payloadSize;

    /* The size of message buffer is not null. */
    __CPROVER_assume( pMessageBuffer != NULL );

    /* pFileId should be pointing to a file. */
    __CPROVER_assume( pFileId != NULL );

    /* pBlockId should point to a block inside the file. */
    __CPROVER_assume( pBlockId != NULL );

    /* The block should have non-zero size. */
    __CPROVER_assume( pBlockSize != NULL );

    /* the size of the Payload should be non-zero. */
    __CPROVER_assume( pPayloadSize != NULL );

    /* Call the proof. */
    err = decodeFileBlock_Http( pMessageBuffer, messageSize, pFileId, pBlockId, pBlockSize, pPayload, pPayloadSize );

    /* Assert because the function cannot return values other OtaErrNone and OtaErrInvalidArg. */
    __CPROVER_assert( ( ( err == OtaErrNone ) || ( err == OtaErrInvalidArg ) ), "Function return should be either None or invalid argument" );

    /* Free allocated memory. */
    free( size );
    free( pMessageBuffer );
}
