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

    /* Initializing the unconstrained variables. These variables can never be NUll
     *  since they have been declared statically in the decodeAndStoreDataBlock() function. */
    pFileId = &fileId;
    pBlockId = &blockId;
    pBlockSize = &blockSize;

    /* Initialize the pPayload pointer. */
    pPayload = ( char ** ) malloc( sizeof( char * ) );

    /* pPayload cannot point to NULL since it is always initialized in the ingestDataBlock function. */
    __CPROVER_assume( pPayload != NULL );

    /* Allocate memory for the payload and the buffer to store the message. */
    *pPayload = ( char * ) malloc( messageSize );
    pMessageBuffer = ( uint8_t * ) malloc( messageSize );

    /* size can never be NULL since it is a pointer to the payload buffer which is initialized
     *  statically in the ingestDataBlock() Function. */
    __CPROVER_assume( *pPayload != NULL );

    /* Initializing the variable. */
    /**pPayload = size; */
    pPayloadSize = &payloadSize;

    /* This assumption is made because the pMessageBuffer is always pointing to a
     *  static array. */
    __CPROVER_assume( pMessageBuffer != NULL );

    err = decodeFileBlock_Http( pMessageBuffer, messageSize, pFileId,
                                pBlockId, pBlockSize, pPayload, pPayloadSize );

    /* Assert because the function cannot return values other OtaErrNone and OtaErrInvalidArg. */
    __CPROVER_assert( ( ( err == OtaErrNone ) || ( err == OtaErrInvalidArg ) ),
                      "Function return should be either None or invalid argument" );

    /* Free allocated memory. */
    /*free( size ); */
    free( pMessageBuffer );
}
