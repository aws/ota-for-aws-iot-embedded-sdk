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

#include "ota_http_private.h"


void decodeFileBlock_Http_harness()
{
    uint8_t * pMessageBuffer;
    size_t messageSize;
    int32_t * pFileId;
    int32_t * pBlockId;
    int32_t * pBlockSize;
    uint8_t ** pPayload;
    size_t * pPayloadSize;

    __CPROVER_assume( messageSize < ( OTA_FILE_BLOCK_SIZE + 1 ) && messageSize != 0 );

    pMessageBuffer = ( uint8_t * ) malloc( messageSize );

    pFileId = ( int32_t * ) malloc( sizeof( int32_t ) );
    pBlockId = ( int32_t * ) malloc( sizeof( int32_t ) );
    pBlockSize = ( int32_t * ) malloc( sizeof( int32_t ) );

    char * temp = malloc( messageSize );
    __CPROVER_assume( temp != NULL );

    pPayload = &temp;

    pPayloadSize = ( size_t * ) malloc( sizeof( size_t ) );

    __CPROVER_assume( pMessageBuffer != NULL && pFileId != NULL && pBlockId != NULL &&
                      pBlockSize != NULL && pPayloadSize != NULL );

    decodeFileBlock_Http( pMessageBuffer, messageSize, pFileId, pBlockId, pBlockSize, pPayload, pPayloadSize );
}
