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
 * @file validateDataBlock_harness.c
 * @brief Implements the proof harness for validateDataBlock function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include <stdlib.h>

bool __CPROVER_file_local_ota_c_validateDataBlock( const OtaFileContext_t * pFileContext,
                                                   uint32_t blockIndex,
                                                   uint32_t blockSize );

void validateDataBlock_harness()
{
    OtaFileContext_t * pFileContext;
    uint32_t blockIndex;
    uint32_t blockSize;
    uint32_t fileSize;

    pFileContext = ( OtaFileContext_t * ) malloc( sizeof( OtaFileContext_t ) );

    /* Pre-conditions.
     * otaAgent.pFileContext is passed as the fileContext to validateDataBlock. This can be
     * seen in the processDataHandler function. */
    __CPROVER_assume( pFileContext != NULL );

    __CPROVER_assume( fileSize <= MAX_FILE_SIZE );

    pFileContext->fileSize = fileSize;

    __CPROVER_file_local_ota_c_validateDataBlock( pFileContext, blockIndex, blockSize );

    free( pFileContext );
}
