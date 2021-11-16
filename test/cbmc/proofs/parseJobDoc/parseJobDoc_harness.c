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
 * @file parseJobDoc_harness.c
 * @brief Implements the proof harness for parseJobDoc function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "stubs.h"
#include <string.h>
#include <stdlib.h>
#include "ota_interface_private.h"

extern OtaAgentContext_t otaAgent;
extern OtaFileContext_t * parseJobDoc( const JsonDocParam_t * pJsonExpectedParams,
                                       uint16_t numJobParams,
                                       const char * pJson,
                                       uint32_t messageLength,
                                       bool * pUpdateJob );

/* Stub to initialize the json docModel. */
DocParseErr_t initDocModel( JsonDocModel_t * pDocModel,
                            const JsonDocParam_t * pBodyDef,
                            void * contextBaseAddr,
                            uint32_t contextSize,
                            uint16_t numJobParams )
{
    DocParseErr_t err;

    /* contextBaseAddr is initialized to the fileContext from otaAgent which is statically
     * initialized and hence cannot be NULL. */
    __CPROVER_assert( contextBaseAddr != NULL,
                      "Invalid contextBaseAddr val: Expected a non-NULL value." );

    __CPROVER_assume( ( err >= DocParseErrUnknown ) && ( err <= DocParseErrInvalidToken ) );
    return err;
}

/* Stub to extract information from job doc. */
DocParseErr_t parseJSONbyModel( const char * pJson,
                                uint32_t messageLength,
                                JsonDocModel_t * pDocModel )
{
    DocParseErr_t err;

    /* pDocModel is statically declared in parseJobDoc and hence cannot be NULL.*/
    __CPROVER_assert( pDocModel != NULL, "Error: pDocModel cannot be NULL" );

    __CPROVER_assume( ( err >= DocParseErrUnknown ) && ( err <= DocParseErrInvalidToken ) );
    return err;
}

/* Stub to handle any errors during job parsing. */
void handleJobParsingError( const OtaFileContext_t * pFileContext,
                            OtaJobParseErr_t err )
{
    __CPROVER_assert( pFileContext != NULL,
                      "Invalid pFileContext val: Expected a non-NULL value." );

    __CPROVER_assert( err != OtaJobParseErrNone,
                      "Invalid err val: Expected a value other than OtaJobParseErrNone from OtaJobParseErr_t enum." );
}

/* Stub to validate and start the job. */
OtaJobParseErr_t validateAndStartJob( OtaFileContext_t * pFileContext,
                                      OtaFileContext_t ** pFinalFile,
                                      bool * pUpdateJob )
{
    OtaJobParseErr_t err;

    __CPROVER_assume( ( err >= OtaJobParseErrUnknown ) && ( err <= OtaJobParseErrNoActiveJobs ) );

    /* Preconditions.
     * pFileContext, pFinalFile, pUpdateJob are declared in parseJobDoc before calling
     * validateAndStartJob and thus can never be NULL. */
    __CPROVER_assert( pFileContext != NULL,
                      "Invalid pFileContext val: Expected a non-NULL value." );

    __CPROVER_assert( pFinalFile != NULL,
                      "Invalid pFinalFile val: Expected a non-NULL value." );

    __CPROVER_assert( pFinalFile != NULL,
                      "Invalid pFinalFile val: Expected a non-NULL value." );

    return err;
}

void parseJobDoc_harness()
{
    JsonDocParam_t * pJsonExpectedParams;
    uint16_t numJobParams;
    char * pJson;
    uint32_t messageLength;
    uint32_t pJsonSize;
    bool updateJob;

    /* pJsonExpectedParams is a statically defined structure in ota.c with the maximum size
     * defined by OTA_DOC_MODEL_MAX_PARAMS. */
    __CPROVER_assume( numJobParams <= OTA_DOC_MODEL_MAX_PARAMS + 1 );

    /* pJsonSize is the size of message store inside the pJson buffer. The message length
     * should always be less than the size of the buffer.*/
    __CPROVER_assume( messageLength < pJsonSize );

    pJsonExpectedParams = ( JsonDocParam_t * ) malloc( sizeof( JsonDocParam_t ) * numJobParams );
    pJson = ( char * ) malloc( sizeof( char ) * pJsonSize );

    if( pJson != NULL )
    {
        pJson[ messageLength ] = '\0';
        memset( pJson, 'a', messageLength );
    }

    /* Preconditions. */
    otaAgent.OtaAppCallback = otaAppCallbackStub;

    parseJobDoc( pJsonExpectedParams,
                 numJobParams, pJson, messageLength, &updateJob );

    free( pJsonExpectedParams );
    free( pJson );
}
