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
 * @file parseJSONbyModel_harness.c
 * @brief Implements the proof harness for parseJSONbyModel function.
 */
/*  Ota Agent includes. */
#include "ota.h"
#include "core_json.h"

extern OtaAgentContext_t otaAgent;
extern JsonDocParam_t otaJobDocModelParamStructure[ OTA_NUM_JOB_PARAMS ];
extern DocParseErr_t parseJSONbyModel( const char * pJson,
                                       uint32_t messageLength,
                                       JsonDocModel_t * pDocModel );

/* Initialize the src key for JSON files. */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

/* Stub to validate the JSON string. */
DocParseErr_t validateJSON( const char * pJson,
                            uint32_t messageLength )
{
    DocParseErr_t parseErr;

    __CPROVER_assume( ( parseErr >= DocParseErrUnknown ) && ( parseErr <= DocParseErrInvalidToken ) );

    return parseErr;
}

/* Stub to search for constants in a JSON string. */
JSONStatus_t JSON_SearchConst( const char * buf,
                               size_t max,
                               const char * query,
                               size_t queryLength,
                               const char ** outValue,
                               size_t * outValueLength,
                               JSONTypes_t * outType )
{
    JSONStatus_t status;
    size_t value;

    __CPROVER_assume( ( status >= JSONPartial ) && ( status <= JSONBadParameter ) );

    /* valueLength cannot exceed the length of buffer.*/
    __CPROVER_assume( value > 2u && value < OTA_FILE_BLOCK_SIZE );

    *outValueLength = value;
    *outValue = buf;

    return status;
}

/* Stub to extract parameters from a JSON string. */
DocParseErr_t extractParameter( JsonDocParam_t docParam,
                                void * pContextBase,
                                const char * pValueInJson,
                                size_t valueLength )
{
    DocParseErr_t parseErr;

    __CPROVER_assume( ( parseErr >= DocParseErrUnknown ) && ( parseErr <= DocParseErrInvalidToken ) );

    /* pContextBase and pValueInJson are defined in parseJSONbyModel function
     * before calling extractParameter.*/
    __CPROVER_assert( pContextBase != NULL, "Error: Expected a non-NULL pContextBase value. " );
    __CPROVER_assert( pValueInJson != NULL, "Error: Expected a non-NULL pValueInJson value. " );

    return parseErr;
}

/* Stub to Check if all the required parameters for job document are extracted from the JSON. */
DocParseErr_t verifyRequiredParamsExtracted( const JsonDocParam_t * pModelParam,
                                             const JsonDocModel_t * pDocModel )
{
    DocParseErr_t parseErr;

    __CPROVER_assume( ( parseErr >= DocParseErrUnknown ) && ( parseErr <= DocParseErrInvalidToken ) );

    /* pModelParam and pDocModel are defined in parseJSONbyModel function
     * before calling extractParameter.*/
    __CPROVER_assert( pModelParam != NULL, "Error: Expected a non-NULL pContextBase value. " );
    __CPROVER_assert( pDocModel != NULL, "Error: Expected a non-NULL pValueInJson value. " );

    return parseErr;
}

void parseJSONbyModel_harness()
{
    /* pJson is always passed as a global buffer from OtaEventData)t which is
     * enforced in processJobHandler. */
    DocParseErr_t parseErr;
    JsonDocModel_t docModel;
    char pJson[ OTA_DATA_BLOCK_SIZE ];
    uint32_t messageLength;

    /* Preconditions. */
    /* Length of the message cannot exceed the size of the message buffer. */
    __CPROVER_assume( messageLength < OTA_DATA_BLOCK_SIZE );

    /* Initialize the docModel. */
    docModel.pBodyDef = otaJobDocModelParamStructure;
    docModel.numModelParams = OTA_NUM_JOB_PARAMS;
    docModel.contextBase = &( otaAgent.fileContext );
    docModel.contextSize = sizeof( OtaFileContext_t );

    parseErr = parseJSONbyModel( pJson, messageLength, &docModel );

    __CPROVER_assert( ( parseErr >= DocParseErrUnknown ) && ( parseErr <= DocParseErrInvalidToken ),
                      "Error: Expected an return value of DocParseErr_t enum. " );
}
