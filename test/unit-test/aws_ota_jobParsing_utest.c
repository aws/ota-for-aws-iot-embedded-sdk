/*
 * FreeRTOS OTA V1.2.0
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
 * @file aws_ota_jobParsing_utest.c
 * @brief Unit tests for job parsing functions in aws_iot_ota_agent.c
 */

#include <string.h>
#include <stdbool.h>
#include "unity.h"

/* For accessing OTA private functions. */
#include "aws_iot_ota_agent_private.h"
#include "aws_iot_ota_agent.c"
#include "core_json.h"

/* Error defines based on aws_iot_ota_agent_private.h */
#define DocParseErrUnknown                  -1
#define DocParseErrNone                     0
#define DocParseErrOutOfMemory              1
#define DocParseErrFieldTypeMismatch        2
#define DocParseErrBase64Decode             3
#define DocParseErrInvalidNumChar           4
#define DocParseErrDuplicatesNotAllowed     5
#define DocParseErrMalformedDoc             6
#define DocParseErr_InvalidJSONBuffer       7
#define DocParseErrNullModelPointer         8
#define DocParseErrNullBodyPointer          9
#define DocParseErrNullDocPointer           10
#define DocParseErrTooManyParams            11
#define DocParseErrParamKeyNotInModel       12
#define DocParseErrInvalidModelParamType    13
#define DocParseErrInvalidToken             14

/* Testing Constants. */

#define JOB_PARSING_VALID_JSON                               "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":180568,\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_PARSING_VALID_JSON_LENGTH                        ( strlen( JOB_PARSING_VALID_JSON ) )

/* JSON document with an invalid structure. */
#define JOB_PARSING_MALFORMED_JSON                           "{\"clientToken\":0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":180568,\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_PARSING_MALFORMED_JSON_LENGTH                    ( strlen( JOB_PARSING_VALID_JSON ) )

/* Removed the required parameter 'filepath'. */
#define JOB_PARSING_INVALID_JSON_MISSING_FILEPATH            "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filesize\":180568,\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_PARSING_INVALID_JSON_MISSING_FILEPATH_LENGTH     ( strlen( JOB_PARSING_INVALID_JSON_MISSING_FILEPATH ) )

/* Replaced numeric value of 'fileid' with string. */
#define JOB_PARSING_INVALID_JSON_INVALID_NUMERIC             "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":180568,\"fileid\":\"text\",\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}"
#define JOB_PARSING_INVALID_JSON_INVALID_NUMERIC_LENGTH      ( strlen( JOB_PARSING_INVALID_JSON_INVALID_NUMERIC ) )

/* Invalid base64 signature key with 3 padding symbols */
#define JOB_PARSING_INVALID_JSON_INVALID_BASE64KEY           "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-XYZ\",\"files\":[{\"filepath\":\"/test/demo\",\"filesize\":180568,\"fileid\":0,\"certfile\":\"test.crt\",\"sig-sha256-ecdsa\":\"Rk9PQkFS===\"}] }}}}"
#define JOB_PARSING_INVALID_JSON_INVALID_BASE64KEY_LENGTH    ( strlen( JOB_PARSING_INVALID_JSON_INVALID_BASE64KEY ) )

/* Firmware version. */
const AppVersion32_t appFirmwareVersion =
{
    .u.x.major = 1,
    .u.x.minor = 0,
    .u.x.build = 0,
};

/* OTA code signing signature algorithm. */
const char OTA_JsonFileSignatureKey[ OTA_FILE_SIG_KEY_STR_MAX_LENGTH ] = "sig-sha256-ecdsa";

/* ============================   UNITY FIXTURES ============================ */

void setUp( void )
{
    static const JsonDocParam_t otaJobDocModelParamStructure[ OTA_NUM_JOB_PARAMS ] =
    {
        { OTA_JSON_CLIENT_TOKEN_KEY,    OTA_JOB_PARAM_OPTIONAL, { OTA_DONT_STORE_PARAM  }, ModelParamTypeStringInDoc },                         /*lint !e9078 !e923 Get address of token as value. */
        { OTA_JSON_TIMESTAMP_KEY,       OTA_JOB_PARAM_OPTIONAL, { OTA_DONT_STORE_PARAM  }, ModelParamTypeUInt32      },
        { OTA_JSON_EXECUTION_KEY,       OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM  }, ModelParamTypeObject      },
        { OTA_JSON_JOB_ID_KEY,          OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pJobName )}, ModelParamTypeStringCopy  },
        { OTA_JSON_STATUS_DETAILS_KEY,  OTA_JOB_PARAM_OPTIONAL, { OTA_DONT_STORE_PARAM  }, ModelParamTypeObject      },
        { OTA_JSON_SELF_TEST_KEY,       OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, isInSelfTest )}, ModelParamTypeIdent       },
        { OTA_JSON_UPDATED_BY_KEY,      OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, updaterVersion )}, ModelParamTypeUInt32      },
        { OTA_JSON_JOB_DOC_KEY,         OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM  }, ModelParamTypeObject      },
        { OTA_JSON_OTA_UNIT_KEY,        OTA_JOB_PARAM_REQUIRED, { OTA_DONT_STORE_PARAM  }, ModelParamTypeObject      },
        { OTA_JSON_STREAM_NAME_KEY,     OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, pStreamName )}, ModelParamTypeStringCopy  },
        { OTA_JSON_PROTOCOLS_KEY,       OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pProtocols )}, ModelParamTypeArrayCopy   },
        { OTA_JSON_FILE_GROUP_KEY,      OTA_JOB_PARAM_REQUIRED, { OTA_STORE_NESTED_JSON }, ModelParamTypeArray       },
        { OTA_JSON_FILE_PATH_KEY,       OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pFilePath )}, ModelParamTypeStringCopy  },
        { OTA_JSON_FILE_SIZE_KEY,       OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, fileSize )}, ModelParamTypeUInt32      },
        { OTA_JSON_FILE_ID_KEY,         OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, serverFileID )}, ModelParamTypeUInt32      },
        { OTA_JSON_FILE_CERT_NAME_KEY,  OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pCertFilepath )}, ModelParamTypeStringCopy  },
        { OTA_JSON_UPDATE_DATA_URL_KEY, OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, pUpdateUrlPath )}, ModelParamTypeStringCopy  },
        { OTA_JSON_AUTH_SCHEME_KEY,     OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, pAuthScheme )}, ModelParamTypeStringCopy  },
        { OTA_JsonFileSignatureKey,     OTA_JOB_PARAM_REQUIRED, { offsetof( OtaFileContext_t, pSignature )}, ModelParamTypeSigBase64   },
        { OTA_JSON_FILE_ATTRIBUTE_KEY,  OTA_JOB_PARAM_OPTIONAL, { offsetof( OtaFileContext_t, fileAttributes )}, ModelParamTypeUInt32      },
    };
}

void tearDown( void )
{
}

/* ========================================================================== */

/**
 * @brief Test that parseJobDoc is able to generate a FileContext by processing a valid JSON document.
 */
void test_OTA_JobParsing_Valid_Parse_Job_Doc( void )
{
    bool updateJob;
    JSONStatus_t result;
    OtaFileContext_t * pFileContext = parseJobDoc( JOB_PARSING_VALID_JSON, JOB_PARSING_VALID_JSON_LENGTH, &updateJob );

    TEST_ASSERT_NOT_NULL( pFileContext );
}

/**
 * @brief Test that parseJSONbyModel is able to process a valid JSON document correctly.
 */
void test_OTA_JobParsing_Valid_JSON( void )
{
    static OtaFileContext_t fileContext = { 0 };
    OtaJobParseErr_t err = OtaJobParseErrUnknown;
    OtaFileContext_t * pFileContext = &fileContext;
    JsonDocModel_t otaJobDocModel;

    err = initDocModel( &otaJobDocModel,
                        otaJobDocModelParamStructure,
                        ( void * ) pFileContext, /*lint !e9078 !e923 Intentionally casting context pointer to a value for initDocModel. */
                        sizeof( OtaFileContext_t ),
                        OTA_NUM_JOB_PARAMS );
    err = parseJSONbyModel( JOB_PARSING_VALID_JSON, JOB_PARSING_VALID_JSON_LENGTH, &otaJobDocModel );

    TEST_ASSERT_EQUAL( DocParseErrNone, err );
}

/**
 * @brief Test that parseJSONbyModel is able to classify an invalid JSON document correctly.
 */
void test_OTA_JobParsing_Invalid_JSON( void )
{
    static OtaFileContext_t fileContext = { 0 };
    OtaJobParseErr_t err = OtaJobParseErrUnknown;
    OtaFileContext_t * pFileContext = &fileContext;
    JsonDocModel_t otaJobDocModel;
    JsonDocModel_t otaJobDocModelCopy;

    err = initDocModel( &otaJobDocModel,
                        otaJobDocModelParamStructure,
                        ( void * ) pFileContext, /*lint !e9078 !e923 Intentionally casting context pointer to a value for initDocModel. */
                        sizeof( OtaFileContext_t ),
                        OTA_NUM_JOB_PARAMS );

    err = parseJSONbyModel( JOB_PARSING_MALFORMED_JSON, JOB_PARSING_MALFORMED_JSON_LENGTH, &otaJobDocModel );
    TEST_ASSERT_EQUAL( DocParseErr_InvalidJSONBuffer, err );

    err = parseJSONbyModel( NULL, 0, &otaJobDocModel );
    TEST_ASSERT_EQUAL( DocParseErrNullDocPointer, err );

    memcpy( &otaJobDocModelCopy, &otaJobDocModel, sizeof( JsonDocModel_t ) );
    err = parseJSONbyModel( JOB_PARSING_INVALID_JSON_MISSING_FILEPATH, JOB_PARSING_INVALID_JSON_MISSING_FILEPATH_LENGTH, &otaJobDocModelCopy );
    TEST_ASSERT_EQUAL( DocParseErrMalformedDoc, err );

    memcpy( &otaJobDocModelCopy, &otaJobDocModel, sizeof( JsonDocModel_t ) );
    err = parseJSONbyModel( JOB_PARSING_INVALID_JSON_INVALID_BASE64KEY, JOB_PARSING_INVALID_JSON_INVALID_BASE64KEY_LENGTH, &otaJobDocModelCopy );
    TEST_ASSERT_EQUAL( DocParseErrBase64Decode, err );

    memcpy( &otaJobDocModelCopy, &otaJobDocModel, sizeof( JsonDocModel_t ) );
    err = parseJSONbyModel( JOB_PARSING_INVALID_JSON_INVALID_NUMERIC, JOB_PARSING_INVALID_JSON_INVALID_NUMERIC_LENGTH, &otaJobDocModelCopy );
    TEST_ASSERT_EQUAL( DocParseErrInvalidNumChar, err );
}

/**
 * @brief Tests that initDocModel detects malformed document specifications.
 */
void test_OTA_jobParsing_invalidDocModel( void )
{
    static OtaFileContext_t fileContext = { 0 };
    OtaJobParseErr_t err = OtaJobParseErrUnknown;
    OtaFileContext_t * pFileContext = &fileContext;
    JsonDocModel_t otaJobDocModel;

    /* Test for invalid json document model. */
    err = initDocModel( NULL,
                        otaJobDocModelParamStructure,
                        ( void * ) pFileContext, /*lint !e9078 !e923 Intentionally casting context pointer to a value for initDocModel. */
                        sizeof( OtaFileContext_t ),
                        OTA_NUM_JOB_PARAMS );
    TEST_ASSERT_EQUAL( DocParseErrNullModelPointer, err );

    /*Test for invalid job document parameters. */
    err = initDocModel( &otaJobDocModel,
                        NULL,
                        ( void * ) pFileContext, /*lint !e9078 !e923 Intentionally casting context pointer to a value for initDocModel. */
                        sizeof( OtaFileContext_t ),
                        OTA_NUM_JOB_PARAMS );
    TEST_ASSERT_EQUAL( DocParseErrNullBodyPointer, err );

    /*Test when the document has more parameters than expected */
    err = initDocModel( &otaJobDocModel,
                        otaJobDocModelParamStructure,
                        ( void * ) pFileContext, /*lint !e9078 !e923 Intentionally casting context pointer to a value for initDocModel. */
                        sizeof( OtaFileContext_t ),
                        OTA_DOC_MODEL_MAX_PARAMS + 1 );
    TEST_ASSERT_EQUAL( DocParseErrTooManyParams, err );
}
