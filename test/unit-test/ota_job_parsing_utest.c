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
 * @file ota_jobParsing_utest.c
 * @brief Unit tests for job parsing functions in ota.c
 */

#include <string.h>
#include <stdbool.h>
#include "unity.h"

/* For accessing OTA private functions. */
#include "ota_private.h"
#include "ota.c"
#include "core_json.h"

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

/* OTA interfaces. */
static OtaInterfaces_t otaInterfaces;

/* OTA application buffer. */
static OtaAppBuffer_t otaAppBuffer;
static uint8_t pUserBuffer[ 300 ];

/* ============================   UNITY FIXTURES ============================ */

void setUp( void )
{
    otaAppBuffer.pUpdateFilePath = pUserBuffer;
    otaAppBuffer.updateFilePathsize = 100;
    otaAppBuffer.pCertFilePath = otaAppBuffer.pUpdateFilePath + otaAppBuffer.updateFilePathsize;
    otaAppBuffer.certFilePathSize = 100;
    otaAppBuffer.pStreamName = otaAppBuffer.pCertFilePath + otaAppBuffer.certFilePathSize;
    otaAppBuffer.streamNameSize = 50;

    otaAgent.fileContext.pFilePath = otaAppBuffer.pUpdateFilePath;
    otaAgent.fileContext.filePathMaxSize = otaAppBuffer.updateFilePathsize;
    otaAgent.fileContext.pCertFilepath = otaAppBuffer.pCertFilePath;
    otaAgent.fileContext.certFilePathMaxSize = otaAppBuffer.certFilePathSize;
    otaAgent.fileContext.pStreamName = otaAppBuffer.pStreamName;
    otaAgent.fileContext.streamNameMaxSize = otaAppBuffer.streamNameSize;

    otaInterfaces.os.mem.malloc = malloc;
    otaInterfaces.os.mem.free = free;

    otaAgent.pOtaInterface = &otaInterfaces;
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
