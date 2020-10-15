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
 * @file aws_ota_base64_utest.c
 * @brief Unit tests for functions in aws_ota_base64.c
 */

#include <string.h>
#include <stdbool.h>
#include "unity.h"

/* For accessing OTA private functions. */
#include "aws_iot_ota_agent_private.h"
#include "aws_iot_ota_agent.c"
#include "core_json.h"

/* Error defines based on aws_iot_ota_agent_private.h */
#define DocParseErrUnknown  -1         
#define DocParseErrNone  0
#define DocParseErrOutOfMemory   1         
#define DocParseErrFieldTypeMismatch  2    
#define DocParseErrBase64Decode  3       
#define DocParseErrInvalidNumChar  4       
#define DocParseErrDuplicatesNotAllowed  5   
#define DocParseErrMalformedDoc   6       
#define DocParseErr_InvalidJSONBuffer  7     
#define DocParseErrNullModelPointer  8      
#define DocParseErrNullBodyPointer  9        
#define DocParseErrNullDocPointer   10       
#define DocParseErrTooManyParams   11        
#define DocParseErrParamKeyNotInModel  12    
#define DocParseErrInvalidModelParamType  13 
#define DocParseErrInvalidToken  14

/* Testing Constants. */

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

}

void tearDown( void )
{

}

/* ========================================================================== */

void test_jobParsing_ValidJSON( void )
{
    const char * pcJSON = "{\"clientToken\":\"0:testclient\",\"timestamp\":1602795143,\"execution\":{\"jobId\":\"AFR_OTA-testjob20\",\"status\":\"QUEUED\",\"queuedAt\":1602795128,\"lastUpdatedAt\":1602795128,\"versionNumber\":1,\"executionNumber\":1,\"jobDocument\":{\"afr_ota\":{\"protocols\":[\"MQTT\"],\"streamname\":\"AFR_OTA-6f74f1bd-c23b-4355-a688-9c34daaf9492\",\"files\":[{\"filepath\":\"/home/ubuntu/dev/aws-iot-device-sdk-embedded-C-staging/ota_demo4\",\"filesize\":180568,\"fileid\":0,\"certfile\":\"/home/ubuntu/dev/aws-iot-device-sdk-embedded-C-staging/demos/certificates/ecdsasigner.crt\",\"sig-sha256-ecdsa\":\"MEQCIF2QDvww1G/kpRGZ8FYvQrok1bSZvXjXefRk7sqNcyPTAiB4dvGt8fozIY5NC0vUDJ2MY42ZERYEcrbwA4n6q7vrBg==\"}] }}}}";
    char * query = "clientToken";
    size_t queryKeyLength = strlen(query);
    size_t jsonLength = strlen(pcJSON);
    char * value;
    size_t valueLength;
    bool updateJob;
    JSONStatus_t result;
    OtaFileContext_t * pFileContext = parseJobDoc(pcJSON, jsonLength, &updateJob);

    TEST_ASSERT_NOT_NULL(pFileContext);
}