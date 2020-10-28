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


/* Standard library include. */
#include <stdbool.h>
#include <string.h>
#include <stdio.h>

/* OTA includes. */
#include "aws_iot_ota_agent.h"
#include "aws_iot_ota_agent_private.h"
#include "aws_iot_ota_http_private.h"



/* Jump to cleanup section. */
#define OTA_GOTO_CLEANUP()              IOT_GOTO_CLEANUP()

/* Start of the cleanup section. */
#define OTA_FUNCTION_CLEANUP_BEGIN()    IOT_FUNCTION_CLEANUP_BEGIN()

/* End of the cleanup section. */
#define OTA_FUNCTION_CLEANUP_END()

/* Empty cleanup section. */
#define OTA_FUNCTION_NO_CLEANUP()    OTA_FUNCTION_CLEANUP_BEGIN(); OTA_FUNCTION_CLEANUP_END()

/* Maximum OTA file size string in byte. The OTA service current limits the file size to 16 MB.*/
#define OTA_MAX_FILE_SIZE_STR        "16777216"

/* String length of the maximum OTA file size string, not including the null character. */
#define OTA_MAX_FILE_SIZE_STR_LEN    ( sizeof( OTA_MAX_FILE_SIZE_STR ) - 1 )

/* TLS port for HTTPS. */
#define HTTPS_PORT                   ( ( uint16_t ) 443 )

/* Baltimore Cybertrust associated with the S3 server certificate. */
#define HTTPS_TRUSTED_ROOT_CA                                            \
    "-----BEGIN CERTIFICATE-----\n"                                      \
    "MIIDdzCCAl+gAwIBAgIEAgAAuTANBgkqhkiG9w0BAQUFADBaMQswCQYDVQQGEwJJ\n" \
    "RTESMBAGA1UEChMJQmFsdGltb3JlMRMwEQYDVQQLEwpDeWJlclRydXN0MSIwIAYD\n" \
    "VQQDExlCYWx0aW1vcmUgQ3liZXJUcnVzdCBSb290MB4XDTAwMDUxMjE4NDYwMFoX\n" \
    "DTI1MDUxMjIzNTkwMFowWjELMAkGA1UEBhMCSUUxEjAQBgNVBAoTCUJhbHRpbW9y\n" \
    "ZTETMBEGA1UECxMKQ3liZXJUcnVzdDEiMCAGA1UEAxMZQmFsdGltb3JlIEN5YmVy\n" \
    "VHJ1c3QgUm9vdDCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBAKMEuyKr\n" \
    "mD1X6CZymrV51Cni4eiVgLGw41uOKymaZN+hXe2wCQVt2yguzmKiYv60iNoS6zjr\n" \
    "IZ3AQSsBUnuId9Mcj8e6uYi1agnnc+gRQKfRzMpijS3ljwumUNKoUMMo6vWrJYeK\n" \
    "mpYcqWe4PwzV9/lSEy/CG9VwcPCPwBLKBsua4dnKM3p31vjsufFoREJIE9LAwqSu\n" \
    "XmD+tqYF/LTdB1kC1FkYmGP1pWPgkAx9XbIGevOF6uvUA65ehD5f/xXtabz5OTZy\n" \
    "dc93Uk3zyZAsuT3lySNTPx8kmCFcB5kpvcY67Oduhjprl3RjM71oGDHweI12v/ye\n" \
    "jl0qhqdNkNwnGjkCAwEAAaNFMEMwHQYDVR0OBBYEFOWdWTCCR1jMrPoIVDaGezq1\n" \
    "BE3wMBIGA1UdEwEB/wQIMAYBAf8CAQMwDgYDVR0PAQH/BAQDAgEGMA0GCSqGSIb3\n" \
    "DQEBBQUAA4IBAQCFDF2O5G9RaEIFoN27TyclhAO992T9Ldcw46QQF+vaKSm2eT92\n" \
    "9hkTI7gQCvlYpNRhcL0EYWoSihfVCr3FvDB81ukMJY2GQE/szKN+OMY3EU/t3Wgx\n" \
    "jkzSswF07r51XgdIGn9w/xZchMB5hbgF/X++ZRGjD8ACtPhSNzkE1akxehi/oCr0\n" \
    "Epn3o0WC4zxe9Z2etciefC7IpJ5OCBRLbf1wbWsaY71k5h+3zvDyny67G7fyUIhz\n" \
    "ksLi4xaNmjICq44Y3ekQEe5+NauQrz4wlHrQMz2nZQ/1/I6eYs9HRCwBXbsdtTLS\n" \
    "R9I4LtD+gdwyah617jzV/OeBHRnDJELqYzmp\n"                             \
    "-----END CERTIFICATE-----\n"

/* Buffer size for HTTP connection context. This is the minimum size from HTTP library, we cannot
 * use it directly because it's only available at runtime. */
#define HTTPS_CONNECTION_USER_BUFFER_SIZE       256

/* Buffer size for HTTP request context and header.*/
#define HTTPS_REQUEST_USER_BUFFER_SIZE          2048

/* Buffer size for HTTP response context and header.*/
#define HTTPS_RESPONSE_USER_BUFFER_SIZE         1024

/* Buffer size for HTTP response body.*/
#define HTTPS_RESPONSE_BODY_BUFFER_SIZE         OTA_FILE_BLOCK_SIZE

/* Default timeout for HTTP synchronous request. */
#define HTTP_SYNC_TIMEOUT                       3000

/**
 * The maximum length of the "Range" field in HTTP header.
 *
 * The maximum file size of OTA download is OTA_MAX_FILE_SIZE_STR bytes. The header value string is
 * of the form: "bytes=N-M". So the length is len("bytes=-") + len(N) + len(M) + the NULL terminator.
 * The maximum length is 7 + OTA_MAX_FILE_SIZE_STR_LEN * 2 + 1.
 */
#define HTTP_HEADER_RANGE_VALUE_MAX_LEN         ( 7 + ( OTA_MAX_FILE_SIZE_STR_LEN ) * 2 + 1 )

/**
 * The maximum length of the "Connection" field in HTTP header.
 *
 * The value could be "close" or "keep-alive", so the maximum length is sizeof("keep-alive"), this
 * includes the NULL terminator.
 */
#define HTTP_HEADER_CONNECTION_VALUE_MAX_LEN    ( sizeof( "keep-alive" ) )

/* Struct for HTTP callback data. */
typedef struct _httpCallbackData
{
    char pRangeValueStr[ HTTP_HEADER_RANGE_VALUE_MAX_LEN ]; /* Buffer to write the HTTP "range" header value string. */
} _httpCallbackData_t;



/* Struct to keep track of the internal HTTP downloader state. */
typedef enum
{
    OTA_HTTP_ERR_NONE = 0,
    OTA_HTTP_ERR_GENERIC = 101,
    OTA_HTTP_ERR_CANCELED = 102,
    OTA_HTTP_ERR_NEED_RECONNECT = 103,
    OTA_HTTP_ERR_URL_EXPIRED = 104
} _httpErr;

typedef enum
{
    OTA_HTTP_IDLE = 0,
    OTA_HTTP_SENDING_REQUEST,
    OTA_HTTP_WAITING_RESPONSE,
    OTA_HTTP_PROCESSING_RESPONSE
} _httpState;

/* Buffers for HTTP library. */
uint8_t * pConnectionUserBuffer = NULL; /* Buffer to store the HTTP connection context. */
uint8_t * pRequestUserBuffer = NULL;    /* Buffer to store the HTTP request context and header. */
uint8_t * pResponseUserBuffer = NULL;   /* Buffer to store the HTTP response context and header. */
uint8_t * pResponseBodyBuffer = NULL;   /* Buffer to store the HTTP response body. */

/* We need to use this function defined in iot_logging_task_dynamic_buffers.c to print HTTP message
 * without appending the task name and tick count. */
void vLoggingPrint( const char * pcMessage );

/*-----------------------------------------------------------*/

OtaErr_t _AwsIotOTA_InitFileTransfer_HTTP( OtaAgentContext_t * pAgentCtx )
{
    OTA_LOG_L1( "Invoking _AwsIotOTA_InitFileTransfer_HTTP" );

    /* Return status. */
    OtaErr_t status = OTA_ERR_NONE;

    /* Pre-signed URL. */
    const char * pURL = NULL;

    /* File context from OTA agent. */
    OtaFileContext_t * fileContext = &( pAgentCtx->pOtaFiles[ pAgentCtx->fileIndex ] );

    /* Get pre-signed URL from pAgentCtx. */
    pURL = ( const char * ) ( fileContext->pUpdateUrlPath );
    OTA_LOG_L1( "Pre-signed URL size: %d.", strlen( pURL ) );

    /* Connect to the HTTP server and initialize download information. */
    pAgentCtx->pOTAHttpInterface->init( pURL );

    return OTA_ERR_NONE;
}
uint32_t currBlock;
OtaErr_t _AwsIotOTA_RequestDataBlock_HTTP( OtaAgentContext_t * pAgentCtx )
{
    OTA_LOG_L1( "Invoking _AwsIotOTA_RequestDataBlock_HTTP" );

    /* Return status. */
    OtaErr_t status = OTA_ERR_NONE;

    /* Values for the "Range" field in HTTP header. */
    uint32_t rangeStart = 0;
    uint32_t rangeEnd = 0;

    /* File context from OTA agent. */
    OtaFileContext_t * fileContext = &( pAgentCtx->pOtaFiles[ pAgentCtx->fileIndex ] );

    /* Calculate ranges. */
    rangeStart = currBlock * OTA_FILE_BLOCK_SIZE;

    if( fileContext->blocksRemaining == 1 )
    {
        rangeEnd = fileContext->fileSize - 1;
    }
    else
    {
        rangeEnd = rangeStart + OTA_FILE_BLOCK_SIZE - 1;
    }

    pAgentCtx->pOTAHttpInterface->request( rangeStart, rangeEnd );

    return status;
}

OtaErr_t _AwsIotOTA_DecodeFileBlock_HTTP( uint8_t * pMessageBuffer,
                                          size_t messageSize,
                                          int32_t * pFileId,
                                          int32_t * pBlockId,
                                          int32_t * pBlockSize,
                                          uint8_t ** pPayload,
                                          size_t * pPayloadSize )
{
    /* Unused parameters. */
    ( void ) messageSize;

    *pPayload = pMessageBuffer;
    *pFileId = 0;
    *pBlockId = currBlock;
    *pBlockSize = messageSize;
    *pPayloadSize = messageSize;

    /* Current block is processed, set the file block to next one and the state to idle. */
    currBlock += 1;

    return OTA_ERR_NONE;
}


OtaErr_t _AwsIotOTA_CleanupData_HTTP( OtaAgentContext_t * pAgentCtx )
{
    /* Unused parameters. */
    ( void ) pAgentCtx;


    return OTA_ERR_NONE;
}
