/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file buildStatusMessageReceiving_harness.c
 * @brief Implements the proof harness for buildStatusMessageReceiving function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

#define OTA_STATUS_MSG_MAX_SIZE    128U                 /*!< Max length of a job status message to the service. */
#define U32_MAX_LEN                10U                  /*!< Maximum number of output digits of an unsigned long value. */

/* Declaration of the test function with the mangled name. */
uint32_t __CPROVER_file_local_ota_mqtt_c_buildStatusMessageReceiving( char * pMsgBuffer,
                                                                      size_t msgBufferSize,
                                                                      OtaJobStatus_t status,
                                                                      const OtaFileContext_t * pOTAFileCtx );

/* Stubs required for the test function. */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringSize;

    /* pBuffer is initialized in updateJobStatus_Mqtt function before passing it to the
    * stringBuilder function in buildStatusMessageReceiving and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized buildStatusMessageReceiving function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The static size of the pBuffer in the updateJobStatus_Mqtt function is
     * defined by bufferSizeBytes. Hence, the value stringSize can
     * never exceed bufferSizeBytes. */
    __CPROVER_assume( stringSize > 0 && stringSize < bufferSizeBytes );

    return stringSize;
}

size_t __CPROVER_file_local_ota_mqtt_c_stringBuilderUInt32Decimal( char * pBuffer,
                                                                   size_t bufferSizeBytes,
                                                                   uint32_t value )
{
    size_t stringSize;

    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    __CPROVER_assume( stringSize > 0 && stringSize <= U32_MAX_LEN + 1 );

    return stringSize;
}
/*****************************************************************************/

void buildStatusMessageReceiving_harness()
{
    char pMsg[ OTA_STATUS_MSG_MAX_SIZE ];
    size_t msgBufferSize;
    OtaJobStatus_t status;
    OtaFileContext_t pOTAfileCtx;

    /* buildStatusMessageReceiving function is always called with msgBufferSize equal to
     * OTA_STATUS_MSG_MAX_SIZE. */
    msgBufferSize = OTA_STATUS_MSG_MAX_SIZE;

    /* The buildStatusMessageReceiving function is only called when status is JobStatusInProgress. */
    __CPROVER_assume( status == JobStatusInProgress );

    /* The maximum size of the firmware image should be less than 1 >> OTA_FILE_BLOCK_SIZE. */
    __CPROVER_assume( pOTAfileCtx.fileSize < UINT32_MAX - ( OTA_FILE_BLOCK_SIZE - 1U ) );

    /* The blocksRemaining field in the pOTAfileCtx has a upper bound calculated. */
    __CPROVER_assume( pOTAfileCtx.blocksRemaining <= ( ( pOTAfileCtx.fileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) )
                                                       >> otaconfigLOG2_FILE_BLOCK_SIZE ) );

    ( void ) __CPROVER_file_local_ota_mqtt_c_buildStatusMessageReceiving( pMsg, msgBufferSize, status, &pOTAfileCtx );
}