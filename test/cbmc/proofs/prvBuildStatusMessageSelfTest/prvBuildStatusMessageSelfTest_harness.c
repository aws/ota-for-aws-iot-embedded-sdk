/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file prvBuildStatusMessageSelfTest_harness.c
 * @brief Implements the proof harness for prvBuildStatusMessageSelfTest function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

#define OTA_STATUS_MSG_MAX_SIZE    128U                 /*!< Max length of a job status message to the service. */
#define U32_MAX_LEN                10U                  /*!< Maximum number of output digits of an unsigned long value. */

uint32_t __CPROVER_file_local_ota_mqtt_c_prvBuildStatusMessageSelfTest( char * pMsgBuffer,
                                                                        size_t msgBufferSize,
                                                                        OtaJobStatus_t status,
                                                                        int32_t reason );

/* Stubs required for the test function. */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringSize;

    /* pBuffer is initialized in updateJobStatus_Mqtt function before passing it to the
     * stringBuilder function in prvBuildStatusMessageSelfTest and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized prvBuildStatusMessageSelfTest function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The static size of the pBuffer in the updateJobStatus_Mqtt function is
     * defined by bufferSizeBytes. Hence, the value stringSize can
     * never exceed bufferSizeBytes. */
    __CPROVER_assume( stringSize > 0U && stringSize < bufferSizeBytes );

    return stringSize;
}

size_t __CPROVER_file_local_ota_mqtt_c_stringBuilderUInt32Hex( char * pBuffer,
                                                               size_t bufferSizeBytes,
                                                               uint32_t value )
{
    size_t buffersize;

    return buffersize;
}

/*****************************************************************************/

void prvBuildStatusMessageSelfTest_harness()
{
    size_t msgBufferSize;
    OtaJobStatus_t status;
    int32_t reason;

    /* The pMsg if statically defined in the updateJobStatus_Mqtt with its size
     * defined by OTA_STATUS_MSG_MAX_SIZE.*/
    char pMsg[ OTA_STATUS_MSG_MAX_SIZE ];

    msgBufferSize = OTA_STATUS_MSG_MAX_SIZE;

    /* The prvBuildStatusMessageSelfTest function is only called when status
     * is JobStatusInProgress. */
    __CPROVER_assume( status == JobStatusInProgress );

    /* Since reason is of OtaJobReason_t datatype it follows the values ranging from 0 to 6.*/
    __CPROVER_assume( reason >= 0 && reason < 6 );

    ( void ) __CPROVER_file_local_ota_mqtt_c_prvBuildStatusMessageSelfTest( pMsg,
                                                                            msgBufferSize, status, reason );
}
