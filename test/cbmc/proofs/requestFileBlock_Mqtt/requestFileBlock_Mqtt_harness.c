/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */
/**
 * @file requestFileBlock_Mqtt_harness.c
 * @brief Implements the proof harness for requestFileBlock_Mqtt function.
 */
/* Include headers for mqtt interface.*/
#include "ota_mqtt_private.h"

size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringSize;

    /* pBuffer is initialized in updateJobStatus_Mqtt function before passing it to the
    * stringBuilder function in prvBuildStatusMessageFinish and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized prvBuildStatusMessageFinish function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The static size of the pBuffer in the updateJobStatus_Mqtt function is
     * defined by bufferSizeBytes. Hence, the value stringSize can
     * never exceed bufferSizeBytes. */
    __CPROVER_assume( stringSize > 0U && stringSize < bufferSizeBytes );

    return stringSize;
}

bool OTA_CBOR_Encode_GetStreamRequestMessage( uint8_t * pMessageBuffer,
                                              size_t messageBufferSize,
                                              size_t * pEncodedMessageSize,
                                              const char * pClientToken,
                                              int32_t fileId,
                                              int32_t blockSize,
                                              int32_t blockOffset,
                                              uint8_t * pBlockBitmap,
                                              size_t blockBitmapSize,
                                              int32_t numOfBlocksRequested )
{
    bool cborEncodeRet;

    return cborEncodeRet;
}         

void requestFileBlock_Mqtt_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaAgentContext_t agent;

    /* OTA agent is defined as a global variable in ota.c and thus cannot be NULL.*/
    pAgentCtx = &agent;

    requestFileBlock_Mqtt ( pAgentCtx );
}
