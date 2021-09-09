/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file decodeFileBlock_Mqtt_harness.c
 * @brief Implements the proof harness for decodeFileBlock_Mqtt function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

bool OTA_CBOR_Decode_GetStreamResponseMessage( const uint8_t * pMessageBuffer,
                                               size_t messageSize,
                                               int32_t * pFileId,
                                               int32_t * pBlockId,
                                               int32_t * pBlockSize,
                                               uint8_t ** pPayload,
                                               size_t * pPayloadSize )
{
    bool status;

    /* If any of the arguments to the function are not initialized
     * correctly then the functions should return FALSE. */
    if( ( pFileId == NULL ) ||
        ( pBlockId == NULL ) ||
        ( pBlockSize == NULL ) ||
        ( pPayload == NULL ) ||
        ( pPayloadSize == NULL ) ||
        ( pMessageBuffer == NULL ) )
    {
        status = false;
    }

    return status;
}

void decodeFileBlock_Mqtt_harness()
{
    uint8_t * pMessageBuffer;
    size_t messageSize;
    int32_t * pFileId;
    int32_t * pBlockId;
    int32_t * pBlockSize;
    uint8_t ** pPayload;
    size_t * pPayloadSize;

    decodeFileBlock_Mqtt( pMessageBuffer,
                          messageSize,
                          pFileId,
                          pBlockId,
                          pBlockSize,
                          pPayload,
                          pPayloadSize );
}
