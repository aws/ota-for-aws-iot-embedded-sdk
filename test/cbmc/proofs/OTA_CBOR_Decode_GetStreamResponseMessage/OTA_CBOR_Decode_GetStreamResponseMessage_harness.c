/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file OTA_CBOR_Decode_GetStreamResponseMessage_harness.c
 * @brief Implements the proof harness for OTA_CBOR_Decode_GetStreamResponseMessage function.
 */
/* Include headers for cbor parsing. */
#include "cbor.h"
#include "ota_cbor_private.h"

CborError cbor_value_map_find_value( const CborValue * map,
                                     const char * string,
                                     CborValue * element )
{
    CborError err;

    return err;
}

CborError __CPROVER_file_local_ota_cbor_c_checkDataType( CborType expectedType,
                                                         CborValue * cborValue )
{
    CborError err;

    return err;
}

CborError __CPROVER_file_local_cbor_h_cbor_value_get_int( const CborValue * value,
                                                          int * result )
{
    CborError err;

    return err;
}

CborError cbor_value_calculate_string_length( const CborValue * value,
                                              size_t * len )
{
    CborError err;

    size_t stringSize;
    *len = stringSize;

    return err;
}

CborError __CPROVER_file_local_cbor_h_cbor_value_copy_byte_string( const CborValue * value,
                                                                   uint8_t * buffer,
                                                                   size_t * buflen,
                                                                   CborValue * next )
{
    CborError err;

    return err;
}

void OTA_CBOR_Decode_GetStreamResponseMessage_harness()
{
    uint8_t * pMessageBuffer;
    size_t messageSize;
    int32_t * pFileId;
    int32_t * pBlockId;
    int32_t * pBlockSize;
    uint8_t ** pPayload;
    size_t * pPayloadSize;

    /* Allocating memory to the variables. Since malloc can fail this also covers cases where
     * the variables are pointing at NULL. */
    pMessageBuffer = ( uint8_t * ) malloc( messageSize );
    pFileId = ( int32_t * ) malloc( sizeof( uint32_t ) );
    pBlockId = ( int32_t * ) malloc( sizeof( uint32_t ) );
    pBlockSize = ( int32_t * ) malloc( sizeof( int32_t ) );
    pPayloadSize = ( size_t * ) malloc( sizeof( size_t ) );
    pPayload = ( uint8_t ** ) malloc( sizeof( uint8_t * ) );

    if( pPayload != NULL )
    {
        *pPayload = ( uint8_t * ) malloc( sizeof( uint8_t ) );
    }

    OTA_CBOR_Decode_GetStreamResponseMessage( pMessageBuffer, messageSize, pFileId, pBlockId, pBlockSize, pPayload, pPayloadSize );
}
