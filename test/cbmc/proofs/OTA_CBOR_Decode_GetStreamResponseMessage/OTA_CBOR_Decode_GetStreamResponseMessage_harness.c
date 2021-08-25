/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */
/**
 * @file OTA_CBOR_Decode_GetStreamResponseMessage_harness.c
 * @brief Implements the proof harness for OTA_CBOR_Decode_GetStreamResponseMessage function.
 */
/* Include headers for cbor parsing. */
#include "cbor.h"
#include "ota_cbor_private.h"

CborError cbor_parser_init( const uint8_t * buffer,
                            size_t size,
                            uint32_t flags,
                            CborParser * parser,
                            CborValue * it )
{
    CborError err;
    return err;
}          

bool __CPROVER_file_local_cbor_h_cbor_value_is_map( const CborValue * value )
{
    return value->type == CborMapType;
}          

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

    OTA_CBOR_Decode_GetStreamResponseMessage(pMessageBuffer,messageSize, pFileId, pBlockId, pBlockSize, pPayload, pPayloadSize );
}
