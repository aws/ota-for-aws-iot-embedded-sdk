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
 * @file ota_cbor.c
 * @brief CBOR encode/decode routines for AWS IoT Over-the-Air updates.
 */

#include <stdlib.h>
#include "cbor.h"
#include "ota_cbor_private.h"

/**
 * @brief Message field definitions, per the server specification.
 */

#define OTA_CBOR_GETSTREAMREQUEST_ITEM_COUNT    6


/**
 * @brief Decode a Get Stream response message from AWS IoT OTA.
 */
bool OTA_CBOR_Decode_GetStreamResponseMessage( const uint8_t * pMessageBuffer,
                                               size_t messageSize,
                                               int32_t * pFileId,
                                               int32_t * pBlockId,
                                               int32_t * pBlockSize,
                                               uint8_t ** pPayload,
                                               size_t * pPayloadSize )
{
    CborError cborResult = CborNoError;
    CborParser cborParser;
    CborValue cborValue, cborMap;

    /* Initialize the parser. */
    cborResult = cbor_parser_init( pMessageBuffer,
                                   messageSize,
                                   0,
                                   &cborParser,
                                   &cborMap );

    /* Get the outer element and confirm that it's a "map," i.e., a set of
     * CBOR key/value pairs. */
    if( CborNoError == cborResult )
    {
        if( false == cbor_value_is_map( &cborMap ) )
        {
            cborResult = CborErrorIllegalType;
        }
    }

    /* Find the file ID. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_FILEID_KEY,
                                                &cborValue );
    }

    if( CborNoError == cborResult )
    {
        if( CborIntegerType != cbor_value_get_type( &cborValue ) )
        {
            cborResult = CborErrorIllegalType;
        }
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_get_int( &cborValue,
                                         pFileId );
    }

    /* Find the block ID. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_BLOCKID_KEY,
                                                &cborValue );
    }

    if( CborNoError == cborResult )
    {
        if( CborIntegerType != cbor_value_get_type( &cborValue ) )
        {
            cborResult = CborErrorIllegalType;
        }
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_get_int( &cborValue,
                                         pBlockId );
    }

    /* Find the block size. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_BLOCKSIZE_KEY,
                                                &cborValue );
    }

    if( CborNoError == cborResult )
    {
        if( CborIntegerType != cbor_value_get_type( &cborValue ) )
        {
            cborResult = CborErrorIllegalType;
        }
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_get_int( &cborValue,
                                         pBlockSize );
    }

    /* Find the payload bytes. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_map_find_value( &cborMap,
                                                OTA_CBOR_BLOCKPAYLOAD_KEY,
                                                &cborValue );
    }

    if( CborNoError == cborResult )
    {
        if( CborByteStringType != cbor_value_get_type( &cborValue ) )
        {
            cborResult = CborErrorIllegalType;
        }
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_calculate_string_length( &cborValue,
                                                         pPayloadSize );
    }

    if( CborNoError == cborResult )
    {
        *pPayload = malloc( *pPayloadSize );

        if( NULL == *pPayload )
        {
            cborResult = CborErrorOutOfMemory;
        }
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_value_copy_byte_string( &cborValue,
                                                  *pPayload,
                                                  pPayloadSize,
                                                  NULL );
    }

    return CborNoError == cborResult;
}



/**
 * @brief Create an encoded Get Stream Request message for the AWS IoT OTA
 * service. The service allows block count or block bitmap to be requested,
 * but not both.
 */
bool OTA_CBOR_Encode_GetStreamRequestMessage( uint8_t * pMessageBuffer,
                                              size_t messageBufferSize,
                                              size_t * pEncodedMessageSize,
                                              const char * pClientToken,
                                              int32_t fileId,
                                              int32_t blockSize,
                                              int32_t blockOffset,
                                              const uint8_t * pBlockBitmap,
                                              size_t blockBitmapSize,
                                              int32_t numOfBlocksRequested )
{
    CborError cborResult = CborNoError;
    CborEncoder cborEncoder, cborMapEncoder;

    /* Initialize the CBOR encoder. */
    cbor_encoder_init( &cborEncoder,
                       pMessageBuffer,
                       messageBufferSize,
                       0 );
    cborResult = cbor_encoder_create_map( &cborEncoder,
                                          &cborMapEncoder,
                                          OTA_CBOR_GETSTREAMREQUEST_ITEM_COUNT );

    /* Encode the client token key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_CLIENTTOKEN_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               pClientToken );
    }

    /* Encode the file ID key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_FILEID_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder,
                                      fileId );
    }

    /* Encode the block size key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_BLOCKSIZE_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder,
                                      blockSize );
    }

    /* Encode the block offset key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_BLOCKOFFSET_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder,
                                      blockOffset );
    }

    /* Encode the block bitmap key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_BLOCKBITMAP_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_byte_string( &cborMapEncoder,
                                              pBlockBitmap,
                                              blockBitmapSize );
    }

    /* Encode the number of blocks requested key and value. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz( &cborMapEncoder,
                                               OTA_CBOR_NUMBEROFBLOCKS_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int( &cborMapEncoder,
                                      numOfBlocksRequested );
    }

    /* Done with the encoder. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encoder_close_container_checked( &cborEncoder,
                                                           &cborMapEncoder );
    }

    /* Get the encoded size. */
    if( CborNoError == cborResult )
    {
        *pEncodedMessageSize = cbor_encoder_get_buffer_size( &cborEncoder,
                                                             pMessageBuffer );
    }

    return CborNoError == cborResult;
}
