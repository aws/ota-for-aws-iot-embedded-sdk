/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file OTA_CBOR_Encode_GetStreamRequestMessage_harness.c
 * @brief Implements the proof harness for OTA_CBOR_Encode_GetStreamRequestMessage function.
 */
/* Include headers for cbor parsing. */
#include "cbor.h"
#include "ota_cbor_private.h"
#include <stdlib.h>

#define OTA_MAX_BLOCK_BITMAP_SIZE    128U                                                 /*!< @brief Max allowed number of bytes to track all blocks of an OTA file. Adjust block size if more range is needed. */
#define OTA_REQUEST_MSG_MAX_SIZE     ( 3U * OTA_MAX_BLOCK_BITMAP_SIZE )                   /*!< @brief Maximum size of the message */


/* Stub to initialize the encoder. */
void cbor_encoder_init( CborEncoder * encoder,
                        uint8_t * buffer,
                        size_t size,
                        int flags )
{
}

/* Stub to create a cbor map for cbor stream. */
CborError cbor_encoder_create_map( CborEncoder * encoder,
                                   CborEncoder * mapEncoder,
                                   size_t length )
{
    CborError err;

    return err;
}

/* Stub to encode the text strings. */
CborError __CPROVER_file_local_cbor_h_cbor_encode_text_stringz( CborEncoder * encoder,
                                                                const char * string )
{
    CborError err;

    return err;
}

/* Stub to encode integer values. */
CborError cbor_encode_int( CborEncoder * encoder,
                           int64_t value )
{
    CborError err;

    return err;
}

/* Stub to append the string to a CBOR stream. */
CborError cbor_encode_byte_string( CborEncoder * encoder,
                                   const uint8_t * string,
                                   size_t length )
{
    CborError err;

    return err;
}

/* Stub to close the CBOR container. */
CborError cbor_encoder_close_container_checked( CborEncoder * encoder,
                                                const CborEncoder * containerEncoder )
{
    CborError err;

    return err;
}

/* Stub to return the size of buffer. */
size_t __CPROVER_file_local_cbor_h_cbor_encoder_get_buffer_size( const CborEncoder * encoder,
                                                                 const uint8_t * buffer )
{
    size_t bufferSize;

    return bufferSize;
}

void OTA_CBOR_Encode_GetStreamRequestMessage_harness()
{
    uint8_t * pMessageBuffer;
    size_t messageBufferSize;
    size_t * pEncodedMessageSize;
    char * pClientToken;
    int32_t fileId;
    int32_t blockSize;
    int32_t blockOffset;
    uint8_t * pBlockBitmap;
    size_t blockBitmapSize;
    int32_t numOfBlocksRequested;
    size_t clientTokenSize;

    /* The pMessageBuffer pointer is pointing to an array of size messageBufferSize. */
    pMessageBuffer = ( uint8_t * ) malloc( messageBufferSize * sizeof( uint8_t ) );

    /* pEncodedMessage should be pointing to a valid location in the memory. */
    pEncodedMessageSize = ( size_t * ) malloc( sizeof( size_t ) );

    /* The size of pclienttoken can be anything and thus is varied using the
     * clientTokenSize variable. */
    pClientToken = ( char * ) malloc( clientTokenSize * sizeof( char ) );

    /* The pBlockBitmap is pointing to an array of size blockBitmapSize. */
    pBlockBitmap = ( uint8_t * ) malloc( blockBitmapSize * sizeof( uint8_t ) );

    OTA_CBOR_Encode_GetStreamRequestMessage( pMessageBuffer, messageBufferSize, pEncodedMessageSize,
                                             pClientToken,
                                             fileId, blockSize, blockOffset, pBlockBitmap, blockBitmapSize, numOfBlocksRequested );

    free( pMessageBuffer );
    free( pEncodedMessageSize );
    free( pClientToken );
    free( pBlockBitmap );
}
