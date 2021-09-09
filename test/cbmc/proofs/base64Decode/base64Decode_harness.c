/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file base64Decode_harness.c
 * @brief Implements the proof harness for base64Decode function.
 */
/* Include headers for base64 decoding. */
#include "ota_base64_private.h"
#include <stdlib.h>

#define VALID_BASE64_SYMBOL_INDEX_RANGE_MAX    63U

/* Maximum size of the decode buffer for storing the PEM signature. */
#define MAX_DECODE_BUFFER_SIZE                 256

/* For every 3 bytes in the decode there are 4 bytes in the encode buffer. The
 * maximum size of the encode buffer is 4/3 times the decode buffer. */
#define MAX_ENCODE_BUFFER_SIZE                 344

/* Returns the number of whitespace and padding in the encoded buffer. */
Base64Status_t __CPROVER_file_local_ota_base64_c_preprocessBase64Index( uint8_t base64Index,
                                                                        int64_t * pNumPadding,
                                                                        int64_t * pNumWhitespace )
{
    Base64Status_t status;

    return status;
}

/* updates the number of valid symbol in the decoding buffer. */
void __CPROVER_file_local_ota_base64_c_updateBase64DecodingBuffer( const uint8_t base64Index,
                                                                   uint32_t * pBase64IndexBuffer,
                                                                   uint32_t * pNumDataInBuffer )
{
    uint32_t numDataInBuffer = *pNumDataInBuffer;

    /* Increment the number of valid symbols present in the index buffer. */
    if( base64Index <= VALID_BASE64_SYMBOL_INDEX_RANGE_MAX )
    {
        numDataInBuffer++;
    }

    *pNumDataInBuffer = numDataInBuffer;
}

/* This functions decodes every 4 bytes of encoded data. */
Base64Status_t __CPROVER_file_local_ota_base64_c_decodeBase64IndexBuffer( uint32_t * pBase64IndexBuffer,
                                                                          uint32_t * pNumDataInBuffer,
                                                                          uint8_t * pDest,
                                                                          const size_t destLen,
                                                                          size_t * pOutputLen )
{
    Base64Status_t status;

    /* After decoding, Reset the number of valid bytes present in the decoding Buffer. */
    *pNumDataInBuffer = 0;

    return status;
}

void base64Decode_harness()
{
    uint8_t * pDest;
    size_t destLen;
    size_t * pResultLen;
    uint8_t * pEncodedData;
    size_t encodedLen;

    size_t resultLen;

    /* The base64Decode function is used to decode the PEM signature and
     * the maximum size of the decoded signature is 256. This limit is set
     * to limit loop unwinding in the base64Decode function. */
    __CPROVER_assume( destLen <= MAX_DECODE_BUFFER_SIZE );

    /* This limit is set to limit loop unwinding in the base64Decode function.   */
    __CPROVER_assume( encodedLen <= MAX_ENCODE_BUFFER_SIZE );

    pDest = ( uint8_t * ) malloc( destLen * sizeof( uint8_t ) );
    pEncodedData = ( uint8_t * ) malloc( encodedLen * sizeof( uint8_t ) );

    pResultLen = &resultLen;

    ( void ) base64Decode( pDest, destLen, pResultLen, pEncodedData, encodedLen );

    free( pDest );
    free( pEncodedData );
}
