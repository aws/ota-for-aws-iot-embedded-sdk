/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file decodeBase64IndexBuffer_harness.c
 * @brief Implements the proof harness for decodeBase64IndexBuffer function.
 */
/* Include headers for base64 decoding. */
#include "ota_base64_private.h"

/* Only 24bits are required to store the 4 sextets of the encoded value. */
#define MAX_BITS_IN_DECODE_BUFFER      24U

/* Smallest amount of data that can be Base64 encoded is a byte. */
#define MIN_VALID_ENCODED_DATA_SIZE    2U

/* Maximum number of Base64 symbols to store in a buffer before decoding them. */
#define MAX_NUM_BASE64_DATA            4U

/* Declaration of the mangled name static function which is created by CBMC for static functions. */
Base64Status_t __CPROVER_file_local_ota_base64_c_decodeBase64IndexBuffer( uint8_t * pDest,
                                                                          const size_t destLen,
                                                                          size_t * pResultLen,
                                                                          const uint8_t * pEncodedData,
                                                                          const size_t encodedLen );

void decodeBase64IndexBuffer_harness()
{
    uint32_t * pBase64IndexBuffer;
    uint32_t * pNumDataInBuffer;
    uint8_t * pDest;
    size_t destLen;
    size_t * pOutputLen;
    uint32_t base64IndexBuffer;
    uint32_t numDataInBuffer;
    size_t outputLen;

    /* These values are defined in the base64Decode function before passing
     * it to the decodeBase64IndexBuffer function and thus cannot be NULL. */
    pBase64IndexBuffer = &base64IndexBuffer;
    pNumDataInBuffer = &numDataInBuffer;
    pOutputLen = &outputLen;

    /* The outputLen is the length of the decoded data filled in the
     * pDest buffer. This value cannot exceed UINT32_MAX - 4. */
    __CPROVER_assume( outputLen < UINT32_MAX - 4 );

    pDest = ( uint8_t * ) malloc( destLen * sizeof( uint8_t ) );

    /* This condition is used to prevent scenarios where malloc fails and
     * returns NULL pointer. */
    __CPROVER_assume( pDest != NULL );

    /* The pNumDataInBuffer stores the number of bytes present in the base64Buffer.
     * The minimum and maximum number of bytes stored in the buffer are defined. */
    __CPROVER_assume( *pNumDataInBuffer >= MIN_VALID_ENCODED_DATA_SIZE && *pNumDataInBuffer <= MAX_NUM_BASE64_DATA );

    /* The maximum number of sextet in the base64IndexBuffer is 4. The total
     * number of bytes occupied to store all the 4 sextets in a single 4 Byte buffer is
     * 24. Thus the value of base64IndexBuffer cannot exceed 1 << MAX_BITS_IN_DECODE_BUFFER. */
    __CPROVER_assume( base64IndexBuffer < ( 1 << MAX_BITS_IN_DECODE_BUFFER ) );

    ( void ) __CPROVER_file_local_ota_base64_c_decodeBase64IndexBuffer( pBase64IndexBuffer, pNumDataInBuffer, pDest, destLen, pOutputLen );

    free(pDest);
}
