/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file updateBase64DecodingBuffer_harness.c
 * @brief Implements the proof harness for updateBase64DecodingBuffer function.
 */
/* Include headers for base64 decoding. */
#include "ota_base64_private.h"

/* Inclusive upper bound for valid values that can be contained in pBase64SymbolToIndexMap. */
#define SYMBOL_TO_INDEX_MAP_VALUE_UPPER_BOUND    67U

void __CPROVER_file_local_ota_base64_c_updateBase64DecodingBuffer( const uint8_t base64Index,
                                                                   uint32_t * pBase64IndexBuffer,
                                                                   uint32_t * pNumDataInBuffer );

void updateBase64DecodingBuffer_harness()
{
    uint8_t base64Index;
    uint32_t * pBase64IndexBuffer;
    uint32_t * pNumDataInBuffer;
    uint32_t base64IndexBuffer;
    uint32_t numDataInBuffer;

    pBase64IndexBuffer = &base64IndexBuffer;
    pNumDataInBuffer = &numDataInBuffer;

    /* SYMBOL_TO_INDEX_MAP_VALUE_UPPER_BOUND is the maximum value of the
     * base64Index which is enforced in ota_base64.c. */
    __CPROVER_assume( base64Index < SYMBOL_TO_INDEX_MAP_VALUE_UPPER_BOUND );

    /* The maximum number of data in the pBase64IndexBuffer should not
     * exceed UINT32_MAX. */
    __CPROVER_assume( numDataInBuffer < UINT32_MAX );

    __CPROVER_file_local_ota_base64_c_updateBase64DecodingBuffer( base64Index, pBase64IndexBuffer, pNumDataInBuffer );
}
