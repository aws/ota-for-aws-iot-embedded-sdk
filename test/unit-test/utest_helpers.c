/*
 * FreeRTOS OTA V2.0.0
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

/* Standard includes. */
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

/* OTA library includes. */
#include "ota_cbor_private.h"

/* 3rdparty includes. */
#include "cbor.h"

/* test includes. */
#include "utest_helpers.h"

/* ========================================================================== */

CborError createOtaStreammingMessage( uint8_t * pMessageBuffer,
                                      size_t messageBufferSize,
                                      int blockIndex,
                                      uint8_t * pBlockPayload,
                                      size_t blockPayloadSize,
                                      size_t * pEncodedSize )
{
    CborError cborResult = CborNoError;
    CborEncoder cborEncoder, cborMapEncoder;

    /* Initialize the CBOR encoder. */
    cbor_encoder_init(
        &cborEncoder,
        pMessageBuffer,
        messageBufferSize,
        0 );
    cborResult = cbor_encoder_create_map(
        &cborEncoder,
        &cborMapEncoder,
        CBOR_TEST_GETSTREAMRESPONSE_MESSAGE_ITEM_COUNT );

    /* Encode the file identity. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz(
            &cborMapEncoder,
            OTA_CBOR_FILEID_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int(
            &cborMapEncoder,
            CBOR_TEST_FILEIDENTITY_VALUE );
    }

    /* Encode the block identity. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz(
            &cborMapEncoder,
            OTA_CBOR_BLOCKID_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int(
            &cborMapEncoder,
            blockIndex );
    }

    /* Encode the block size. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz(
            &cborMapEncoder,
            OTA_CBOR_BLOCKSIZE_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_int(
            &cborMapEncoder,
            blockPayloadSize );
    }

    /* Encode the block payload. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_text_stringz(
            &cborMapEncoder,
            OTA_CBOR_BLOCKPAYLOAD_KEY );
    }

    if( CborNoError == cborResult )
    {
        cborResult = cbor_encode_byte_string(
            &cborMapEncoder,
            pBlockPayload,
            blockPayloadSize );
    }

    /* Done with the encoder. */
    if( CborNoError == cborResult )
    {
        cborResult = cbor_encoder_close_container_checked(
            &cborEncoder,
            &cborMapEncoder );
    }

    /* Get the encoded size. */
    if( ( CborNoError == cborResult ) && ( pEncodedSize != NULL ) )
    {
        *pEncodedSize = cbor_encoder_get_buffer_size(
            &cborEncoder,
            pMessageBuffer );
    }

    return cborResult;
}
