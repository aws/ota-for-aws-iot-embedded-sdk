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

#ifndef __OTAC_BOR__H__
#define __OTAC_BOR__H__

/**
 * @brief Message field definitions, per the server specification. These are
 * not part of the library interface but are included here for testability.
 */
#define OTA_CBOR_CLIENTTOKEN_KEY          "c"
#define OTA_CBOR_FILEID_KEY               "f"
#define OTA_CBOR_BLOCKSIZE_KEY            "l"
#define OTA_CBOR_BLOCKOFFSET_KEY          "o"
#define OTA_CBOR_BLOCKBITMAP_KEY          "b"
#define OTA_CBOR_STREAMDESCRIPTION_KEY    "d"
#define OTA_CBOR_STREAMFILES_KEY          "r"
#define OTA_CBOR_FILESIZE_KEY             "z"
#define OTA_CBOR_BLOCKID_KEY              "i"
#define OTA_CBOR_BLOCKPAYLOAD_KEY         "p"
#define OTA_CBOR_NUMBEROFBLOCKS_KEY       "n"

/**
 * @brief Decode a Get Stream response message from AWS IoT OTA.
 */
bool OTA_CBOR_Decode_GetStreamResponseMessage( const uint8_t * pMessageBuffer,
                                               size_t messageSize,
                                               int32_t * pFileId,
                                               int32_t * pBlockId,
                                               int32_t * pBlockSize,
                                               uint8_t ** pPayload,
                                               size_t * pPayloadSize );

/**
 * @brief Create an encoded Get Stream Request message for the AWS IoT OTA
 * service.
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
                                              int32_t numOfBlocksRequested );

#endif /* ifndef __OTACBOR__H__ */
