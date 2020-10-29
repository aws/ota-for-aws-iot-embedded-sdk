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
 * @file ota_base64_private.h
 * @brief Function declarations and error codes for ota_base64.c.
 */

#ifndef __OTA_BASE64_PRIVATE__H__
#define __OTA_BASE64_PRIVATE__H__

/* Standard includes. */
#include <stdint.h>
#include <stdlib.h>
#include <inttypes.h>

/**
 * @brief Base64 function success.
 */
#define OTA_BASE64_SUCCESS                        0

/**
 * @brief Invalid symbol in the encoded data.
 */
#define OTA_ERR_BASE64_INVALID_SYMBOL             1

/**
 * @brief A Base64 symbol is in an invalid location within the encoded data.
 */
#define OTA_ERR_BASE64_INVALID_SYMBOL_ORDERING    2

/**
 * @brief Length of the encoded data is impossible to have been created with
 *        valid Base64 encoding.
 */
#define OTA_ERR_BASE64_INVALID_INPUT_SIZE         3

/**
 * @brief Input parameter for pointer is null.
 */
#define OTA_ERR_BASE64_NULL_PTR                   4

/**
 * @brief Provided buffer is too small.
 */
#define OTA_ERR_BASE64_INVALID_BUFFER_SIZE        5

/**
 * @brief Padding bits inside of the encoded data are invalid because they are
 *        not zero.
 */
#define OTA_ERR_BASE64_NON_ZERO_PADDING           6

/**
 * @brief Invalid number of padding symbols.
 */
#define OTA_ERR_BASE64_INVALID_PADDING_SYMBOL     7

/**
 * @brief Decode Base64 encoded data.
 *
 * @param[out] pDest Pointer to a buffer for storing the decoded result.
 * @param[in]  destLen Length of the pDest buffer.
 * @param[out] pResultLen Pointer to the length of the decoded result.
 * @param[in]  pEncodedData Pointer to a buffer containing the Base64 encoded
 *             data that is intended to be decoded.
 * @param[in]  encodedLen Length of the pEncodedData buffer.
 *
 * @return     One of the following:
 *             - #OTA_BASE64_SUCCESS if the Base64 encoded data was valid
 *               and successfully decoded.
 *             - An error code defined in ota_base64_private.h if the
 *               encoded data or input parameters are invalid.
 */
int32_t base64Decode( uint8_t * pDest,
                      const size_t destLen,
                      size_t * pResultLen,
                      const uint8_t * pEncodedData,
                      const size_t encodedLen );

#endif /* ifndef __OTA_BASE64_PRIVATE__H__ */
