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
 * @file aws_ota_base64.c
 * @brief Implements a Base64 decoding routine.
 */

#include "aws_ota_base64_private.h"

/**
 * @brief Number to represent both line feed and carriage return symbols in the
 *        pBase64SymbolToIndexMap table.
 */
#define NEWLINE                                 64U

/**
 * @brief Number to represent the whitespace character in the pBase64SymbolToIndexMap table.
 */
#define WHITESPACE                              65U

/**
 * @brief Number to represent the Base64 padding symbol in the pBase64SymbolToIndexMap table.
 */
#define PADDING_SYMBOL                          66U

/**
 * @brief Number to represent values that are invalid in the pBase64SymbolToIndexMap table.
 */
#define NON_BASE64_INDEX                        67U

/**
 * @brief Size of the pBase64SymbolToIndexMap table.
 */
#define ASCII_BASE64_MAP_SIZE                   256

/**
 * @brief Number of bits in a sextet.
 */
#define SEXTET_SIZE                             6

/**
 * @brief Bitmask for the six least significant bits.
 */
#define SIX_LEAST_SIG_BITS                      0x3F

/**
 * @brief Maximum number of Base64 symbols to store in a buffer before decoding them.
 */
#define MAX_NUM_BASE64_DATA                     4

/**
 * @brief Maximum number of padding symbols in a string of encoded data that is considered valid.
 */
#define MAX_EXPECTED_NUM_PADDING                2

/**
 * @brief Number of elements that will be written to the decode output buffer when the sextet
 *        buffer for encoded data is full.
 */
#define MAX_LENGTH_OF_BUFFER_WRITE              3

/**
 * @brief Smallest amount of data that can be base64 encoded is a byte. Encoding a single
 *        byte of data results in 2 bytes of encoded data. Therefore if the encoded data is smaller
 *        than 2 bytes, there is an error with the data.
 */
#define MIN_VALID_ENCODED_DATA_SIZE             2

/**
 * @brief The number of bits in a single octet.
 */
#define SIZE_OF_ONE_OCTET                       8

/**
 * @brief The number of bits in two octets.
 */
#define SIZE_OF_TWO_OCTETS                      16

/**
 * @brief The number of padding bits that are present when there are two sextets of encoded data.
 */
#define SIZE_OF_PADDING_WITH_TWO_SEXTETS        4

/**
 * @brief The number of padding bits that are present when there are three sextets of encoded data.
 */
#define SIZE_OF_PADDING_WITH_THREE_SEXTETS      2

/**
 * @brief This table takes is indexed by an Ascii character and returns the respective base64 index.
 *        Valid base64 symbols will have an index ranging from 0-63. Valid base64 symbolsThe base64
 *        digits being used are "ABCDEFGHIJKLMNOPQRSTUVWXYabcdefghijklmnopqrstuvwxyz0123456789+/"
 *        where 'A' is the 0th index of the base64 symbols and '/' is the 63rd index.
 *
 *        Outside of the numbers 0-63, there are magic numbers in this table:
 *        - The 11th entry in this table has the number 64. This is to identify the ascii character
 *          '\n' as a newline character.
 *        - The 14th entry in this table has the number 64. This is to identify the ascii character
 *          '\r' as a newline character.
 *        - The 33rd entry in this table has the number 65. This is to identify the ascii character
 *          ' ' as a whitespace character.
 *        - The 62nd entry in this table has the number 66. This is to identify the ascii character
 *          '=' as the padding character.
 *        - All positions in the ascii table that are invalid symbols are identified with the
 *          number 67 (other than '\n','\r',' ','=').
 */
static const unsigned char pBase64SymbolToIndexMap[] = {
    67,67,67,67,67,67,67,67,67,67,
    64,67,67,64,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,65,67,67,67,67,67,67,67,
    67,67,67,62,67,67,67,63,52,53,
    54,55,56,57,58,59,60,61,67,67,
    67,66,67,67,67, 0, 1, 2, 3, 4,
     5, 6, 7, 8, 9,10,11,12,13,14,
    15,16,17,18,19,20,21,22,23,24,
    25,67,67,67,67,67,67,26,27,28,
    29,30,31,32,33,34,35,36,37,38,
    39,40,41,42,43,44,45,46,47,48,
    49,50,51,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67,67,67,67,67,
    67,67,67,67,67,67
};

/**
 * @brief Decode Base64 encoded data.
 * 
 * @param[out] pDest Pointer to a buffer for storing the decoded result.
 * @param[in]  destLen Length of the pDest buffer.
 * @param[out] pResultLen Pointer to the length of the decoded result.
 * @param[in]  pEncodedData Pointer to a buffer containing the Base64 encoded data that is intended
 *             to be decoded.
 * @param[in]  encodedLen The number of elements in the Base64 encoded data buffer.
 * 
 * @return     One of the following:
 *             - #SUCCESS if the Base64 encoded data was valid and succesfully decoded.
 *             - An error code defined in aws_ota_base64_private.h if the encoded data is invalid
 *               or the input parameters are invalid.
 */
int base64Decode( unsigned char* pDest, size_t destLen, size_t* pResultLen, const unsigned char* pEncodedData, size_t encodedLen )
{
    uint32_t dataBuffer = 0; /* Buffer for storing up to 4 sextets of encoded data. */
    size_t numDataInBuffer = 0;
    const unsigned char* pCurrBase64Symbol = pEncodedData;
    size_t outputLen = 0;
    size_t numPadding = 0;
    size_t numWhitespace = 0;
    int return_val = SUCCESS;

    if ( pEncodedData == NULL || pDest == NULL || pResultLen == NULL )
    {
        return_val = NULL_PTR_ERROR;
    }

    if ( encodedLen < MIN_VALID_ENCODED_DATA_SIZE )
    {
        return_val = INVALID_DATA_SIZE;
    }

    /* This loop will decode the first (encodedLen - (encodedLen % 4)) amount of data. */
    while ( return_val == SUCCESS && ( pCurrBase64Symbol < ( pEncodedData + encodedLen ) ) )
    {
        unsigned char base64Index = 0;
        /* Read in the next Ascii character that represents the current base64 symbol. */
        uint32_t base64AsciiSymbol = *pCurrBase64Symbol++;
        /* Convert the base64 symbol into the corresponding base64 index. */
        base64Index = pBase64SymbolToIndexMap[ base64AsciiSymbol ];

        /* Validate that the base64 symbol (represented by its index) is valid and in an
         * appropriate place. */
        switch ( base64Index )
        {
        case NON_BASE64_INDEX:
            return INVALID_SYMBOL_ERROR;
        case PADDING_SYMBOL:
            if ( ++numPadding > MAX_EXPECTED_NUM_PADDING )
            {
                return_val = INVALID_NUMBER_OF_PADDING_SYMBOL;
                continue;
            }
            if ( numWhitespace != 0 )
            {
                return_val = INVALID_SYMBOL_ORDERING;
            }
            continue;
        case WHITESPACE:
            ++numWhitespace;
            continue;
        case NEWLINE:
            continue;
        default:
            /* Whitespace characters and padding are only valid at the end of the data. */
            if ( numWhitespace != 0 || numPadding != 0 )
            {
                return_val = INVALID_SYMBOL_ORDERING;
                continue;
            }
        }

        /* Shift the previously stored data over to make room for the next base64 sextet and
         * store the current base64 index that is represented by the 6 least significant bits. 
         * Six is the number of bits you need to represent a character in base64 (log2(64) = 6). 
         * The remaining two most significant bits will always be 0 since the only valid range of
         * input data is between 0 and 63. */
        dataBuffer = ( dataBuffer << SEXTET_SIZE ) | base64Index;
        ++numDataInBuffer;

        /* The data buffer is considered full when it contains 4 sextets of data (aka 4 pieces of
         * encoded data). If the buffer is full, convert the 4 sextets of encoded data into 3
         * sequential octects of decoded data starting from the most significant bits and ending
         * at the least significant bits. */
        if ( numDataInBuffer == MAX_NUM_BASE64_DATA )
        {
            numDataInBuffer = 0;
            if ( outputLen + MAX_LENGTH_OF_BUFFER_WRITE <= destLen )
            {
                pDest[ outputLen++ ] = ( dataBuffer >> SIZE_OF_TWO_OCTETS ) & 0xFF;
                pDest[ outputLen++ ] = ( dataBuffer >> SIZE_OF_ONE_OCTET ) & 0xFF;
                pDest[ outputLen++ ] = dataBuffer & 0xFF;
                dataBuffer = 0;
            }
            else
            {
                return_val = DST_BUFFER_TOO_SMALL_ERROR;
                continue;
            }
        }
    }

    /* Handle the scenarios where there is padding at the end of the encoded data. This happens
     * when the length of the data excluding padding and newlines is not a multiple of four. The
     * two valid scenarios are when there are two or three sextets of data remaining at the end of
     * the encoded data buffer. For example, "TWE=" and "TQ==".
     * 
     * This implementation of base64 decoding assumes that non-zero padding bits are an error. This
     * prevents having multiple non-matching encoded data strings map to identical decoded strings. */
    if( return_val == SUCCESS)
    {
        if ( numDataInBuffer == 3 )
        {
            /* When there are only three sextets of data remaining at the end of the encoded data,
             * it is assumed that these three sextets should be decoded into two octets of data. In
             * this case, the two least significant bits are ignored and the following sixteen
             * least significant bits are converted into two octets of data. */
            if ( dataBuffer & 0x3 )
            {
                return_val = NON_ZERO_PADDING_ERROR;
            }
            if ( return_val == SUCCESS )
            {
                dataBuffer = dataBuffer >> SIZE_OF_PADDING_WITH_THREE_SEXTETS;
                pDest[ outputLen++ ] = ( dataBuffer >> SIZE_OF_ONE_OCTET ) & 0xFF;
                pDest[ outputLen++ ] = dataBuffer & 0xFF;
            }
        }
        else if ( numDataInBuffer == 2 )
        {
            /* When there are only two sextets of data remaining at the end of the encoded data, it
             * is assumed that these two sextets should be decoded into one octet of data. In this
             * case, the four least significant bits are ignored and the following eight least
             * significant bits are converted into one octet of data. */
            if ( dataBuffer & 0xF )
            {
                return_val = NON_ZERO_PADDING_ERROR;
            }
            if ( return_val == SUCCESS )
            {
                dataBuffer = dataBuffer >> SIZE_OF_PADDING_WITH_TWO_SEXTETS;
                pDest[ outputLen++ ] = dataBuffer & 0xFF;
            }
        }
        /* This scenario is only possible when the number of encoded symbols ( excluding newlines
         * and padding ) being decoded mod four is equal to one. There is no valid scenario where
         * unencoded data can be encoded to create a result of this size. Therefore if this size
         * is encountered, it is assumed to have been a mistake and is considered an error. */
        else if ( numDataInBuffer == 1 )
        {
            return_val = UNEXPECTED_NUMBER_OF_DATA;
        }
    }

    if ( return_val == SUCCESS )
    {
        *pResultLen = outputLen;
    }

    return return_val;
}

/*-----------------------------------------------------------*/
