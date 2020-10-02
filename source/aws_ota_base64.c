#include "aws_ota_base64_private.h"

/* Magic number defines for interpreting the pBase64SymbolToIndexMap table. */
#define NEWLINE 64 /* Magic number to represent both line feed and carriage return symbols. */
#define WHITESPACE 65 /* Magic number to represent the space character. */
#define PADDING_SYMBOL 66 /* Magic number to represent the base64 padding symbol, which is '=' for this implementation */
#define NON_BASE64_INDEX 67 /* Magic number to represent possible Ascii characters that are not part of the base64 digits */

/* Misc. defines that are related to boundaries. */
#define ASCII_BASE64_MAP_SIZE 256
#define SEXTET_SIZE 6
#define SIX_LEAST_SIG_BITS 0x3F
#define MAX_NUM_BASE64_DATA 4
#define MAX_EXPECTED_NUM_PADDING 2
#define MAX_LENGTH_OF_BUFFER_WRITE 3
#define MIN_VALID_ENCODED_DATA_SIZE 2
#define SIZE_OF_ONE_OCTET 8
#define SIZE_OF_TWO_OCTETS 16
#define SIZE_OF_PADDING_WITH_TWO_SEXTETS 4
#define SIZE_OF_PADDING_WITH_THREE_SEXTETS 2

/* Error defines. */
#define INVALID_SYMBOL_ERROR -1
#define INVALID_SYMBOL_ORDERING -2
#define INVALID_DATA_SIZE -3
#define UNEXPECTED_NUMBER_OF_DATA -4
#define NULL_PTR_ERROR -5
#define DST_BUFFER_TOO_SMALL_ERROR -6
#define NON_ZERO_PADDING_ERROR -7
#define INVALID_NUMBER_OF_PADDING_SYMBOL -8

/*
 *    This table takes is indexed by an Ascii character and returns the
 *    respective base64 index. Valid base64 symbols will have an index ranging
 *    from 0-63. Valid base64 symbolsThe base64 digits being used are 
 *    "ABCDEFGHIJKLMNOPQRSTUVWXYabcdefghijklmnopqrstuvwxyz0123456789+/" where 'A'
 *    is the 0th index of the base64 symbols and '/' is the 63rd index.
 *
 *    Outside of the numbers 0-63, there are magic numbers in this table:
 *    - The 11th entry in this table has the number 64. This is to identify the ascii character '\n' as a newline character
 *    - The 14th entry in this table has the number 64. This is to identify the ascii character '\r' as a newline character
 *    - The 33rd entry in this table has the number 65. This is to identify the ascii character ' ' as a whitespace character
 *    - The 62nd entry in this table has the number 66. This is to identify the ascii character '=' as the padding character
 *    - All positions in the ascii table that are invalid symbols are identified with the number 67 (other than '\n','\r',' ','=')
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


/*
 * Implementation remarks:
 * - Padding is not required, but the amount of padding can not exceed 2
 * - The output length, represented by pResultLen, is only valid if this function returns 0
 * - Any padding bits that are not set to 0 will result in an error
 * - Newlines are allowed in the data and are skipped
 * - Padding and whitespace present in the middle of the data will result in an error
 * 
 * Terminology:
 * - "Base64 symbol": 
 *                     These are characters that represent the 64 different base64 digits. 
 *                     In order, they are "ABCDEFGHIJKLMNOPQRSTUVWXYabcdefghijklmnopqrstuvwxyz0123456789+/"
 * - "Base64 index":  
 *                     Every base64 has a corresponding index number that defines the value of the digit. These
 *                     indices range from the value of 0 up to the value of 63. The base64 symbol "A" has an 
 *                     index (aka value) of 0. "B" has an index of 1, "C" has an index of 2, and so on up to "/",
 *                     which has an index of 63.
 */
int base64Decode( unsigned char* pDest, size_t destLen, size_t* pResultLen, const unsigned char* pEncodedData, size_t encodedLen )
{
    uint32_t dataBuffer = 0; /* A buffer that will store up to 4 pieces of encoded data before being decoded. */
    size_t numDataInBuffer = 0;
    const unsigned char* pCurrBase64Symbol = pEncodedData;
    size_t outputLen = 0;
    size_t numPadding = 0;
    size_t numWhitespace = 0;

    if ( pEncodedData == NULL || pDest == NULL || pResultLen == NULL )
    {
        return NULL_PTR_ERROR;
    }

    /* The smallest amount of data that can be base64 encoded is a byte. Encoding a single byte of data results
     * in 2 bytes of encoded data. Therefore if the encoded data is smaller than 2 bytes, there is an error with
     * the data */
    if ( encodedLen < MIN_VALID_ENCODED_DATA_SIZE )
    {
        return INVALID_DATA_SIZE;
    }

    /* This loop will decode the first (encodedLen - (encodedLen % 4)) amount of data. */
    while ( pCurrBase64Symbol < pEncodedData + encodedLen )
    {
        unsigned char base64Index = 0;
        /* Read in the next Ascii character that represents the current base64 symbol.*/
        uint32_t base64AsciiSymbol = *pCurrBase64Symbol++;
        /* Convert the base64 symbol into the corresponding base64 index. */
        base64Index = pBase64SymbolToIndexMap[ base64AsciiSymbol ];

        /* Validate that the base64 symbol (represented by its index) is valid and in an appropriate place. */
        switch ( base64Index )
        {
        case NON_BASE64_INDEX:
            return INVALID_SYMBOL_ERROR;
        case PADDING_SYMBOL:
            if ( ++numPadding > MAX_EXPECTED_NUM_PADDING )
            {
                return INVALID_NUMBER_OF_PADDING_SYMBOL;
            }
            if ( numWhitespace != 0 )
            {
                return INVALID_SYMBOL_ORDERING;
            }
            continue;
        case WHITESPACE:
            ++numWhitespace;
            continue;
        case NEWLINE:
            continue;
        default:
            /* Whitespace characters and padding are only valid if they are at the end of the data. */
            if ( numWhitespace != 0 || numPadding != 0 )
            {
                return INVALID_SYMBOL_ORDERING;
            }
        }

        /* Shift the previously stored data over to make room for the next base64 sextet and
         * store the current base64 index that is represented by the 6 least significant bits. 
         * Six is the number of bits you need to represent a character in base64 (log2(64) = 6). 
         * The remaining two most significant bits will always be 0 since the only valid range of
         * input data is between 0 and 63.*/
        dataBuffer = ( dataBuffer << SEXTET_SIZE ) | base64Index;
        ++numDataInBuffer;

        /* The data buffer is considered full when it contains 4 sextets of data (aka 4 pieces of encoded data).
         * If the buffer is full, convert the 4 sextets of encoded data into 3 sequential octects of decoded data
         * starting from the most significant bits and ending at the least significant bits. */
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
                return DST_BUFFER_TOO_SMALL_ERROR;
            }
        }
    }

    /* Handle the scenarios where there is padding at the end of the encoded data. This happens when the length
     * of the data excluding padding and newlines is not a multiple of four. The two valid scenarios are when
     * there are two or three sextets of data remaining at the end of the encoded data buffer. For example,
     * "TWE=" and "TQ==".
     * 
     * Remark: This implementation of base64 decoding assumes that non-zero padding bits are an error. This is
     * to prevent having multiple non-matching encoded data strings map to identical decoded strings. */
    if ( numDataInBuffer == 3 )
    {
        /* When there are only three sextets of data remaining at the end of the encoded data, it is assumed that
         * these three sextets should be decoded into two octets of data. In this case, the two least significant
         * bits are ignored and the following sixteen least significant bits are converted into two octets of data. */
        if ( dataBuffer & 0x3 )
        {
            return NON_ZERO_PADDING_ERROR;
        }
        dataBuffer = dataBuffer >> SIZE_OF_PADDING_WITH_THREE_SEXTETS;
        pDest[ outputLen++ ] = ( dataBuffer >> SIZE_OF_ONE_OCTET ) & 0xFF;
        pDest[ outputLen++ ] = dataBuffer & 0xFF;
    }
    else if ( numDataInBuffer == 2 )
    {
        /* When there are only two sextets of data remaining at the end of the encoded data, it is assumed that
         * these two sextets should be decoded into one octet of data. In this case, the four least significant
         * bits are ignored and the following eight least significant bits are converted into one octet of data. */
        if ( dataBuffer & 0xF )
        {
            return NON_ZERO_PADDING_ERROR;
        }
        dataBuffer = dataBuffer >> SIZE_OF_PADDING_WITH_TWO_SEXTETS;
        pDest[ outputLen++ ] = dataBuffer & 0xFF;
    } 
    /* This scenario is only possible when the number of encoded symbols ( excluding newlines and padding ) being
     * decoded mod four is equal to one. There is no valid scenario where unencoded data can be encoded to create
     * a result of this size. Therefore if this size is encountered, it is assumed to have been a mistake and is
     * considered an error. */
    else if ( numDataInBuffer == 1 )
    {
        return UNEXPECTED_NUMBER_OF_DATA;
    }

    *pResultLen = outputLen;
    return 0;
}

/*-----------------------------------------------------------*/
