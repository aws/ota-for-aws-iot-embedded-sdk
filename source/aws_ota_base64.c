#include "ota_base64_decode.h"
#include <stdio.h>

// magic numbers defines for the ascii_to_base64_map
#define NEWLINE 64 // symbolizes both line feed and carriage return ( '\n' '\r)
#define WHITESPACE 65// defines the Space character (' ')
#define PADDING_SYMBOL 66 // the padding symbol is assuming to be '='
#define NON_BASE64_SYMBOL 67

// boundary defines
#define ASCII_BASE64_MAP_SIZE 256
#define SEXTET_SIZE 6
#define SIX_LEAST_SIG_BITS 0x3F
#define MAX_NUM_BASE64_DATA 4
#define MAX_EXPECTED_NUM_PADDING 2

// error defines 
#define INVALID_SYMBOL_ERROR -1
#define INVALID_SYMBOL_ORDERING -2
#define INVALID_DATA_SIZE -3
#define UNEXPECTED_NUMBER_OF_DATA -4
#define NULL_PTR_ERROR -5
#define DST_BUFFER_TOO_SMALL_ERROR -6
#define FINAL_DATA_PADDING_NON_ZERO_ERROR -7
#define INVALID_NUMBER_OF_PADDING_SYMBOL -8

/*
	This table is indexed by an ascii character that represents the symbol for a base64 digit.
	It returns the base64 index for that symbol (what number in the sequence of base64 digits it is).
	The base64 digits being used are "ABCDEFGHIJKLMNOPQRSTUVWXYabcdefghijklmnopqrstuvwxyz0123456789+/"
	in that order where 'A' is the 0th index of the base64 digits and '/' is the 63rd index.

	There are some magic numbers in this table:
	- The 11th entry in this table has the number 64. This is to identify the ascii character '\n' as a newline character
	- The 14th entry in this table has the number 64. This is to identify the ascii character '\r' as a newline character
	- The 33rd entry in this table has the number 65. This is to identify the ascii character ' ' as a whitespace character
	- The 62nd entry in this table has the number 66. This is to identify the ascii character '=' as the padding character
	- All positions in the ascii table that are invalid characters are identified with the number 67

*/
static const unsigned char ascii_to_base64_map[] = {
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
Implementation details:
- Allows for excess pad characters at the end of the sequence. They will be ignored.
- Output length is only valid if this function returns 0
- Padding bits are expected to be 0
- Newlines are allowed in the data and are skipped
- Whitespace is only allowed at the end of the buffer
*/
int ota_base64_decode(unsigned char* dst, size_t dlen, size_t* olen, const unsigned char* src, size_t slen)
{
	// Create a buffer initialized to 0
	unsigned data_buffer = 0;
	unsigned numDataInBuffer = 0;
	unsigned char* curr_pos = src;
	unsigned outputLength = 0; 
	unsigned num_padding = 0;
	unsigned num_whitespace = 0;

	// check for null pointers
	if (src == NULL || dst == NULL || olen == NULL)
		return NULL_PTR_ERROR;

	if (slen < 2)
		return INVALID_DATA_SIZE;

	/* This loop will handle the first (dataSize - (dataSize % 4)) amount of data */
	while (curr_pos < src + slen)
	{
		unsigned char base64_symbol;

		// read in the next character of base64 encoded data and get it's equivalent base64 symbol
		unsigned ascii_symbol = *curr_pos++;
		base64_symbol = ascii_to_base64_map[ascii_symbol];

		// Check to make sure it is a valid symbol
		if (base64_symbol == NON_BASE64_SYMBOL)
			return INVALID_SYMBOL_ERROR;

		// Make sure that this is a valid character
		switch (base64_symbol)
		{
		case NON_BASE64_SYMBOL:
			return -1;
		case PADDING_SYMBOL:
			if (++num_padding > 2)
				return INVALID_NUMBER_OF_PADDING_SYMBOL;
			continue;
		case WHITESPACE:
			++num_whitespace;
			continue;
		case NEWLINE:
			continue;
		default:
			// Whitespace characters and padding are only okay if they are at the end of the data
			if (num_whitespace != 0 || num_padding != 0)
				return INVALID_SYMBOL_ORDERING;
		}

		// shift the data in the buffer over to make room for the next character
		data_buffer = (data_buffer << SEXTET_SIZE);

		// store the 6 least significant bits. Six is the number of bits you need to 
		// represent a character in base64 (log2(64) = 6) and logical or the data into 
		// the 6 least significant bits of the data buffer that should now be set to 0
		data_buffer |= (base64_symbol & SIX_LEAST_SIG_BITS);
		++numDataInBuffer;

		// store the content of the data buffer into the output when the data buffer has 4 sextets in it
		// We are storing 4 sextets because 4 sextets are represented by 24 bits, which is divisible
		// by the size of a char, 8 bits.
		if (numDataInBuffer == MAX_NUM_BASE64_DATA)
		{
			numDataInBuffer = 0;
			// then take the data buffer and store the lower 24 bits of it into the next 3 characters of the output buffer
			if (outputLength + 3 <= dlen)
			{
				dst[outputLength++] = (data_buffer >> 16) & 0xFF;
				dst[outputLength++] = (data_buffer >> 8) & 0xFF;
				dst[outputLength++] = data_buffer & 0xFF;
				data_buffer = 0;
			}
			else
			{
				return DST_BUFFER_TOO_SMALL_ERROR;
			}
		}
	}

	// check the remaining size if there are 3 characters of data left (one padding). For ex. "TWE="
	if (numDataInBuffer == 3)
	{
		// The padding bits (two least significant bits) are expected to be 0
		// There are two paddings bits in the case of 3 sextets in the buffer because it is assumed
		// that when the last segmant of data is 3 sextets, there are two octets of data in the output.
		// 3 sextets are 18 bits and the output is only 16 bits, with the two extra bits in the original
		// 18 being padding.
		if (data_buffer & 0x3)
			return FINAL_DATA_PADDING_NON_ZERO_ERROR;
		//  take the lower 16 bits and convert those into two characters in the output buffer
		data_buffer = data_buffer >> 2; // remove the padding bits
		dst[outputLength++] = (data_buffer >> 8) & 0xFF;
		dst[outputLength++] = data_buffer & 0xFF;
	}
	// check the remaining size to see if there are 2 characters of data left (two padding). For ex. "TQ=="
	else if (numDataInBuffer == 2)
	{
		// The four least significant bits are padding bits and are expected to be 0
		// This is for a similar reason to the case where there are 3 sextets in the buffer
		// take the lower 8 bits and store them as a character in the output buffer
		if (data_buffer & 0xF)
			return FINAL_DATA_PADDING_NON_ZERO_ERROR;
		data_buffer = data_buffer >> 4; // remove the padding bits
		dst[outputLength++] = data_buffer & 0xFF;
	} 
	else if (numDataInBuffer == 1)
	{
		return UNEXPECTED_NUMBER_OF_DATA;
	}

	*olen = outputLength; //reset output length;
	return 0;
}
