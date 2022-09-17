/*
 * AWS IoT Over-the-air Update v3.4.0
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 */

/**
 * @file stringBuilder_harness.c
 * @brief Implements the proof harness for stringBuilder function.
 */
#include "ota_mqtt_private.h"

/* Declaration of the mangled name function generated by CBMC for static functions. */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] );

void stringBuilder_harness()
{
    char * pBuffer;
    size_t bufferSizeBytes;
    char ** strings;

    size_t numStrings;
    size_t stringSize;
    size_t i;
    size_t stringLength;

    /* The pBuffer is statically allocated with a non-zero size before passing it to the stringBuilder function.*/
    __CPROVER_assume( bufferSizeBytes > 0 );
    pBuffer = ( char * ) malloc( bufferSizeBytes );

    /* pBuffer can never be NULL since it it always initialized before passing it to the stringBuilder function. */
    __CPROVER_assume( pBuffer != NULL );

    /* The minimum and the maximum number of strings inside the numStrings are 0 and 11. */
    __CPROVER_assume( numStrings > 0 && numStrings < UINT32_MAX );

    /* Initializing an array of strings with size numStrings. */
    strings = ( char ** ) malloc( numStrings * sizeof( char * ) );

    /* The size of each string inside the strings array passed to the stringBuilder
     * function is greater than 0. */
    __CPROVER_assume( stringSize > 0 );

    /* The strings array cannot be NULL as it is always initialized before
     *  passing to the function. */
    __CPROVER_assume( strings != NULL );

    for( i = 0; i < numStrings - 1; ++i )
    {
        strings[ i ] = ( char * ) malloc( stringSize );

        /* The strings inside the strings array are defined before passing it to
         * the stringBuilder function. */
        __CPROVER_assume( strings[ i ] != NULL );
        strings[ i ][ stringSize - 1 ] = '\0';
    }

    /* Strings array is always passed with a NULL string at the end. */
    __CPROVER_assume( strings[ numStrings - 1 ] == NULL );

    __CPROVER_file_local_ota_mqtt_c_stringBuilder( pBuffer, bufferSizeBytes, strings );

    /* Free the allocated memory. */
    free( pBuffer );

    for( i = 0; i < numStrings - 1; ++i )
    {
        free( strings[ i ] );
    }

    free( strings );
}
