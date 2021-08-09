/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * Insert copyright notice
 */

/**
 * @file stringBuilder_harness.c
 * @brief Implements the proof harness for stringBuilder function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include "ota_mqtt_private.h"

size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] );

void stringBuilder_harness()
{
    /* Insert argument declarations */
    char * pBuffer;
    size_t bufferSizeBytes;
    char ** strings;

    size_t numStrings;
    size_t stringSize;
    size_t i;

    /* The size of the pBuffer is always equal to the bufferSizeBytes. */
    pBuffer = ( char * ) malloc( bufferSizeBytes );

    /* pBuffer can never be NULL since it it always initialized by a null character. */
    __CPROVER_assume( pBuffer != NULL );

    /* The minimum and the maximum number of strings inside the numStrings is 11. */
    __CPROVER_assume( numStrings > 0 && numStrings < 13 );

    /* Initializing an array of strings. */
    strings = ( char ** ) malloc( numStrings * sizeof( char * ) );

    /* The strings array cannot be NULL as it is always initialized before
     *  passing to the function. */
    __CPROVER_assume( strings != NULL );
    
    /* Assuming that the size of the strings can never be NULL. */
    __CPROVER_assume( stringSize > 0 && stringSize < 1500 );

    for( i = 0; i < numStrings; ++i )
    {
        strings[ i ] = ( char * ) malloc( stringSize );
    }

    /* Strings array is always passed with a NULL string at the end. */
    __CPROVER_assume( strings[ numStrings - 1 ] == NULL );

    __CPROVER_file_local_ota_mqtt_c_stringBuilder( pBuffer, bufferSizeBytes, strings );

    /* Free the allocated memory. */
    free( pBuffer );

    for( i = 0; i < numStrings; ++i )
    {
        free( strings[ i ] );
    }

    free( strings );
}
