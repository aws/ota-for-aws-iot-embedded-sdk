/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * Insert copyright notice
 */

/**
 * @file stringBuilderUInt32Decimal_harness.c
 * @brief Implements the proof harness for stringBuilderUInt32Decimal function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */

#include "ota_mqtt_private.h"

#define U32_MAX_LEN    10U

size_t __CPROVER_file_local_ota_mqtt_c_stringBuilderUInt32Decimal( char * pBuffer,
                                                                   size_t bufferSizeBytes,
                                                                   uint32_t value );

void stringBuilderUInt32Decimal_harness()
{
    /* The pBuffer is used as string in various functions but the maximum size of the. */
    char * pBuffer;
    size_t bufferSizebytes;
    uint32_t value;

    /* The bufferSizebytes is the size of the pBuffer. The pBuffer is statically initialized with
     *  a size of U32_MAX_LEN + 1 in all the functions which call stringBuilderUInt32Decimal. Hence,
     *  the size can never be below that. */
    __CPROVER_assume( bufferSizebytes > U32_MAX_LEN );

    pBuffer = ( char * ) malloc( bufferSizebytes );

    /* pBuffer is always initialized statically before passing it to the function. Hence,
     *  it can never be NULL. */
    __CPROVER_assume( pBuffer != NULL );

    ( void ) __CPROVER_file_local_ota_mqtt_c_stringBuilderUInt32Decimal( pBuffer, bufferSizebytes, value );

    free( pBuffer );
}
