/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * Insert copyright notice
 */

/**
 * @file stringBuilderUInt32Hex_harness.c
 * @brief Implements the proof harness for stringBuilderUInt32Hex function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include "ota_mqtt_private.h"

#define U32_MAX_LEN            10U   

size_t __CPROVER_file_local_ota_mqtt_c_stringBuilderUInt32Hex( char * pBuffer,
                                      size_t bufferSizeBytes,
                                      uint32_t value );

void stringBuilderUInt32Hex_harness(){
	char* pBuffer;
	size_t bufferSizebytes;
	uint32_t value;
	
	/* The input to the function is always a non-NULL pointer. */
	__CPROVER_assume(pBuffer != NULL);
	__CPROVER_assume(bufferSizebytes >= U32_MAX_LEN);
	
	(void) __CPROVER_file_local_ota_mqtt_c_stringBuilderUInt32Hex(pBuffer,bufferSizebytes, value);
}
