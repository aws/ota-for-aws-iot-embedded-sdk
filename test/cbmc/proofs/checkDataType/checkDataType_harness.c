/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file checkDataType_harness.c
 * @brief Implements the proof harness for checkDataType function.
 */
/* Include headers for cbor parsing. */
#include "cbor.h"
#include "ota_cbor_private.h"

CborError __CPROVER_file_local_ota_cbor_c_checkDataType( CborType expectedType,
                                                         CborValue * cborValue );

void checkDataType_harness()
{
    CborType expectedType;
    CborValue * pcborValue;
    CborValue cborvalue;

    /* cborvalue is always statically initialized in OTA_CBOR_Decode_GetStreamResponseMessage
     * before checkDataType is called. */
    pcborValue = &cborvalue;

    __CPROVER_file_local_ota_cbor_c_checkDataType( expectedType, pcborValue );
}
