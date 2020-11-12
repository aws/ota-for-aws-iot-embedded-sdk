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

#ifndef __AWS_IOT_OTA_INTERFACE__H__
#define __AWS_IOT_OTA_INTERFACE__H__

/* OTA includes. */
#include "ota.h"
#include "ota_private.h"

/* General Constants. */

/* OTA control protocol constants. */
#define OTA_CONTROL_OVER_MQTT     0x00000001

/* OTA data protocol constants. */
#define OTA_DATA_OVER_MQTT        0x00000001
#define OTA_DATA_OVER_HTTP        0x00000002
#define OTA_DATA_NUM_PROTOCOLS    ( 2U )


/**
 * @brief Represents the OTA control interface functions.
 *
 * The functions in this structure are used for the control operations
 * during over the air updates like OTA job status updates.
 */
typedef struct
{
    OtaErr_t ( * requestJob )( OtaAgentContext_t * pAgentCtx ); /*!< Request for the next available OTA job from the job service. */
    OtaErr_t ( * updateJobStatus )( OtaAgentContext_t * pAgentCtx,
                                    OtaJobStatus_t status,
                                    int32_t reason,
                                    int32_t subReason );           /*!< Updates the OTA job status with information like in progress, completion, or failure. */
    OtaErr_t ( * cleanup )( const OtaAgentContext_t * pAgentCtx ); /*!< Cleanup related to OTA control plane. */
} OtaControlInterface_t;

/**
 * @brief Represents the OTA data interface functions.
 *
 * The functions in this structure are used for the data operations
 * during over the air updates like requesting file blocks.
 */
typedef struct
{
    OtaErr_t ( * initFileTransfer )( OtaAgentContext_t * pAgentCtx ); /*!< Initialize file transfer. */
    OtaErr_t ( * requestFileBlock )( OtaAgentContext_t * pAgentCtx ); /*!< Request File block. */
    OtaErr_t ( * decodeFileBlock )( uint8_t * pMessageBuffer,
                                    size_t messageSize,
                                    int32_t * pFileId,
                                    int32_t * pBlockId,
                                    int32_t * pBlockSize,
                                    uint8_t ** pPayload,
                                    size_t * pPayloadSize );       /*!< Decode a cbor encoded fileblock. */
    OtaErr_t ( * cleanup )( const OtaAgentContext_t * pAgentCtx ); /*!< Cleanup related to OTA data plane. */
} OtaDataInterface_t;

/**
 * @brief Set control interface for OTA operations.
 *
 * This function updates the OTA control operation functions as per the config
 * options selected.
 *
 * @param[out] pControlInterface OTA Control interface.
 *
 */
void setControlInterface( OtaControlInterface_t * pControlInterface );

/**
 * @brief Set data interface for OTA operations.
 *
 * This function updates the OTA data operation functions as per the config
 * options selected.
 *
 * @param[out] pDataInterface OTA data interface.
 *
 * @param[in] pProtocol Protocols used for the download.
 *
 */

OtaErr_t setDataInterface( OtaDataInterface_t * pDataInterface,
                           const uint8_t * pProtocol );

#endif /* ifndef __AWS_IOT_OTA_INTERFACE__H__ */
