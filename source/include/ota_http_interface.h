/*
 * FreeRTOS OTA V2.0.0
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

#ifndef _OTA_HTTP_INTERFACE_H_
#define _OTA_HTTP_INTERFACE_H_

/* Standard library includes. */
#include <stddef.h>
#include <stdint.h>

/**
 * @brief OTA Error type.
 */
typedef uint32_t OtaErr_t;

/**
 * @brief Init OTA Http interface.
 *
 * This function parses the pre-signed url and initializes connection.
 *
 * @param[in] pUrl         Pointer to the pre-signed url for downloading update file.
 *
 * @return              OtaErrorNone if success , other error code on failure.
 */

typedef OtaErr_t ( * ota_HttpInit_t ) ( char * pUrl );

/**
 * @brief Request file block over Http.
 *
 * This function requests file block over Http from the rangeStart and rangeEnd.
 *
 * @param[in] rangeStart  Starting index of the file data to be requested.
 *
 * @param[in] rangeEnd    End index of the file data to be requested.
 *
 * @return             OtaErrorNone if success , other error code on failure.
 */

typedef OtaErr_t ( * ota_HttpRequest_t )  ( uint32_t rangeStart,
                                            uint32_t rangeEnd );

/**
 * @brief Deinit OTA Http interface.
 *
 * This function cleanups Http connection and other data used for
 * requesting file blocks using the pre-signed url.
 *
 * @return        OtaErrorNone if success , other error code on failure.
 */
typedef OtaErr_t ( * ota_HttpDeinit )( void );

/**
 * @brief OTA Event Interface structure.
 *
 */
typedef struct OtaHttpInterface
{
    ota_HttpInit_t init;       /*!< Reference to HTTP initialization. */
    ota_HttpRequest_t request; /*!< Reference to HTTP data request. */
    ota_HttpDeinit deinit;     /*!< Reference to HTTP deinitialize. */
} OtaHttpInterface_t;

#endif /* ifndef _OTA_HTTP_INTERFACE_H_ */
