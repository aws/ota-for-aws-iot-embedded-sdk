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

#ifndef _AWS_OTA_OS_FREERTOS_H_
#define _AWS_OTA_OS_FREERTOS_H_

 /* Standard library include. */
#include <stddef.h>

/* Demo config include. */
#include "demo_config.h"

 /* OTA library interface include. */
#include "ota_os_interface.h"

struct OtaEventContext
{
	/* Unused.*/
	uint32_t dummy;
};

struct OtaTimerContext
{
	/* Unused.*/
	uint32_t dummy;
};

OtaErr_t ota_InitEvent( OtaEventContext_t * pContext );

OtaErr_t ota_SendEvent( OtaEventContext_t * pContext,
	                    const void* pEventMsg,
	                    unsigned int timeout );

OtaErr_t ota_ReceiveEvent( OtaEventContext_t * pContext,
	                       void* pEventMsg,
                           uint32_t timeout );

OtaErr_t ota_DeinitEvent( OtaEventContext_t * pContext );


OtaErr_t ota_StartTimer ( OtaTimerContext_t * pContext,
                          const char * const pTimerName,
                          const uint32_t timeout,
                          void ( * callback )( void * ) );

OtaErr_t ota_StopTimer ( OtaTimerContext_t * pContext );

OtaErr_t ota_DeleteTimer( OtaTimerContext_t * pContext );

#endif
