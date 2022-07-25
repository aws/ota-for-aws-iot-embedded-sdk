/*
 * AWS IoT Over-the-air Update v3.3.0
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
 * @file Posix_OtaSendEvent_harness.c
 * @brief Implements the proof harness for Posix_OtaSendEvent function.
 */
/*  POSIX includes for OTA library. */
#include "ota_os_posix.h"
#include <poll.h>

int poll( struct pollfd * fds,
          nfds_t nfds,
          int timeout )
{
    int returnVal;

    if( nondet_bool() )
    {
        /* Case when timeout does not happen and data is present to be read. */
        __CPROVER_assume( returnVal > 0 );
        fds->revents = POLLIN;
    }
    else
    {
        /* Case when timeout happens. */
        returnVal = 0;
        fds->revents = 0;
    }
}

void Posix_OtaSendEvent_harness()
{
    OtaEventContext_t * pEventCtx;
    void * pEventMsg;
    unsigned int timeout;

    Posix_OtaSendEvent( pEventCtx, pEventMsg, timeout );
}
