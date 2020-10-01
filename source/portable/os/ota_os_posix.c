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

/* Standard Includes.*/
#include <sys/types.h>
#include <stdlib.h>
#include <mqueue.h>
#include <sys/time.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* OTA OS POSIX Interface Includes.*/
#include "ota_os_posix.h"

/* OTA Event queue attributes.*/
#define OTA_QUEUE_NAME   "/otaqueue"
#define QUEUE_PERMISSIONS 0777
#define MAX_MESSAGES 10
#define MAX_MSG_SIZE 12

/* OTA Event queue attributes.*/
static mqd_t otaEventQueue;

OtaErr_t ota_InitEvent( OtaEventContext_t* pContext )
{
    (void) pContext;

    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;
    struct mq_attr attr;

    /* Unlink the event queue.*/
    mq_unlink( OTA_QUEUE_NAME );

    /* Initialize queue attributes.*/
    attr.mq_flags = 0;
    attr.mq_maxmsg = MAX_MESSAGES;
    attr.mq_msgsize = MAX_MSG_SIZE;
    attr.mq_curmsgs = 0;

    /* Open the event queue .*/
    if ( ( otaEventQueue = mq_open ( OTA_QUEUE_NAME, O_CREAT | O_RDWR, QUEUE_PERMISSIONS, &attr ) ) == -1 )
    {
        LogError( (  "OTA Event Queue create failed." ) );

        otaErrRet = OTA_ERR_EVENT_Q_CREATE_FAILED;
    }
    else
    {
        LogInfo( (  "OTA Event Queue created." ) );
        
        otaErrRet = OTA_ERR_NONE;
    }
    
    return otaErrRet;
}

OtaErr_t ota_SendEvent( OtaEventContext_t* pContext,
                       const void* pEventMsg,
                       unsigned int timeout)
{

    (void) pContext;
    (void) timeout;

    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

    /* Send the event to OTA event queue.*/
    if ( mq_send ( otaEventQueue, pEventMsg, MAX_MSG_SIZE, 0 ) == -1)
    {
        LogError( (  "OTA Event Send failed." ) );

        otaErrRet = OTA_ERR_EVENT_Q_SEND_FAILED;

    }else
    {
        LogInfo( (  "OTA Event Sent." ) );

        otaErrRet = OTA_ERR_NONE;
    }

}

OtaErr_t ota_ReceiveEvent( OtaEventContext_t* pContext,
                          void* pEventMsg,
                          uint32_t timeout)
{
    (void) pContext;
    (void) timeout;

    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

    char buff[MAX_MSG_SIZE];

    /* Delay a bit.*/
    sleep(1);

    if ( mq_receive ( otaEventQueue, buff, sizeof(buff), NULL) == -1 )
    {
        LogError( (  "OTA Event receive fatal error." ) );

        otaErrRet = OTA_ERR_EVENT_Q_RECEIVE_FAILED;
    }
    else
    {
        LogInfo( (  "OTA Event received" ) );

        /* copy the data from local buffer.*/
        memcpy( pEventMsg, buff, MAX_MSG_SIZE );

        otaErrRet = OTA_ERR_NONE;
    }

    return otaErrRet;
}

OtaErr_t ota_DeinitEvent( OtaEventContext_t* pContext )
{
  (void) pContext;

  OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

  /* Remove the event queue.*/
  if ( mq_unlink( OTA_QUEUE_NAME ) == -1 )
  {
        LogError( (  "OTA Event queue delete failed." ) );

        otaErrRet = OTA_ERR_EVENT_Q_DELETE_FAILED;
    }
    else
    {
        LogInfo( (  "OTA Event queue deleted." ) );

        otaErrRet = OTA_ERR_NONE;
    }

    return otaErrRet;

}
