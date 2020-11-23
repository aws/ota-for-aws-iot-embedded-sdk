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

#ifndef _OTA_OS_INTERFACE_H_
#define _OTA_OS_INTERFACE_H_

typedef uint32_t                 OtaErr_t;

struct OtaEventContext;
typedef struct OtaEventContext   OtaEventContext_t;

struct OtaTimerContext;
typedef struct OtaTimerContext   OtaTimerContext_t;

typedef enum
{
    OtaRequestTimer = 0,
    OtaSelfTestTimer,
    OtaNumOfTimers
} OtaTimerId_t;

/**
 * @brief Initialize the OTA events.
 *
 * This function initializes the OTA events mechanism.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @return               OtaErr_t, OtaErrorNone if success , other error code on failure.
 */

typedef OtaErr_t ( * OtaInitEvent_t ) ( OtaEventContext_t * pEventCtx );

/**
 * @brief Sends an OTA event.
 *
 * This function sends an event to OTA library event handler.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @param[pEventMsg]     Event to be sent to the OTA handler.
 *
 * @param[timeout]       The maximum amount of time (msec) the task should block.
 *
 * @return               OtaErr_t, OtaErrorNone if success , other error code on failure.
 */

typedef OtaErr_t ( * OtaSendEvent_t )( OtaEventContext_t * pEventCtx,
                                       const void * pEventMsg,
                                       unsigned int timeout );

/**
 * @brief Receive an OTA event.
 *
 * This function receives next event from the pending OTA events.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @param[pEventMsg]     Pointer to store message.
 *
 * @param[timeout]       The maximum amount of time the task should block.
 *
 * @return               OtaErr_t, OtaErrorNone if success , other error code on failure.
 */

typedef OtaErr_t ( * OtaReceiveEvent_t )( OtaEventContext_t * pEventCtx,
                                          void * pEventMsg,
                                          uint32_t timeout );

/**
 * @brief Deinitialize the OTA Events mechanism.
 *
 * This function deinitialize the OTA events mechanism and frees any resources
 * used.
 *
 * @param[pEventCtx]     Pointer to the OTA event context.
 *
 * @return               OtaErr_t, OtaErrorNone if success , other error code on failure.
 */

typedef OtaErr_t ( * OtaDeinitEvent_t )( OtaEventContext_t * pEventCtx );

/**
 * @brief Timer callback.
 *
 * Type definition for timer callback.
 *
 * @param[otaTimerId]       Timer ID of type otaTimerId_t
 *
 * @return                  OtaErr_t, OtaErrorNone if success , other error code on failure.
 */

typedef void ( * OtaTimerCallback_t )( OtaTimerId_t otaTimerId );

/**
 * @brief Start timer.
 *
 * This function starts the timer or resets it if it is already started.
 *
 * @param[otaTimerId]       Timer ID of type otaTimerId_t
 *
 * @param[pTimerName]       Timer name.
 *
 * @param[timeout]          Timeout for the timer in milliseconds.
 *
 * @param[callback]         Callback to be called when timer expires.
 *
 * @return                  OtaErr_t, OtaErrorNone if success , other error code on failure.
 */

typedef OtaErr_t ( * OtaStartTimer_t ) ( OtaTimerId_t otaTimerId,
                                         const char * const pTimerName,
                                         const uint32_t timeout,
                                         OtaTimerCallback_t callback );

/**
 * @brief Stop timer.
 *
 * This function stops the time.
 *
 * @param[otaTimerId]     Timer ID of type otaTimerId_t
 *
 * @return                OtaErr_t, OtaErrorNone if success , other error code on failure.
 */

typedef OtaErr_t ( * OtaStopTimer_t ) ( OtaTimerId_t otaTimerId );

/**
 * @brief Delete a timer.
 *
 * This function deletes a timer for POSIX platforms.
 *
 * @param[otaTimerId]       Timer ID of type otaTimerId_t
 *
 * @return                  OtaErr_t, OtaErrorNone if success , other error code on failure.
 */

typedef OtaErr_t ( * OtaDeleteTimer_t ) ( OtaTimerId_t otaTimerId );

/**
 * @brief Allocate memory.
 *
 * This function allocates the requested memory and returns a pointer to it.
 *
 * @param[size]        This is the size of the memory block, in bytes..
 *
 * @return             This function returns a pointer to the allocated memory, or NULL if
 *                     the request fails.
 */

typedef void * ( * OtaMalloc_t ) ( size_t size );

/**
 * @brief Free memory.
 *
 * This function deallocates the memory previously allocated by a call to allocation
 * function of type OtaMalloc_t.
 *
 * @param[ptr]         This is the pointer to a memory block previously allocated with function
 *                     of type OtaMalloc_t. If a null pointer is passed as argument, no action occurs.
 *
 * @return             None.
 */

typedef void ( * OtaFree_t ) ( void * ptr );

/**
 *  OTA Event Interface structure.
 */
typedef struct OtaEventInterface
{
    OtaInitEvent_t init;               /*!< Initialization event. */
    OtaSendEvent_t send;               /*!< Send data. */
    OtaReceiveEvent_t recv;            /*!< Receive data. */
    OtaDeinitEvent_t deinit;           /*!< Deinitialize event. */
    OtaEventContext_t * pEventContext; /*!< Event context to store event information. */
} OtaEventInterface_t;

/**
 *  OTA Retry Timer Interface.
 */
typedef struct OtaTimerInterface
{
    OtaStartTimer_t start;   /*!< Timer start state. */
    OtaStopTimer_t stop;     /*!< Timer stop state. */
    OtaDeleteTimer_t delete; /*!< Delete timer. */
} OtaTimerInterface_t;

/**
 *  OTA memory allocation interface.
 */
typedef struct OtaMallocInterface
{
    OtaMalloc_t malloc; /*!< OTA memory allocate interface. */
    OtaFree_t free;     /*!< OTA memory deallocate interface. */
} OtaMallocInterface_t;

/**
 * @brief  OTA OS Interface.
 */
typedef struct OtaOSInterface
{
    OtaEventInterface_t event; /*!< OTA Event interface. */
    OtaTimerInterface_t timer; /*!< OTA Timer interface. */
    OtaMallocInterface_t mem;  /*!< OTA memory interface. */
} OtaOSInterface_t;

#endif /* ifndef _OTA_OS_INTERFACE_H_ */
