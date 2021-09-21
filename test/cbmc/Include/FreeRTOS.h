#ifndef INC_FREERTOS_H
#define INC_FREERTOS_H

#include "FreeRTOSConfig.h"
#include <stdint.h>

/* Data types required for CBMC proofs of FreeRTOS dependent
 * functions in OTA. */

/**
 * @brief Type definitions
 */
#define portBASE_TYPE     int
#define portSTACK_TYPE    uint32_t

typedef portBASE_TYPE    BaseType_t;
typedef portSTACK_TYPE   StackType_t;
typedef unsigned long    UBaseType_t;

#if ( configUSE_16_BIT_TICKS == 1 )
    typedef uint16_t     TickType_t;
    #define portMAX_DELAY    ( TickType_t ) 0xffff
#else
    typedef uint32_t     TickType_t;
    #define portMAX_DELAY    ( TickType_t ) 0xffffffffUL
#endif

#define pdFALSE              ( ( BaseType_t ) 0 )
#define pdTRUE               ( ( BaseType_t ) 1 )

struct xSTATIC_MINI_LIST_ITEM
{
    #if ( configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES == 1 )
        TickType_t xDummy1;
    #endif
    TickType_t xDummy2;
    void * pvDummy3[ 2 ];
};
typedef struct xSTATIC_MINI_LIST_ITEM StaticMiniListItem_t;

typedef struct xSTATIC_LIST
{
    #if ( configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES == 1 )
        TickType_t xDummy1;
    #endif
    UBaseType_t uxDummy2;
    void * pvDummy3;
    StaticMiniListItem_t xDummy4;
    #if ( configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES == 1 )
        TickType_t xDummy5;
    #endif
} StaticList_t;

typedef struct xSTATIC_QUEUE
{
    void * pvDummy1[ 3 ];

    union
    {
        void * pvDummy2;
        UBaseType_t uxDummy2;
    } u;

    StaticList_t xDummy3[ 2 ];
    UBaseType_t uxDummy4[ 3 ];
    uint8_t ucDummy5[ 2 ];

    #if ( ( configSUPPORT_STATIC_ALLOCATION == 1 ) && ( configSUPPORT_DYNAMIC_ALLOCATION == 1 ) )
        uint8_t ucDummy6;
    #endif

    #if ( configUSE_QUEUE_SETS == 1 )
        void * pvDummy7;
    #endif

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxDummy8;
        uint8_t ucDummy9;
    #endif
} StaticQueue_t;

#endif /* INC_FREERTOS_H */
