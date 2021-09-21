#include "list.h"
#include "FreeRTOS.h"

struct tskTaskControlBlock;
typedef struct tskTaskControlBlock * TaskHandle_t;

/*
 * Defines the prototype to which the application task hook function must
 * conform.
 */
typedef BaseType_t (* TaskHookFunction_t)( void * );

