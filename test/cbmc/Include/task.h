#ifndef INC_TASK_H
#define INC_TASK_H

#include "list.h"

/* Data structures required for CBMC proofs of FreeRTOS dependent
 * functions in OTA. */
struct tskTaskControlBlock;
typedef struct tskTaskControlBlock * TaskHandle_t;

typedef BaseType_t (* TaskHookFunction_t)( void * );

#endif /* ifndef INC_TASK_H */
