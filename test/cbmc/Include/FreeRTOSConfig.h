#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

/* Configuration parameters required for FreeRTOS headers. */
#define configUSE_16_BIT_TICKS                     0
#define configUSE_TRACE_FACILITY                   1
#define configUSE_MUTEXES                          1
#define configUSE_TIMERS                           1
#define configUSE_APPLICATION_TASK_TAG             1
#define configNUM_THREAD_LOCAL_STORAGE_POINTERS    16
#define configGENERATE_RUN_TIME_STATS              0
#define configUSE_NEWLIB_REENTRANT                 1

/* Memory allocation configuration */
#define configSUPPORT_DYNAMIC_ALLOCATION           1
#define configSUPPORT_STATIC_ALLOCATION            1
#define configMAX_TASK_NAME_LEN                    10

#define INCLUDE_xTaskAbortDelay                    1

#endif /* FREERTOS_CONFIG_H */
