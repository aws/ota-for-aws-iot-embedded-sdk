#ifndef TIMERS_H
#define TIMERS_H

/* Data structures required for CBMC proofs of FreeRTOS dependent
 * functions in OTA. */
struct tmrTimerControl;
typedef struct tmrTimerControl * TimerHandle_t;

/*
 * Defines the prototype to which timer callback functions must conform.
 */
typedef void (* TimerCallbackFunction_t)( TimerHandle_t xTimer );

#endif
