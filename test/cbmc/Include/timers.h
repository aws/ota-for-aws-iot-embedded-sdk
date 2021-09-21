#include "list.h"

/* The old naming convention is used to prevent breaking kernel aware debuggers. */
struct tmrTimerControl;
typedef struct tmrTimerControl * TimerHandle_t;

/*
 * Defines the prototype to which timer callback functions must conform.
 */
typedef void (* TimerCallbackFunction_t)( TimerHandle_t xTimer );
