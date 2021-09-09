/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file cleanupControl_Mqtt_harness.c
 * @brief Implements the proof harness for cleanupControl_Mqtt function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

/* Stub required to unsubscribe from a job notification topic function. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_unsubscribeFromJobNotificationTopic( const OtaAgentContext_t * pAgentCtx )
{
    OtaMqttStatus_t mqttStatus;

    /* Since OTA agent is initialized before passing to unsubscribeFromJobNotificationTopic,
     * pAgentCtx is expected to be a non-NULL value. */
    __CPROVER_assert( pAgentCtx != NULL, "Unable to use pAgentCtx:"
                                         "Expected a non-NULL value." );

    return mqttStatus;
}

void cleanupControl_Mqtt_harness()
{
    OtaAgentContext_t agent;

    /* OTA agent is declared as a global variable in ota.c and thus cannot be NULL. */
    ( void ) cleanupControl_Mqtt( &agent );
}
