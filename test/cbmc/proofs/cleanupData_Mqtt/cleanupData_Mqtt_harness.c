/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file cleanupData_Mqtt_harness.c
 * @brief Implements the proof harness for cleanupData_Mqtt function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

/* Stub required for to unsubscribe from the firmware receive topic. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_unsubscribeFromDataStream( const OtaAgentContext_t * pAgentCtx )
{
    OtaMqttStatus_t mqttStatus;

    /* OTA agent is defined in the ota.c and thus should not be NULL. */
    __CPROVER_assert( pAgentCtx != NULL, "Unable to use pAgentCtx:"
                                         "Expected a non-NULL value." );

    return mqttStatus;
}

void cleanupData_Mqtt_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaAgentContext_t agent;

    /* OTA agent is declared globally in ota.c and thus cannot be NULL. */
    ( void ) cleanupData_Mqtt( &agent );
}
