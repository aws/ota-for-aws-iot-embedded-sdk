/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * Insert copyright notice
 */

/**
 * @file subscribeToJobNotificationTopics_harness.c
 * @brief Implements the proof harness for subscribeToJobNotificationTopics function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */

/* Inclue files required for the function. */
#include "ota_mqtt_private.h"

#define MAX_TOPIC_NOTIFY_NEXT_BUFFER_SIZE   96U

/* Mangled Name for static function subscribeToJobNotificationTopics. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_subscribeToJobNotificationTopics( const OtaAgentContext_t * pAgentCtx );

/* Stubs required for the test functions. */
size_t stringBuilder( char * pBuffer,
                      size_t bufferSizeBytes,
                      const char * strings[] )
{
    size_t stringLength;

    __CPROVER_assert(pBuffer != NULL, 
        "pBuffer is always statically initialized in the subscribeToJobNotificationTopics and hence cannot be NULL");

    __CPROVER_assert(strings != NULL,
        "strings is always statically initialized in the subscribeToJobNotificationTopics and hence cannot be NULL");

    /* The size of the static buffer is declared inside subscribeToJobNotificationTopics 
        function. */
    __CPROVER_assume( stringLength > 0U && stringLength < MAX_TOPIC_NOTIFY_NEXT_BUFFER_SIZE );

    return stringLength;
}

OtaMqttStatus_t subscribe( const char * pTopicFilter,
                           uint16_t topicFilterLength,
                           uint8_t ucQoS )
{
    OtaMqttStatus_t status;

    return status;
}

/*********************************************************/

void subscribeToJobNotificationTopics_harness()
{
    OtaAgentContext_t agent;
    OtaAgentContext_t * pAgentCtx;

    OtaInterfaces_t otaInterface;

    /* Initialize the mqtt interface with the resepctive subscribe
        function. */
    otaInterface.mqtt.subscribe = subscribe;

    /* Initialize the agent with the interface. */
    agent.pOtaInterface = &otaInterface;

    pAgentCtx = &agent;

    ( void ) __CPROVER_file_local_ota_mqtt_c_subscribeToJobNotificationTopics( pAgentCtx );
}
