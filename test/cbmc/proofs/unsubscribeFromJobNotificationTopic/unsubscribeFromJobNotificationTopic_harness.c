/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file unsubscribeFromJobNotificationTopic_harness.c
 * @brief Implements the proof harness for unsubscribeFromJobNotificationTopic function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

/* Max buffer size of pBuffer in unsubscribeFromJobNotificationTopic function. */
#define TOPIC_NOTIFY_NEXT_BUFFER_SIZE    96                         /*!< Max buffer size for `jobs/notify-next` topic. */

/* Declaration of the test function with the mangled name. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_unsubscribeFromJobNotificationTopic( const OtaAgentContext_t * pAgentCtx );

/* Stub required to combine a set of strings(to form a topic). */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringSize;

    /* pBuffer is initialized in unsubscribeFromJobNotificationTopic function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized unsubscribeFromJobNotificationTopic function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The static size of the pBuffer in the unsubscribeFromJobNotificationTopic function is
     * defined by TOPIC_GET_STREAM_BUFFER_SIZE. Hence, the value stringSize can
     * never exceed TOPIC_GET_STREAM_BUFFER_SIZE. */
    __CPROVER_assume( stringSize > 0 && stringSize < TOPIC_NOTIFY_NEXT_BUFFER_SIZE );

    return stringSize;
}

/* Stub to user defined MQTT-Unsubscribe operation. */
OtaMqttStatus_t unsubscribe( const char * pTopicFilter,
                             uint16_t topicFilterLength,
                             uint8_t ucQoS )
{
    OtaMqttStatus_t status;

    return status;
}

/*****************************************************************************/

void unsubscribeFromJobNotificationTopic_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaMqttInterface_t mqtt;

    OtaAgentContext_t agent;
    OtaInterfaces_t otaInterface;


    /* unsubscribe reference to the mqtt function is expected to be assigned by the user and thus
     * assumed not to be NULL. */
    mqtt.unsubscribe = unsubscribe;
    otaInterface.mqtt = mqtt;

    agent.pOtaInterface = &otaInterface;
    pAgentCtx = &agent;

    /* The agent can never be NULL as it is defined as a global variable. */
    __CPROVER_assume( pAgentCtx != NULL );

    ( void ) __CPROVER_file_local_ota_mqtt_c_unsubscribeFromJobNotificationTopic( pAgentCtx );
}
