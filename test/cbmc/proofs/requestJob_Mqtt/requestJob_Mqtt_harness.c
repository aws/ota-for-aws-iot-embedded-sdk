/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file requestJob_Mqtt_harness.c
 * @brief Implements the proof harness for requestJob_Mqtt function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

/* Stubs required for the test functions. */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringLength;

    /* pBuffer is initialized in requestJob_Mqtt function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized requestJob_Mqtt function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The size of the static pbuffer is declared inside requestJob_Mqtt
     * function. */
    __CPROVER_assume( stringLength > 0U && stringLength < bufferSizeBytes );

    return stringLength;
}

size_t __CPROVER_file_local_ota_mqtt_c_stringBuilderUInt32Decimal( char * pBuffer,
                                                                   size_t bufferSizeBytes,
                                                                   uint32_t value )
{
    size_t buffersize;

    /* pBuffer is always initialized before passing it to the stringBuilderUInt32Decimal
     * function and thus should not be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );


    return buffersize;
}

OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_subscribeToJobNotificationTopics( const OtaAgentContext_t * pAgentCtx )
{
    OtaMqttStatus_t mqttStatus;

    return mqttStatus;
}

OtaMqttStatus_t publish( const char * const pacTopic,
                         uint16_t usTopicLen,
                         const char * pcMsg,
                         uint32_t ulMsgSize,
                         uint8_t ucQoS )
{
    OtaMqttStatus_t status;

    return status;
}

/*****************************************************************************/

void requestJob_Mqtt_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaMqttInterface_t mqtt;
    OtaAgentContext_t agent;
    OtaInterfaces_t otaInterface;

    /* publish reference to the mqtt function is expected to be assigned by the user and thus
     * assumed not to be NULL. */
    mqtt.publish = publish;
    otaInterface.mqtt = mqtt;

    agent.pOtaInterface = &otaInterface;
    pAgentCtx = &agent;

    /* OTA agent is defined globally in ota.c and thus cannot be NULL. */
    __CPROVER_assume( pAgentCtx != NULL );

    requestJob_Mqtt( pAgentCtx );
}
