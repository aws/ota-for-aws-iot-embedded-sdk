/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file publishStatusMessage_harness.c
 * @brief Implements the proof harness for publishStatusMessage function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

#define TOPIC_JOB_STATUS_BUFFER_SIZE    222U            /*!< Max buffer size of pBuffer in publishStatusMessage function. */
#define OTA_STATUS_MSG_MAX_SIZE         128U            /*!< Max length of a job status message to the service. */

/* Declaration of the test function with the mangled name. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_publishStatusMessage( OtaAgentContext_t * pAgentCtx,
                                                                      const char * pMsg,
                                                                      uint32_t msgSize,
                                                                      uint8_t qos );

/* Stubs required for the test function. */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringSize;

    /* pBuffer is initialized in publishStatusMessage function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    /* strings is initialized publishStatusMessage function before passing it to the
     * stringBuilder function and thus cannot be NULL. */
    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The static size of the pBuffer in the publishStatusMessage function is
     * defined by TOPIC_GET_STREAM_BUFFER_SIZE. Hence, the value stringSize can
     * never exceed TOPIC_GET_STREAM_BUFFER_SIZE. */
    __CPROVER_assume( stringSize > 0 && stringSize < TOPIC_JOB_STATUS_BUFFER_SIZE );

    return stringSize;
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

void publishStatusMessage_harness()
{
    OtaAgentContext_t * pAgentCtx;
    OtaMqttInterface_t mqtt;

    OtaAgentContext_t agent;
    OtaInterfaces_t otaInterface;

    /* pMsg is declared statically in the updateJobStatus_Mqtt and passed to publishStatusMessage function. */
    char pMsg[ OTA_STATUS_MSG_MAX_SIZE ];
    uint32_t msgSize;
    uint8_t qos;

    /* publish reference to the mqtt function is expected to be assigned by the user and thus
     * assumed not to be NULL. */
    mqtt.publish = publish;
    otaInterface.mqtt = mqtt;

    agent.pOtaInterface = &otaInterface;
    pAgentCtx = &agent;

    /* The agent can never be NULL as it is defined as a global variable. */
    __CPROVER_assume( pAgentCtx != NULL );

    ( void ) __CPROVER_file_local_ota_mqtt_c_publishStatusMessage( pAgentCtx, pMsg, msgSize, qos );
}
