/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * Insert copyright notice
 */

/**
 * @file publishStatusMessage_harness.c
 * @brief Implements the proof harness for publishStatusMessage function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include "ota_mqtt_private.h"

#define TOPIC_JOB_STATUS_BUFFER_SIZE    222             /*!< Max buffer size for `jobs/notify-next` topic. */
#define OTA_STATUS_MSG_MAX_SIZE         128U            /*!< Max length of a job status message to the service. */

/* Declaration of the test function with the mangled name. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_publishStatusMessage( OtaAgentContext_t * pAgentCtx,
                                                                      const char * pMsg,
                                                                      uint32_t msgSize,
                                                                      uint8_t qos );

/* Stubs required for the test function. */
size_t stringBuilder( char * pBuffer,
                      size_t bufferSizeBytes,
                      const char * strings )
{
    size_t stringSize;

    /* The static size of the pBuffer in the unsubscribeFromDataStream function is
     *  defined by TOPIC_JOB_STATUS_BUFFER_SIZE. Hence, the value stringSize can
     *  never exceed TOPIC_JOB_STATUS_BUFFER_SIZE. */

    __CPROVER_assume( stringSize > 0 && stringSize < TOPIC_JOB_STATUS_BUFFER_SIZE );

    return stringSize;
}

/* This is a stub of an mqtt interface function required for the proof. */
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
    /* Insert argument declarations */
    OtaAgentContext_t * pAgentCtx;
    OtaMqttInterface_t mqtt;

    OtaAgentContext_t agent;
    OtaInterfaces_t otaInterface;

    char pMsg[ OTA_STATUS_MSG_MAX_SIZE ];
    uint32_t msgSize;
    uint8_t qos;

    /* Initialize the Mqtt interface. */
    mqtt.unsubscribe = publish;
    otaInterface.mqtt = mqtt;


    /* Initialize the agent with the interface. */
    agent.pOtaInterface = &otaInterface;
    pAgentCtx = &agent;

    /* The agent can never be NULL as it is defined as a global variable. */
    __CPROVER_assume( pAgentCtx != NULL );


    ( void ) __CPROVER_file_local_ota_mqtt_c_publishStatusMessage( pAgentCtx, pMsg, msgSize, qos );
}
