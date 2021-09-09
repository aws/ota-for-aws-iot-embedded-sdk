/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * @file initFileTransfer_Mqtt_harness.c
 * @brief Implements the proof harness for initFileTransfer_Mqtt function.
 */
/* Include headers for mqtt interface. */
#include "ota_mqtt_private.h"

/* Maximum size of the pBuffer for initFileTransfer_Mqtt function. */
#define TOPIC_STREAM_DATA_BUFFER_SIZE    96U


/* Stub required to combine a set of strings(to form a topic). */
size_t __CPROVER_file_local_ota_mqtt_c_stringBuilder( char * pBuffer,
                                                      size_t bufferSizeBytes,
                                                      const char * strings[] )
{
    size_t stringLength;

    __CPROVER_assert( pBuffer != NULL,
                      "Unable to use pBuffer: passed pointer value is NULL." );

    __CPROVER_assert( strings != NULL,
                      "Unable to use strings: passed pointer value is NULL." );

    /* The size of the static pbuffer is declared inside initFileTransfer_Mqtt
     * function. */
    __CPROVER_assume( stringLength > 0U && stringLength < TOPIC_STREAM_DATA_BUFFER_SIZE );

    return stringLength;
}

/* Stub to a user defined MQTT-subscribe function. */
OtaMqttStatus_t subscribe( const char * pTopicFilter,
                           uint16_t topicFilterLength,
                           uint8_t ucQoS )
{
    OtaMqttStatus_t status;

    return status;
}

/*********************************************************/

void initFileTransfer_Mqtt_harness()
{
    OtaAgentContext_t agent;
    OtaFileContext_t filecontext;
    OtaInterfaces_t pOtaInterface;

    /* subscribe reference to the mqtt function is expected to be assigned by the user and thus
     * assumed not to be NULL. */
    pOtaInterface.mqtt.subscribe = subscribe;
    agent.pOtaInterface = &pOtaInterface;

    /* initFileTransfer_Mqtt function is only called when there is a file
     * ready to be downloaded. Thus filecontext cannot be NULL */
    agent.fileContext = filecontext;

    /* OTA agent is defined as a global variable in ota.c and thus cannot be NULL.*/
    initFileTransfer_Mqtt( &agent );
}
