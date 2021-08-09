/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * Insert copyright notice
 */

/**
 * @file unsubscribeFromDataStream_harness.c
 * @brief Implements the proof harness for unsubscribeFromDataStream function.
 */

/*
 * Insert project header files that
 *   - include the declaration of the function
 *   - include the types needed to declare function arguments
 */
#include "ota_mqtt_private.h"

#define TOPIC_GET_STREAM_BUFFER_SIZE 144    /* Max buffer size for `streams/<stream_name>/data/cbor` topic. */ 

/* Declaration of the test function with the mangled name. */
OtaMqttStatus_t __CPROVER_file_local_ota_mqtt_c_unsubscribeFromDataStream(const OtaAgentContext_t * pAgentCtx );


/* Stubs required for the test function. */
size_t stringBuilder(char* pBuffer, size_t bufferSizeBytes, const char* strings){
	size_t stringSize; 
	
    /* The static size of the pBuffer in the unsubscribeFromDataStream function is
        defined by TOPIC_GET_STREAM_BUFFER_SIZE. Hence, the value stringSize can 
        never exceed TOPIC_GET_STREAM_BUFFER_SIZE. */
    __CPROVER_assume(stringSize > 0 && stringSize < TOPIC_GET_STREAM_BUFFER_SIZE);

	return stringSize;
}

/* This is a stub of an mqtt interface function required for the proof. */
OtaMqttStatus_t unsubscribe(const char * pTopicFilter,
						   uint16_t topicFilterLength,
							uint8_t ucQoS ){

	OtaMqttStatus_t status; 
	
	return status; 
}

/*****************************************************************************/

void unsubscribeFromDataStream_harness()
{
    OtaAgentContext_t* pAgentCtx;
    OtaMqttInterface_t mqtt;

    OtaAgentContext_t agent;
    OtaInterfaces_t otaInterface; 


    /* Initialize the Mqtt interface. */
    mqtt.unsubscribe = unsubscribe;
    otaInterface.mqtt = mqtt;


    /* Initialize the agent with the interface. */ 
    agent.pOtaInterface = &otaInterface;
    pAgentCtx = &agent;

    /* The agent can never be NULL as it is defined as a global variable. */
    __CPROVER_assume(pAgentCtx != NULL);

    (void)__CPROVER_file_local_ota_mqtt_c_unsubscribeFromDataStream ( pAgentCtx );
}
