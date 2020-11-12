/*
 * FreeRTOS OTA V1.2.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#ifndef _OTA_MQTT_INTERFACE_H_
#define _OTA_MQTT_INTERFACE_H_

/* Standard library includes. */
#include <stddef.h>
#include <stdint.h>

/**
 * @brief OTA Error type.
 */
typedef uint32_t OtaErr_t;

/**
 * @brief OTA Mqtt callback.
 */
typedef void ( * OtaMqttCallback_t )( void * pvParam );

/**
 * @brief Subscribe to the Mqtt topics.
 *
 * This function subscribes to the Mqtt topics with the Quality of service
 * received as parameter. This function also registers a callback for the
 * topicfilter.
 *
 * @param[pTopicFilter]         Mqtt topic filter.
 *
 * @param[topicFilterLength]    Length of the topic filter.
 *
 * @param[ucQoS]                Quality of Service
 *
 * @param[pvCallback]           Callback to be registered.
 *
 * @return                      OTA_OS_ERR_OK if success , other error code on failure.
 */

typedef OtaErr_t ( * OtaMqttSubscribe_t ) ( const char * pTopicFilter,
                                            uint16_t topicFilterLength,
                                            uint8_t ucQoS,
                                            OtaMqttCallback_t callback );

/**
 * @brief Unsubscribe to the Mqtt topics.
 *
 * This function unsubscribes to the Mqtt topics with the Quality of service
 * received as parameter.
 *
 * @param[pTopicFilter]         Mqtt topic filter.
 *
 * @param[topicFilterLength]    Length of the topic filter.
 *
 * @param[ucQoS]                Quality of Service
 *
 * @return                      OTA_OS_ERR_OK if success , other error code on failure.
 */

typedef OtaErr_t ( * OtaMqttUnsubscribe_t )  ( const char * pTopicFilter,
                                               uint16_t topicFilterLength,
                                               uint8_t ucQoS );

/**
 * @brief Publish message to a topic.
 *
 * This function publishes a message to a given topic & QoS.
 *
 * @param[pacTopic]             Mqtt topic filter.
 *
 * @param[usTopicLen]           Length of the topic filter.
 *
 * @param[pcMsg]                Message to publish.
 *
 * @param[ulMsgSize]            Message size.
 *
 * @param[ucQoS]                Quality of Service
 *
 * @return                      OTA_OS_ERR_OK if success , other error code on failure.
 */
typedef OtaErr_t ( * OtaMqttPublish_t )( const char * const pacTopic,
                                         uint16_t usTopicLen,
                                         const char * pcMsg,
                                         uint32_t ulMsgSize,
                                         uint8_t ucQos );

/**
 *  OTA Event Interface structure.
 */
typedef struct OtaMqttInterface
{
    OtaMqttSubscribe_t subscribe;       /*!< Interface for subscribing to Mqtt topics. */
    OtaMqttUnsubscribe_t unsubscribe;   /*!< interface for unsubscribing to MQTT topics. */
    OtaMqttPublish_t publish;           /*!< Interface for publishing MQTT messages. */
    OtaMqttCallback_t jobCallback;      /*!< Interface for a callback that notifies the OTA library when a job document is received. */
    OtaMqttCallback_t dataCallback;     /*!< Interface for a callback that notifies the OTA library when a data block is received. */
} OtaMqttInterface_t;

#endif /* ifndef _OTA_MQTT_INTERFACE_H_ */
