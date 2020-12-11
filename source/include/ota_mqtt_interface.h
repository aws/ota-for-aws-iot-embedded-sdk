/*
 * AWS IoT Over-the-air Update v2.0.0 (Release Candidate)
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
 */

/**
 * @file ota_mqtt_interface.h
 * @brief Contains OTA MQTT Statuses, function type definitions and mqtt interface structure.
 */

#ifndef OTA_MQTT_INTERFACE_H
#define OTA_MQTT_INTERFACE_H

/* Standard library includes. */
#include <stddef.h>
#include <stdint.h>

/**
 * @ingroup ota_enum_types
 * @brief The OTA MQTT interface return status.
 */
typedef enum OtaMqttStatus
{
    OtaMqttSuccess = 0,          /*!< @brief OTA MQTT interface success. */
    OtaMqttPublishFailed = 0xa0, /*!< @brief Attempt to publish a MQTT message failed. */
    OtaMqttSubscribeFailed,      /*!< @brief Failed to subscribe to a topic. */
    OtaMqttUnsubscribeFailed     /*!< @brief Failed to unsubscribe from a topic. */
} OtaMqttStatus_t;

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
 * @return                      OtaMqttSuccess if success , other error code on failure.
 */

typedef OtaMqttStatus_t ( * OtaMqttSubscribe_t ) ( const char * pTopicFilter,
                                                   uint16_t topicFilterLength,
                                                   uint8_t ucQoS );

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
 * @return                      OtaMqttSuccess if success , other error code on failure.
 */

typedef OtaMqttStatus_t ( * OtaMqttUnsubscribe_t )  ( const char * pTopicFilter,
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
 * @return                      OtaMqttSuccess if success , other error code on failure.
 */
typedef OtaMqttStatus_t ( * OtaMqttPublish_t )( const char * const pacTopic,
                                                uint16_t usTopicLen,
                                                const char * pcMsg,
                                                uint32_t ulMsgSize,
                                                uint8_t ucQos );

/**
 * @ingroup ota_struct_types
 * @brief OTA Event Interface structure.
 */
typedef struct OtaMqttInterface
{
    OtaMqttSubscribe_t subscribe;     /*!< @brief Interface for subscribing to Mqtt topics. */
    OtaMqttUnsubscribe_t unsubscribe; /*!< @brief interface for unsubscribing to MQTT topics. */
    OtaMqttPublish_t publish;         /*!< @brief Interface for publishing MQTT messages. */
} OtaMqttInterface_t;

#endif /* ifndef OTA_MQTT_INTERFACE_H */
