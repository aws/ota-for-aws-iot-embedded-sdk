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
 * @file ota_interface.c
 * @brief Internal interface for setting the data and control planes.
 */

/* Standard library includes. */
#include <string.h>
#include <assert.h>

/* OTA interface includes. */
#include "ota_interface_private.h"

/* OTA transport interface includes. */

#if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) || ( configENABLED_CONTROL_PROTOCOL & OTA_CONTROL_OVER_MQTT )
    #include "ota_mqtt_private.h"
#endif

#if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP )
    #include "ota_http_private.h"
#endif

/* Check if primary protocol is enabled in aws_iot_ota_agent_config.h. */

#if !( configENABLED_DATA_PROTOCOLS & configOTA_PRIMARY_DATA_PROTOCOL )
    #error "Primary data protocol must be enabled in aws_iot_ota_agent_config.h"
#endif

void setControlInterface( OtaControlInterface_t * pControlInterface )
{
    assert( pControlInterface != NULL );

    #if ( configENABLED_CONTROL_PROTOCOL == OTA_CONTROL_OVER_MQTT )
        pControlInterface->requestJob = requestJob_Mqtt;
        pControlInterface->updateJobStatus = updateJobStatus_Mqtt;
        pControlInterface->cleanup = cleanupControl_Mqtt;
    #else
    #error "Enable MQTT control as control operations are only supported over MQTT."
    #endif
}

/**
 * @brief Set the data interface used by the OTA Agent for streaming file
 *        blocks based on the user configuration and job document.
 *
 *        - If only one of the protocols is enabled, then that protocol is set.
 *        - If the job document specifies which protocol to use, then that
 *          protocol will be used unless it is disabled.
 *        - If both of the protocols are enabled and the user lists both of
 *          them in the job document, then the higher priority protocol will
 *          be selected.
 */
OtaErr_t setDataInterface( OtaDataInterface_t * pDataInterface,
                           const uint8_t * pProtocol )
{
    OtaErr_t err = OtaErrNone;

    #if !( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) | ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) )
    #error "One or more of the data protocols must be set with configENABLED_DATA_PROTOCOLS."
    #elif !( ( configOTA_PRIMARY_DATA_PROTOCOL & OTA_DATA_OVER_MQTT ) | ( configOTA_PRIMARY_DATA_PROTOCOL & OTA_DATA_OVER_HTTP ) )
    #error "configOTA_PRIMARY_DATA_PROTOCOL must be set to OTA_DATA_OVER_MQTT or OTA_DATA_OVER_HTTP."
    #elif ( configOTA_PRIMARY_DATA_PROTOCOL >= ( OTA_DATA_OVER_MQTT | OTA_DATA_OVER_HTTP ) )
    #error "Invalid value for configOTA_PRIMARY_DATA_PROTOCOL: Value is expected to be OTA_DATA_OVER_MQTT or OTA_DATA_OVER_HTTP."
    #elif ( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) && !( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) )
        ( void ) pProtocol;
        pDataInterface->initFileTransfer = initFileTransfer_Mqtt;
        pDataInterface->requestFileBlock = requestFileBlock_Mqtt;
        pDataInterface->decodeFileBlock = decodeFileBlock_Mqtt;
        pDataInterface->cleanup = cleanupData_Mqtt;
    #elif ( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) && !( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) )
        ( void ) pProtocol;
        pDataInterface->initFileTransfer = initFileTransfer_Http;
        pDataInterface->requestFileBlock = requestDataBlock_Http;
        pDataInterface->decodeFileBlock = decodeFileBlock_Http;
        pDataInterface->cleanup = cleanupData_Http;
    #else /* if !( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) | ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) ) */
        char protocolBuffer[ OTA_PROTOCOL_BUFFER_SIZE ] = { 0 };
        bool httpInJobDoc = false;
        bool mqttInJobDoc = false;

        ( void ) memcpy( protocolBuffer, pProtocol, OTA_PROTOCOL_BUFFER_SIZE );
        httpInJobDoc = ( strstr( protocolBuffer, "HTTP" ) != NULL ) ? true : false;
        mqttInJobDoc = ( strstr( protocolBuffer, "MQTT" ) != NULL ) ? true : false;

        #if ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_MQTT )
            if( mqttInJobDoc == true )
            {
                pDataInterface->initFileTransfer = initFileTransfer_Mqtt;
                pDataInterface->requestFileBlock = requestFileBlock_Mqtt;
                pDataInterface->decodeFileBlock = decodeFileBlock_Mqtt;
                pDataInterface->cleanup = cleanupData_Mqtt;
            }
            else if( httpInJobDoc == true )
            {
                pDataInterface->initFileTransfer = initFileTransfer_Http;
                pDataInterface->requestFileBlock = requestDataBlock_Http;
                pDataInterface->decodeFileBlock = decodeFileBlock_Http;
                pDataInterface->cleanup = cleanupData_Http;
            }
            else
            {
                err = OtaErrInvalidDataProtocol;
            }
        #elif ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_HTTP )
            if( httpInJobDoc == true )
            {
                pDataInterface->initFileTransfer = initFileTransfer_Http;
                pDataInterface->requestFileBlock = requestDataBlock_Http;
                pDataInterface->decodeFileBlock = decodeFileBlock_Http;
                pDataInterface->cleanup = cleanupData_Http;
            }
            else if( mqttInJobDoc == true )
            {
                pDataInterface->initFileTransfer = initFileTransfer_Mqtt;
                pDataInterface->requestFileBlock = requestFileBlock_Mqtt;
                pDataInterface->decodeFileBlock = decodeFileBlock_Mqtt;
                pDataInterface->cleanup = cleanupData_Mqtt;
            }
            else
            {
                err = OtaErrInvalidDataProtocol;
            }
        #endif /* if ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_HTTP ) */
    #endif /* if !( ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) | ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) ) */

    return err;
}
