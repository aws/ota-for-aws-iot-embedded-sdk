/*
 * FreeRTOS OTA V2.0.0
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

OtaErr_t setDataInterface( OtaDataInterface_t * pDataInterface,
                           const uint8_t * pProtocol )
{
    assert( pDataInterface != NULL );
    assert( pProtocol != NULL );

    OtaErr_t err = OtaErrorInvalidDataProtocol;
    uint32_t i;

    /*
     * Primary data protocol will be the protocol used for file download if more
     * than one protocol is selected while creating OTA job.
     */
    #if ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_MQTT )
        const char * pProtocolPriority[ OTA_DATA_NUM_PROTOCOLS ] =
        {
            "MQTT",
            "HTTP"
        };
    #elif ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_HTTP )
        const char * pProtocolPriority[ OTA_DATA_NUM_PROTOCOLS ] =
        {
            "HTTP",
            "MQTT"
        };
    #endif /* if ( configOTA_PRIMARY_DATA_PROTOCOL == OTA_DATA_OVER_MQTT ) */

    for( i = 0; i < OTA_DATA_NUM_PROTOCOLS; i++ )
    {
        if( NULL != strstr( ( const char * ) pProtocol, pProtocolPriority[ i ] ) )
        {
            #if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT )
                if( strcmp( pProtocolPriority[ i ], "MQTT" ) == 0 )
                {
                    pDataInterface->initFileTransfer = initFileTransfer_Mqtt;
                    pDataInterface->requestFileBlock = requestFileBlock_Mqtt;
                    pDataInterface->decodeFileBlock = decodeFileBlock_Mqtt;
                    pDataInterface->cleanup = cleanupData_Mqtt;

                    LogInfo( ( "Data interface is set to MQTT.\r\n" ) );

                    err = OtaErrorNone;
                    break;
                }
            #endif /* if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_MQTT ) */

            #if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP )
                if( strcmp( pProtocolPriority[ i ], "HTTP" ) == 0 )
                {
                    pDataInterface->initFileTransfer = initFileTransfer_Http;
                    pDataInterface->requestFileBlock = requestDataBlock_Http;
                    pDataInterface->decodeFileBlock = decodeFileBlock_Http;
                    pDataInterface->cleanup = cleanupData_Http;

                    LogInfo( ( "Data interface is set to HTTP.\r\n" ) );

                    err = OtaErrorNone;
                    break;
                }
            #endif /* if ( configENABLED_DATA_PROTOCOLS & OTA_DATA_OVER_HTTP ) */
        }
    }

    return err;
}
