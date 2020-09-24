# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# OTA library source files.
set( OTA_SOURCES
    "${CMAKE_CURRENT_LIST_DIR}/source/include/aws_iot_ota_agent.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/include/aws_iot_ota_types.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/aws_iot_ota_agent_internal.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/aws_iot_ota_agent.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/aws_iot_ota_interface.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/aws_iot_ota_interface.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/portable/aws_iot_ota_pal.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/portable/ota_os_interface.h"
)

# OTA library public include directories.
set( OTA_INCLUDE_PUBLIC_DIRS
    "${CMAKE_CURRENT_LIST_DIR}/source/include"
    "${CMAKE_CURRENT_LIST_DIR}/source/portable"
)

# OTA library private include directories.
set( OTA_INCLUDE_PRIVATE_DIRS
    "${CMAKE_CURRENT_LIST_DIR}/source"
)

# OTA library MQTT backend source files.
set( OTA_MQTT_SOURCES
    "${CMAKE_CURRENT_LIST_DIR}/source/mqtt/aws_iot_ota_cbor_internal.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/mqtt/aws_iot_ota_cbor.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/mqtt/aws_iot_ota_cbor.h"
    "${CMAKE_CURRENT_LIST_DIR}/source/mqtt/aws_iot_ota_mqtt.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/mqtt/aws_iot_ota_mqtt.h"
)

# OTA library HTTP backend source files.
set( OTA_HTTP_SOURCES
    "${CMAKE_CURRENT_LIST_DIR}/source/http/aws_iot_ota_http.c"
    "${CMAKE_CURRENT_LIST_DIR}/source/http/aws_iot_ota_http.h"
)
