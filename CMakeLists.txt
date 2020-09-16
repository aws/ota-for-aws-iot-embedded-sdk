set(src_dir "${CMAKE_CURRENT_LIST_DIR}/source")
set(test_dir "${CMAKE_CURRENT_LIST_DIR}/test")

add_library(ota
    "${src_dir}/include/aws_iot_ota_agent.h"
    "${src_dir}/include/aws_iot_ota_types.h"
    "${src_dir}/aws_iot_ota_agent_internal.h"
    "${src_dir}/aws_iot_ota_agent.c"
    "${src_dir}/aws_iot_ota_interface.c"
    "${src_dir}/aws_iot_ota_interface.h"
    "${src_dir}/aws_iot_ota_pal.h"
)

# TODO, make sure, src_dir is in PRIVATE INCLUDE
target_include_directories(ota
    PUBLIC "${src_dir}/include" "${src_dir}/portable" "${src_dir}"
    # PRIVATE "${src_dir}"
)

# TODO, remove jsmn and mbedtls from dependencies
target_link_libraries(ota
    PUBLIC ota_os
    PRIVATE ota_mqtt ota_pal jsmn mbedtls
)

# Link to this INTERFACE target to enable the MQTT backend.
add_library(ota_mqtt INTERFACE)
target_sources(ota_mqtt
    INTERFACE
    "${src_dir}/mqtt/aws_iot_ota_cbor_internal.h"
    "${src_dir}/mqtt/aws_iot_ota_cbor.c"
    "${src_dir}/mqtt/aws_iot_ota_cbor.h"
    "${src_dir}/mqtt/aws_iot_ota_mqtt.c"
    "${src_dir}/mqtt/aws_iot_ota_mqtt.h"
)
target_link_libraries(ota_mqtt INTERFACE mqtt tinycbor)

# Link to this INTERFACE target to enable the HTTP backend.
add_library(ota_http INTERFACE)
target_sources(ota_http
    INTERFACE
    "${src_dir}/http/aws_iot_ota_http.c"
    "${src_dir}/http/aws_iot_ota_http.h"
)
target_link_libraries(ota_http INTERFACE http)
