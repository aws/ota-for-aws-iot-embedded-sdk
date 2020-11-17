# Include filepaths for source and include.
include( ${MODULE_ROOT_DIR}/otaFilePaths.cmake )

# ====================  Define your project name (edit) ========================
set(project_name "aws_ota")

# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
list(APPEND mock_list
    "${MODULE_ROOT_DIR}/source/include/ota_private.h"
    "${MODULE_ROOT_DIR}/source/include/ota_platform_interface.h"
)
# list the directories your mocks need
list(APPEND mock_include_list
    .
    "${MODULE_ROOT_DIR}/source/include"
    "${MODULE_ROOT_DIR}/source/portable"
)
#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
    ""
)

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
    "${MODULE_ROOT_DIR}/source/ota.c"
    "${MODULE_ROOT_DIR}/source/ota_interface.c"
    "${MODULE_ROOT_DIR}/source/ota_base64.c"
    "${MODULE_ROOT_DIR}/source/ota_mqtt.c"
    "${MODULE_ROOT_DIR}/source/ota_http.c"
    "${MODULE_ROOT_DIR}/source/ota_cbor.c"
    ${TINYCBOR_SOURCES}
    ${JSON_SOURCES}
    "utest_helpers.c"
)
# list the directories the module under test includes
list(APPEND real_include_directories
    "."
    ${OTA_INCLUDE_PUBLIC_DIRS}
    ${OTA_INCLUDE_PRIVATE_DIRS}
    ${OTA_INCLUDE_OS_POSIX_DIRS}
)

list(APPEND real_include_directories_http
    "../http_configs"
    ${OTA_INCLUDE_PUBLIC_DIRS}
    ${OTA_INCLUDE_PRIVATE_DIRS}
    ${OTA_INCLUDE_OS_POSIX_DIRS}
)

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories ".")

# =============================  (end edit)  ===================================

set(mock_name "${project_name}_mock")
set(real_name "${project_name}_real")
set(real_name_http "${project_name}_real_http")

create_mock_list(${mock_name}
    "${mock_list}"
    "${MODULE_ROOT_DIR}/tools/cmock/project.yml"
    "${mock_include_list}"
    "${mock_define_list}"
)

create_real_library(${real_name}
    "${real_source_files}"
    "${real_include_directories}"
    "${mock_name}"
)

create_real_library(${real_name_http}
    "${real_source_files}"
    "${real_include_directories_http}"
    "${mock_name}"
)

list(APPEND utest_link_list
    -lpthread
    -l${mock_name}
    lib${real_name}.a
)

list(APPEND utest_link_list_http
    -lpthread
    -l${mock_name}
    lib${real_name_http}.a
)

list(APPEND utest_dep_list
    ${real_name}
)

list(APPEND utest_dep_list_http
    ${real_name_http}
)

create_test(ota_utest
    "ota_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)

create_test(ota_base64_utest
    "ota_base64_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)

create_test(ota_job_parsing_utest
    "ota_job_parsing_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)

create_test(ota_cbor_utest
    "ota_cbor_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)

create_test(ota_http_utest
    "ota_http_utest.c"
    "${utest_link_list_http}"
    "${utest_dep_list_http}"
    "${test_include_directories}"
    "../http_configs"
)

# Disable unity memory handling since we need to free memory allocated from library.
target_compile_definitions(ota_cbor_utest PRIVATE UNITY_FIXTURE_NO_EXTRAS)
