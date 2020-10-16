# Include filepaths for source and include.
include( ${MODULE_ROOT_DIR}/otaFilePaths.cmake )

# ====================  Define your project name (edit) ========================
set(project_name "aws_ota")

# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
list(APPEND mock_list
#    "${MODULE_ROOT_DIR}/dependency/coreJSON/source/include/core_json.h"
    "${MODULE_ROOT_DIR}/source/include/aws_iot_ota_pal.h"
)
# list the directories your mocks need
list(APPEND mock_include_list
    .
#    "${MODULE_ROOT_DIR}/dependency/coreJSON/source/include"
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
    "${MODULE_ROOT_DIR}/source/aws_iot_ota_agent.c"
    "${MODULE_ROOT_DIR}/source/aws_iot_ota_interface.c"
    "${MODULE_ROOT_DIR}/source/aws_ota_base64.c"
    "${MODULE_ROOT_DIR}/source/aws_iot_ota_mqtt.c"
    "${MODULE_ROOT_DIR}/source/aws_iot_ota_cbor.c"
    ${TINYCBOR_SOURCES}
    ${JSON_SOURCES}
)
# list the directories the module under test includes
list(APPEND real_include_directories
    .
    ${OTA_INCLUDE_PUBLIC_DIRS}
    ${OTA_INCLUDE_PRIVATE_DIRS}
    ${OTA_INCLUDE_OS_POSIX_DIRS}
)

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
    .
    ${OTA_INCLUDE_PUBLIC_DIRS}
)

# =============================  (end edit)  ===================================

set(mock_name "${project_name}_mock")
set(real_name "${project_name}_real")

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

list(APPEND utest_link_list
    -lpthread
    -l${mock_name}
    lib${real_name}.a
)

list(APPEND utest_dep_list
    ${real_name}
)

set(utest_name "aws_ota_utest")
create_test(aws_ota_utest
    "aws_ota_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)

create_test("aws_ota_base64_utest"
    "aws_ota_base64_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)

create_test("aws_ota_jobParsing_utest"
    "aws_ota_jobParsing_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)
