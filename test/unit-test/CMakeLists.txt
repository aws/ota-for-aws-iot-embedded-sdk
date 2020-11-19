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
    "${MODULE_ROOT_DIR}/source/portable/os"
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
    "${MODULE_ROOT_DIR}/source/ota_cbor.c"
    "${MODULE_ROOT_DIR}/source/portable/os/ota_os_posix.c"
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

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories ".")

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
    -lrt
)

list(APPEND utest_dep_list
    ${real_name}
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

create_test(ota_os_posix_utest
    "ota_os_posix_utest.c"
    "${utest_link_list}"
    "${utest_dep_list}"
    "${test_include_directories}"
)
# Disable unity memory handling since we need to free memory allocated from library.
target_compile_definitions(ota_cbor_utest PRIVATE UNITY_FIXTURE_NO_EXTRAS)

# Use Address sanitizer to check memory operations
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address -fsanitize=leak -g")