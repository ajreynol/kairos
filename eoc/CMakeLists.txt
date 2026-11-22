# kairos-eoc: the Kairos code-generation stage, built out of tree against the
# Ethos source tree that Logos pins (see scripts/get-deps.sh). It uses Ethos's
# own plugin infrastructure (cmake/EthosPlugin.cmake): the Ethos core as a
# static library and Ethos's src/main.cpp, with our stage selected through
# ETHOS_PLUGIN_HEADER / ETHOS_PLUGIN_CLASS. Nothing in Ethos is patched.
#
#   cmake -S eoc -B build/eoc -DETHOS_SOURCE_DIR=<ethos tree>
#   cmake --build build/eoc --target kairos-eoc
cmake_minimum_required(VERSION 3.12)
project(kairos_eoc LANGUAGES CXX)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if(NOT ETHOS_SOURCE_DIR)
  message(FATAL_ERROR "ETHOS_SOURCE_DIR must name the pinned Ethos tree "
                      "(scripts/get-deps.sh sets it)")
endif()
get_filename_component(ETHOS_SOURCE_DIR "${ETHOS_SOURCE_DIR}" ABSOLUTE)
if(NOT EXISTS "${ETHOS_SOURCE_DIR}/cmake/EthosPlugin.cmake")
  message(FATAL_ERROR "${ETHOS_SOURCE_DIR} has no cmake/EthosPlugin.cmake")
endif()
list(APPEND CMAKE_MODULE_PATH "${ETHOS_SOURCE_DIR}/cmake")

find_package(GMP REQUIRED)
include(EthosPlugin)

ethos_set_default_build_type()
ethos_add_core_library(kairos-ethos-core)

option(KAIROS_WERROR "Treat warnings in Kairos's own sources as errors" OFF)

# The shared meta-reduction layer of Ethos's plugins, which our stage derives
# from. It is not a stable API; the Logos pin is what keeps it fixed.
set(ETHOS_PLUGIN_LAYER
    "${ETHOS_SOURCE_DIR}/plugins/std_plugin.cpp"
    "${ETHOS_SOURCE_DIR}/plugins/meta_reduce_plugin.cpp"
    "${ETHOS_SOURCE_DIR}/plugins/utils.cpp"
    "${ETHOS_SOURCE_DIR}/plugins/native_layer.cpp")

set(KAIROS_SRC "${CMAKE_CURRENT_LIST_DIR}/kairos_meta/kairos_meta_reduce.cpp")

add_ethos_plugin_executable(kairos-eoc
  PLUGIN_HEADER "kairos_meta/kairos_meta_reduce.h"
  PLUGIN_CLASS ethos::KairosMetaReduce
  SOURCES ${KAIROS_SRC} ${ETHOS_PLUGIN_LAYER})
ethos_configure_target(kairos-eoc)
target_include_directories(kairos-eoc PRIVATE "${ETHOS_SOURCE_DIR}/plugins")
target_link_libraries(kairos-eoc PRIVATE kairos-ethos-core)
if(KAIROS_WERROR)
  set_source_files_properties(${KAIROS_SRC} PROPERTIES COMPILE_OPTIONS "-Werror")
endif()

# Templates are read from this directory (kairos_meta/templates/...), never
# from the Ethos tree; output defaults to the build tree and is overridden by
# ETHOS_PLUGIN_OUTPUT_DIR in scripts/generate.sh.
target_compile_definitions(kairos-eoc PRIVATE
  ETHOS_PLUGIN_SOURCE_DIR="${CMAKE_CURRENT_LIST_DIR}"
  ETHOS_PLUGIN_OUTPUT_DIR="${PROJECT_BINARY_DIR}/out")
