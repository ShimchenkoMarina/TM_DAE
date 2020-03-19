# Copyright (C) Eta Scale AB. Licensed under the Eta Scale Open Source License. See the LICENSE file for details.
#include_directories(${SVF_INCLUDE_DIR})
include_directories(${PROJECTS_MAIN_SRC_DIR}/../../SVF-project/SVF/include)
set(CMAKE_BUILD_TYPE Debug)

add_library(TM_DAE_integrated SHARED
  TM_DAE_integrated.cpp
  ${PROJECTS_MAIN_SRC_DIR}/Util/Annotation/MetadataInfo.cpp
  ${PROJECTS_MAIN_INCLUDE_DIR}/Util/Analysis
  )




                   


