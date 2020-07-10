# Install script for directory: C:/Users/bottl/source/repos/z3/src

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "C:/Users/bottl/Source/Repos/z3/out/install/x64-Debug")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Debug")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY OPTIONAL FILES "C:/Users/bottl/source/repos/z3/out/build/x64-Debug/libz3.lib")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE SHARED_LIBRARY FILES "C:/Users/bottl/source/repos/z3/out/build/x64-Debug/libz3.dll")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include" TYPE FILE FILES
    "C:/Users/bottl/source/repos/z3/src/api/z3_algebraic.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_api.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_ast_containers.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_fixedpoint.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_fpa.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3.h"
    "C:/Users/bottl/source/repos/z3/src/api/c++/z3++.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_macros.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_optimization.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_polynomial.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_rcf.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_v1.h"
    "C:/Users/bottl/source/repos/z3/src/api/z3_spacer.h"
    "C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/util/z3_version.h"
    )
endif()

if(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/util/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/polynomial/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/sat/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/nlsat/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/util/lp/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/hilbert/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/simplex/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/automata/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/interval/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/realclosure/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/subpaving/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ast/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ast/rewriter/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ast/normal_forms/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/model/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ast/substitution/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/parsers/util/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/grobner/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/euclid/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/core/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/math/subpaving/tactic/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/aig/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/solver/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/sat/tactic/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/arith/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/nlsat/tactic/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ackermannization/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/cmd_context/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/cmd_context/extra_cmds/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/parsers/smt2/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ast/proofs/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ast/fpa/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ast/macros/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ast/pattern/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/ast/rewriter/bit_blaster/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/smt/params/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/smt/proto_model/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/smt/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/bv/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/smt/tactic/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/sls/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/qe/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/base/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/dataflow/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/transforms/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/rel/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/clp/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/tab/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/bmc/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/ddnf/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/spacer/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/muz/fp/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/ufbv/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/sat/sat_solver/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/smtlogics/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/fpa/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/fd_solver/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/tactic/portfolio/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/opt/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/api/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/api/dll/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/shell/cmake_install.cmake")
  include("C:/Users/bottl/source/repos/z3/out/build/x64-Debug/src/test/cmake_install.cmake")

endif()

