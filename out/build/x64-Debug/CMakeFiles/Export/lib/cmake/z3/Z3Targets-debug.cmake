#----------------------------------------------------------------
# Generated CMake target import file for configuration "Debug".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "z3::libz3" for configuration "Debug"
set_property(TARGET z3::libz3 APPEND PROPERTY IMPORTED_CONFIGURATIONS DEBUG)
set_target_properties(z3::libz3 PROPERTIES
  IMPORTED_IMPLIB_DEBUG "${_IMPORT_PREFIX}/lib/libz3.lib"
  IMPORTED_LOCATION_DEBUG "${_IMPORT_PREFIX}/lib/libz3.dll"
  )

list(APPEND _IMPORT_CHECK_TARGETS z3::libz3 )
list(APPEND _IMPORT_CHECK_FILES_FOR_z3::libz3 "${_IMPORT_PREFIX}/lib/libz3.lib" "${_IMPORT_PREFIX}/lib/libz3.dll" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
