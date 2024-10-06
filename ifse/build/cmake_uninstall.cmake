if(NOT EXISTS "/home/user/ifse/build/install_manifest.txt")
  message(FATAL_ERROR "Cannot find install manifest: "
          "/home/user/ifse/build/install_manifest.txt")
endif()

file(READ "/home/user/ifse/build/install_manifest.txt" files)
string(REGEX REPLACE "\n" ";" files "${files}")
foreach(file ${files})
  set(file_path "$ENV{DESTDIR}${file}")
  message(STATUS "Uninstalling ${file_path}")
  if(IS_SYMLINK "${file_path}" OR EXISTS "${file_path}")
    # We could use ``file(REMOVE ...)`` here but then we wouldn't
    # know if the removal failed.
    execute_process(COMMAND
      "/usr/bin/cmake" "-E" "remove" "${file_path}"
      RESULT_VARIABLE rm_retval
    )
    if(NOT "${rm_retval}" STREQUAL 0)
      message(FATAL_ERROR "Problem when removing \"${file_path}\"")
    endif()
  else()
    message(STATUS "File \"${file_path}\" does not exist.")
  endif()
endforeach()
