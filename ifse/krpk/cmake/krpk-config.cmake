
find_path(KRPK_INCLUDE_DIR NAMES krpk.h PATHS ${CMAKE_CURRENT_LIST_DIR}/../include)
find_library(KRPK_LIBRARY libkrpk.so ${CMAKE_CURRENT_LIST_DIR}/../target/release ${CMAKE_CURRENT_LIST_DIR}/../target/debug)
if (KRPK_INCLUDE_DIR AND KRPK_LIBRARY)
    set(KRPK_FOUND TRUE)
endif ()