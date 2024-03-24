configure_file(ffi.cpp "${CMAKE_BINARY_DIR}/util/ffi.cpp" @ONLY)


add_library(util OBJECT name.cpp name_set.cpp
  escaped.cpp bit_tricks.cpp ascii.cpp
  path.cpp lbool.cpp init_module.cpp list_fn.cpp
  timeit.cpp timer.cpp
  name_generator.cpp kvmap.cpp map_foreach.cpp
  options.cpp option_declarations.cpp shell.cpp
  "${CMAKE_BINARY_DIR}/util/ffi.cpp")



# Tracy
# -----
# https://stackoverflow.com/questions/54587052/cmake-on-mac-could-not-find-threads-missing-threads-found
# assume built-in pthreads on MacOS
IF(APPLE)
    set(CMAKE_THREAD_LIBS_INIT "-lpthread")
    set(CMAKE_HAVE_THREADS_LIBRARY 1)
    set(CMAKE_USE_WIN32_THREADS_INIT 0)
    set(CMAKE_USE_PTHREADS_INIT 1)
    set(THREADS_PREFER_PTHREAD_FLAG ON)
ENDIF()

# option(TRACY_NO_EXIT "" 1)
# option(TRACY_ENABLE "" ON)
# option(TRACY_ON_DEMAND "" ON)
# add_subdirectory(tracy) # target: TracyClient or alias Tracy::TracyClient
target_include_directories(util PUBLIC tracy/public/tracy/)
target_include_directories(util PUBLIC tracy/public/)
# target_link_libraries(util PUBLIC TracyClient)
