cmake_minimum_required(VERSION 3.10)

project(deviceconsole)

set(CMAKE_CXX_STANDARD 11)

include_directories(.)

add_executable(deviceconsole
        main.c)
#add_executable(dsce
#        dsce.c)
set_target_properties(deviceconsole PROPERTIES LINK_FLAGS "-F/System/Library/PrivateFrameworks")

target_link_libraries(deviceconsole
        "-framework MobileDevice"
        "-framework CoreFoundation"
        objc)
