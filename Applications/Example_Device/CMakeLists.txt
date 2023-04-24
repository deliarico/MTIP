
cmake_minimum_required(VERSION 3.14)

project(DEVICE LANGUAGES CXX)

set(CMAKE_INCLUDE_CURRENT_DIR ON)

set(CMAKE_AUTOUIC ON)
set(CMAKE_AUTOMOC ON)
set(CMAKE_AUTORCC ON)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(CMAKE_PREFIX_PATH "/qt5-5.15/qtbase/lib/cmake/Qt5/") #indicate your path

find_package(QT NAMES Qt6 Qt5 COMPONENTS Core Network REQUIRED)
find_package(Qt${QT_VERSION_MAJOR} COMPONENTS Core Network REQUIRED)

add_library(MTIP SHARED IMPORTED)
set_property(TARGET MTIP PROPERTY IMPORTED_LOCATION  ${CMAKE_CURRENT_SOURCE_DIR}/../MTIP/libMTIP.so)

add_executable(DEVICE Device.cpp)
target_link_libraries(DEVICE Qt${QT_VERSION_MAJOR}::Core Qt${QT_VERSION_MAJOR}::Network dl MTIP)
