# CMakeList.txt: проект CMake для lab1_new; включите исходный код и определения,
# укажите здесь логику для конкретного проекта.
#
project(lab1_new)
# Добавьте источник в исполняемый файл этого проекта.
add_executable (lab1_new "lab1_new.cpp" )

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET lab1_new PROPERTY CXX_STANDARD 20)
endif()

# TODO: Добавьте тесты и целевые объекты, если это необходимо.
