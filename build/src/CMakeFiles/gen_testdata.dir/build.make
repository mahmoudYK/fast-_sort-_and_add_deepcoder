# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.5

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/mahmouka/master/deep_coder/deep-coder

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/mahmouka/master/deep_coder/deep-coder/build

# Include any dependencies generated for this target.
include src/CMakeFiles/gen_testdata.dir/depend.make

# Include the progress variables for this target.
include src/CMakeFiles/gen_testdata.dir/progress.make

# Include the compile flags for this target's objects.
include src/CMakeFiles/gen_testdata.dir/flags.make

src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o: src/CMakeFiles/gen_testdata.dir/flags.make
src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o: ../src/generate_testdata.cc
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mahmouka/master/deep_coder/deep-coder/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o"
	cd /home/mahmouka/master/deep_coder/deep-coder/build/src && /usr/bin/c++   $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/gen_testdata.dir/generate_testdata.cc.o -c /home/mahmouka/master/deep_coder/deep-coder/src/generate_testdata.cc

src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/gen_testdata.dir/generate_testdata.cc.i"
	cd /home/mahmouka/master/deep_coder/deep-coder/build/src && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mahmouka/master/deep_coder/deep-coder/src/generate_testdata.cc > CMakeFiles/gen_testdata.dir/generate_testdata.cc.i

src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/gen_testdata.dir/generate_testdata.cc.s"
	cd /home/mahmouka/master/deep_coder/deep-coder/build/src && /usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mahmouka/master/deep_coder/deep-coder/src/generate_testdata.cc -o CMakeFiles/gen_testdata.dir/generate_testdata.cc.s

src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o.requires:

.PHONY : src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o.requires

src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o.provides: src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o.requires
	$(MAKE) -f src/CMakeFiles/gen_testdata.dir/build.make src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o.provides.build
.PHONY : src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o.provides

src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o.provides.build: src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o


# Object files for target gen_testdata
gen_testdata_OBJECTS = \
"CMakeFiles/gen_testdata.dir/generate_testdata.cc.o"

# External object files for target gen_testdata
gen_testdata_EXTERNAL_OBJECTS =

src/gen_testdata: src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o
src/gen_testdata: src/CMakeFiles/gen_testdata.dir/build.make
src/gen_testdata: lib/libdeepcoder.a
src/gen_testdata: src/CMakeFiles/gen_testdata.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/mahmouka/master/deep_coder/deep-coder/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable gen_testdata"
	cd /home/mahmouka/master/deep_coder/deep-coder/build/src && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/gen_testdata.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
src/CMakeFiles/gen_testdata.dir/build: src/gen_testdata

.PHONY : src/CMakeFiles/gen_testdata.dir/build

src/CMakeFiles/gen_testdata.dir/requires: src/CMakeFiles/gen_testdata.dir/generate_testdata.cc.o.requires

.PHONY : src/CMakeFiles/gen_testdata.dir/requires

src/CMakeFiles/gen_testdata.dir/clean:
	cd /home/mahmouka/master/deep_coder/deep-coder/build/src && $(CMAKE_COMMAND) -P CMakeFiles/gen_testdata.dir/cmake_clean.cmake
.PHONY : src/CMakeFiles/gen_testdata.dir/clean

src/CMakeFiles/gen_testdata.dir/depend:
	cd /home/mahmouka/master/deep_coder/deep-coder/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/mahmouka/master/deep_coder/deep-coder /home/mahmouka/master/deep_coder/deep-coder/src /home/mahmouka/master/deep_coder/deep-coder/build /home/mahmouka/master/deep_coder/deep-coder/build/src /home/mahmouka/master/deep_coder/deep-coder/build/src/CMakeFiles/gen_testdata.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/CMakeFiles/gen_testdata.dir/depend

