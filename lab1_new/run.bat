cd build
cmake ..
msbuild lab1_new.sln
cd ..
start "" /B "build\debug\lab1_new.exe"
z3.exe smt.smt2