cmake_minimum_required(VERSION 3.5)
project(crazy-j)

add_compile_definitions(GC_THRESHOLD=1073741824)
#add_compile_definitions(GC_THRESHOLD=4294967296LL)

add_executable(crazy-j crazy-j.c)
#target_compile_options(lazy-k PUBLIC -Wl,-z,stacksize=0x40000000)
