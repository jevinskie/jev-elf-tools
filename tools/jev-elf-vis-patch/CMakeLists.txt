add_executable(jev-elf-vis-patch jev-elf-vis-patch.cpp)
target_link_libraries(jev-elf-vis-patch PRIVATE LIB_LIEF fmt mio ScopeGuard)
