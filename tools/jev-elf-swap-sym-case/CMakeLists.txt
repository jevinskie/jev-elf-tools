add_executable(jev-elf-swap-sym-case jev-elf-swap-sym-case.cpp)
target_link_libraries(jev-elf-swap-sym-case PRIVATE LIB_LIEF fmt mio ScopeGuard)


target_compile_features(jev-elf-swap-sym-case
    PUBLIC
    cxx_std_20
)
