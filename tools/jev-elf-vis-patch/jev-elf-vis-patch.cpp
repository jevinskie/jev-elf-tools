#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <set>
#include <string>
#include <vector>
#include <unistd.h>

#include <fmt/format.h>
#include <fmt/ostream.h>
#include <LIEF/LIEF.hpp>
#include <mio/mmap.hpp>
#include <scope.h>

#define STN_UNDEF 0

using namespace std::string_literals;
using buf_t = std::vector<uint8_t>;

void delete_and_touch_file(const char *path, size_t sz = 0) {
    if (!::access(path, F_OK)) {
        int unlink_res = ::unlink(path);
        if (unlink_res != 0) {
            perror("unlink bad");
            exit(-1);
        }
    }
    int fd = open(path, O_CREAT | O_WRONLY | O_TRUNC, 0664);
    assert(fd > 0);
    assert(!close(fd));
    assert(!truncate(path, sz));
}

std::set<std::string> read_lines(const char *path) {
    std::set<std::string> res{};
    std::ifstream file{path};
    for (std::string line; std::getline(file, line); ) {
        res.emplace(line);
    }
    return res;
}

void set_exports(const std::set<std::string> &exported_sym_names, buf_t &symtab_buf, const buf_t &strtab_buf) {
    auto *sym_begin = (LIEF::ELF::Elf64_Sym *)symtab_buf.data();
    auto *sym_end = (LIEF::ELF::Elf64_Sym *)(symtab_buf.data() + symtab_buf.size());

    const auto *strtab_begin = (const char *)strtab_buf.data();
    const auto *strtab_end = (const char *)(strtab_buf.data() + strtab_buf.size());

    int i = 0;
    for (auto *p = sym_begin; p != sym_end; ++p, ++i) {
        const auto strtab_off = p->st_name;
        const auto sym_name = std::string{&strtab_begin[strtab_off]};
        const auto types = static_cast<LIEF::ELF::ELF_SYMBOL_TYPES>(p->st_info & 0x0f);
        const auto binding = static_cast<LIEF::ELF::SYMBOL_BINDINGS>(p->st_info >> 4);
        // fmt::print("sym[{:d}]: {:s} types: {} bind: {}\n", i, sym_name, (int)types, (int)binding);
        if (((int)binding == 1) && !exported_sym_names.contains(sym_name)) {
            p->st_info = (p->st_info & 0x0f) | (0 << 4);
            // fmt::print("changed binding on {:s} wow!\n", sym_name);
        } else if ((int)binding == 1) {
            fmt::print("not unexporting {:s} OK?\n", sym_name);
        }
    }
}

void tweak_vis(const std::set<std::string> &exported_sym_names, const char *in_elf_path, const char *out_elf_path) {
    auto in_fh = sr::make_unique_resource_checked(::open(in_elf_path, O_RDONLY), -1, &::close);
    auto in_buf = mio::mmap_source(in_fh.get(), 0, mio::map_entire_file);
    auto in_vec = buf_t(in_buf.begin(), in_buf.end());
    auto out_vec = buf_t(in_buf.begin(), in_buf.end());
    auto in_elf = LIEF::ELF::Parser::parse(in_vec, in_elf_path);
    fmt::print("in_elf: {}\n", in_elf);


    // auto exported_syms = in_elf->exported_symbols();
    // for (auto &sym : exported_syms) {
    //     std::string orig_name = sym.name();
    //     fmt::print("sym: name: {:s} val: {:#x}\n", orig_name, sym.value());
    // }

    const auto symtab_sec = in_elf->get_section(".symtab");
    fmt::print("symtab_sec: {:p}\n", (void*)&symtab_sec);
    auto symtab_buf = symtab_sec.content();

    const auto strtab_sec = in_elf->get_section(".strtab");
    fmt::print("strtab_sec: {:p}\n", (void*)&strtab_sec);
    const auto strtab_buf = strtab_sec.content();

    set_exports(exported_sym_names, symtab_buf, strtab_buf);
    std::copy(symtab_buf.begin(), symtab_buf.end(), out_vec.begin() + symtab_sec.offset());


    delete_and_touch_file(out_elf_path, out_vec.size());
    std::error_code rw_mmap_error;
    auto out_buf = mio::make_mmap_sink(out_elf_path, 0, out_vec.size(), rw_mmap_error);
    assert(!rw_mmap_error);
    std::copy(out_vec.begin(), out_vec.end(), out_buf.begin());
}

int main(int argc, const char **argv) {
    assert(argc == 4);
    auto exported_syms_file = argv[1];
    auto in_elf_path = argv[2];
    auto out_elf_path = argv[3];

    const auto exported_sym_names = read_lines(exported_syms_file);

    fmt::print("exporting: {}\n", fmt::join(exported_sym_names, ", "));

    tweak_vis(exported_sym_names, in_elf_path, out_elf_path);

    return 0;
}
