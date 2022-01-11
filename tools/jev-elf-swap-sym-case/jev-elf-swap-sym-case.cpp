#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <set>
#include <string>
#include <vector>
#include <unistd.h>

#include <fmt/format.h>
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

uint32_t elf_hash(const char *name)
{
    uint32_t h = 0, g;
    const uint8_t *uname = (const uint8_t*)name;
    while (*uname)
    {
        h = (h << 4) + *uname++;
        if ((g = h & 0xf0000000)) {
            h ^= g >> 24;
        }
        h &= ~g;
    }
    return h;
}

char swap_case_char(char c) {
    if (std::islower(c)) {
        return std::toupper(c); 
    } else {
        return std::tolower(c); 
    }
}

std::string swap_case(const std::string &str) {
    std::string res = str;
    std::transform(res.begin(), res.end(), res.begin(), swap_case_char);
    return res;
}

void swap_case_dirty(const char *in_elf_path, const char *out_elf_path) {
    auto in_elf = LIEF::ELF::Parser::parse(in_elf_path);

    for (auto &sym : in_elf->exported_symbols()) {
        std::string orig_name = sym.name();
        auto swapped_name = swap_case(orig_name);
        assert(swapped_name != orig_name);
        fmt::print("sym: name: {:s} val: {:#x} swapped: {:s}\n", orig_name, sym.value(), swapped_name);
        sym.name(swapped_name);
    }

    in_elf->write(out_elf_path);
}

void swap_case_strtab(std::set<std::string> targets, buf_t &strtab_buf) {
    auto *strtab_begin = (char *)strtab_buf.data();
    auto *strtab_end = (char *)(strtab_buf.data() + strtab_buf.size());

    std::vector<std::string> suffix_blocklist{
        "_init",
        "sleep",
        "alarm",
        "remove",
        "shutdown",
        "free",
        "perror",
        "time",
    };

    int i = 0;
    for (auto *p = strtab_begin; p < strtab_end; p += strlen(p) + 1) {
        fmt::print(stderr, "strtab str[{:d}] = '{:s}' before\n", i, p);
        auto sym_name = std::string(p);
        if (targets.contains(sym_name)) {
            auto sym_name_swapped = swap_case(sym_name);
            bool suffix_blocked = false;
            std::string final_blocked_suffix;
            for (const auto &blocked_suffix : suffix_blocklist) {
                if (sym_name.ends_with(blocked_suffix)) {
                    suffix_blocked = true;
                    final_blocked_suffix = blocked_suffix;
                    break;
                }
            }
            if (suffix_blocked) {
                fmt::print(stderr, "sym '{:s}' ends with '{:s}', swapping first alpha char\n", sym_name, final_blocked_suffix);
                sym_name_swapped = sym_name;
                auto idx = sym_name_swapped.find_first_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ");
                if (idx != std::string::npos) {
                    sym_name_swapped[idx] = swap_case_char(sym_name_swapped[idx]);
                }
            }
            std::copy(sym_name_swapped.begin(), sym_name_swapped.end(), p);
        }
        fmt::print(stderr, "strtab str[{:d}] = '{:s}' after\n", i, p);
        ++i;
    }
}

void swap_case_shstrtab_hashes(buf_t &strtab_buf) {
    auto *strtab_begin = (char *)strtab_buf.data();
    auto *strtab_end = (char *)(strtab_buf.data() + strtab_buf.size());
    std::set<std::string> targets{".gnu.hash", ".hash"};
    // std::set<std::string> targets{".gnu.hash"};

    int i = 0;
    for (auto *p = strtab_begin; p < strtab_end; p += strlen(p) + 1) {
        fmt::print(stderr, "shstrtab str[{:d}] = '{:s}' before\n", i, p);
        auto sec_name = std::string(p);
        if (targets.contains(sec_name)) {
            auto sec_name_swapped = swap_case(sec_name);
            std::copy(sec_name_swapped.begin(), sec_name_swapped.end(), p);
        }
        fmt::print(stderr, "shstrtab str[{:d}] = '{:s}' after\n", i, p);
        ++i;
    }
}

void sysv_rehash(const buf_t &dynstr_buf, const buf_t &dynsym_buf, buf_t &hash_buf) {
    auto *hash_begin = (char *)hash_buf.data();
    auto *hash_end = (char *)(hash_buf.data() + hash_buf.size());


    const auto *strtab_begin = (char *)dynstr_buf.data();
    const auto *strtab_end = (char *)(dynstr_buf.data() + dynstr_buf.size());

    const auto *sym_begin = (const LIEF::ELF::Elf64_Sym *)dynsym_buf.data();
    const auto *sym_end = (const LIEF::ELF::Elf64_Sym *)(dynsym_buf.data() + dynsym_buf.size());

    const auto num_sym = dynsym_buf.size() / sizeof(LIEF::ELF::Elf64_Sym);

    fmt::print("num_sym: {:d}\n", num_sym);

    const auto nbuckets = *(uint32_t *)hash_begin;
    const auto nchains = *(uint32_t *)(hash_begin + sizeof(uint32_t));
    fmt::print("nbuckets: {:d} nchains: {:d}\n", nbuckets, nchains);

    auto *buckets = (uint32_t *)(hash_begin + 2*sizeof(uint32_t));
    auto *chains = (uint32_t *)(hash_begin + (2 + nbuckets) * sizeof(uint32_t));

    memset((void*)buckets, 0x0, hash_buf.size() - 2*sizeof(uint32_t));

    for (auto i = 0; i < num_sym; ++i) {
        auto *symp = &sym_begin[i];
        const auto stidx = symp->st_name;
        const auto *sym_name = strtab_begin + stidx;
        const uint32_t new_hash = elf_hash(sym_name);
        fmt::print("sym_name: {:s} hash: {:#010x}\n", sym_name, new_hash);
        if (buckets[new_hash % nbuckets] == STN_UNDEF) {
            buckets[new_hash % nbuckets] = i;
        } else {
            uint32_t y = buckets[new_hash % nbuckets];
            while (chains[y] != STN_UNDEF) {
                y = chains[y];
            }
            chains[y] = i;
        }
    }

    // int i = 0;
    // for (auto *p = strtab_begin; p < strtab_end; p += strlen(p) + 1) {
    //  auto sym_name = std::string(p);
    //  fmt::print(stderr, "sysv_rehash sym str[{:d}] = '{:s}'\n", i, sym_name);
    //  ++i;
    // }
}


void sec_hdrs_gnu_hash_type_to_null(buf_t &sec_hdr_buf) {
    auto *sec_hdr_begin = (LIEF::ELF::Elf64_Shdr *)sec_hdr_buf.data();
    auto *sec_hdr_end = (LIEF::ELF::Elf64_Shdr *)(sec_hdr_buf.data() + sec_hdr_buf.size());

    int i = 0;
    for (auto *p = sec_hdr_begin; p < sec_hdr_end; ++p) {
        fmt::print(stderr, "sec_hdr[{:d}]->type = '{:d}' before\n", i, p->sh_type);
        if (p->sh_type == (LIEF::ELF::Elf64_Word)LIEF::ELF::ELF_SECTION_TYPES::SHT_GNU_HASH) {
            fmt::print(stderr, "sec_hdr[{:d}] changing gnu hash type to note type\n", i);
            p->sh_type = (LIEF::ELF::Elf64_Word)LIEF::ELF::ELF_SECTION_TYPES::SHT_NULL;
        }
        // if (p->sh_type == (LIEF::ELF::Elf64_Word)LIEF::ELF::ELF_SECTION_TYPES::SHT_HASH) {
        //  fmt::print(stderr, "sec_hdr[{:d}] changing sysv hash type to note type\n", i);
        //  p->sh_type = (LIEF::ELF::Elf64_Word)LIEF::ELF::ELF_SECTION_TYPES::SHT_NULL;
        // }
        // fmt::print(stderr, "sec_hdr[{:d}]->type = '{:d}' after\n", i, p->sh_type);
        ++i;
    }
}

void dynamic_null_out_gnu_hash(buf_t &dynamic_buf) {
    auto *dyn_begin = (LIEF::ELF::Elf64_Dyn *)dynamic_buf.data();
    auto *dyn_end = (LIEF::ELF::Elf64_Dyn *)(dynamic_buf.data() + dynamic_buf.size());

    // int i = 0;
    // for (auto *p = dyn_begin; p < dyn_end; ++p) {
    //  fmt::print(stderr, "dyn[{:d}]->d_tag = '{:#x}' ptr = {:p} before\n", i, p->d_tag, (void*)p->d_un.d_ptr);
    //  if (p->d_tag == (LIEF::ELF::Elf64_Sxword)LIEF::ELF::DYNAMIC_TAGS::DT_GNU_HASH) {
    //      fmt::print(stderr, "dyn[{:d}] changing gnu hash ptr to null\n", i);
    //      p->d_un.d_ptr = 0;
    //  }
    //  if (p->d_tag == (LIEF::ELF::Elf64_Sxword)LIEF::ELF::DYNAMIC_TAGS::DT_HASH) {
    //      fmt::print(stderr, "dyn[{:d}] changing sysv ptr type to null\n", i);
    //      p->d_un.d_ptr = 0;
    //  }
    //  fmt::print(stderr, "dyn[{:d}]->d_tag = '{:#x}' ptr = {:p} after\n", i, p->d_tag, (void*)p->d_un.d_ptr);
    //  ++i;
    // }

    int i = 0;
    for (auto *p = dyn_begin; p < dyn_end; ++p) {
        fmt::print(stderr, "dyn[{:d}]->d_tag = '{:#x}' ptr = {:p} before\n", i, p->d_tag, (void*)p->d_un.d_ptr);
        if (p->d_tag == (LIEF::ELF::Elf64_Sxword)LIEF::ELF::DYNAMIC_TAGS::DT_GNU_HASH) {
            fmt::print(stderr, "dyn[{:d}] erasing gnu hash ptr\n", i);
            std::copy(std::next(p), dyn_end, p);
        }
        fmt::print(stderr, "dyn[{:d}]->d_tag = '{:#x}' ptr = {:p} after\n", i, p->d_tag, (void*)p->d_un.d_ptr);
        ++i;
    }

}

void swap_case_clean(const char *in_elf_path, const char *out_elf_path) {
    auto in_fh = sr::make_unique_resource_checked(::open(in_elf_path, O_RDONLY), -1, &::close);
    auto in_buf = mio::mmap_source(in_fh.get(), 0, mio::map_entire_file);
    auto in_vec = buf_t(in_buf.begin(), in_buf.end());
    auto out_vec = buf_t(in_buf.begin(), in_buf.end());
    auto in_elf = LIEF::ELF::Parser::parse(in_vec, in_elf_path);

    std::set<std::string> targets;
    for (auto &sym : in_elf->exported_symbols()) {
        std::string orig_name = sym.name();
        auto swapped_name = swap_case(orig_name);
        assert(swapped_name != orig_name);
        // fmt::print("sym: name: {:s} val: {:#x} swapped: {:s}\n", orig_name, sym.value(), swapped_name);
        targets.emplace(orig_name);
        // sym.name(swapped_name);
    }


    auto dynstr_sec = in_elf->get_section(".dynstr");
    fmt::print(stderr, "dynstr_sec: {:p}\n", (void*)&dynstr_sec);

    auto dynstr_buf = dynstr_sec.content();
    swap_case_strtab(targets, dynstr_buf);
    std::copy(dynstr_buf.begin(), dynstr_buf.end(), out_vec.begin() + dynstr_sec.offset());
    // dynstr_sec.content(dynstr_buf);


    auto strtab_sec = in_elf->get_section(".strtab");
    fmt::print(stderr, "strtab_sec: {:p}\n", (void*)&strtab_sec);

    auto strtab_buf = strtab_sec.content();
    swap_case_strtab(targets, strtab_buf);
    std::copy(strtab_buf.begin(), strtab_buf.end(), out_vec.begin() + strtab_sec.offset());
    // strtab_sec.content(strtab_buf);

    // auto shstrtab_sec = in_elf->get_section(".shstrtab");
    // fmt::print(stderr, "shstrtab_sec: {:p}\n", (void*)&shstrtab_sec);

    // auto shstrtab_buf = shstrtab_sec.content();
    // swap_case_shstrtab_hashes(shstrtab_buf);
    // std::copy(shstrtab_buf.begin(), shstrtab_buf.end(), out_vec.begin() + shstrtab_sec.offset());
    // shstrtab_sec.content(shstrtab_buf);


    // auto *sec_hdr_begin = in_vec.data() + in_elf->header().section_headers_offset();
    // auto *sec_hdr_end = sec_hdr_begin + (in_elf->header().numberof_sections() * in_elf->header().section_header_size());
    // auto sec_hdr_buf = buf_t(sec_hdr_begin, sec_hdr_end);
    // sec_hdrs_gnu_hash_type_to_null(sec_hdr_buf);
    // std::copy(sec_hdr_buf.begin(), sec_hdr_buf.end(), out_vec.begin() + in_elf->header().section_headers_offset());


    // auto dynamic_sec = in_elf->get_section(".dynamic");
    // fmt::print(stderr, "dynamic_sec: {:p}\n", (void*)&dynamic_sec);

    // auto dynamic_buf = dynamic_sec.content();
    // dynamic_null_out_gnu_hash(dynamic_buf);
    // std::copy(dynamic_buf.begin(), dynamic_buf.end(), out_vec.begin() + dynamic_sec.offset());
    // shstrtab_sec.content(shstrtab_buf);

    const auto dynsym_sec = in_elf->get_section(".dynsym");
    fmt::print(stderr, "dynsym_sec: {:p}\n", (void*)&dynsym_sec);
    const auto dynsym_buf = dynsym_sec.content();

    auto hash_sec = in_elf->get_section(".hash");
    fmt::print(stderr, "hash_sec: {:p}\n", (void*)&hash_sec);

    auto hash_buf = hash_sec.content();
    sysv_rehash(dynstr_buf, dynsym_buf, hash_buf);
    std::copy(hash_buf.begin(), hash_buf.end(), out_vec.begin() + hash_sec.offset());
    // shstrtab_sec.content(shstrtab_buf);

    delete_and_touch_file(out_elf_path, out_vec.size());
    std::error_code rw_mmap_error;
    auto out_buf = mio::make_mmap_sink(out_elf_path, 0, out_vec.size(), rw_mmap_error);
    assert(!rw_mmap_error);
    std::copy(out_vec.begin(), out_vec.end(), out_buf.begin());
}

int main(int argc, const char **argv) {
    assert(argc == 4);
    auto in_elf_path = argv[2];
    auto out_elf_path = argv[3];

    if (argv[1] == "dirty"s) {
        swap_case_dirty(in_elf_path, out_elf_path);
    } else if (argv[1] == "clean"s) {
        swap_case_clean(in_elf_path, out_elf_path);
    } else {
        assert(!"not dirty or clean swap type");
    }

    return 0;
}
