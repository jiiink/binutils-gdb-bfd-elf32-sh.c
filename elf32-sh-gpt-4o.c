/* Renesas / SuperH SH specific support for 32-bit ELF
   Copyright (C) 1996-2025 Free Software Foundation, Inc.
   Contributed by Ian Lance Taylor, Cygnus Support.

   This file is part of BFD, the Binary File Descriptor library.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street - Fifth Floor, Boston,
   MA 02110-1301, USA.  */

#include "sysdep.h"
#include "bfd.h"
#include "bfdlink.h"
#include "libbfd.h"
#include "elf-bfd.h"
#include "elf-vxworks.h"
#include "elf/sh.h"
#include "dwarf2.h"
#include "libiberty.h"
#include "../opcodes/sh-opc.h"

/* All users of this file have bfd_octets_per_byte (abfd, sec) == 1.  */
#define OCTETS_PER_BYTE(ABFD, SEC) 1

static bfd_reloc_status_type sh_elf_reloc
  (bfd *, arelent *, asymbol *, void *, asection *, bfd *, char **);
static bfd_reloc_status_type sh_elf_ignore_reloc
  (bfd *, arelent *, asymbol *, void *, asection *, bfd *, char **);
static bool sh_elf_relax_delete_bytes
  (bfd *, asection *, bfd_vma, int);
static bool sh_elf_align_loads
  (bfd *, asection *, Elf_Internal_Rela *, bfd_byte *, bool *);
static bool sh_elf_swap_insns
  (bfd *, asection *, void *, bfd_byte *, bfd_vma);
static int sh_elf_optimized_tls_reloc
  (struct bfd_link_info *, int, int);
static bfd_vma dtpoff_base
  (struct bfd_link_info *);
static bfd_vma tpoff
  (struct bfd_link_info *, bfd_vma);

/* The name of the dynamic interpreter.  This is put in the .interp
   section.  */

#define ELF_DYNAMIC_INTERPRETER "/usr/lib/libc.so.1"

/* FDPIC binaries have a default 128K stack.  */
#define DEFAULT_STACK_SIZE 0x20000

#define MINUS_ONE ((bfd_vma) 0 - 1)

/* Decide whether a reference to a symbol can be resolved locally or
   not.  If the symbol is protected, we want the local address, but
   its function descriptor must be assigned by the dynamic linker.  */
#define SYMBOL_FUNCDESC_LOCAL(INFO, H) \
  (SYMBOL_REFERENCES_LOCAL (INFO, H) \
   || ! elf_hash_table (INFO)->dynamic_sections_created)

#define SH_PARTIAL32 true
#define SH_SRC_MASK32 0xffffffff
#define SH_ELF_RELOC sh_elf_reloc
static reloc_howto_type sh_elf_howto_table[] =
{
#include "elf32-sh-relocs.h"
};

#define SH_PARTIAL32 false
#define SH_SRC_MASK32 0
#define SH_ELF_RELOC bfd_elf_generic_reloc
static reloc_howto_type sh_vxworks_howto_table[] =
{
#include "elf32-sh-relocs.h"
};

/* Return true if OUTPUT_BFD is a VxWorks object.  */

static bool vxworks_object_p(bfd *abfd) {
#if !defined SH_TARGET_ALREADY_DEFINED
  extern const bfd_target sh_elf32_vxworks_le_vec;
  extern const bfd_target sh_elf32_vxworks_vec;

  return (abfd->xvec == &sh_elf32_vxworks_le_vec || abfd->xvec == &sh_elf32_vxworks_vec);
#else
  return false;
#endif
}

/* Return true if OUTPUT_BFD is an FDPIC object.  */

#include <stdbool.h>

static bool fdpic_object_p(bfd *abfd) {
#if !defined SH_TARGET_ALREADY_DEFINED
  extern const bfd_target sh_elf32_fdpic_le_vec;
  extern const bfd_target sh_elf32_fdpic_be_vec;

  if (abfd == NULL) {
    return false;
  }

  return (abfd->xvec == &sh_elf32_fdpic_le_vec || abfd->xvec == &sh_elf32_fdpic_be_vec);
#else
  return false;
#endif
}

/* Return the howto table for ABFD.  */

static reloc_howto_type *get_howto_table(bfd *abfd) {
    return vxworks_object_p(abfd) ? sh_vxworks_howto_table : sh_elf_howto_table;
}

#include <stdlib.h>
#include <assert.h>

static bfd_reloc_status_type sh_elf_reloc_loop(int r_type ATTRIBUTE_UNUSED, bfd *input_bfd,
                                               asection *input_section, bfd_byte *contents,
                                               bfd_vma addr, asection *symbol_section,
                                               bfd_vma start, bfd_vma end) {
    static bfd_vma last_addr;
    static asection *last_symbol_section;
    bfd_vma current_addr = addr;
    int cum_diff = -6;
    bfd_signed_vma x;
    int insn;

    if (current_addr > bfd_get_section_limit(input_bfd, input_section))
        return bfd_reloc_outofrange;

    if (last_addr == 0) {
        last_addr = current_addr;
        last_symbol_section = symbol_section;
        return bfd_reloc_ok;
    }

    assert(last_addr == current_addr);
    last_addr = 0;

    if (!symbol_section || last_symbol_section != symbol_section || end < start)
        return bfd_reloc_outofrange;

    if (symbol_section != input_section && elf_section_data(symbol_section)->this_hdr.contents == NULL) {
        if (!bfd_malloc_and_get_section(input_bfd, symbol_section, &contents))
            return bfd_reloc_outofrange;
    } else {
        contents = elf_section_data(symbol_section)->this_hdr.contents;
    }

#define IS_PPI(PTR) ((bfd_get_16(input_bfd, (PTR)) & 0xfc00) == 0xf800)
    bfd_byte *start_ptr = contents + start;
    bfd_byte *ptr = contents + end;

    while (cum_diff < 0 && ptr > start_ptr) {
        bfd_byte *last_ptr = ptr;
        ptr -= 4;
        while (ptr >= start_ptr && IS_PPI(ptr)) {
            ptr -= 2;
        }
        ptr += 2;
        int diff = (last_ptr - ptr) >> 1;
        cum_diff += diff & 1;
        cum_diff += diff;
    }

    if (cum_diff >= 0) {
        start -= 4;
        end = (ptr + cum_diff * 2) - contents;
    } else {
        bfd_vma start0 = start - 4;
        while (start0 && IS_PPI(contents + start0)) {
            start0 -= 2;
        }
        start0 = start - 2 - ((start - start0) & 2);
        start = start0 - cum_diff - 2;
        end = start0;
    }

    if (elf_section_data(symbol_section)->this_hdr.contents != contents) {
        free(contents);
    }

    insn = bfd_get_16(input_bfd, contents + addr);
    x = (insn & 0x200 ? end : start) - addr;
    if (input_section != symbol_section) {
        x += ((symbol_section->output_section->vma + symbol_section->output_offset)
              - (input_section->output_section->vma + input_section->output_offset));
    }
    x >>= 1;
    if (x < -128 || x > 127) {
        return bfd_reloc_overflow;
    }

    x = (insn & ~0xff) | (x & 0xff);
    bfd_put_16(input_bfd, (bfd_vma)x, contents + addr);

    return bfd_reloc_ok;
}

/* This function is used for normal relocs.  This used to be like the COFF
   function, and is almost certainly incorrect for other ELF targets.  */

static bfd_reloc_status_type sh_elf_reloc(bfd *abfd, arelent *reloc_entry, asymbol *symbol_in, void *data, asection *input_section, bfd *output_bfd, char **error_message ATTRIBUTE_UNUSED) {
    if (output_bfd != NULL) {
        reloc_entry->address += input_section->output_offset;
        return bfd_reloc_ok;
    }

    enum elf_sh_reloc_type r_type = (enum elf_sh_reloc_type)reloc_entry->howto->type;
    bfd_vma addr = reloc_entry->address;
    bfd_size_type octets = addr * OCTETS_PER_BYTE(abfd, input_section);
    bfd_byte *hit_data = (bfd_byte *)data + octets;

    if (r_type == R_SH_IND12W && (symbol_in->flags & BSF_LOCAL) != 0) {
        return bfd_reloc_ok;
    }

    if (symbol_in != NULL && bfd_is_und_section(symbol_in->section)) {
        return bfd_reloc_undefined;
    }

    if (octets + bfd_get_reloc_size(reloc_entry->howto) > bfd_get_section_limit_octets(abfd, input_section)) {
        return bfd_reloc_outofrange;
    }

    bfd_vma sym_value = bfd_is_com_section(symbol_in->section) ? 0 : (symbol_in->value + symbol_in->section->output_section->vma + symbol_in->section->output_offset);

    switch (r_type) {
        case R_SH_DIR32: {
            bfd_vma insn = bfd_get_32(abfd, hit_data);
            insn += sym_value + reloc_entry->addend;
            bfd_put_32(abfd, insn, hit_data);
            break;
        }
        case R_SH_IND12W: {
            bfd_vma insn = bfd_get_16(abfd, hit_data);
            sym_value += reloc_entry->addend;
            sym_value -= (input_section->output_section->vma + input_section->output_offset + addr + 4);
            sym_value += (((insn & 0xfff) ^ 0x800) - 0x800) << 1;
            insn = (insn & 0xf000) | ((sym_value >> 1) & 0xfff);
            bfd_put_16(abfd, insn, hit_data);
            if (sym_value + 0x1000 >= 0x2000 || (sym_value & 1) != 0) {
                return bfd_reloc_overflow;
            }
            break;
        }
        default:
            abort();
    }

    return bfd_reloc_ok;
}

/* This function is used for relocs which are only used for relaxing,
   which the linker should otherwise ignore.  */

static bfd_reloc_status_type sh_elf_ignore_reloc(bfd *abfd, arelent *reloc_entry, asymbol *symbol, void *data, asection *input_section, bfd *output_bfd, char **error_message) {
    if (output_bfd != NULL) {
        reloc_entry->address += input_section->output_offset;
    }
    return bfd_reloc_ok;
}

/* This structure is used to map BFD reloc codes to SH ELF relocs.  */

struct elf_reloc_map
{
  bfd_reloc_code_real_type bfd_reloc_val;
  unsigned char elf_reloc_val;
};

/* An array mapping BFD reloc codes to SH ELF relocs.  */

static const struct elf_reloc_map sh_reloc_map[] =
{
  { BFD_RELOC_NONE, R_SH_NONE },
  { BFD_RELOC_32, R_SH_DIR32 },
  { BFD_RELOC_16, R_SH_DIR16 },
  { BFD_RELOC_8, R_SH_DIR8 },
  { BFD_RELOC_CTOR, R_SH_DIR32 },
  { BFD_RELOC_32_PCREL, R_SH_REL32 },
  { BFD_RELOC_SH_PCDISP8BY2, R_SH_DIR8WPN },
  { BFD_RELOC_SH_PCDISP12BY2, R_SH_IND12W },
  { BFD_RELOC_SH_PCRELIMM8BY2, R_SH_DIR8WPZ },
  { BFD_RELOC_SH_PCRELIMM8BY4, R_SH_DIR8WPL },
  { BFD_RELOC_8_PCREL, R_SH_SWITCH8 },
  { BFD_RELOC_SH_SWITCH16, R_SH_SWITCH16 },
  { BFD_RELOC_SH_SWITCH32, R_SH_SWITCH32 },
  { BFD_RELOC_SH_USES, R_SH_USES },
  { BFD_RELOC_SH_COUNT, R_SH_COUNT },
  { BFD_RELOC_SH_ALIGN, R_SH_ALIGN },
  { BFD_RELOC_SH_CODE, R_SH_CODE },
  { BFD_RELOC_SH_DATA, R_SH_DATA },
  { BFD_RELOC_SH_LABEL, R_SH_LABEL },
  { BFD_RELOC_VTABLE_INHERIT, R_SH_GNU_VTINHERIT },
  { BFD_RELOC_VTABLE_ENTRY, R_SH_GNU_VTENTRY },
  { BFD_RELOC_SH_LOOP_START, R_SH_LOOP_START },
  { BFD_RELOC_SH_LOOP_END, R_SH_LOOP_END },
  { BFD_RELOC_SH_TLS_GD_32, R_SH_TLS_GD_32 },
  { BFD_RELOC_SH_TLS_LD_32, R_SH_TLS_LD_32 },
  { BFD_RELOC_SH_TLS_LDO_32, R_SH_TLS_LDO_32 },
  { BFD_RELOC_SH_TLS_IE_32, R_SH_TLS_IE_32 },
  { BFD_RELOC_SH_TLS_LE_32, R_SH_TLS_LE_32 },
  { BFD_RELOC_SH_TLS_DTPMOD32, R_SH_TLS_DTPMOD32 },
  { BFD_RELOC_SH_TLS_DTPOFF32, R_SH_TLS_DTPOFF32 },
  { BFD_RELOC_SH_TLS_TPOFF32, R_SH_TLS_TPOFF32 },
  { BFD_RELOC_32_GOT_PCREL, R_SH_GOT32 },
  { BFD_RELOC_32_PLT_PCREL, R_SH_PLT32 },
  { BFD_RELOC_SH_COPY, R_SH_COPY },
  { BFD_RELOC_SH_GLOB_DAT, R_SH_GLOB_DAT },
  { BFD_RELOC_SH_JMP_SLOT, R_SH_JMP_SLOT },
  { BFD_RELOC_SH_RELATIVE, R_SH_RELATIVE },
  { BFD_RELOC_32_GOTOFF, R_SH_GOTOFF },
  { BFD_RELOC_SH_GOTPC, R_SH_GOTPC },
  { BFD_RELOC_SH_GOTPLT32, R_SH_GOTPLT32 },
  { BFD_RELOC_SH_GOT20, R_SH_GOT20 },
  { BFD_RELOC_SH_GOTOFF20, R_SH_GOTOFF20 },
  { BFD_RELOC_SH_GOTFUNCDESC, R_SH_GOTFUNCDESC },
  { BFD_RELOC_SH_GOTFUNCDESC20, R_SH_GOTFUNCDESC20 },
  { BFD_RELOC_SH_GOTOFFFUNCDESC, R_SH_GOTOFFFUNCDESC },
  { BFD_RELOC_SH_GOTOFFFUNCDESC20, R_SH_GOTOFFFUNCDESC20 },
  { BFD_RELOC_SH_FUNCDESC, R_SH_FUNCDESC },
};

/* Given a BFD reloc code, return the howto structure for the
   corresponding SH ELF reloc.  */

static reloc_howto_type *sh_elf_reloc_type_lookup(bfd *abfd, bfd_reloc_code_real_type code) {
    if (abfd == NULL) {
        return NULL;
    }

    size_t map_size = sizeof(sh_reloc_map) / sizeof(sh_reloc_map[0]);
    for (size_t i = 0; i < map_size; i++) {
        if (sh_reloc_map[i].bfd_reloc_val == code) {
            return get_howto_table(abfd) + sh_reloc_map[i].elf_reloc_val;
        }
    }

    return NULL;
}

static reloc_howto_type *sh_elf_reloc_name_lookup(bfd *abfd, const char *r_name) {
    reloc_howto_type *howto_table = vxworks_object_p(abfd) ? sh_vxworks_howto_table : sh_elf_howto_table;
    size_t table_size = vxworks_object_p(abfd) ? sizeof(sh_vxworks_howto_table) : sizeof(sh_elf_howto_table);
    size_t entry_size = sizeof(howto_table[0]);

    for (size_t i = 0; i < table_size / entry_size; i++) {
        if (howto_table[i].name != NULL && strcasecmp(howto_table[i].name, r_name) == 0) {
            return &howto_table[i];
        }
    }

    return NULL;
}

/* Given an ELF reloc, fill in the howto field of a relent.  */

static bool sh_elf_info_to_howto(bfd *abfd, arelent *cache_ptr, Elf_Internal_Rela *dst) {
    unsigned int r = ELF32_R_TYPE(dst->r_info);
    const unsigned int invalid_reloc_types[][2] = {
        {R_SH_FIRST_INVALID_RELOC_6, UINT_MAX},
        {R_SH_FIRST_INVALID_RELOC, R_SH_LAST_INVALID_RELOC},
        {R_SH_FIRST_INVALID_RELOC_2, R_SH_LAST_INVALID_RELOC_2},
        {R_SH_FIRST_INVALID_RELOC_3, R_SH_LAST_INVALID_RELOC_3},
        {R_SH_FIRST_INVALID_RELOC_4, R_SH_LAST_INVALID_RELOC_4},
        {R_SH_FIRST_INVALID_RELOC_5, R_SH_LAST_INVALID_RELOC_5}
    };

    for (size_t i = 0; i < sizeof(invalid_reloc_types) / sizeof(invalid_reloc_types[0]); i++) {
        if (r >= invalid_reloc_types[i][0] && r <= invalid_reloc_types[i][1]) {
            _bfd_error_handler(_("%pB: unsupported relocation type %#x"), abfd, r);
            bfd_set_error(bfd_error_bad_value);
            return false;
        }
    }

    cache_ptr->howto = get_howto_table(abfd) + r;
    return true;
}

/* This function handles relaxing for SH ELF.  See the corresponding
   function in coff-sh.c for a description of what this does.  FIXME:
   There is a lot of duplication here between this code and the COFF
   specific code.  The format of relocs and symbols is wound deeply
   into this code, but it would still be better if the duplication
   could be eliminated somehow.  Note in particular that although both
   functions use symbols like R_SH_CODE, those symbols have different
   values; in coff-sh.c they come from include/coff/sh.h, whereas here
   they come from enum elf_sh_reloc_type in include/elf/sh.h.  */

static bool
sh_elf_relax_section(bfd *abfd, asection *sec, struct bfd_link_info *link_info, bool *again)
{
    *again = false;

    if (bfd_link_relocatable(link_info) || !(sec->flags & SEC_HAS_CONTENTS) || !(sec->flags & SEC_RELOC) || sec->reloc_count == 0)
        return true;

    Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr(abfd);
    Elf_Internal_Rela *internal_relocs = _bfd_elf_link_read_relocs(abfd, sec, NULL, (Elf_Internal_Rela *)NULL, link_info->keep_memory);
    if (internal_relocs == NULL)
        return cleanup(false, NULL, NULL, internal_relocs);

    bool have_code = false;
    Elf_Internal_Sym *isymbuf = NULL;
    bfd_byte *contents = NULL;

    for (Elf_Internal_Rela *irel = internal_relocs, *irelend = internal_relocs + sec->reloc_count; irel < irelend; irel++) {
        if (ELF32_R_TYPE(irel->r_info) == R_SH_CODE)
            have_code = true;

        if (ELF32_R_TYPE(irel->r_info) != R_SH_USES)
            continue;

        contents = get_section_contents(sec, abfd, contents);
        if (!contents)
            return cleanup(false, isymbuf, contents, internal_relocs);

        bfd_vma laddr = irel->r_offset + 4 + irel->r_addend;
        if (!check_offset(laddr, sec->size))
            error_handler(abfd, irel->r_offset, "bad R_SH_USES offset");

        unsigned short insn = bfd_get_16(abfd, contents + laddr);
        if (!check_instruction(insn))
            error_handler(abfd, irel->r_offset, "R_SH_USES points to unrecognized insn 0x%x"), insn;

        bfd_vma paddr = calculate_paddr(laddr, insn);
        if (!check_offset(paddr, sec->size))
            error_handler(abfd, irel->r_offset, "bad R_SH_USES load offset");

        Elf_Internal_Rela *irelfn = find_reloc(internal_relocs, irelend, paddr, R_SH_DIR32);
        if (!irelfn)
            error_handler(abfd, paddr, "could not find expected reloc");

        if (!isymbuf && symtab_hdr->sh_info != 0)
            isymbuf = get_symbols(abfd, symtab_hdr);

        if (!isymbuf)
            return cleanup(false, isymbuf, contents, internal_relocs);

        bfd_vma symval = get_symbol_value(abfd, sec, symtab_hdr, isymbuf, irelfn);

        symval += (get_howto_table(abfd)[R_SH_DIR32].partial_inplace) ? bfd_get_32(abfd, contents + paddr) : irelfn->r_addend;

        if (!can_shorten_call(symval, irel->r_offset, sec))
            continue;

        *again = true;

        if (!update_function_call(abfd, contents, irel, irelfn, symval))
            return cleanup(false, isymbuf, contents, internal_relocs);

        irel->r_addend += bfd_get_32(abfd, contents + paddr);

        Elf_Internal_Rela *irelscan = find_matching_uses(internal_relocs, irelend, laddr);
        if (irelscan)
            continue;

        Elf_Internal_Rela *irelcount = find_reloc(internal_relocs, irelend, paddr, R_SH_COUNT);
        if (!irelcount)
            error_handler(abfd, paddr, "could not find expected COUNT reloc");
        else if (!update_count_reloc(irelcount) || !delete_unused_address(abfd, sec, irelcount, irelfn))
            return cleanup(false, isymbuf, contents, internal_relocs);
    }

    if (have_code && (elf_elfheader(abfd)->e_flags & EF_SH_MACH_MASK) != EF_SH4) {
        contents = get_section_contents(sec, abfd, contents);
        if (!contents)
            return cleanup(false, isymbuf, contents, internal_relocs);

        bool swapped;
        if (!adjust_loads(abfd, sec, internal_relocs, contents, &swapped))
            return cleanup(false, isymbuf, contents, internal_relocs);

        if (swapped)
            cache_section_contents(sec, internal_relocs, contents, symtab_hdr, isymbuf);
    }

    return cleanup(true, isymbuf, contents, internal_relocs);
}

bool cleanup(bool result, Elf_Internal_Sym *isymbuf, bfd_byte *contents, Elf_Internal_Rela *internal_relocs)
{
    if (isymbuf && symtab_hdr->contents != (unsigned char *) isymbuf)
        free_memory(isymbuf, link_info);
    if (contents && elf_section_data(sec)->this_hdr.contents != contents)
        free_memory(contents, link_info);
    if (elf_section_data(sec)->relocs != internal_relocs)
        free(internal_relocs);

    return result;
}

bfd_byte *get_section_contents(asection *sec, bfd *abfd, bfd_byte *contents)
{
    if (!contents) {
        contents = elf_section_data(sec)->this_hdr.contents;
        if (!contents && !bfd_malloc_and_get_section(abfd, sec, &contents))
            return NULL;
    }
    return contents;
}

void error_handler(bfd *abfd, uint64_t offset, const char *message)
{
    _bfd_error_handler(_("%pB: %#" PRIx64 ": warning: %s"), abfd, offset, message);
}

bfd_vma calculate_paddr(bfd_vma laddr, unsigned short insn)
{
    bfd_vma paddr = (insn & 0xff) * 4;
    paddr += (laddr + 4) & ~3;
    return paddr;
}

bool check_offset(bfd_vma offset, bfd_size_type size)
{
    return offset < size;
}

bool check_instruction(unsigned short insn)
{
    return (insn & 0xf000) == 0xd000;
}

Elf_Internal_Rela *find_matching_uses(Elf_Internal_Rela *internal_relocs, Elf_Internal_Rela *irelend, bfd_vma laddr)
{
    for (Elf_Internal_Rela *irelscan = internal_relocs; irelscan < irelend; irelscan++)
        if (ELF32_R_TYPE(irelscan->r_info) == R_SH_USES && laddr == irelscan->r_offset + 4 + irelscan->r_addend)
            return irelscan;
    return NULL;
}

Elf_Internal_Rela *find_reloc(Elf_Internal_Rela *internal_relocs, Elf_Internal_Rela *irelend, bfd_vma paddr, int type)
{
    for (Elf_Internal_Rela *irelfn = internal_relocs; irelfn < irelend; irelfn++)
        if (irelfn->r_offset == paddr && ELF32_R_TYPE(irelfn->r_info) == type)
            return irelfn;
    return NULL;
}

Elf_Internal_Sym *get_symbols(bfd *abfd, Elf_Internal_Shdr *symtab_hdr)
{
    Elf_Internal_Sym *isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;
    if (!isymbuf)
        isymbuf = bfd_elf_get_elf_syms(abfd, symtab_hdr, symtab_hdr->sh_info, 0, NULL, NULL, NULL);
    return isymbuf;
}

bfd_vma get_symbol_value(bfd *abfd, asection *sec, Elf_Internal_Shdr *symtab_hdr, Elf_Internal_Sym *isymbuf, Elf_Internal_Rela *irelfn)
{
    bfd_vma symval = 0;
    unsigned long indx = ELF32_R_SYM(irelfn->r_info) - symtab_hdr->sh_info;
    struct elf_link_hash_entry *h = elf_sym_hashes(abfd)[indx];
    
    if (ELF32_R_SYM(irelfn->r_info) < symtab_hdr->sh_info) {
        Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM(irelfn->r_info);
        if (isym->st_shndx == _bfd_elf_section_from_bfd_section(abfd, sec))
            symval = isym->st_value + sec->output_section->vma + sec->output_offset;
    } else if (h && (h->root.type == bfd_link_hash_defined || h->root.type == bfd_link_hash_defweak)) {
        symval = h->root.u.def.value + h->root.u.def.section->output_section->vma + h->root.u.def.section->output_offset;
    }
    
    return symval;
}

bool can_shorten_call(bfd_vma symval, bfd_vma offset, asection *sec)
{
    bfd_signed_vma foff = symval - (offset + sec->output_section->vma + sec->output_offset + 4);
    return foff >= -0x1000 && foff < 0x1000 - 8;
}

bool update_function_call(bfd *abfd, bfd_byte *contents, Elf_Internal_Rela *irel, Elf_Internal_Rela *irelfn, bfd_vma symval)
{
    cache_section_contents(sec, internal_relocs, contents, symtab_hdr, isymbuf);
    
    irel->r_info = ELF32_R_INFO(ELF32_R_SYM(irelfn->r_info), R_SH_IND12W);
    uint16_t current_insn = bfd_get_16(abfd, contents + irel->r_offset);
    uint16_t new_insn = (current_insn & 0x0020) ? 0xb000 : 0xa000;
    bfd_put_16(abfd, new_insn, contents + irel->r_offset);
    
    return sh_elf_relax_delete_bytes(abfd, sec, irel->r_offset + 4 + irel->r_addend, 2);
}

bool update_count_reloc(Elf_Internal_Rela *irelcount)
{
    if (irelcount->r_addend == 0) {
        error_handler(abfd, irelcount->r_offset, "bad count");
        return false;
    }
    --irelcount->r_addend;
    return true;
}

bool delete_unused_address(bfd *abfd, asection *sec, Elf_Internal_Rela *irelcount, Elf_Internal_Rela *irelfn)
{
    if (irelcount->r_addend == 0)
        return sh_elf_relax_delete_bytes(abfd, sec, irelfn->r_offset, 4);
    return true;
}

void cache_section_contents(asection *sec, Elf_Internal_Rela *internal_relocs, bfd_byte *contents, Elf_Internal_Shdr *symtab_hdr, Elf_Internal_Sym *isymbuf)
{
    elf_section_data(sec)->relocs = internal_relocs;
    elf_section_data(sec)->this_hdr.contents = contents;
    symtab_hdr->contents = (unsigned char *) isymbuf;
}

void free_memory(void *ptr, struct bfd_link_info *link_info)
{
    if (!link_info->keep_memory)
        free(ptr);
}

// Additional helpers like adjust_loads, free_memory, cache_section_contents, etc., would be defined to encapsulate specific functionality.


/* Delete some bytes from a section while relaxing.  FIXME: There is a
   lot of duplication between this function and sh_relax_delete_bytes
   in coff-sh.c.  */

static bool sh_elf_relax_delete_bytes(bfd *abfd, asection *sec, bfd_vma addr, int count) {
    Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr(abfd);
    Elf_Internal_Sym *isymbuf = (Elf_Internal_Sym *)symtab_hdr->contents;
    unsigned int sec_shndx = _bfd_elf_section_from_bfd_section(abfd, sec);
    bfd_byte *contents = elf_section_data(sec)->this_hdr.contents;
    Elf_Internal_Rela *irel = elf_section_data(sec)->relocs, *irelend = irel + sec->reloc_count;
    Elf_Internal_Rela *irelalign = NULL;
    bfd_vma toaddr = sec->size;

    for (; irel < irelend; ++irel) {
        if (ELF32_R_TYPE(irel->r_info) == (int)R_SH_ALIGN && irel->r_offset > addr && count < (1 << irel->r_addend)) {
            irelalign = irel;
            toaddr = irel->r_offset;
            break;
        }
    }

    memmove(contents + addr, contents + addr + count, (size_t)(toaddr - addr - count));
    if (irelalign == NULL) {
        sec->size -= count;
    } else {
        for (int i = 0; i < count; i += 2)
            bfd_put_16(abfd, (bfd_vma)0x0009, contents + toaddr - count + i);
    }

    for (irel = elf_section_data(sec)->relocs; irel < irelend; ++irel) {
        bfd_vma nraddr = irel->r_offset;
        if ((irel->r_offset > addr && irel->r_offset < toaddr) || (ELF32_R_TYPE(irel->r_info) == (int)R_SH_ALIGN && irel->r_offset == toaddr))
            nraddr -= count;

        if (irel->r_offset >= addr && irel->r_offset < addr + count &&
            ELF32_R_TYPE(irel->r_info) != (int)R_SH_ALIGN &&
            ELF32_R_TYPE(irel->r_info) != (int)R_SH_CODE &&
            ELF32_R_TYPE(irel->r_info) != (int)R_SH_DATA &&
            ELF32_R_TYPE(irel->r_info) != (int)R_SH_LABEL) {
            irel->r_info = ELF32_R_INFO(ELF32_R_SYM(irel->r_info), (int)R_SH_NONE);
        }

        bfd_vma start = 0, stop = addr;
        int insn = 0, adjust = 0, off = 0, oinsn;
        bfd_signed_vma voff = 0;
        bool overflow = false;

        switch ((enum elf_sh_reloc_type)ELF32_R_TYPE(irel->r_info)) {
            case R_SH_DIR8WPN:
            case R_SH_IND12W:
            case R_SH_DIR8WPZ:
            case R_SH_DIR8WPL:
                start = irel->r_offset;
                insn = bfd_get_16(abfd, contents + nraddr);
                break;
            default:
                break;
        }

        switch ((enum elf_sh_reloc_type)ELF32_R_TYPE(irel->r_info)) {
            case R_SH_DIR32: {
                if (ELF32_R_SYM(irel->r_info) < symtab_hdr->sh_info) {
                    Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM(irel->r_info);
                    if (isym->st_shndx == sec_shndx && (isym->st_value <= addr || isym->st_value >= toaddr)) {
                        bfd_vma val;
                        if (get_howto_table(abfd)[R_SH_DIR32].partial_inplace) {
                            val = bfd_get_32(abfd, contents + nraddr) + isym->st_value;
                            if (val > addr && val < toaddr)
                                bfd_put_32(abfd, val - count, contents + nraddr);
                        } else {
                            val = isym->st_value + irel->r_addend;
                            if (val > addr && val < toaddr)
                                irel->r_addend -= count;
                        }
                    }
                }
                break;
            }
            case R_SH_DIR8WPN:
                off = insn & 0xff;
                if (off & 0x80) off -= 0x100;
                stop = (bfd_vma)((bfd_signed_vma)start + 4 + off * 2);
                break;
            case R_SH_IND12W:
                off = insn & 0xfff;
                if (!off) {
                    break;
                }
                if (off & 0x800) off -= 0x1000;
                stop = (bfd_vma)((bfd_signed_vma)start + 4 + off * 2);
                if (stop > addr && stop < toaddr)
                    irel->r_addend -= count;
                break;
            case R_SH_DIR8WPZ:
                off = insn & 0xff;
                stop = start + 4 + off * 2;
                break;
            case R_SH_DIR8WPL:
                off = insn & 0xff;
                stop = (start & ~(bfd_vma) 3) + 4 + off * 4;
                break;
            case R_SH_SWITCH8:
            case R_SH_SWITCH16:
            case R_SH_SWITCH32:
                stop = irel->r_offset;
                start = (bfd_vma)((bfd_signed_vma)stop - (long)irel->r_addend);

                if ((start > addr && start < toaddr && (stop <= addr || stop >= toaddr)) ||
                    (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))) {
                    irel->r_addend += (stop > addr && stop < toaddr) ? -count : count;
                }

                voff = (ELF32_R_TYPE(irel->r_info) == (int)R_SH_SWITCH8) ? bfd_get_8(abfd, contents + nraddr) :
                       (ELF32_R_TYPE(irel->r_info) == (int)R_SH_SWITCH16) ? bfd_get_signed_16(abfd, contents + nraddr) :
                       bfd_get_signed_32(abfd, contents + nraddr);
                stop = (bfd_vma)((bfd_signed_vma)start + voff);
                break;
            case R_SH_USES:
                start = irel->r_offset;
                stop = (bfd_vma)((bfd_signed_vma)start + (long)irel->r_addend + 4);
                break;
            default:
                start = stop = addr;
                break;
        }

        adjust = (start > addr && start < toaddr && (stop <= addr || stop >= toaddr)) ? count : 
                 (stop > addr && stop < toaddr && (start <= addr || start >= toaddr)) ? -count : 0;

        if (adjust != 0) {
            oinsn = insn;
            switch ((enum elf_sh_reloc_type)ELF32_R_TYPE(irel->r_info)) {
                case R_SH_DIR8WPN:
                case R_SH_DIR8WPZ:
                    insn += adjust / 2;
                    if ((oinsn & 0xff00) != (insn & 0xff00)) overflow = true;
                    bfd_put_16(abfd, (bfd_vma)insn, contents + nraddr);
                    break;
                case R_SH_IND12W:
                    insn += adjust / 2;
                    if ((oinsn & 0xf000) != (insn & 0xf000)) overflow = true;
                    bfd_put_16(abfd, (bfd_vma)insn, contents + nraddr);
                    break;
                case R_SH_DIR8WPL:
                    if (count >= 4) {
                        insn += adjust / 4;
                    } else {
                        if ((irel->r_offset & 3) == 0) ++insn;
                    }
                    if ((oinsn & 0xff00) != (insn & 0xff00)) overflow = true;
                    bfd_put_16(abfd, (bfd_vma)insn, contents + nraddr);
                    break;
                case R_SH_SWITCH8:
                    voff += adjust;
                    if (voff < 0 || voff >= 0xff) overflow = true;
                    bfd_put_8(abfd, voff, contents + nraddr);
                    break;
                case R_SH_SWITCH16:
                    voff += adjust;
                    if (voff < -0x8000 || voff >= 0x8000) overflow = true;
                    bfd_put_signed_16(abfd, (bfd_vma)voff, contents + nraddr);
                    break;
                case R_SH_SWITCH32:
                    voff += adjust;
                    bfd_put_signed_32(abfd, (bfd_vma)voff, contents + nraddr);
                    break;
                case R_SH_USES:
                    irel->r_addend += adjust;
                    break;
                default:
                    abort();
            }

            if (overflow) {
                _bfd_error_handler("reloc overflow while relaxing", abfd, (uint64_t)irel->r_offset);
                bfd_set_error(bfd_error_bad_value);
                return false;
            }
        }

        irel->r_offset = nraddr;
    }

    asection *o = abfd->sections;
    while (o != NULL) {
        if (o != sec && (o->flags & SEC_HAS_CONTENTS) && (o->flags & SEC_RELOC) && o->reloc_count > 0) {
            Elf_Internal_Rela *internal_relocs = _bfd_elf_link_read_relocs(abfd, o, NULL, NULL, true);
            if (internal_relocs == NULL) return false;
            bfd_byte *ocontents = NULL;
            for (Elf_Internal_Rela *irelscan = internal_relocs, *irelscanend = internal_relocs + o->reloc_count; irelscan < irelscanend; ++irelscan) {
                if (ELF32_R_TYPE(irelscan->r_info) == (int)R_SH_SWITCH32) {
                    if (ocontents == NULL) {
                        if (elf_section_data(o)->this_hdr.contents != NULL) {
                            ocontents = elf_section_data(o)->this_hdr.contents;
                        } else {
                            if (!bfd_malloc_and_get_section(abfd, o, &ocontents)) {
                                free(ocontents);
                                return false;
                            }
                            elf_section_data(o)->this_hdr.contents = ocontents;
                        }
                    }

                    bfd_vma stop = irelscan->r_offset;
                    bfd_vma start = (bfd_vma)((bfd_signed_vma)stop - (long)irelscan->r_addend);
                    if (start > addr && start < toaddr)
                        irelscan->r_addend += count;

                    bfd_signed_vma voff = bfd_get_signed_32(abfd, ocontents + irelscan->r_offset);
                    stop = (bfd_vma)((bfd_signed_vma)start + voff);
                    if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr)) {
                        bfd_put_signed_32(abfd, (bfd_vma)(voff + count), ocontents + irelscan->r_offset);
                    } else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr)) {
                        bfd_put_signed_32(abfd, (bfd_vma)(voff - count), ocontents + irelscan->r_offset);
                    }
                }

                if (ELF32_R_TYPE(irelscan->r_info) != (int)R_SH_DIR32)
                    continue;

                if (ELF32_R_SYM(irelscan->r_info) >= symtab_hdr->sh_info)
                    continue;

                Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM(irelscan->r_info);
                if (isym->st_shndx == sec_shndx && (isym->st_value <= addr || isym->st_value >= toaddr)) {
                    if (ocontents == NULL) {
                        if (elf_section_data(o)->this_hdr.contents != NULL) {
                            ocontents = elf_section_data(o)->this_hdr.contents;
                        } else {
                            if (!bfd_malloc_and_get_section(abfd, o, &ocontents)) {
                                free(ocontents);
                                return false;
                            }
                            elf_section_data(o)->this_hdr.contents = ocontents;
                        }
                    }

                    bfd_vma val = bfd_get_32(abfd, ocontents + irelscan->r_offset) + isym->st_value;
                    if (val > addr && val < toaddr)
                        bfd_put_32(abfd, val - count, ocontents + irelscan->r_offset);
                }
            }
        }
        o = o->next;
    }

    for (Elf_Internal_Sym *isym = isymbuf, *isymend = isymbuf + symtab_hdr->sh_info; isym < isymend; ++isym) {
        if (isym->st_shndx == sec_shndx && isym->st_value > addr && isym->st_value < toaddr)
            isym->st_value -= count;
    }

    unsigned int symcount = (symtab_hdr->sh_size / sizeof(Elf32_External_Sym)) - symtab_hdr->sh_info;
    struct elf_link_hash_entry **sym_hashes = elf_sym_hashes(abfd);
    struct elf_link_hash_entry **end_hashes = sym_hashes + symcount;
    for (; sym_hashes < end_hashes; ++sym_hashes) {
        struct elf_link_hash_entry *sym_hash = *sym_hashes;
        if ((sym_hash->root.type == bfd_link_hash_defined || sym_hash->root.type == bfd_link_hash_defweak) && sym_hash->root.u.def.section == sec && sym_hash->root.u.def.value > addr && sym_hash->root.u.def.value < toaddr) {
            sym_hash->root.u.def.value -= count;
        }
    }

    if (irelalign != NULL) {
        bfd_vma alignto = BFD_ALIGN(toaddr, 1 << irelalign->r_addend);
        bfd_vma alignaddr = BFD_ALIGN(irelalign->r_offset, 1 << irelalign->r_addend);
        if (alignto != alignaddr) {
            return sh_elf_relax_delete_bytes(abfd, sec, alignaddr, (int)(alignto - alignaddr));
        }
    }

    return true;
}

/* Look for loads and stores which we can align to four byte
   boundaries.  This is like sh_align_loads in coff-sh.c.  */

static bool sh_elf_align_loads(bfd *abfd, asection *sec, Elf_Internal_Rela *internal_relocs, bfd_byte *contents, bool *pswapped) {
    if (abfd == NULL || sec == NULL || internal_relocs == NULL || pswapped == NULL) {
        return false;
    }

    *pswapped = false;
    Elf_Internal_Rela *irel, *irelend = internal_relocs + sec->reloc_count;
    size_t label_count = 0;

    for (irel = internal_relocs; irel < irelend; ++irel) {
        if (ELF32_R_TYPE(irel->r_info) == R_SH_LABEL) {
            ++label_count;
        }
    }

    if (label_count == 0) {
        return true;
    }

    bfd_vma *labels = malloc(label_count * sizeof(bfd_vma));
    if (labels == NULL) {
        return false;
    }

    bfd_vma *label_end = labels;
    for (irel = internal_relocs; irel < irelend; ++irel) {
        if (ELF32_R_TYPE(irel->r_info) == R_SH_LABEL) {
            *label_end++ = irel->r_offset;
        }
    }

    bfd_vma *label = labels;

    for (irel = internal_relocs; irel < irelend; ++irel) {
        if (ELF32_R_TYPE(irel->r_info) != R_SH_CODE) {
            continue;
        }

        bfd_vma start = irel->r_offset;
        while (++irel < irelend && ELF32_R_TYPE(irel->r_info) != R_SH_DATA);
        bfd_vma stop = (irel < irelend) ? irel->r_offset : sec->size;

        if (!_bfd_sh_align_load_span(abfd, sec, contents, sh_elf_swap_insns, internal_relocs, &label, label_end, start, stop, pswapped)) {
            free(labels);
            return false;
        }
    }

    free(labels);
    return true;
}

/* Swap two SH instructions.  This is like sh_swap_insns in coff-sh.c.  */

#include <stdbool.h>
#include <stdint.h>

static bool sh_elf_swap_insns(bfd *abfd, asection *sec, void *relocs, bfd_byte *contents, bfd_vma addr) {
    Elf_Internal_Rela *internal_relocs = (Elf_Internal_Rela *)relocs;
    Elf_Internal_Rela *irel, *irelend = internal_relocs + sec->reloc_count;
    unsigned short i1 = bfd_get_16(abfd, contents + addr);
    unsigned short i2 = bfd_get_16(abfd, contents + addr + 2);

    bfd_put_16(abfd, (bfd_vma)i2, contents + addr);
    bfd_put_16(abfd, (bfd_vma)i1, contents + addr + 2);

    for (irel = internal_relocs; irel < irelend; irel++) {
        enum elf_sh_reloc_type type = (enum elf_sh_reloc_type)ELF32_R_TYPE(irel->r_info);
        if (type == R_SH_ALIGN || type == R_SH_CODE || type == R_SH_DATA || type == R_SH_LABEL) {
            continue;
        }

        if (type == R_SH_USES) {
            bfd_vma off = irel->r_offset + 4 + irel->r_addend;
            if (off == addr) {
                irel->r_addend += 2;
            } else if (off == addr + 2) {
                irel->r_addend -= 2;
            }
        }

        int add = 0;
        if (irel->r_offset == addr) {
            irel->r_offset += 2;
            add = -2;
        } else if (irel->r_offset == addr + 2) {
            irel->r_offset -= 2;
            add = 2;
        }

        if (add != 0) {
            bfd_byte *loc = contents + irel->r_offset;
            unsigned short insn = bfd_get_16(abfd, loc);
            unsigned short oinsn = insn;
            bool overflow = false;

            switch (type) {
                case R_SH_DIR8WPN:
                case R_SH_DIR8WPZ:
                case R_SH_IND12W:
                    insn += add / 2;
                    if ((oinsn & 0xff00) != (insn & 0xff00) || ((oinsn & 0xf000) != (insn & 0xf000) && type == R_SH_IND12W)) {
                        overflow = true;
                    }
                    break;

                case R_SH_DIR8WPL:
                    if ((addr & 3) != 0) {
                        insn += add / 2;
                        if ((oinsn & 0xff00) != (insn & 0xff00)) {
                            overflow = true;
                        }
                    }
                    break;

                default:
                    break;
            }

            bfd_put_16(abfd, (bfd_vma)insn, loc);
            if (overflow) {
                _bfd_error_handler("%pB: %#" PRIx64 ": fatal: reloc overflow while relaxing", abfd, (uint64_t)irel->r_offset);
                bfd_set_error(bfd_error_bad_value);
                return false;
            }
        }
    }

    return true;
}

/* Describes one of the various PLT styles.  */

struct elf_sh_plt_info
{
  /* The template for the first PLT entry, or NULL if there is no special
     first entry.  */
  const bfd_byte *plt0_entry;

  /* The size of PLT0_ENTRY in bytes, or 0 if PLT0_ENTRY is NULL.  */
  bfd_vma plt0_entry_size;

  /* Index I is the offset into PLT0_ENTRY of a pointer to
     _GLOBAL_OFFSET_TABLE_ + I * 4.  The value is MINUS_ONE
     if there is no such pointer.  */
  bfd_vma plt0_got_fields[3];

  /* The template for a symbol's PLT entry.  */
  const bfd_byte *symbol_entry;

  /* The size of SYMBOL_ENTRY in bytes.  */
  bfd_vma symbol_entry_size;

  /* Byte offsets of fields in SYMBOL_ENTRY.  Not all fields are used
     on all targets.  The comments by each member indicate the value
     that the field must hold.  */
  struct {
    bfd_vma got_entry; /* the address of the symbol's .got.plt entry */
    bfd_vma plt; /* .plt (or a branch to .plt on VxWorks) */
    bfd_vma reloc_offset; /* the offset of the symbol's JMP_SLOT reloc */
    bool got20; /* TRUE if got_entry points to a movi20 instruction
		   (instead of a constant pool entry).  */
  } symbol_fields;

  /* The offset of the resolver stub from the start of SYMBOL_ENTRY.  */
  bfd_vma symbol_resolve_offset;

  /* A different PLT layout which can be used for the first
     MAX_SHORT_PLT entries.  It must share the same plt0.  NULL in
     other cases.  */
  const struct elf_sh_plt_info *short_plt;
};

/* The size in bytes of an entry in the procedure linkage table.  */

#define ELF_PLT_ENTRY_SIZE 28

/* First entry in an absolute procedure linkage table look like this.  */

/* Note - this code has been "optimised" not to use r2.  r2 is used by
   GCC to return the address of large structures, so it should not be
   corrupted here.  This does mean however, that this PLT does not conform
   to the SH PIC ABI.  That spec says that r0 contains the type of the PLT
   and r2 contains the GOT id.  This version stores the GOT id in r0 and
   ignores the type.  Loaders can easily detect this difference however,
   since the type will always be 0 or 8, and the GOT ids will always be
   greater than or equal to 12.  */
static const bfd_byte elf_sh_plt0_entry_be[ELF_PLT_ENTRY_SIZE] =
{
  0xd0, 0x05,	/* mov.l 2f,r0 */
  0x60, 0x02,	/* mov.l @r0,r0 */
  0x2f, 0x06,	/* mov.l r0,@-r15 */
  0xd0, 0x03,	/* mov.l 1f,r0 */
  0x60, 0x02,	/* mov.l @r0,r0 */
  0x40, 0x2b,	/* jmp @r0 */
  0x60, 0xf6,	/*  mov.l @r15+,r0 */
  0x00, 0x09,	/* nop */
  0x00, 0x09,	/* nop */
  0x00, 0x09,	/* nop */
  0, 0, 0, 0,	/* 1: replaced with address of .got.plt + 8.  */
  0, 0, 0, 0,	/* 2: replaced with address of .got.plt + 4.  */
};

static const bfd_byte elf_sh_plt0_entry_le[ELF_PLT_ENTRY_SIZE] =
{
  0x05, 0xd0,	/* mov.l 2f,r0 */
  0x02, 0x60,	/* mov.l @r0,r0 */
  0x06, 0x2f,	/* mov.l r0,@-r15 */
  0x03, 0xd0,	/* mov.l 1f,r0 */
  0x02, 0x60,	/* mov.l @r0,r0 */
  0x2b, 0x40,	/* jmp @r0 */
  0xf6, 0x60,	/*  mov.l @r15+,r0 */
  0x09, 0x00,	/* nop */
  0x09, 0x00,	/* nop */
  0x09, 0x00,	/* nop */
  0, 0, 0, 0,	/* 1: replaced with address of .got.plt + 8.  */
  0, 0, 0, 0,	/* 2: replaced with address of .got.plt + 4.  */
};

/* Sebsequent entries in an absolute procedure linkage table look like
   this.  */

static const bfd_byte elf_sh_plt_entry_be[ELF_PLT_ENTRY_SIZE] =
{
  0xd0, 0x04,	/* mov.l 1f,r0 */
  0x60, 0x02,	/* mov.l @(r0,r12),r0 */
  0xd1, 0x02,	/* mov.l 0f,r1 */
  0x40, 0x2b,   /* jmp @r0 */
  0x60, 0x13,	/*  mov r1,r0 */
  0xd1, 0x03,	/* mov.l 2f,r1 */
  0x40, 0x2b,	/* jmp @r0 */
  0x00, 0x09,	/* nop */
  0, 0, 0, 0,	/* 0: replaced with address of .PLT0.  */
  0, 0, 0, 0,	/* 1: replaced with address of this symbol in .got.  */
  0, 0, 0, 0,	/* 2: replaced with offset into relocation table.  */
};

static const bfd_byte elf_sh_plt_entry_le[ELF_PLT_ENTRY_SIZE] =
{
  0x04, 0xd0,	/* mov.l 1f,r0 */
  0x02, 0x60,	/* mov.l @r0,r0 */
  0x02, 0xd1,	/* mov.l 0f,r1 */
  0x2b, 0x40,   /* jmp @r0 */
  0x13, 0x60,	/*  mov r1,r0 */
  0x03, 0xd1,	/* mov.l 2f,r1 */
  0x2b, 0x40,	/* jmp @r0 */
  0x09, 0x00,	/*  nop */
  0, 0, 0, 0,	/* 0: replaced with address of .PLT0.  */
  0, 0, 0, 0,	/* 1: replaced with address of this symbol in .got.  */
  0, 0, 0, 0,	/* 2: replaced with offset into relocation table.  */
};

/* Entries in a PIC procedure linkage table look like this.  */

static const bfd_byte elf_sh_pic_plt_entry_be[ELF_PLT_ENTRY_SIZE] =
{
  0xd0, 0x04,	/* mov.l 1f,r0 */
  0x00, 0xce,	/* mov.l @(r0,r12),r0 */
  0x40, 0x2b,	/* jmp @r0 */
  0x00, 0x09,	/*  nop */
  0x50, 0xc2,	/* mov.l @(8,r12),r0 */
  0xd1, 0x03,	/* mov.l 2f,r1 */
  0x40, 0x2b,	/* jmp @r0 */
  0x50, 0xc1,	/*  mov.l @(4,r12),r0 */
  0x00, 0x09,	/* nop */
  0x00, 0x09,	/* nop */
  0, 0, 0, 0,	/* 1: replaced with address of this symbol in .got.  */
  0, 0, 0, 0    /* 2: replaced with offset into relocation table.  */
};

static const bfd_byte elf_sh_pic_plt_entry_le[ELF_PLT_ENTRY_SIZE] =
{
  0x04, 0xd0,	/* mov.l 1f,r0 */
  0xce, 0x00,	/* mov.l @(r0,r12),r0 */
  0x2b, 0x40,	/* jmp @r0 */
  0x09, 0x00,	/*  nop */
  0xc2, 0x50,	/* mov.l @(8,r12),r0 */
  0x03, 0xd1,	/* mov.l 2f,r1 */
  0x2b, 0x40,	/* jmp @r0 */
  0xc1, 0x50,	/*  mov.l @(4,r12),r0 */
  0x09, 0x00,	/*  nop */
  0x09, 0x00,	/* nop */
  0, 0, 0, 0,	/* 1: replaced with address of this symbol in .got.  */
  0, 0, 0, 0    /* 2: replaced with offset into relocation table.  */
};

static const struct elf_sh_plt_info elf_sh_plts[2][2] = {
  {
    {
      /* Big-endian non-PIC.  */
      elf_sh_plt0_entry_be,
      ELF_PLT_ENTRY_SIZE,
      { MINUS_ONE, 24, 20 },
      elf_sh_plt_entry_be,
      ELF_PLT_ENTRY_SIZE,
      { 20, 16, 24, false },
      8,
      NULL
    },
    {
      /* Little-endian non-PIC.  */
      elf_sh_plt0_entry_le,
      ELF_PLT_ENTRY_SIZE,
      { MINUS_ONE, 24, 20 },
      elf_sh_plt_entry_le,
      ELF_PLT_ENTRY_SIZE,
      { 20, 16, 24, false },
      8,
      NULL
    },
  },
  {
    {
      /* Big-endian PIC.  */
      elf_sh_plt0_entry_be,
      ELF_PLT_ENTRY_SIZE,
      { MINUS_ONE, MINUS_ONE, MINUS_ONE },
      elf_sh_pic_plt_entry_be,
      ELF_PLT_ENTRY_SIZE,
      { 20, MINUS_ONE, 24, false },
      8,
      NULL
    },
    {
      /* Little-endian PIC.  */
      elf_sh_plt0_entry_le,
      ELF_PLT_ENTRY_SIZE,
      { MINUS_ONE, MINUS_ONE, MINUS_ONE },
      elf_sh_pic_plt_entry_le,
      ELF_PLT_ENTRY_SIZE,
      { 20, MINUS_ONE, 24, false },
      8,
      NULL
    },
  }
};

#define VXWORKS_PLT_HEADER_SIZE 12
#define VXWORKS_PLT_ENTRY_SIZE 24

static const bfd_byte vxworks_sh_plt0_entry_be[VXWORKS_PLT_HEADER_SIZE] =
{
  0xd1, 0x01,	/* mov.l @(8,pc),r1 */
  0x61, 0x12,	/* mov.l @r1,r1 */
  0x41, 0x2b,	/* jmp @r1 */
  0x00, 0x09,	/* nop */
  0, 0, 0, 0	/* 0: replaced with _GLOBAL_OFFSET_TABLE+8.  */
};

static const bfd_byte vxworks_sh_plt0_entry_le[VXWORKS_PLT_HEADER_SIZE] =
{
  0x01, 0xd1,	/* mov.l @(8,pc),r1 */
  0x12, 0x61,	/* mov.l @r1,r1 */
  0x2b, 0x41,	/* jmp @r1 */
  0x09, 0x00,	/* nop */
  0, 0, 0, 0	/* 0: replaced with _GLOBAL_OFFSET_TABLE+8.  */
};

static const bfd_byte vxworks_sh_plt_entry_be[VXWORKS_PLT_ENTRY_SIZE] =
{
  0xd0, 0x01,	/* mov.l @(8,pc),r0 */
  0x60, 0x02,	/* mov.l @r0,r0 */
  0x40, 0x2b,	/* jmp @r0 */
  0x00, 0x09,	/* nop */
  0, 0, 0, 0,	/* 0: replaced with address of this symbol in .got.  */
  0xd0, 0x01,	/* mov.l @(8,pc),r0 */
  0xa0, 0x00,	/* bra PLT (We need to fix the offset.)  */
  0x00, 0x09,	/* nop */
  0x00, 0x09,	/* nop */
  0, 0, 0, 0,	/* 1: replaced with offset into relocation table.  */
};

static const bfd_byte vxworks_sh_plt_entry_le[VXWORKS_PLT_ENTRY_SIZE] =
{
  0x01, 0xd0,	/* mov.l @(8,pc),r0 */
  0x02, 0x60,	/* mov.l @r0,r0 */
  0x2b, 0x40,	/* jmp @r0 */
  0x09, 0x00,	/* nop */
  0, 0, 0, 0,	/* 0: replaced with address of this symbol in .got.  */
  0x01, 0xd0,	/* mov.l @(8,pc),r0 */
  0x00, 0xa0,	/* bra PLT (We need to fix the offset.)  */
  0x09, 0x00,	/* nop */
  0x09, 0x00,	/* nop */
  0, 0, 0, 0,	/* 1: replaced with offset into relocation table.  */
};

static const bfd_byte vxworks_sh_pic_plt_entry_be[VXWORKS_PLT_ENTRY_SIZE] =
{
  0xd0, 0x01,	/* mov.l @(8,pc),r0 */
  0x00, 0xce,	/* mov.l @(r0,r12),r0 */
  0x40, 0x2b,	/* jmp @r0 */
  0x00, 0x09,	/* nop */
  0, 0, 0, 0,	/* 0: replaced with offset of this symbol in .got.  */
  0xd0, 0x01,	/* mov.l @(8,pc),r0 */
  0x51, 0xc2,	/* mov.l @(8,r12),r1 */
  0x41, 0x2b,	/* jmp @r1 */
  0x00, 0x09,	/* nop */
  0, 0, 0, 0,	/* 1: replaced with offset into relocation table.  */
};

static const bfd_byte vxworks_sh_pic_plt_entry_le[VXWORKS_PLT_ENTRY_SIZE] =
{
  0x01, 0xd0,	/* mov.l @(8,pc),r0 */
  0xce, 0x00,	/* mov.l @(r0,r12),r0 */
  0x2b, 0x40,	/* jmp @r0 */
  0x09, 0x00,	/* nop */
  0, 0, 0, 0,	/* 0: replaced with offset of this symbol in .got.  */
  0x01, 0xd0,	/* mov.l @(8,pc),r0 */
  0xc2, 0x51,	/* mov.l @(8,r12),r1 */
  0x2b, 0x41,	/* jmp @r1 */
  0x09, 0x00,	/* nop */
  0, 0, 0, 0,	/* 1: replaced with offset into relocation table.  */
};

static const struct elf_sh_plt_info vxworks_sh_plts[2][2] = {
  {
    {
      /* Big-endian non-PIC.  */
      vxworks_sh_plt0_entry_be,
      VXWORKS_PLT_HEADER_SIZE,
      { MINUS_ONE, MINUS_ONE, 8 },
      vxworks_sh_plt_entry_be,
      VXWORKS_PLT_ENTRY_SIZE,
      { 8, 14, 20, false },
      12,
      NULL
    },
    {
      /* Little-endian non-PIC.  */
      vxworks_sh_plt0_entry_le,
      VXWORKS_PLT_HEADER_SIZE,
      { MINUS_ONE, MINUS_ONE, 8 },
      vxworks_sh_plt_entry_le,
      VXWORKS_PLT_ENTRY_SIZE,
      { 8, 14, 20, false },
      12,
      NULL
    },
  },
  {
    {
      /* Big-endian PIC.  */
      NULL,
      0,
      { MINUS_ONE, MINUS_ONE, MINUS_ONE },
      vxworks_sh_pic_plt_entry_be,
      VXWORKS_PLT_ENTRY_SIZE,
      { 8, MINUS_ONE, 20, false },
      12,
      NULL
    },
    {
      /* Little-endian PIC.  */
      NULL,
      0,
      { MINUS_ONE, MINUS_ONE, MINUS_ONE },
      vxworks_sh_pic_plt_entry_le,
      VXWORKS_PLT_ENTRY_SIZE,
      { 8, MINUS_ONE, 20, false },
      12,
      NULL
    },
  }
};

/* FDPIC PLT entries.  Two unimplemented optimizations for lazy
   binding are to omit the lazy binding stub when linking with -z now
   and to move lazy binding stubs into a separate region for better
   cache behavior.  */

#define FDPIC_PLT_ENTRY_SIZE 28
#define FDPIC_PLT_LAZY_OFFSET 20

/* FIXME: The lazy binding stub requires a plt0 - which may need to be
   duplicated if it is out of range, or which can be inlined.  So
   right now it is always inlined, which wastes a word per stub.  It
   might be easier to handle the duplication if we put the lazy
   stubs separately.  */

static const bfd_byte fdpic_sh_plt_entry_be[FDPIC_PLT_ENTRY_SIZE] =
{
  0xd0, 0x02,	/* mov.l @(12,pc),r0 */
  0x01, 0xce,	/* mov.l @(r0,r12),r1 */
  0x70, 0x04,	/* add #4, r0 */
  0x41, 0x2b,	/* jmp @r1 */
  0x0c, 0xce,	/* mov.l @(r0,r12),r12 */
  0x00, 0x09,	/* nop */
  0, 0, 0, 0,	/* 0: replaced with offset of this symbol's funcdesc */
  0, 0, 0, 0,	/* 1: replaced with offset into relocation table.  */
  0x60, 0xc2,	/* mov.l @r12,r0 */
  0x40, 0x2b,	/* jmp @r0 */
  0x53, 0xc1,	/*  mov.l @(4,r12),r3 */
  0x00, 0x09,	/* nop */
};

static const bfd_byte fdpic_sh_plt_entry_le[FDPIC_PLT_ENTRY_SIZE] =
{
  0x02, 0xd0,	/* mov.l @(12,pc),r0 */
  0xce, 0x01,	/* mov.l @(r0,r12),r1 */
  0x04, 0x70,	/* add #4, r0 */
  0x2b, 0x41,	/* jmp @r1 */
  0xce, 0x0c,	/* mov.l @(r0,r12),r12 */
  0x09, 0x00,	/* nop */
  0, 0, 0, 0,	/* 0: replaced with offset of this symbol's funcdesc */
  0, 0, 0, 0,	/* 1: replaced with offset into relocation table.  */
  0xc2, 0x60,	/* mov.l @r12,r0 */
  0x2b, 0x40,	/* jmp @r0 */
  0xc1, 0x53,	/*  mov.l @(4,r12),r3 */
  0x09, 0x00,	/* nop */
};

static const struct elf_sh_plt_info fdpic_sh_plts[2] = {
  {
    /* Big-endian PIC.  */
    NULL,
    0,
    { MINUS_ONE, MINUS_ONE, MINUS_ONE },
    fdpic_sh_plt_entry_be,
    FDPIC_PLT_ENTRY_SIZE,
    { 12, MINUS_ONE, 16, false },
    FDPIC_PLT_LAZY_OFFSET,
    NULL
  },
  {
    /* Little-endian PIC.  */
    NULL,
    0,
    { MINUS_ONE, MINUS_ONE, MINUS_ONE },
    fdpic_sh_plt_entry_le,
    FDPIC_PLT_ENTRY_SIZE,
    { 12, MINUS_ONE, 16, false },
    FDPIC_PLT_LAZY_OFFSET,
    NULL
  },
};

/* On SH2A, we can use the movi20 instruction to generate shorter PLT
   entries for the first 64K slots.  We use the normal FDPIC PLT entry
   past that point; we could also use movi20s, which might be faster,
   but would not be any smaller.  */

#define FDPIC_SH2A_PLT_ENTRY_SIZE 24
#define FDPIC_SH2A_PLT_LAZY_OFFSET 16

static const bfd_byte fdpic_sh2a_plt_entry_be[FDPIC_SH2A_PLT_ENTRY_SIZE] =
{
  0, 0, 0, 0,	/* movi20 #gotofffuncdesc,r0 */
  0x01, 0xce,	/* mov.l @(r0,r12),r1 */
  0x70, 0x04,	/* add #4, r0 */
  0x41, 0x2b,	/* jmp @r1 */
  0x0c, 0xce,	/* mov.l @(r0,r12),r12 */
  0, 0, 0, 0,	/* 1: replaced with offset into relocation table.  */
  0x60, 0xc2,	/* mov.l @r12,r0 */
  0x40, 0x2b,	/* jmp @r0 */
  0x53, 0xc1,	/*  mov.l @(4,r12),r3 */
  0x00, 0x09,	/* nop */
};

static const bfd_byte fdpic_sh2a_plt_entry_le[FDPIC_SH2A_PLT_ENTRY_SIZE] =
{
  0, 0, 0, 0,	/* movi20 #gotofffuncdesc,r0 */
  0xce, 0x01,	/* mov.l @(r0,r12),r1 */
  0x04, 0x70,	/* add #4, r0 */
  0x2b, 0x41,	/* jmp @r1 */
  0xce, 0x0c,	/* mov.l @(r0,r12),r12 */
  0, 0, 0, 0,	/* 1: replaced with offset into relocation table.  */
  0xc2, 0x60,	/* mov.l @r12,r0 */
  0x2b, 0x40,	/* jmp @r0 */
  0xc1, 0x53,	/*  mov.l @(4,r12),r3 */
  0x09, 0x00,	/* nop */
};

static const struct elf_sh_plt_info fdpic_sh2a_short_plt_be = {
  /* Big-endian FDPIC, max index 64K.  */
  NULL,
  0,
  { MINUS_ONE, MINUS_ONE, MINUS_ONE },
  fdpic_sh2a_plt_entry_be,
  FDPIC_SH2A_PLT_ENTRY_SIZE,
  { 0, MINUS_ONE, 12, true },
  FDPIC_SH2A_PLT_LAZY_OFFSET,
  NULL
};

static const struct elf_sh_plt_info fdpic_sh2a_short_plt_le = {
  /* Little-endian FDPIC, max index 64K.  */
  NULL,
  0,
  { MINUS_ONE, MINUS_ONE, MINUS_ONE },
  fdpic_sh2a_plt_entry_le,
  FDPIC_SH2A_PLT_ENTRY_SIZE,
  { 0, MINUS_ONE, 12, true },
  FDPIC_SH2A_PLT_LAZY_OFFSET,
  NULL
};

static const struct elf_sh_plt_info fdpic_sh2a_plts[2] = {
  {
    /* Big-endian PIC.  */
    NULL,
    0,
    { MINUS_ONE, MINUS_ONE, MINUS_ONE },
    fdpic_sh_plt_entry_be,
    FDPIC_PLT_ENTRY_SIZE,
    { 12, MINUS_ONE, 16, false },
    FDPIC_PLT_LAZY_OFFSET,
    &fdpic_sh2a_short_plt_be
  },
  {
    /* Little-endian PIC.  */
    NULL,
    0,
    { MINUS_ONE, MINUS_ONE, MINUS_ONE },
    fdpic_sh_plt_entry_le,
    FDPIC_PLT_ENTRY_SIZE,
    { 12, MINUS_ONE, 16, false },
    FDPIC_PLT_LAZY_OFFSET,
    &fdpic_sh2a_short_plt_le
  },
};

/* Return the type of PLT associated with ABFD.  PIC_P is true if
   the object is position-independent.  */

static const struct elf_sh_plt_info *get_plt_info(bfd *abfd, bool pic_p) {
    int is_big_endian = !bfd_big_endian(abfd);
    int arch = sh_get_arch_from_bfd_mach(bfd_get_mach(abfd));

    if (fdpic_object_p(abfd)) {
        return (arch & arch_sh2a_base) ? &fdpic_sh2a_plts[is_big_endian] : &fdpic_sh_plts[is_big_endian];
    } else if (vxworks_object_p(abfd)) {
        return &vxworks_sh_plts[pic_p][is_big_endian];
    } else {
        return &elf_sh_plts[pic_p][is_big_endian];
    }
}

/* Install a 32-bit PLT field starting at ADDR, which occurs in OUTPUT_BFD.
   VALUE is the field's value and CODE_P is true if VALUE refers to code,
   not data.  */

inline static void install_plt_field(bfd *output_bfd, unsigned long value, bfd_byte *addr) {
    if (output_bfd == NULL || addr == NULL) {
        return; // Error handling for null pointers
    }
    bfd_put_32(output_bfd, value, addr);
}

/* The number of PLT entries which can use a shorter PLT, if any.
   Currently always 64K, since only SH-2A FDPIC uses this; a
   20-bit movi20 can address that many function descriptors below
   _GLOBAL_OFFSET_TABLE_.  */
#define MAX_SHORT_PLT 65536

/* Return the index of the PLT entry at byte offset OFFSET.  */

static bfd_vma get_plt_index(const struct elf_sh_plt_info *info, bfd_vma offset) {
    if (info == NULL) {
        return 0;
    }

    if (offset < info->plt0_entry_size) {
        return 0;
    }

    offset -= info->plt0_entry_size;

    if (info->short_plt != NULL && offset > MAX_SHORT_PLT * info->short_plt->symbol_entry_size) {
        offset -= MAX_SHORT_PLT * info->short_plt->symbol_entry_size;
        return MAX_SHORT_PLT + offset / info->symbol_entry_size;
    }

    return offset / info->symbol_entry_size;
}

/* Do the inverse operation.  */

static bfd_vma get_plt_offset(const struct elf_sh_plt_info *info, bfd_vma plt_index) {
    bfd_vma offset = 0;

    if (info->short_plt != NULL && plt_index > MAX_SHORT_PLT) {
        offset = MAX_SHORT_PLT * info->short_plt->symbol_entry_size;
        plt_index -= MAX_SHORT_PLT;
    } else if (info->short_plt != NULL) {
        info = info->short_plt;
    }

    return offset + info->plt0_entry_size + (plt_index * info->symbol_entry_size);
}

union gotref
{
  bfd_signed_vma refcount;
  bfd_vma offset;
};

/* sh ELF linker hash entry.  */

struct elf_sh_link_hash_entry
{
  struct elf_link_hash_entry root;

  bfd_signed_vma gotplt_refcount;

  /* A local function descriptor, for FDPIC.  The refcount counts
     R_SH_FUNCDESC, R_SH_GOTOFFFUNCDESC, and R_SH_GOTOFFFUNCDESC20
     relocations; the PLT and GOT entry are accounted
     for separately.  After adjust_dynamic_symbol, the offset is
     MINUS_ONE if there is no local descriptor (dynamic linker
     managed and no PLT entry, or undefined weak non-dynamic).
     During check_relocs we do not yet know whether the local
     descriptor will be canonical.  */
  union gotref funcdesc;

  /* How many of the above refcounted relocations were R_SH_FUNCDESC,
     and thus require fixups or relocations.  */
  bfd_signed_vma abs_funcdesc_refcount;

  enum got_type {
    GOT_UNKNOWN = 0, GOT_NORMAL, GOT_TLS_GD, GOT_TLS_IE, GOT_FUNCDESC
  } got_type;
};

#define sh_elf_hash_entry(ent) ((struct elf_sh_link_hash_entry *)(ent))

struct sh_elf_obj_tdata
{
  struct elf_obj_tdata root;

  /* got_type for each local got entry.  */
  char *local_got_type;

  /* Function descriptor refcount and offset for each local symbol.  */
  union gotref *local_funcdesc;
};

#define sh_elf_tdata(abfd) \
  ((struct sh_elf_obj_tdata *) (abfd)->tdata.any)

#define sh_elf_local_got_type(abfd) \
  (sh_elf_tdata (abfd)->local_got_type)

#define sh_elf_local_funcdesc(abfd) \
  (sh_elf_tdata (abfd)->local_funcdesc)

#define is_sh_elf(bfd) \
  (bfd_get_flavour (bfd) == bfd_target_elf_flavour \
   && elf_tdata (bfd) != NULL \
   && elf_object_id (bfd) == SH_ELF_DATA)

/* Override the generic function because we need to store sh_elf_obj_tdata
   as the specific tdata.  */

static bool sh_elf_mkobject(bfd *abfd) {
  if (abfd == NULL) {
    return false;
  }
  return bfd_elf_allocate_object(abfd, sizeof(struct sh_elf_obj_tdata)) != NULL;
}

/* sh ELF linker hash table.  */

struct elf_sh_link_hash_table
{
  struct elf_link_hash_table root;

  /* Short-cuts to get to dynamic linker sections.  */
  asection *sfuncdesc;
  asection *srelfuncdesc;
  asection *srofixup;

  /* The (unloaded but important) VxWorks .rela.plt.unloaded section.  */
  asection *srelplt2;

  /* A counter or offset to track a TLS got entry.  */
  union
    {
      bfd_signed_vma refcount;
      bfd_vma offset;
    } tls_ldm_got;

  /* The type of PLT to use.  */
  const struct elf_sh_plt_info *plt_info;

  /* True if the target system uses FDPIC.  */
  bool fdpic_p;
};

/* Traverse an sh ELF linker hash table.  */

#define sh_elf_link_hash_traverse(table, func, info)			\
  (elf_link_hash_traverse						\
   (&(table)->root,							\
    (bool (*) (struct elf_link_hash_entry *, void *)) (func),		\
    (info)))

/* Get the sh ELF linker hash table from a link_info structure.  */

#define sh_elf_hash_table(p) \
  ((is_elf_hash_table ((p)->hash)					\
    && elf_hash_table_id (elf_hash_table (p)) == SH_ELF_DATA)		\
   ? (struct elf_sh_link_hash_table *) (p)->hash : NULL)

/* Create an entry in an sh ELF linker hash table.  */

static struct bfd_hash_entry *sh_elf_link_hash_newfunc(struct bfd_hash_entry *entry, struct bfd_hash_table *table, const char *string) {
    struct elf_sh_link_hash_entry *ret = (struct elf_sh_link_hash_entry *)entry;

    if (ret == NULL) {
        ret = (struct elf_sh_link_hash_entry *)bfd_hash_allocate(table, sizeof(struct elf_sh_link_hash_entry));
        if (ret == NULL) {
            return NULL;
        }
    }

    ret = (struct elf_sh_link_hash_entry *)_bfd_elf_link_hash_newfunc((struct bfd_hash_entry *)ret, table, string);
    if (ret != NULL) {
        ret->gotplt_refcount = 0;
        ret->funcdesc.refcount = 0;
        ret->abs_funcdesc_refcount = 0;
        ret->got_type = GOT_UNKNOWN;
    }

    return (struct bfd_hash_entry *)ret;
}

/* Create an sh ELF linker hash table.  */

#include <stdbool.h>
#include <stdlib.h>
#include <stddef.h>

static struct bfd_link_hash_table *sh_elf_link_hash_table_create(bfd *abfd) {
    struct elf_sh_link_hash_table *ret = bfd_zmalloc(sizeof(struct elf_sh_link_hash_table));
    if (!ret) {
        return NULL;
    }

    if (!_bfd_elf_link_hash_table_init(&ret->root, abfd, sh_elf_link_hash_newfunc, sizeof(struct elf_sh_link_hash_entry))) {
        free(ret);
        return NULL;
    }

    if (fdpic_object_p(abfd)) {
        ret->root.dt_pltgot_required = true;
        ret->fdpic_p = true;
    }

    return &ret->root.root;
}

static bool sh_elf_omit_section_dynsym(bfd *output_bfd ATTRIBUTE_UNUSED, struct bfd_link_info *info, asection *p) {
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);

    if (!htab->fdpic_p) {
        return true;
    }

    unsigned int sh_type = elf_section_data(p)->this_hdr.sh_type;
    
    if (sh_type == SHT_PROGBITS || sh_type == SHT_NOBITS || sh_type == SHT_NULL) {
        return false;
    }

    return true;
}

/* Create .got, .gotplt, and .rela.got sections in DYNOBJ, and set up
   shortcuts to them in our hash table.  */

static bool create_got_section(bfd *dynobj, struct bfd_link_info *info) {
    struct elf_sh_link_hash_table *htab;

    if (!_bfd_elf_create_got_section(dynobj, info))
        return false;

    htab = sh_elf_hash_table(info);
    if (!htab)
        return false;

    struct {
        const char* name;
        unsigned int flags;
        asection** section;
    } sections[] = {
        {".got.funcdesc", SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS | SEC_IN_MEMORY | SEC_LINKER_CREATED, &htab->sfuncdesc},
        {".rela.got.funcdesc", SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS | SEC_IN_MEMORY | SEC_LINKER_CREATED | SEC_READONLY, &htab->srelfuncdesc},
        {".rofixup", SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS | SEC_IN_MEMORY | SEC_LINKER_CREATED | SEC_READONLY, &htab->srofixup}
    };

    for (int i = 0; i < sizeof(sections) / sizeof(sections[0]); i++) {
        *sections[i].section = bfd_make_section_anyway_with_flags(dynobj, sections[i].name, sections[i].flags);
        if (!*sections[i].section || !bfd_set_section_alignment(*sections[i].section, 2))
            return false;
    }

    return true;
}

/* Create dynamic sections when linking against a dynamic object.  */

static bool sh_elf_create_dynamic_sections(bfd *abfd, struct bfd_link_info *info) {
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
  if (htab == NULL) return false;
  if (htab->root.dynamic_sections_created) return true;

  const struct elf_backend_data *bed = get_elf_backend_data(abfd);
  int ptralign = (bed->s->arch_size == 32) ? 2 : (bed->s->arch_size == 64) ? 3 : -1;
  if (ptralign == -1) {
    bfd_set_error(bfd_error_bad_value);
    return false;
  }

  flagword flags = SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS | SEC_IN_MEMORY | SEC_LINKER_CREATED;
  flagword pltflags = flags | SEC_CODE | (bed->plt_readonly ? SEC_READONLY : 0);
  if (bed->plt_not_loaded) {
    pltflags &= ~(SEC_LOAD | SEC_HAS_CONTENTS);
  }

  asection *s = bfd_make_section_anyway_with_flags(abfd, ".plt", pltflags);
  htab->root.splt = s;
  if (s == NULL || !bfd_set_section_alignment(s, bed->plt_alignment)) return false;

  if (bed->want_plt_sym) {
    struct bfd_link_hash_entry *bh = NULL;
    if (!_bfd_generic_link_add_one_symbol(info, abfd, "_PROCEDURE_LINKAGE_TABLE_", BSF_GLOBAL, s, (bfd_vma)0, NULL, false, bed->collect, &bh))
      return false;

    struct elf_link_hash_entry *h = (struct elf_link_hash_entry *)bh;
    h->def_regular = 1;
    h->type = STT_OBJECT;
    htab->root.hplt = h;
    if (bfd_link_pic(info) && !bfd_elf_link_record_dynamic_symbol(info, h))
      return false;
  }

  s = bfd_make_section_anyway_with_flags(abfd, bed->default_use_rela_p ? ".rela.plt" : ".rel.plt", flags | SEC_READONLY);
  htab->root.srelplt = s;
  if (s == NULL || !bfd_set_section_alignment(s, ptralign)) return false;

  if (htab->root.sgot == NULL && !create_got_section(abfd, info)) return false;

  if (bed->want_dynbss) {
    s = bfd_make_section_anyway_with_flags(abfd, ".dynbss", SEC_ALLOC | SEC_LINKER_CREATED);
    htab->root.sdynbss = s;
    if (s == NULL) return false;

    if (!bfd_link_pic(info)) {
      s = bfd_make_section_anyway_with_flags(abfd, bed->default_use_rela_p ? ".rela.bss" : ".rel.bss", flags | SEC_READONLY);
      htab->root.srelbss = s;
      if (s == NULL || !bfd_set_section_alignment(s, ptralign)) return false;
    }
  }

  if (htab->root.target_os == is_vxworks) {
    if (!elf_vxworks_create_dynamic_sections(abfd, info, &htab->srelplt2)) return false;
  }

  return true;
}

/* Adjust a symbol defined by a dynamic object and referenced by a
   regular object.  The current definition is in some section of the
   dynamic object, but we're not including those sections.  We have to
   change the definition to something the rest of the link can
   understand.  */

static bool sh_elf_adjust_dynamic_symbol(struct bfd_link_info *info, struct elf_link_hash_entry *h) {
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
    if (!htab || !htab->root.dynobj)
        return false;

    bool is_func_or_needs_plt = (h->type == STT_FUNC || h->needs_plt);
    bool undefined_weak_alias = (ELF_ST_VISIBILITY(h->other) != STV_DEFAULT && h->root.type == bfd_link_hash_undefweak);
    bool no_need_for_plt = (h->plt.refcount <= 0 || SYMBOL_CALLS_LOCAL(info, h) || undefined_weak_alias);
    
    if (is_func_or_needs_plt) {
        if (no_need_for_plt) {
            h->plt.offset = (bfd_vma)-1;
            h->needs_plt = 0;
        }
        return true;
    }

    h->plt.offset = (bfd_vma)-1;

    if (h->is_weakalias) {
        struct elf_link_hash_entry *def = weakdef(h);
        if (!def || def->root.type != bfd_link_hash_defined)
            return false;
        h->root.u.def.section = def->root.u.def.section;
        h->root.u.def.value = def->root.u.def.value;
        if (info->nocopyreloc)
            h->non_got_ref = def->non_got_ref;
        return true;
    }

    if (bfd_link_pic(info))
        return true;

    if (!h->non_got_ref || (0 && info->nocopyreloc)) {
        h->non_got_ref = 0;
        return true;
    }

    if (0 && !_bfd_elf_readonly_dynrelocs(h)) {
        h->non_got_ref = 0;
        return true;
    }

    asection *s = htab->root.sdynbss;
    if (!s)
        return false;

    if ((h->root.u.def.section->flags & SEC_ALLOC) != 0 && h->size != 0) {
        asection *srel = htab->root.srelbss;
        if (!srel)
            return false;
        srel->size += sizeof(Elf32_External_Rela);
        h->needs_copy = 1;
    }

    return _bfd_elf_adjust_dynamic_copy(info, h, s);
}

/* Allocate space in .plt, .got and associated reloc sections for
   dynamic relocs.  */

static bool allocate_dynrelocs(struct elf_link_hash_entry *h, void *inf) {
    struct bfd_link_info *info = (struct bfd_link_info *)inf;
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
    if (!htab) return false;

    if (h->root.type == bfd_link_hash_indirect) return true;
    struct elf_sh_link_hash_entry *eh = (struct elf_sh_link_hash_entry *)h;

    if ((h->got.refcount > 0 || h->forced_local) && eh->gotplt_refcount > 0) {
        h->got.refcount += eh->gotplt_refcount;
        if (h->plt.refcount >= eh->gotplt_refcount) {
            h->plt.refcount -= eh->gotplt_refcount;
        }
    }

    if (htab->root.dynamic_sections_created && h->plt.refcount > 0 &&
       (ELF_ST_VISIBILITY(h->other) == STV_DEFAULT || h->root.type != bfd_link_hash_undefweak)) {
        
        if (h->dynindx == -1 && !h->forced_local) {
            if (!bfd_elf_link_record_dynamic_symbol(info, h)) return false;
        }

        if (bfd_link_pic(info) || WILL_CALL_FINISH_DYNAMIC_SYMBOL(1, 0, h)) {
            asection *s = htab->root.splt;
            const struct elf_sh_plt_info *plt_info;

            if (s->size == 0) s->size += htab->plt_info->plt0_entry_size;
            h->plt.offset = s->size;

            if (!htab->fdpic_p && !bfd_link_pic(info) && !h->def_regular) {
                h->root.u.def.section = s;
                h->root.u.def.value = h->plt.offset;
            }

            plt_info = htab->plt_info;
            if (plt_info->short_plt != NULL &&
                (get_plt_index(plt_info->short_plt, s->size) < MAX_SHORT_PLT)) {
                plt_info = plt_info->short_plt;
            }
            s->size += plt_info->symbol_entry_size;

            htab->root.sgotplt->size += htab->fdpic_p ? 8 : 4;
            htab->root.srelplt->size += sizeof(Elf32_External_Rela);

            if (htab->root.target_os == is_vxworks && !bfd_link_pic(info)) {
                if (h->plt.offset == htab->plt_info->plt0_entry_size) {
                    htab->srelplt2->size += sizeof(Elf32_External_Rela);
                }
                htab->srelplt2->size += 2 * sizeof(Elf32_External_Rela);
            }
        } else {
            h->plt.offset = (bfd_vma)-1;
            h->needs_plt = 0;
        }
    } else {
        h->plt.offset = (bfd_vma)-1;
        h->needs_plt = 0;
    }

    if (h->got.refcount > 0) {
        asection *s = htab->root.sgot;
        enum got_type got_type = sh_elf_hash_entry(h)->got_type;
        
        if (h->dynindx == -1 && !h->forced_local) {
            if (!bfd_elf_link_record_dynamic_symbol(info, h)) return false;
        }

        h->got.offset = s->size;
        s->size += 4;
        if (got_type == GOT_TLS_GD) s->size += 4;

        bool dyn = htab->root.dynamic_sections_created;
        if (!dyn) {
            if (htab->fdpic_p && !bfd_link_pic(info) &&
                h->root.type != bfd_link_hash_undefweak &&
                (got_type == GOT_NORMAL || got_type == GOT_FUNCDESC)) {
                htab->srofixup->size += 4;
            }
        } else if (got_type == GOT_TLS_IE && !h->def_dynamic && !bfd_link_pic(info)) {
            // No dynamic relocations required when IE->LE conversion happens
        } else if ((got_type == GOT_TLS_GD && h->dynindx == -1) || got_type == GOT_TLS_IE) {
            htab->root.srelgot->size += sizeof(Elf32_External_Rela);
        } else if (got_type == GOT_TLS_GD) {
            htab->root.srelgot->size += 2 * sizeof(Elf32_External_Rela);
        } else if (got_type == GOT_FUNCDESC) {
            if (!bfd_link_pic(info) && SYMBOL_FUNCDESC_LOCAL(info, h)) {
                htab->srofixup->size += 4;
            } else {
                htab->root.srelgot->size += sizeof(Elf32_External_Rela);
            }
        } else if ((ELF_ST_VISIBILITY(h->other) == STV_DEFAULT ||
                    h->root.type != bfd_link_hash_undefweak) &&
                   (bfd_link_pic(info) || WILL_CALL_FINISH_DYNAMIC_SYMBOL(dyn, 0, h))) {
            htab->root.srelgot->size += sizeof(Elf32_External_Rela);
        } else if (htab->fdpic_p && !bfd_link_pic(info) && got_type == GOT_NORMAL &&
                   (ELF_ST_VISIBILITY(h->other) == STV_DEFAULT ||
                    h->root.type != bfd_link_hash_undefweak)) {
            htab->srofixup->size += 4;
        }
    } else {
        h->got.offset = (bfd_vma)-1;
    }

    if (eh->abs_funcdesc_refcount > 0 &&
        (h->root.type != bfd_link_hash_undefweak ||
         (htab->root.dynamic_sections_created && !SYMBOL_CALLS_LOCAL(info, h)))) {
        if (!bfd_link_pic(info) && SYMBOL_FUNCDESC_LOCAL(info, h)) {
            htab->srofixup->size += eh->abs_funcdesc_refcount * 4;
        } else {
            htab->root.srelgot->size += eh->abs_funcdesc_refcount * sizeof(Elf32_External_Rela);
        }
    }

    if ((eh->funcdesc.refcount > 0 ||
         (h->got.offset != MINUS_ONE && eh->got_type == GOT_FUNCDESC)) &&
        h->root.type != bfd_link_hash_undefweak &&
        SYMBOL_FUNCDESC_LOCAL(info, h)) {
        eh->funcdesc.offset = htab->sfuncdesc->size;
        htab->sfuncdesc->size += 8;

        if (!bfd_link_pic(info) && SYMBOL_CALLS_LOCAL(info, h)) {
            htab->srofixup->size += 8;
        } else {
            htab->srelfuncdesc->size += sizeof(Elf32_External_Rela);
        }
    }

    if (!h->dyn_relocs) return true;

    if (bfd_link_pic(info)) {
        if (SYMBOL_CALLS_LOCAL(info, h)) {
            struct elf_dyn_relocs **pp;
            for (pp = &h->dyn_relocs; (p = *pp) != NULL;) {
                p->count -= p->pc_count;
                p->pc_count = 0;
                if (!p->count) {
                    *pp = p->next;
                } else {
                    pp = &p->next;
                }
            }
        }

        if (htab->root.target_os == is_vxworks) {
            struct elf_dyn_relocs **pp;
            for (pp = &h->dyn_relocs; (p = *pp) != NULL;) {
                if (!strcmp(p->sec->output_section->name, ".tls_vars")) {
                    *pp = p->next;
                } else {
                    pp = &p->next;
                }
            }
        }

        if (h->dyn_relocs != NULL && h->root.type == bfd_link_hash_undefweak) {
            if (ELF_ST_VISIBILITY(h->other) != STV_DEFAULT ||
                UNDEFWEAK_NO_DYNAMIC_RELOC(info, h)) {
                h->dyn_relocs = NULL;
            } else if (h->dynindx == -1 && !h->forced_local) {
                if (!bfd_elf_link_record_dynamic_symbol(info, h)) return false;
            }
        }
    } else {
        if (!h->non_got_ref &&
            ((h->def_dynamic && !h->def_regular) ||
             (htab->root.dynamic_sections_created &&
              (h->root.type == bfd_link_hash_undefweak ||
               h->root.type == bfd_link_hash_undefined)))) {
            if (h->dynindx == -1 && !h->forced_local) {
                if (!bfd_elf_link_record_dynamic_symbol(info, h)) return false;
            }

            if (h->dynindx != -1) goto keep;
        }

        h->dyn_relocs = NULL;

    keep: ;
    }

    for (p = h->dyn_relocs; p != NULL; p = p->next) {
        asection *sreloc = elf_section_data(p->sec)->sreloc;
        sreloc->size += p->count * sizeof(Elf32_External_Rela);

        if (htab->fdpic_p && !bfd_link_pic(info)) {
            htab->srofixup->size -= 4 * (p->count - p->pc_count);
        }
    }

    return true;
}

/* This function is called after all the input files have been read,
   and the input sections have been assigned to output sections.
   It's a convenient place to determine the PLT style.  */

bool sh_elf_early_size_sections(bfd *output_bfd, struct bfd_link_info *info) {
    if (!output_bfd || !info) {
        return false;
    }

    struct sh_elf_hash_table *elf_hash_table = sh_elf_hash_table(info);
    if (!elf_hash_table) {
        return false;
    }

    elf_hash_table->plt_info = get_plt_info(output_bfd, bfd_link_pic(info));
    if (elf_hash_table->fdpic_p && !bfd_link_relocatable(info)) {
        if (!bfd_elf_stack_segment_size(output_bfd, info, "__stacksize", DEFAULT_STACK_SIZE)) {
            return false;
        }
    }

    return true;
}

/* Set the sizes of the dynamic sections.  */

static bool sh_elf_late_size_sections(bfd *output_bfd ATTRIBUTE_UNUSED, struct bfd_link_info *info) {
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
    if (htab == NULL) {
        return false;
    }

    bfd *dynobj = htab->root.dynobj;
    if (dynobj == NULL) {
        return true;
    }

    if (htab->root.dynamic_sections_created && bfd_link_executable(info) && !info->nointerp) {
        asection *s = bfd_get_linker_section(dynobj, ".interp");
        BFD_ASSERT(s != NULL);
        s->size = sizeof ELF_DYNAMIC_INTERPRETER;
        s->contents = (unsigned char *)ELF_DYNAMIC_INTERPRETER;
        s->alloced = 1;
    }

    for (bfd *ibfd = info->input_bfds; ibfd != NULL; ibfd = ibfd->link.next) {
        if (!is_sh_elf(ibfd)) {
            continue;
        }

        asection *srel = NULL;
        bfd_signed_vma *local_got = elf_local_got_refcounts(ibfd);
        bfd_size_type locsymcount = elf_symtab_hdr(ibfd).sh_info;

        for (asection *s = ibfd->sections; s != NULL; s = s->next) {
            for (struct elf_dyn_relocs *p = elf_section_data(s)->local_dynrel; p != NULL; p = p->next) {
                if (!bfd_is_abs_section(p->sec) && bfd_is_abs_section(p->sec->output_section)) {
                    continue;
                } else if (htab->root.target_os == is_vxworks && strcmp(p->sec->output_section->name, ".tls_vars") == 0) {
                    continue;
                } else if (p->count != 0) {
                    srel = elf_section_data(p->sec)->sreloc;
                    srel->size += p->count * sizeof(Elf32_External_Rela);
                    if (p->sec->output_section->flags & SEC_READONLY) {
                        info->flags |= DF_TEXTREL;
                        info->callbacks->minfo(_("%pB: dynamic relocation in read-only section `%pA'\n"), p->sec->owner, p->sec);
                    }
                    if (htab->fdpic_p && !bfd_link_pic(info)) {
                        htab->srofixup->size -= 4 * (p->count - p->pc_count);
                    }
                }
            }
        }

        if (local_got) {
            bfd_signed_vma *end_local_got = local_got + locsymcount;
            char *local_got_type = sh_elf_local_got_type(ibfd);
            union gotref *local_funcdesc = sh_elf_local_funcdesc(ibfd);
            for (; local_got < end_local_got; ++local_got) {
                if (*local_got > 0) {
                    *local_got = htab->root.sgot->size;
                    htab->root.sgot->size += 4;
                    if (*local_got_type == GOT_TLS_GD) {
                        htab->root.sgot->size += 4;
                    }
                    if (bfd_link_pic(info)) {
                        htab->root.srelgot->size += sizeof(Elf32_External_Rela);
                    } else {
                        htab->srofixup->size += 4;
                    }

                    if (*local_got_type == GOT_FUNCDESC) {
                        if (local_funcdesc == NULL) {
                            local_funcdesc = (union gotref *)bfd_zalloc(ibfd, locsymcount * sizeof(union gotref));
                            if (local_funcdesc == NULL) {
                                return false;
                            }
                            sh_elf_local_funcdesc(ibfd) = local_funcdesc;
                            local_funcdesc += (local_got - elf_local_got_refcounts(ibfd));
                        }
                        local_funcdesc->refcount++;
                        ++local_funcdesc;
                    }
                } else {
                    *local_got = (bfd_vma)-1;
                }
                ++local_got_type;
            }
        }

        union gotref *local_funcdesc = sh_elf_local_funcdesc(ibfd);
        if (local_funcdesc) {
            union gotref *end_local_funcdesc = local_funcdesc + locsymcount;
            for (; local_funcdesc < end_local_funcdesc; ++local_funcdesc) {
                if (local_funcdesc->refcount > 0) {
                    local_funcdesc->offset = htab->sfuncdesc->size;
                    htab->sfuncdesc->size += 8;
                    if (!bfd_link_pic(info)) {
                        htab->srofixup->size += 8;
                    } else {
                        htab->srelfuncdesc->size += sizeof(Elf32_External_Rela);
                    }
                } else {
                    local_funcdesc->offset = MINUS_ONE;
                }
            }
        }
    }

    if (htab->tls_ldm_got.refcount > 0) {
        htab->tls_ldm_got.offset = htab->root.sgot->size;
        htab->root.sgot->size += 8;
        htab->root.srelgot->size += sizeof(Elf32_External_Rela);
    } else {
        htab->tls_ldm_got.offset = -1;
    }

    if (htab->fdpic_p) {
        BFD_ASSERT(htab->root.sgotplt && htab->root.sgotplt->size == 12);
        htab->root.sgotplt->size = 0;
    }

    elf_link_hash_traverse(&htab->root, allocate_dynrelocs, info);

    if (htab->fdpic_p) {
        htab->root.hgot->root.u.def.value = htab->root.sgotplt->size;
        htab->root.sgotplt->size += 12;
    }

    if (htab->fdpic_p && htab->srofixup != NULL) {
        htab->srofixup->size += 4;
    }

    bool relocs = false;
    for (asection *s = dynobj->sections; s != NULL; s = s->next) {
        if ((s->flags & SEC_LINKER_CREATED) == 0) {
            continue;
        }

        if (s == htab->root.splt || s == htab->root.sgot || s == htab->root.sgotplt || s == htab->sfuncdesc || s == htab->srofixup || s == htab->root.sdynbss) {
            continue;
        } else if (startswith(bfd_section_name(s), ".rela")) {
            if (s->size != 0 && s != htab->root.srelplt && s != htab->srelplt2) {
                relocs = true;
            }
            s->reloc_count = 0;
        } else {
            continue;
        }

        if (s->size == 0) {
            s->flags |= SEC_EXCLUDE;
            continue;
        }

        if ((s->flags & SEC_HAS_CONTENTS) == 0) {
            continue;
        }

        s->contents = (bfd_byte *)bfd_zalloc(dynobj, s->size);
        if (s->contents == NULL) {
            return false;
        }
        s->alloced = 1;
    }

    return _bfd_elf_maybe_vxworks_add_dynamic_tags(output_bfd, info, relocs);
}

/* Add a dynamic relocation to the SRELOC section.  */

inline static bfd_vma sh_elf_add_dyn_reloc(bfd *output_bfd, asection *sreloc, bfd_vma offset, int reloc_type, long dynindx, bfd_vma addend) {
  if (!output_bfd || !sreloc || !sreloc->contents) {
    return (bfd_vma)-1; // error handling: invalid argument
  }

  Elf_Internal_Rela outrel;
  outrel.r_offset = offset;
  outrel.r_info = ELF32_R_INFO(dynindx, reloc_type);
  outrel.r_addend = addend;

  bfd_vma reloc_offset = sreloc->reloc_count * sizeof(Elf32_External_Rela);

  if (reloc_offset >= sreloc->size) {
    return (bfd_vma)-1; // error handling: buffer overflow issue
  }

  bfd_elf32_swap_reloca_out(output_bfd, &outrel, sreloc->contents + reloc_offset);
  sreloc->reloc_count++;

  return reloc_offset;
}

/* Add an FDPIC read-only fixup.  */

inline static void
sh_elf_add_rofixup(bfd *output_bfd, asection *srofixup, bfd_vma offset)
{
    if (srofixup->reloc_count >= srofixup->size / 4) {
        return; // Error handling: prevent overflow
    }

    bfd_vma fixup_offset = srofixup->reloc_count * 4;
    srofixup->reloc_count++;
    bfd_put_32(output_bfd, offset, srofixup->contents + fixup_offset);
}

/* Return the offset of the generated .got section from the
   _GLOBAL_OFFSET_TABLE_ symbol.  */

static bfd_signed_vma sh_elf_got_offset(struct elf_sh_link_hash_table *htab) {
    if (htab == NULL || htab->root.sgot == NULL || htab->root.sgotplt == NULL || htab->root.hgot == NULL) {
        return -1; // Error value indicating a problem
    }
    return htab->root.sgot->output_offset -
           htab->root.sgotplt->output_offset -
           htab->root.hgot->root.u.def.value;
}

/* Find the segment number in which OSEC, and output section, is
   located.  */

static unsigned sh_elf_osec_to_segment(bfd *output_bfd, asection *osec) {
    if (output_bfd->xvec->flavour != bfd_target_elf_flavour || output_bfd->direction == read_direction) {
        return -1;
    }

    Elf_Internal_Phdr *p = _bfd_elf_find_segment_containing_section(output_bfd, osec);
    return (p != NULL) ? p - elf_tdata(output_bfd)->phdr : -1;
}

#include <stdbool.h>

static bool sh_elf_osec_readonly_p(bfd *output_bfd, asection *osec) {
    unsigned seg = sh_elf_osec_to_segment(output_bfd, osec);

    if (seg == (unsigned)-1) {
        return false;
    }

    return !(elf_tdata(output_bfd)->phdr[seg].p_flags & PF_W);
}

/* Generate the initial contents of a local function descriptor, along
   with any relocations or fixups required.  */
bool sh_elf_initialize_funcdesc(bfd *output_bfd, struct bfd_link_info *info, struct elf_link_hash_entry *h, bfd_vma offset, asection *section, bfd_vma value) {
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
    bfd_vma addr, seg;
    int dynindx;

    if (h && SYMBOL_CALLS_LOCAL(info, h)) {
        section = h->root.u.def.section;
        value = h->root.u.def.value;
    }

    if (!h || SYMBOL_CALLS_LOCAL(info, h)) {
        dynindx = elf_section_data(section->output_section)->dynindx;
        addr = value + section->output_offset;
        seg = sh_elf_osec_to_segment(output_bfd, section->output_section);
    } else {
        if (h->dynindx == -1) return false;  // Ensure dynindx is valid
        dynindx = h->dynindx;
        addr = seg = 0;
    }

    if (!bfd_link_pic(info) && SYMBOL_CALLS_LOCAL(info, h)) {
        if (!h || h->root.type != bfd_link_hash_undefweak) {
            bfd_vma fixup_base = offset + htab->sfuncdesc->output_section->vma + htab->sfuncdesc->output_offset;
            sh_elf_add_rofixup(output_bfd, htab->srofixup, fixup_base);
            sh_elf_add_rofixup(output_bfd, htab->srofixup, fixup_base + 4);
        }

        addr += section->output_section->vma;
        seg = htab->root.hgot->root.u.def.value + htab->root.hgot->root.u.def.section->output_section->vma + htab->root.hgot->root.u.def.section->output_offset;
    } else {
        sh_elf_add_dyn_reloc(output_bfd, htab->srelfuncdesc, offset + htab->sfuncdesc->output_section->vma + htab->sfuncdesc->output_offset, R_SH_FUNCDESC_VALUE, dynindx, 0);
    }

    bfd_put_32(output_bfd, addr, htab->sfuncdesc->contents + offset);
    bfd_put_32(output_bfd, seg, htab->sfuncdesc->contents + offset + 4);

    return true;
}

/* Install a 20-bit movi20 field starting at ADDR, which occurs in OUTPUT_BFD.
   VALUE is the field's value.  Return bfd_reloc_ok if successful or an error
   otherwise.  */

static bfd_reloc_status_type install_movi20_field(bfd *output_bfd, unsigned long relocation, 
                                                  bfd *input_bfd, asection *input_section, 
                                                  bfd_byte *contents, bfd_vma offset) {
    if (offset > bfd_get_section_limit(input_bfd, input_section)) {
        return bfd_reloc_outofrange;
    }

    bfd_reloc_status_type overflow_status = bfd_check_overflow(complain_overflow_signed, 20, 0, 
                                                               bfd_arch_bits_per_address(input_bfd), 
                                                               relocation);
    if (overflow_status != bfd_reloc_ok) {
        return overflow_status;
    }

    bfd_byte *addr = contents + offset;
    unsigned long cur_val = bfd_get_16(output_bfd, addr);
    
    unsigned long upper_relocation = (relocation & 0xf0000) >> 12;
    unsigned long lower_relocation = relocation & 0xffff;

    bfd_put_16(output_bfd, cur_val | upper_relocation, addr);
    bfd_put_16(output_bfd, lower_relocation, addr + 2);

    return bfd_reloc_ok;
}

/* Relocate an SH ELF section.  */

```c
static int sh_elf_relocate_section(bfd *output_bfd, struct bfd_link_info *info,
                                   bfd *input_bfd, asection *input_section,
                                   bfd_byte *contents, Elf_Internal_Rela *relocs,
                                   Elf_Internal_Sym *local_syms,
                                   asection **local_sections) {
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
    Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr(input_bfd);
    struct elf_link_hash_entry **sym_hashes = elf_sym_hashes(input_bfd);
    bfd_vma *local_got_offsets = elf_local_got_offsets(input_bfd);
    asection *sgot = NULL, *sgotplt = NULL, *splt = NULL, *sreloc = NULL, *srelgot = NULL;
    bool is_vxworks_tls = false;
    bool fdpic_p = false;
    unsigned isec_segment, got_segment = -1, plt_segment = -1, check_segment[2];

    if (!is_sh_elf(input_bfd)) {
        bfd_set_error(bfd_error_wrong_format);
        return false;
    }

    if (htab) {
        sgot = htab->root.sgot;
        sgotplt = htab->root.sgotplt;
        srelgot = htab->root.srelgot;
        splt = htab->root.splt;
        fdpic_p = htab->fdpic_p;
    }

    isec_segment = sh_elf_osec_to_segment(output_bfd, input_section->output_section);
    if (fdpic_p && sgot) got_segment = sh_elf_osec_to_segment(output_bfd, sgot->output_section);
    if (fdpic_p && splt) plt_segment = sh_elf_osec_to_segment(output_bfd, splt->output_section);

    is_vxworks_tls = (htab && htab->root.target_os == is_vxworks && bfd_link_pic(info) &&
                      !strcmp(input_section->output_section->name, ".tls_vars"));

    for (Elf_Internal_Rela *rel = relocs; rel < relocs + input_section->reloc_count; rel++) {
        unsigned long r_symndx = ELF32_R_SYM(rel->r_info);
        int r_type = ELF32_R_TYPE(rel->r_info);

        if ((r_type >= R_SH_GNU_VTINHERIT && r_type <= R_SH_LABEL) || r_type == R_SH_NONE) continue;

        if (r_type < 0 || r_type >= R_SH_max ||
            ((r_type >= R_SH_FIRST_INVALID_RELOC && r_type <= R_SH_LAST_INVALID_RELOC) ||
             (r_type >= R_SH_FIRST_INVALID_RELOC_2 && r_type <= R_SH_LAST_INVALID_RELOC_2) ||
             (r_type >= R_SH_FIRST_INVALID_RELOC_3 && r_type <= R_SH_LAST_INVALID_RELOC_3) ||
             (r_type >= R_SH_FIRST_INVALID_RELOC_4 && r_type <= R_SH_LAST_INVALID_RELOC_4) ||
             (r_type >= R_SH_FIRST_INVALID_RELOC_5 && r_type <= R_SH_LAST_INVALID_RELOC_5) ||
             (r_type >= R_SH_FIRST_INVALID_RELOC_6 && r_type <= R_SH_LAST_INVALID_RELOC_6))) {
            bfd_set_error(bfd_error_bad_value);
            return false;
        }

        reloc_howto_type *howto = get_howto_table(output_bfd) + r_type;
        bfd_vma relocation = 0, addend = (bfd_vma)0;
        asection *sec = NULL;
        struct elf_link_hash_entry *h = NULL;
        bool resolved_to_zero = false;

        if (!howto->partial_inplace) addend = rel->r_addend;

        if (r_symndx < symtab_hdr->sh_info) {
            Elf_Internal_Sym *sym = local_syms + r_symndx;
            sec = local_sections[r_symndx];
            char *symname = bfd_elf_string_from_elf_section(input_bfd, symtab_hdr->sh_link, sym->st_name);

            if (!symname || *symname == '\0') symname = bfd_section_name(sec);
            if (!sec || discarded_section(sec)) continue;

            relocation = sec->output_section->vma + sec->output_offset + sym->st_value;

            if (bfd_link_relocatable(info)) {
                if (ELF_ST_TYPE(sym->st_info) == STT_SECTION) {
                    if (!howto->partial_inplace) {
                        rel->r_addend += sec->output_offset;
                        continue;
                    }
                    _bfd_relocate_contents(howto, input_bfd, sec->output_offset + sym->st_value, contents + rel->r_offset);
                }
                continue;
            }

            if (!howto->partial_inplace) {
                relocation = _bfd_elf_rela_local_sym(output_bfd, sym, &sec, rel);
                addend = rel->r_addend;
            } else if ((sec->flags & SEC_MERGE) && ELF_ST_TYPE(sym->st_info) == STT_SECTION) {
                if (howto->rightshift || howto->src_mask != 0xffffffff) {
                    _bfd_error_handler("%pB(%pA+%#" PRIx64 "): %s relocation against SEC_MERGE section", input_bfd, input_section, (uint64_t)rel->r_offset, howto->name);
                    return false;
                }

                addend = bfd_get_32(input_bfd, contents + rel->r_offset) - relocation;
                addend += sec->output_section->vma + sec->output_offset;
                bfd_put_32(input_bfd, addend, contents + rel->r_offset);
                addend = 0;
            }
        } else {
            h = sym_hashes[r_symndx - symtab_hdr->sh_info];
            while (h->root.type == bfd_link_hash_indirect || h->root.type == bfd_link_hash_warning) h = (struct elf_link_hash_entry *)h->root.u.i.link;

            if (h->root.type == bfd_link_hash_defined || h->root.type == bfd_link_hash_defweak) {
                sec = h->root.u.def.section;
                if (sec && sec->output_section) {
                    relocation = h->root.u.def.value + sec->output_section->vma + sec->output_offset;
                } else if (!bfd_link_relocatable(info) && _bfd_elf_section_offset(output_bfd, info, input_section, rel->r_offset) == (bfd_vma)-1) {
                    _bfd_error_handler("%pB(%pA+%#" PRIx64 "): unresolvable %s relocation against symbol `%s`", input_bfd, input_section, (uint64_t)rel->r_offset, howto->name, h->root.root.string);
                    return false;
                }
            } else if (h->root.type == bfd_link_hash_undefweak) {
                resolved_to_zero = UNDEFWEAK_NO_DYNAMIC_RELOC(info, h);
            } else if (info->unresolved_syms_in_objects == RM_IGNORE && ELF_ST_VISIBILITY(h->other) == STV_DEFAULT) {
                // no action
            } else if (!bfd_link_relocatable(info)) {
                info->callbacks->undefined_symbol(info, h->root.root.string, input_bfd, input_section, rel->r_offset,
                    (info->unresolved_syms_in_objects == RM_DIAGNOSE && !info->warn_unresolved_syms)
                    || ELF_ST_VISIBILITY(h->other));
            }
        }

        if (sec && discarded_section(sec))
            RELOC_AGAINST_DISCARDED_SECTION(info, input_bfd, input_section, rel, 1, relocs + input_section->reloc_count, R_SH_NONE, howto, 0, contents);

        if (bfd_link_relocatable(info)) continue;
        
        check_segment[0] = isec_segment;
        if (sec) check_segment[1] = sh_elf_osec_to_segment(output_bfd, sec->output_section);
        else check_segment[1] = -1;

        if (r_type == R_SH_DIR8UL || (r_type >= R_SH_DIR4U && r_type <= R_SH_DIR4UL)) {
            if (r_type == R_SH_DIR8UL || r_type == R_SH_DIR8UW || r_type == R_SH_DIR8SW) {
                if (relocation & ((r_type == R_SH_DIR8UL) ? 3 : 1)) {
                    _bfd_error_handler("%pB: %#" PRIx64 ": fatal: unaligned %s relocation %#" PRIx64, input_section->owner, (uint64_t)rel->r_offset, howto->name, (uint64_t)relocation);
                    bfd_set_error(bfd_error_bad_value);
                    return false;
                }
            }
            goto renault_final_link_relocate;
        } else if (r_type == R_SH_PSHA) {
            if ((signed int) relocation < -32 || (signed int) relocation > 32) {
                _bfd_error_handler("%pB: %#" PRIx64 ": fatal: R_SH_PSHA relocation %" PRId64 " not in range -32..32", input_section->owner, (uint64_t)rel->r_offset, (int64_t)relocation);
                bfd_set_error(bfd_error_bad_value);
                return false; 
            }
            goto renault_final_link_relocate;
        } else if (r_type == R_SH_LOOP_START) {
            static bfd_vma start, end;
            start = (relocation + rel->r_addend - (sec->output_section->vma + sec->output_offset));
            sh_elf_reloc_loop(r_type, input_bfd, input_section, contents, rel->r_offset, sec, start, end);
            continue;
        } else if (r_type == R_SH_LOOP_END) {
            static bfd_vma start, end;
            end = (relocation + rel->r_addend - (sec->output_section->vma + sec->output_offset));
            sh_elf_reloc_loop(r_type, input_bfd, input_section, contents, rel->r_offset, sec, start, end);
            continue;
        }

        if (fdpic_p && check_segment[0] != (unsigned) -1 && check_segment[0] != check_segment[1]) {
            if (!h || h->root.type != bfd_link_hash_undefined) {
                if (bfd_link_pic(info)) {
                    info->callbacks->einfo("%X%H: relocation to \"%s\" references a different segment\n", input_bfd, input_section, rel->r_offset, "some symbol");
                    return false;
                } else {
                    info->callbacks->einfo("%H: warning: relocation to \"%s\" references a different segment\n", input_bfd, input_section, rel->r_offset, "some symbol");
                }
            }
            elf_elfheader(output_bfd)->e_flags |= EF_SH_PIC;
        }

        bfd_reloc_status_type r = _bfd_final_link_relocate(howto, input_bfd, input_section, contents, rel->r_offset, relocation, addend);
        if (r != bfd_reloc_ok) {
            if (r == bfd_reloc_overflow) {
                const char *name = NULL;
                if (!h) {
                    name = bfd_elf_string_from_elf_section(input_bfd, symtab_hdr->sh_link, local_syms[r_symndx].st_name);
                    if (!name) return false;
                    if (*name == '\0') name = bfd_section_name(sec);
                }
                info->callbacks->reloc_overflow(info, (h ? &h->root : NULL), name, howto->name, 0, input_bfd, input_section, rel->r_offset);
            }
            return false;
        }
    }

    return true;
}
```

/* This is a version of bfd_generic_get_relocated_section_contents
   which uses sh_elf_relocate_section.  */

static bfd_byte *sh_elf_get_relocated_section_contents(bfd *output_bfd, struct bfd_link_info *link_info, struct bfd_link_order *link_order, bfd_byte *data, bool relocatable, asymbol **symbols) {
    Elf_Internal_Shdr *symtab_hdr;
    asection *input_section = link_order->u.indirect.section;
    bfd *input_bfd = input_section->owner;
    asection **sections = NULL;
    Elf_Internal_Rela *internal_relocs = NULL;
    Elf_Internal_Sym *isymbuf = NULL;

    if (relocatable || elf_section_data(input_section)->this_hdr.contents == NULL) {
        return bfd_generic_get_relocated_section_contents(output_bfd, link_info, link_order, data, relocatable, symbols);
    }

    symtab_hdr = &elf_symtab_hdr(input_bfd);

    bfd_byte *orig_data = data;
    if (!data && !(data = bfd_malloc(input_section->size))) {
        return NULL;
    }
    memcpy(data, elf_section_data(input_section)->this_hdr.contents, (size_t) input_section->size);

    if ((input_section->flags & SEC_RELOC) != 0 && input_section->reloc_count > 0) {
        internal_relocs = _bfd_elf_link_read_relocs(input_bfd, input_section, NULL, NULL, false);
        if (!internal_relocs) {
            goto error_cleanup;
        }

        if (symtab_hdr->sh_info != 0) {
            isymbuf = (Elf_Internal_Sym *)symtab_hdr->contents;
            if (!isymbuf) {
                isymbuf = bfd_elf_get_elf_syms(input_bfd, symtab_hdr, symtab_hdr->sh_info, 0, NULL, NULL, NULL);
                if (!isymbuf) {
                    goto error_cleanup;
                }
            }
        }

        bfd_size_type amt = symtab_hdr->sh_info * sizeof(asection *);
        sections = (asection **)bfd_malloc(amt);
        if (!sections && amt != 0) {
            goto error_cleanup;
        }

        Elf_Internal_Sym *isym = isymbuf, *isymend = isymbuf + symtab_hdr->sh_info;
        for (asection **secpp = sections; isym < isymend; ++isym, ++secpp) {
            if (isym->st_shndx == SHN_UNDEF) {
                *secpp = bfd_und_section_ptr;
            } else if (isym->st_shndx == SHN_ABS) {
                *secpp = bfd_abs_section_ptr;
            } else if (isym->st_shndx == SHN_COMMON) {
                *secpp = bfd_com_section_ptr;
            } else {
                *secpp = bfd_section_from_elf_index(input_bfd, isym->st_shndx);
            }
        }

        if (!sh_elf_relocate_section(output_bfd, link_info, input_bfd, input_section, data, internal_relocs, isymbuf, sections)) {
            goto error_cleanup;
        }

        free(sections);
        if (symtab_hdr->contents != (unsigned char *)isymbuf) {
            free(isymbuf);
        }
        if (elf_section_data(input_section)->relocs != internal_relocs) {
            free(internal_relocs);
        }
    }

    return data;

error_cleanup:
    free(sections);
    if (symtab_hdr->contents != (unsigned char *)isymbuf) {
        free(isymbuf);
    }
    if (elf_section_data(input_section)->relocs != internal_relocs) {
        free(internal_relocs);
    }
    if (!orig_data) {
        free(data);
    }
    return NULL;
}

/* Return the base VMA address which should be subtracted from real addresses
   when resolving @dtpoff relocation.
   This is PT_TLS segment p_vaddr.  */

static bfd_vma dtpoff_base(struct bfd_link_info *info) {
  struct bfd_tls *tls_sec = elf_hash_table(info)->tls_sec;
  if (tls_sec == NULL) {
    // Handle error if not already done
    fprintf(stderr, "Error: TLS section is NULL.\n");
    exit(EXIT_FAILURE);
  }
  return tls_sec->vma;
}

/* Return the relocation value for R_SH_TLS_TPOFF32..  */

static bfd_vma tpoff(struct bfd_link_info *info, bfd_vma address) {
    struct elf_link_hash_table *hash_table = elf_hash_table(info);
    if (hash_table == NULL || hash_table->tls_sec == NULL) {
        return 0;
    }
    
    bfd_vma aligned_offset = align_power((bfd_vma)8, hash_table->tls_sec->alignment_power);
    return address - hash_table->tls_sec->vma + aligned_offset;
}

static asection *sh_elf_gc_mark_hook(asection *sec, struct bfd_link_info *info, Elf_Internal_Rela *rel, struct elf_link_hash_entry *h, Elf_Internal_Sym *sym) {
    if (h != NULL && (ELF32_R_TYPE(rel->r_info) == R_SH_GNU_VTINHERIT || ELF32_R_TYPE(rel->r_info) == R_SH_GNU_VTENTRY)) {
        return NULL;
    }
    return _bfd_elf_gc_mark_hook(sec, info, rel, h, sym);
}

/* Copy the extra info we tack onto an elf_link_hash_entry.  */

static void sh_elf_copy_indirect_symbol(struct bfd_link_info *info, struct elf_link_hash_entry *dir, struct elf_link_hash_entry *ind) {
    struct elf_sh_link_hash_entry *edir = (struct elf_sh_link_hash_entry *) dir;
    struct elf_sh_link_hash_entry *eind = (struct elf_sh_link_hash_entry *) ind;

    edir->gotplt_refcount = eind->gotplt_refcount;
    eind->gotplt_refcount = 0;

    edir->funcdesc.refcount += eind->funcdesc.refcount;
    eind->funcdesc.refcount = 0;

    edir->abs_funcdesc_refcount += eind->abs_funcdesc_refcount;
    eind->abs_funcdesc_refcount = 0;

    if (ind->root.type == bfd_link_hash_indirect && dir->got.refcount <= 0) {
        edir->got_type = eind->got_type;
        eind->got_type = GOT_UNKNOWN;
    }

    if (ind->root.type != bfd_link_hash_indirect && dir->dynamic_adjusted) {
        if (dir->versioned != versioned_hidden) {
            dir->ref_dynamic |= ind->ref_dynamic;
        }
        dir->ref_regular |= ind->ref_regular;
        dir->ref_regular_nonweak |= ind->ref_regular_nonweak;
        dir->needs_plt |= ind->needs_plt;
    } else {
        _bfd_elf_link_hash_copy_indirect(info, dir, ind);
    }
}

static int sh_elf_optimized_tls_reloc(struct bfd_link_info *info, int r_type, int is_local) {
    if (bfd_link_pic(info)) {
        return r_type;
    }

    switch (r_type) {
        case R_SH_TLS_GD_32:
            if (!is_local) return R_SH_TLS_IE_32;
            // fall through
        case R_SH_TLS_IE_32:
        case R_SH_TLS_LD_32:
            return R_SH_TLS_LE_32;
        default:
            return r_type;
    }
}

/* Look through the relocs for a section during the first phase.
   Since we don't do .gots or .plts, we just need to consider the
   virtual table relocs for gc.  */

static bool sh_elf_check_relocs(bfd *abfd, struct bfd_link_info *info, asection *sec, const Elf_Internal_Rela *relocs) {
    Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr(abfd);
    struct elf_link_hash_entry **sym_hashes = elf_sym_hashes(abfd);
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
    const Elf_Internal_Rela *rel_end = relocs + sec->reloc_count;
    asection *sreloc = NULL;
    unsigned int r_type;
    enum got_type got_type, old_got_type;

    if (bfd_link_relocatable(info) || !htab) return true;
    BFD_ASSERT(is_sh_elf(abfd));

    for (const Elf_Internal_Rela *rel = relocs; rel < rel_end; rel++) {
        struct elf_link_hash_entry *h = NULL;
        unsigned long r_symndx = ELF32_R_SYM(rel->r_info);
        r_type = ELF32_R_TYPE(rel->r_info);

        if (r_symndx >= symtab_hdr->sh_info) {
            h = sym_hashes[r_symndx - symtab_hdr->sh_info];
            while (h && (h->root.type == bfd_link_hash_indirect || h->root.type == bfd_link_hash_warning)) {
                h = (struct elf_link_hash_entry *) h->root.u.i.link;
            }
        }

        r_type = sh_elf_optimized_tls_reloc(info, r_type, h == NULL);
        if (!bfd_link_pic(info) && r_type == R_SH_TLS_IE_32 && h && h->root.type != bfd_link_hash_undefined &&
            h->root.type != bfd_link_hash_undefweak && (h->dynindx == -1 || h->def_regular)) {
            r_type = R_SH_TLS_LE_32;
        }

        if (htab->fdpic_p) {
            switch (r_type) {
                case R_SH_GOTOFFFUNCDESC:
                case R_SH_GOTOFFFUNCDESC20:
                case R_SH_FUNCDESC:
                case R_SH_GOTFUNCDESC:
                case R_SH_GOTFUNCDESC20:
                    if (h && h->dynindx == -1) {
                        switch (ELF_ST_VISIBILITY(h->other)) {
                            case STV_INTERNAL:
                            case STV_HIDDEN:
                                break;
                            default:
                                bfd_elf_link_record_dynamic_symbol(info, h);
                                break;
                        }
                    }
                    break;
            }
        }

        if (!htab->root.sgot) {
            switch (r_type) {
                case R_SH_DIR32:
                    if (!htab->fdpic_p) break;
                case R_SH_GOTPLT32:
                case R_SH_GOT32:
                case R_SH_GOT20:
                case R_SH_GOTOFF:
                case R_SH_GOTOFF20:
                case R_SH_FUNCDESC:
                case R_SH_GOTFUNCDESC:
                case R_SH_GOTFUNCDESC20:
                case R_SH_GOTOFFFUNCDESC:
                case R_SH_GOTOFFFUNCDESC20:
                case R_SH_GOTPC:
                case R_SH_TLS_GD_32:
                case R_SH_TLS_LD_32:
                case R_SH_TLS_IE_32:
                    if (!htab->root.dynobj) htab->root.dynobj = abfd;
                    if (!create_got_section(htab->root.dynobj, info)) return false;
                    break;
            }
        }

        switch (r_type) {
            case R_SH_GNU_VTINHERIT:
                if (!bfd_elf_gc_record_vtinherit(abfd, sec, h, rel->r_offset)) return false;
                break;

            case R_SH_GNU_VTENTRY:
                if (!bfd_elf_gc_record_vtentry(abfd, sec, h, rel->r_addend)) return false;
                break;

            case R_SH_TLS_IE_32:
                if (bfd_link_pic(info)) info->flags |= DF_STATIC_TLS;
            case R_SH_TLS_GD_32:
            case R_SH_GOT32:
            case R_SH_GOT20:
            case R_SH_GOTFUNCDESC:
            case R_SH_GOTFUNCDESC20:
                got_type = determine_got_type(r_type);

                if (h) {
                    increment_got_refcount(h, got_type);
                    old_got_type = sh_elf_hash_entry(h)->got_type;
                } else {
                    if (!update_local_got_refcounts(abfd, r_symndx)) return false;
                    old_got_type = sh_elf_local_got_type(abfd)[r_symndx];
                }

                if (old_got_type != got_type && old_got_type != GOT_UNKNOWN &&
                    (old_got_type != GOT_TLS_GD || got_type != GOT_TLS_IE)) {
                    if (!merge_got_types(abfd, h, old_got_type, got_type)) return false;
                }

                if (old_got_type != got_type) {
                    if (h) sh_elf_hash_entry(h)->got_type = got_type;
                    else sh_elf_local_got_type(abfd)[r_symndx] = got_type;
                }
                break;

            case R_SH_TLS_LD_32:
                htab->tls_ldm_got.refcount++;
                break;

            case R_SH_FUNCDESC:
            case R_SH_GOTOFFFUNCDESC:
            case R_SH_GOTOFFFUNCDESC20:
                if (!process_function_desc_reloc(info, abfd, htab, h, rel, r_type)) return false;
                break;

            case R_SH_GOTPLT32:
                if (process_plt32_reloc(info, h)) goto force_got;
                break;

            case R_SH_PLT32:
                if (!process_plt32_reloc(info, h)) break;
                break;

            case R_SH_DIR32:
            case R_SH_REL32:
                if (!process_dir32_rel32_reloc(info, htab, abfd, sec, sreloc, r_type, r_symndx, h)) return false;
                break;

            case R_SH_TLS_LE_32:
                if (bfd_link_dll(info)) {
                    report_tls_error(abfd);
                    return false;
                }
                break;

            case R_SH_TLS_LDO_32:
                break;

            default:
                break;
        }
    }

    return true;
} 

enum got_type determine_got_type(unsigned int r_type) {
    switch (r_type) {
        case R_SH_TLS_GD_32:
            return GOT_TLS_GD;
        case R_SH_TLS_IE_32:
            return GOT_TLS_IE;
        case R_SH_GOTFUNCDESC:
        case R_SH_GOTFUNCDESC20:
            return GOT_FUNCDESC;
        default:
            return GOT_NORMAL;
    }
}

void increment_got_refcount(struct elf_link_hash_entry *h, enum got_type got_type) {
    h->got.refcount++;
}

bool update_local_got_refcounts(bfd *abfd, unsigned long r_symndx) {
    bfd_signed_vma *local_got_refcounts = elf_local_got_refcounts(abfd);
    if (!local_got_refcounts) {
        bfd_size_type size = elf_symtab_hdr(abfd).sh_info * (sizeof(bfd_signed_vma) + 1);
        local_got_refcounts = (bfd_signed_vma *) bfd_zalloc(abfd, size);
        if (!local_got_refcounts) return false;
        elf_local_got_refcounts(abfd) = local_got_refcounts;
        sh_elf_local_got_type(abfd) = (char *) (local_got_refcounts + elf_symtab_hdr(abfd).sh_info);
    }
    local_got_refcounts[r_symndx]++;
    return true;
}

bool merge_got_types(bfd *abfd, struct elf_link_hash_entry *h, enum got_type old_got_type, enum got_type got_type) {
    if (old_got_type == GOT_TLS_IE && got_type == GOT_TLS_GD) {
        got_type = GOT_TLS_IE;
    } else {
        const char *error_msg = nullptr;
        if ((old_got_type == GOT_FUNCDESC || got_type == GOT_FUNCDESC) &&
            (old_got_type == GOT_NORMAL || got_type == GOT_NORMAL)) {
            error_msg = _("accessed both as normal and FDPIC symbol");
        } else if (old_got_type == GOT_FUNCDESC || got_type == GOT_FUNCDESC) {
            error_msg = _("accessed both as FDPIC and thread local symbol");
        } else {
            error_msg = _("accessed both as normal and thread local symbol");
        }
        if (error_msg) {
            _bfd_error_handler(_("%pB: `%s' %s"), abfd, h ? h->root.root.string : "local", error_msg);
            return false;
        }
    }
    return true;
}

bool process_function_desc_reloc(struct bfd_link_info *info, bfd *abfd, struct elf_sh_link_hash_table *htab, struct elf_link_hash_entry *h, const Elf_Internal_Rela *rel, unsigned int r_type) {
    if (rel->r_addend) {
        report_function_desc_error(abfd);
        return false;
    }

    if (!h) {
        union gotref *local_funcdesc = sh_elf_local_funcdesc(abfd);
        if (!local_funcdesc) {
            local_funcdesc = create_local_funcdesc(abfd, htab);
            if (!local_funcdesc) return false;
        }
        increment_local_funcdesc_refcount(r_type, local_funcdesc, htab, abfd, symtab_hdr(abfd));
    } else {
        increment_funcdesc_refcount(r_type, h, info, htab);
    }
    return true;
}

union gotref *create_local_funcdesc(bfd *abfd, struct elf_sh_link_hash_table *htab) {
    bfd_size_type size = symtab_hdr(abfd).sh_info * sizeof(union gotref);
    union gotref *local_funcdesc = (union gotref *) bfd_zalloc(abfd, size);
    if (!local_funcdesc) return NULL;
    sh_elf_local_funcdesc(abfd) = local_funcdesc;
    return local_funcdesc;
}

void increment_local_funcdesc_refcount(unsigned int r_type, union gotref *local_funcdesc, struct elf_sh_link_hash_table *htab, bfd *abfd, const Elf_Internal_Shdr *symtab_hdr) {
    local_funcdesc[ELF32_R_SYM(symtab_hdr->sh_info)].refcount++;
    if (r_type == R_SH_FUNCDESC) {
        record_funcdesc_rofixup(htab, abfd);
    }
}

void increment_funcdesc_refcount(unsigned int r_type, struct elf_link_hash_entry *h, struct bfd_link_info *info, struct elf_sh_link_hash_table *htab) {
    sh_elf_hash_entry(h)->funcdesc.refcount++;
    if (r_type == R_SH_FUNCDESC) {
        sh_elf_hash_entry(h)->abs_funcdesc_refcount++;
        old_got_type = sh_elf_hash_entry(h)->got_type;
        if (old_got_type != GOT_FUNCDESC && old_got_type != GOT_UNKNOWN) {
            report_conflicting_funcdesc_error(old_got_type, h, info);
        }
    }
}

void record_funcdesc_rofixup(struct elf_sh_link_hash_table *htab, bfd *abfd) {
    if (!bfd_link_pic(info)) {
        htab->srofixup->size += 4;
    } else {
        htab->root.srelgot->size += sizeof(Elf32_External_Rela);
    }
}

bool process_plt32_reloc(struct bfd_link_info *info, struct elf_link_hash_entry *h) {
    if (!h || h->forced_local || !bfd_link_pic(info) || info->symbolic || h->dynindx == -1) return false;
    h->needs_plt = 1;
    h->plt.refcount++;
    ((struct elf_sh_link_hash_entry *)h)->gotplt_refcount++;
    return true;
}

bool process_dir32_rel32_reloc(struct bfd_link_info *info,
    struct elf_sh_link_hash_table *htab, bfd *abfd, asection *sec, asection *sreloc,
    unsigned int r_type, unsigned long r_symndx, struct elf_link_hash_entry *h) {
    if ((bfd_link_pic(info) && (sec->flags & SEC_ALLOC)
        && (r_type != R_SH_REL32 || (h && (!info->symbolic || h->root.type == bfd_link_hash_defweak || !h->def_regular))))
        || (!bfd_link_pic(info) && (sec->flags & SEC_ALLOC) && h
            && (h->root.type == bfd_link_hash_defweak || !h->def_regular))) {
        
        if (!update_dynamic_relocs(info, htab, abfd, sec, sreloc, h, r_symndx, r_type)) return false;
    }

    if (htab->fdpic_p && !bfd_link_pic(info) && r_type == R_SH_DIR32 && (sec->flags & SEC_ALLOC)) {
        htab->srofixup->size += 4;
    }
    return true;
}

bool update_dynamic_relocs(struct bfd_link_info *info, struct elf_sh_link_hash_table *htab, bfd *abfd, asection *sec, asection *sreloc, struct elf_link_hash_entry *h, unsigned long r_symndx, unsigned int r_type) {
    struct elf_dyn_relocs **head;
    
    if (!htab->root.dynobj) {
        htab->root.dynobj = abfd;
    }
    
    if (!sreloc) {
        sreloc = _bfd_elf_make_dynamic_reloc_section(sec, htab->root.dynobj, 2, abfd, true);
        if (!sreloc) return false;
    }
    
    
    if (h) {
        head = &h->dyn_relocs;
    } else {
        asection *s;
        Elf_Internal_Sym *isym = bfd_sym_from_r_symndx(&htab->root.sym_cache, abfd, r_symndx);
        if (!isym) return false;
        
        s = bfd_section_from_elf_index(abfd, isym->st_shndx);
        if (!s) s = sec;
        
        head = (struct elf_dyn_relocs **)&elf_section_data(s)->local_dynrel;
    }
    
    struct elf_dyn_relocs *p = *head;
    if (!p || p->sec != sec) {
        size_t amt = sizeof(*p);
        p = bfd_alloc(htab->root.dynobj, amt);
        if (!p) return false;
        p->next = *head;
        *head = p;
        p->sec = sec;
        p->count = 0;
        p->pc_count = 0;
    }
    
    p->count++;
    if (r_type == R_SH_REL32) p->pc_count++;
    return true;
}

void report_tls_error(bfd *abfd) {
    _bfd_error_handler(_("%pB: TLS local exec code cannot be linked into shared objects"), abfd);
}

void report_function_desc_error(bfd *abfd) {
    _bfd_error_handler(_("%pB: Function descriptor relocation with non-zero addend"), abfd);
}

void report_conflicting_funcdesc_error(enum got_type old_got_type, struct elf_link_hash_entry *h, struct bfd_link_info *info) {
    if (old_got_type == GOT_NORMAL) {
        _bfd_error_handler(_("%pB: `%s' accessed both as normal and FDPIC symbol"), h->root.root.string);
    } else {
        _bfd_error_handler(_("%pB: `%s' accessed both as FDPIC and thread local symbol"), h->root.root.string);
    }
}

#ifndef sh_elf_set_mach_from_flags
static unsigned int sh_ef_bfd_table[] = { EF_SH_BFD_TABLE };

static bool
sh_elf_set_mach_from_flags (bfd *abfd)
{
  flagword flags = elf_elfheader (abfd)->e_flags & EF_SH_MACH_MASK;

  if (flags >= ARRAY_SIZE (sh_ef_bfd_table) || sh_ef_bfd_table[flags] == 0)
    return false;

  bfd_default_set_arch_mach (abfd, bfd_arch_sh, sh_ef_bfd_table[flags]);

  return true;
}


/* Reverse table lookup for sh_ef_bfd_table[].
   Given a bfd MACH value from archures.c
   return the equivalent ELF flags from the table.
   Return -1 if no match is found.  */

int sh_elf_get_flags_from_mach(unsigned long mach) {
    for (int i = ARRAY_SIZE(sh_ef_bfd_table) - 1; i > 0; i--) {
        if (sh_ef_bfd_table[i] == mach) {
            return i;
        }
    }
    return -1;
}
#endif /* not sh_elf_set_mach_from_flags */

#ifndef sh_elf_copy_private_data
/* Copy backend specific data from one object module to another */

static bool sh_elf_copy_private_data(bfd *ibfd, bfd *obfd) {
  if (!is_sh_elf(ibfd) || !is_sh_elf(obfd)) {
    return true;
  }

  return _bfd_elf_copy_private_bfd_data(ibfd, obfd) && sh_elf_set_mach_from_flags(obfd);
}
#endif /* not sh_elf_copy_private_data */

#ifndef sh_elf_merge_private_data

/* This function returns the ELF architecture number that
   corresponds to the given arch_sh* flags.  */

#include <stddef.h>

int sh_find_elf_flags(unsigned int arch_set) {
    if (arch_set == 0) return -1;
    
    extern unsigned long sh_get_bfd_mach_from_arch_set(unsigned int);
    extern int sh_elf_get_flags_from_mach(unsigned long);

    unsigned long bfd_mach = sh_get_bfd_mach_from_arch_set(arch_set);
    if (bfd_mach == 0) return -1;

    int flags = sh_elf_get_flags_from_mach(bfd_mach);
    return flags;
}

/* Merge the architecture type of two BFD files, such that the
   resultant architecture supports all the features required
   by the two input BFDs.
   If the input BFDs are multually incompatible - i.e. one uses
   DSP while the other uses FPU - or there is no known architecture
   that fits the requirements then an error is emitted.  */

static bool sh_merge_bfd_arch(bfd *ibfd, struct bfd_link_info *info) {
    bfd *obfd = info->output_bfd;
    if (!_bfd_generic_verify_endian_match(ibfd, info)) {
        return false;
    }

    unsigned int old_arch = sh_get_arch_up_from_bfd_mach(bfd_get_mach(obfd));
    unsigned int new_arch = sh_get_arch_up_from_bfd_mach(bfd_get_mach(ibfd));
    unsigned int merged_arch = SH_MERGE_ARCH_SET(old_arch, new_arch);

    if (!SH_VALID_CO_ARCH_SET(merged_arch) || !SH_VALID_ARCH_SET(merged_arch)) {
        const char *new_arch_type = SH_ARCH_SET_HAS_DSP(new_arch) ? "dsp" : "floating point";
        const char *old_arch_type = SH_ARCH_SET_HAS_DSP(old_arch) ? "dsp" : "floating point";

        if (!SH_VALID_CO_ARCH_SET(merged_arch)) {
            _bfd_error_handler(_("%pB: uses %s instructions while previous modules use %s instructions"),
                               ibfd, new_arch_type, old_arch_type);
        } else {
            _bfd_error_handler(_("internal error: merge of architecture '%s' with architecture '%s' produced unknown architecture"),
                               bfd_printable_name(obfd), bfd_printable_name(ibfd));
        }

        bfd_set_error(bfd_error_bad_value);
        return false;
    }

    bfd_default_set_arch_mach(obfd, bfd_arch_sh, sh_get_bfd_mach_from_arch_set(merged_arch));
    return true;
}

/* This routine initialises the elf flags when required and
   calls sh_merge_bfd_arch() to check dsp/fpu compatibility.  */

bool sh_elf_merge_private_data(bfd *ibfd, struct bfd_link_info *info) {
    bfd *obfd = info->output_bfd;

    if ((ibfd->flags & DYNAMIC) != 0 || !is_sh_elf(ibfd) || !is_sh_elf(obfd)) {
        return true;
    }

    if (!elf_flags_init(obfd)) {
        elf_flags_init(obfd) = true;
        elf_elfheader(obfd)->e_flags = elf_elfheader(ibfd)->e_flags;
        sh_elf_set_mach_from_flags(obfd);
        if (elf_elfheader(obfd)->e_flags & EF_SH_FDPIC) {
            elf_elfheader(obfd)->e_flags &= ~EF_SH_PIC;
        }
    }

    if (!sh_merge_bfd_arch(ibfd, info)) {
        _bfd_error_handler(_("%pB: uses instructions which are incompatible "
                             "with instructions used in previous modules"), ibfd);
        bfd_set_error(bfd_error_bad_value);
        return false;
    }

    elf_elfheader(obfd)->e_flags = (elf_elfheader(obfd)->e_flags & ~EF_SH_MACH_MASK) 
                                   | sh_elf_get_flags_from_mach(bfd_get_mach(obfd));

    if (fdpic_object_p(ibfd) != fdpic_object_p(obfd)) {
        _bfd_error_handler(_("%pB: attempt to mix FDPIC and non-FDPIC objects"), ibfd);
        bfd_set_error(bfd_error_bad_value);
        return false;
    }

    return true;
}
#endif /* not sh_elf_merge_private_data */

/* Override the generic function because we need to store sh_elf_obj_tdata
   as the specific tdata.  We set also the machine architecture from flags
   here.  */

static bool sh_elf_object_p(bfd *abfd) {
    if (!sh_elf_set_mach_from_flags(abfd)) {
        return false;
    }

    bool ef_sh_fdpic = (elf_elfheader(abfd)->e_flags & EF_SH_FDPIC) != 0;
    return ef_sh_fdpic == fdpic_object_p(abfd);
}

/* Finish up dynamic symbol handling.  We set the contents of various
   dynamic sections here.  */

static bool
sh_elf_finish_dynamic_symbol(bfd *output_bfd, struct bfd_link_info *info,
                             struct elf_link_hash_entry *h, Elf_Internal_Sym *sym)
{
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
    if (!htab) return false;

    if (h->plt.offset != (bfd_vma)-1)
    {
        asection *splt = htab->root.splt;
        asection *sgotplt = htab->root.sgotplt;
        asection *srelplt = htab->root.srelplt;

        if (!(splt && sgotplt && srelplt && h->dynindx != -1)) return false;

        bfd_vma plt_index = get_plt_index(htab->plt_info, h->plt.offset);
        const struct elf_sh_plt_info *plt_info = (htab->plt_info->short_plt && plt_index <= MAX_SHORT_PLT)
                                                     ? htab->plt_info->short_plt
                                                     : htab->plt_info;

        bfd_vma got_offset = (htab->fdpic_p)
                                 ? plt_index * 8 + 12 - sgotplt->size
                                 : (plt_index + 3) * 4;

#ifdef GOT_BIAS
        if (bfd_link_pic(info))
            got_offset -= GOT_BIAS;
#endif

        memcpy(splt->contents + h->plt.offset, plt_info->symbol_entry, plt_info->symbol_entry_size);

        if (bfd_link_pic(info) || htab->fdpic_p)
        {
            if (plt_info->symbol_fields.got20)
            {
                if (install_movi20_field(output_bfd, got_offset, splt->owner, splt, splt->contents,
                                         h->plt.offset + plt_info->symbol_fields.got_entry) != bfd_reloc_ok)
                {
                    return false;
                }
            }
            else
            {
                install_plt_field(output_bfd, false, got_offset, splt->contents + h->plt.offset + plt_info->symbol_fields.got_entry);
            }
        }
        else
        {
            if (!plt_info->symbol_fields.got20)
            {
                install_plt_field(output_bfd, false, sgotplt->output_section->vma + sgotplt->output_offset + got_offset,
                                  splt->contents + h->plt.offset + plt_info->symbol_fields.got_entry);
                if (htab->root.target_os == is_vxworks)
                {
                    unsigned int reachable_plts = (4096 - plt_info->plt0_entry_size - (plt_info->symbol_fields.plt + 4)) /
                                                    plt_info->symbol_entry_size +
                                                  1;
                    unsigned int plts_per_4k = 4096 / plt_info->symbol_entry_size;
                    int distance = (plt_index < reachable_plts)
                                       ? -(h->plt.offset + plt_info->symbol_fields.plt)
                                       : -(((plt_index - reachable_plts) % plts_per_4k + 1) * plt_info->symbol_entry_size);

                    bfd_put_16(output_bfd, 0xa000 | (0x0fff & ((distance - 4) / 2)),
                               splt->contents + h->plt.offset + plt_info->symbol_fields.plt);
                }
                else
                {
                    install_plt_field(output_bfd, true, splt->output_section->vma + splt->output_offset,
                                      splt->contents + h->plt.offset + plt_info->symbol_fields.plt);
                }
            }
        }

#ifdef GOT_BIAS
        if (bfd_link_pic(info))
            got_offset += GOT_BIAS;
#endif

        if (htab->fdpic_p)
            got_offset = plt_index * 8;

        if (plt_info->symbol_fields.reloc_offset != MINUS_ONE)
        {
            install_plt_field(output_bfd, false,
                              plt_index * sizeof(Elf32_External_Rela),
                              splt->contents + h->plt.offset + plt_info->symbol_fields.reloc_offset);
        }

        bfd_put_32(output_bfd,
                   splt->output_section->vma + splt->output_offset + h->plt.offset + plt_info->symbol_resolve_offset,
                   sgotplt->contents + got_offset);

        if (htab->fdpic_p)
        {
            bfd_put_32(output_bfd, sh_elf_osec_to_segment(output_bfd, splt->output_section),
                       sgotplt->contents + got_offset + 4);
        }

        Elf_Internal_Rela rel = {
            .r_offset = sgotplt->output_section->vma + sgotplt->output_offset + got_offset,
            .r_addend = 0
#ifdef GOT_BIAS
        };
        if (bfd_link_pic(info))
        {
            rel.r_addend = GOT_BIAS;
#endif

            if (htab->fdpic_p)
            {
                rel.r_info = ELF32_R_INFO(h->dynindx, R_SH_FUNCDESC_VALUE);
            }
            else
            {
                rel.r_info = ELF32_R_INFO(h->dynindx, R_SH_JMP_SLOT);
            }

            bfd_byte *loc = srelplt->contents + plt_index * sizeof(Elf32_External_Rela);
            bfd_elf32_swap_reloca_out(output_bfd, &rel, loc);

            if (htab->root.target_os == is_vxworks && !bfd_link_pic(info))
            {
                loc = htab->srelplt2->contents + (plt_index * 2 + 1) * sizeof(Elf32_External_Rela);
                rel.r_offset = splt->output_section->vma + splt->output_offset + h->plt.offset +
                               plt_info->symbol_fields.got_entry;
                rel.r_info = ELF32_R_INFO(htab->root.hgot->indx, R_SH_DIR32);
                rel.r_addend = got_offset;
                bfd_elf32_swap_reloca_out(output_bfd, &rel, loc);
                loc += sizeof(Elf32_External_Rela);

                rel.r_offset = sgotplt->output_section->vma + sgotplt->output_offset + got_offset;
                rel.r_info = ELF32_R_INFO(htab->root.hplt->indx, R_SH_DIR32);
                rel.r_addend = 0;
                bfd_elf32_swap_reloc_out(output_bfd, &rel, loc);
            }
        }

        if (!h->def_regular)
        {
            sym->st_shndx = SHN_UNDEF;
        }
    }

    if (h->got.offset != (bfd_vma)-1 && sh_elf_hash_entry(h)->got_type != GOT_TLS_GD &&
        sh_elf_hash_entry(h)->got_type != GOT_TLS_IE && sh_elf_hash_entry(h)->got_type != GOT_FUNCDESC)
    {
        asection *sgot = htab->root.sgot;
        asection *srelgot = htab->root.srelgot;
        if (!(sgot && srelgot)) return false;

        Elf_Internal_Rela rel = {
            .r_offset = sgot->output_section->vma + sgot->output_offset + (h->got.offset & ~(bfd_vma)1),
        };

        if (bfd_link_pic(info) && (h->root.type == bfd_link_hash_defined || h->root.type == bfd_link_hash_defweak) &&
            SYMBOL_REFERENCES_LOCAL(info, h))
        {
            if (htab->fdpic_p)
            {
                asection *sec = h->root.u.def.section;
                int dynindx = elf_section_data(sec->output_section)->dynindx;

                rel.r_info = ELF32_R_INFO(dynindx, R_SH_DIR32);
                rel.r_addend = h->root.u.def.value + h->root.u.def.section->output_offset;
            }
            else
            {
                rel.r_info = ELF32_R_INFO(0, R_SH_RELATIVE);
                rel.r_addend = h->root.u.def.value + h->root.u.def.section->output_section->vma +
                               h->root.u.def.section->output_offset;
            }
        }
        else
        {
            bfd_put_32(output_bfd, (bfd_vma)0, sgot->contents + h->got.offset);
            rel.r_info = ELF32_R_INFO(h->dynindx, R_SH_GLOB_DAT);
            rel.r_addend = 0;
        }

        bfd_byte *loc = srelgot->contents + srelgot->reloc_count++ * sizeof(Elf32_External_Rela);
        bfd_elf32_swap_reloca_out(output_bfd, &rel, loc);
    }

    if (h->needs_copy)
    {
        if (h->dynindx == -1 || !(h->root.type == bfd_link_hash_defined || h->root.type == bfd_link_hash_defweak))
            return false;

        asection *s = bfd_get_linker_section(htab->root.dynobj, ".rela.bss");
        if (!s) return false;

        Elf_Internal_Rela rel = {
            .r_offset = h->root.u.def.value + h->root.u.def.section->output_section->vma +
                        h->root.u.def.section->output_offset,
            .r_info = ELF32_R_INFO(h->dynindx, R_SH_COPY),
            .r_addend = 0};
        bfd_byte *loc = s->contents + s->reloc_count++ * sizeof(Elf32_External_Rela);
        bfd_elf32_swap_reloca_out(output_bfd, &rel, loc);
    }

    if (h == htab->root.hdynamic || (htab->root.target_os != is_vxworks && h == htab->root.hgot))
    {
        sym->st_shndx = SHN_ABS;
    }

    return true;
}

/* Finish up the dynamic sections.  */

static bool sh_elf_finish_dynamic_sections(bfd *output_bfd, struct bfd_link_info *info) {
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
    if (!htab) return false;

    asection *sgotplt = htab->root.sgotplt;
    asection *sdyn = bfd_get_linker_section(htab->root.dynobj, ".dynamic");

    if (htab->root.dynamic_sections_created) {
        BFD_ASSERT(sgotplt && sdyn);

        Elf32_External_Dyn *dyncon = (Elf32_External_Dyn *) sdyn->contents;
        Elf32_External_Dyn *dynconend = (Elf32_External_Dyn *) (sdyn->contents + sdyn->size);

        while (dyncon < dynconend) {
            Elf_Internal_Dyn dyn;
            asection *s;

            bfd_elf32_swap_dyn_in(htab->root.dynobj, dyncon, &dyn);
            bool vxworks_entry = (htab->root.target_os == is_vxworks && elf_vxworks_finish_dynamic_entry(output_bfd, &dyn));

            switch (dyn.d_tag) {
                case DT_PLTGOT:
                    BFD_ASSERT(htab->root.hgot);
                    s = htab->root.hgot->root.u.def.section;
                    dyn.d_un.d_ptr = htab->root.hgot->root.u.def.value + s->output_section->vma + s->output_offset;
                    break;
                case DT_JMPREL:
                    s = htab->root.srelplt;
                    dyn.d_un.d_ptr = s->output_section->vma + s->output_offset;
                    break;
                case DT_PLTRELSZ:
                    s = htab->root.srelplt;
                    dyn.d_un.d_val = s->size;
                    break;
                default:
                    if (vxworks_entry) bfd_elf32_swap_dyn_out(output_bfd, &dyn, dyncon);
                    break;
            }

            if (dyn.d_tag == DT_PLTGOT || dyn.d_tag == DT_JMPREL || dyn.d_tag == DT_PLTRELSZ) {
                bfd_elf32_swap_dyn_out(output_bfd, &dyn, dyncon);
            }
            dyncon++;
        }

        if (htab->root.splt && htab->root.splt->size > 0 && htab->plt_info->plt0_entry) {
            unsigned int i;
            asection *splt = htab->root.splt;

            memcpy(splt->contents, htab->plt_info->plt0_entry, htab->plt_info->plt0_entry_size);
            for (i = 0; i < ARRAY_SIZE(htab->plt_info->plt0_got_fields); i++) {
                if (htab->plt_info->plt0_got_fields[i] != MINUS_ONE) {
                    install_plt_field(output_bfd, false, sgotplt->output_section->vma + sgotplt->output_offset + (i * 4),
                                      splt->contents + htab->plt_info->plt0_got_fields[i]);
                }
            }

            if (htab->root.target_os == is_vxworks) {
                Elf_Internal_Rela rel;
                bfd_byte *loc = htab->srelplt2->contents;

                rel.r_offset = splt->output_section->vma + splt->output_offset + htab->plt_info->plt0_got_fields[2];
                rel.r_info = ELF32_R_INFO(htab->root.hgot->indx, R_SH_DIR32);
                rel.r_addend = 8;
                bfd_elf32_swap_reloca_out(output_bfd, &rel, loc);
                loc += sizeof(Elf32_External_Rela);

                while (loc < htab->srelplt2->contents + htab->srelplt2->size) {
                    bfd_elf32_swap_reloc_in(output_bfd, loc, &rel);
                    rel.r_info = ELF32_R_INFO(htab->root.hgot->indx, R_SH_DIR32);
                    bfd_elf32_swap_reloc_out(output_bfd, &rel, loc);
                    loc += sizeof(Elf32_External_Rela);

                    bfd_elf32_swap_reloc_in(output_bfd, loc, &rel);
                    rel.r_info = ELF32_R_INFO(htab->root.hplt->indx, R_SH_DIR32);
                    bfd_elf32_swap_reloc_out(output_bfd, &rel, loc);
                    loc += sizeof(Elf32_External_Rela);
                }
            }
            elf_section_data(splt->output_section)->this_hdr.sh_entsize = 4;
        }
    }

    if (sgotplt && sgotplt->size > 0 && !htab->fdpic_p) {
        bfd_put_32(output_bfd, (sdyn ? sdyn->output_section->vma + sdyn->output_offset : 0), sgotplt->contents);
        bfd_put_32(output_bfd, 0, sgotplt->contents + 4);
        bfd_put_32(output_bfd, 0, sgotplt->contents + 8);
    }

    if (sgotplt && sgotplt->size > 0) {
        elf_section_data(sgotplt->output_section)->this_hdr.sh_entsize = 4;
    }

    if (htab->fdpic_p && htab->srofixup) {
        struct elf_link_hash_entry *hgot = htab->root.hgot;
        bfd_vma got_value = hgot->root.u.def.value + hgot->root.u.def.section->output_section->vma + hgot->root.u.def.section->output_offset;
        sh_elf_add_rofixup(output_bfd, htab->srofixup, got_value);
        BFD_ASSERT(htab->srofixup->reloc_count * 4 == htab->srofixup->size);
    }

    if (htab->srelfuncdesc) {
        BFD_ASSERT(htab->srelfuncdesc->reloc_count * sizeof(Elf32_External_Rela) == htab->srelfuncdesc->size);
    }

    if (htab->root.srelgot) {
        BFD_ASSERT(htab->root.srelgot->reloc_count * sizeof(Elf32_External_Rela) == htab->root.srelgot->size);
    }

    return true;
}

static enum elf_reloc_type_class
sh_elf_reloc_type_class (const struct bfd_link_info *info,
                         const asection *rel_sec,
                         const Elf_Internal_Rela *rela)
{
  int reloc_type = ELF32_R_TYPE (rela->r_info);
  if (reloc_type == R_SH_RELATIVE) {
    return reloc_class_relative;
  } else if (reloc_type == R_SH_JMP_SLOT) {
    return reloc_class_plt;
  } else if (reloc_type == R_SH_COPY) {
    return reloc_class_copy;
  }
  return reloc_class_normal;
}

#if !defined SH_TARGET_ALREADY_DEFINED
/* Support for Linux core dump NOTE sections.  */

bool elf32_shlin_grok_prstatus(bfd *abfd, Elf_Internal_Note *note) {
    if (note->descsz != 168) {
        return false;
    }

    elf_tdata(abfd)->core->signal = bfd_get_16(abfd, note->descdata + 12);
    elf_tdata(abfd)->core->lwpid = bfd_get_32(abfd, note->descdata + 24);
    int offset = 72;
    unsigned int size = 92;

    return _bfd_elfcore_make_pseudosection(abfd, ".reg", size, note->descpos + offset);
}

static bool elf32_shlin_grok_psinfo(bfd *abfd, Elf_Internal_Note *note) {
    if (note->descsz != 124) {
        return false;
    }

    elf_tdata(abfd)->core->program = _bfd_elfcore_strndup(abfd, note->descdata + 28, 16);
    elf_tdata(abfd)->core->command = _bfd_elfcore_strndup(abfd, note->descdata + 44, 80);

    char *command = elf_tdata(abfd)->core->command;
    size_t len = strlen(command);

    if (len > 0 && command[len - 1] == ' ') {
        command[len - 1] = '\0';
    }

    return true;
}
#endif /* not SH_TARGET_ALREADY_DEFINED */


/* Return address for Ith PLT stub in section PLT, for relocation REL
   or (bfd_vma) -1 if it should not be included.  */

static bfd_vma sh_elf_plt_sym_val(bfd_vma i, const asection *plt, const arelent *rel) {
    const struct elf_sh_plt_info *plt_info = get_plt_info(plt->owner, (plt->owner->flags & DYNAMIC) != 0);
    if (plt_info == NULL) {
        // Proper error handling should be implemented as per the application's error handling policy
        return 0; // or an appropriate error code
    }
    return plt->vma + get_plt_offset(plt_info, i);
}

/* Decide whether to attempt to turn absptr or lsda encodings in
   shared libraries into pcrel within the given input section.  */

bool sh_elf_use_relative_eh_frame(struct bfd_link_info *info) {
    return !sh_elf_hash_table(info)->fdpic_p;
}

/* Adjust the contents of an eh_frame_hdr section before they're output.  */

static bfd_byte sh_elf_encode_eh_address(bfd *abfd, struct bfd_link_info *info, asection *osec, bfd_vma offset, asection *loc_sec, bfd_vma loc_offset, bfd_vma *encoded) {
    struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
    struct elf_link_hash_entry *h;

    if (!htab || !htab->fdpic_p) {
        return _bfd_elf_encode_eh_address(abfd, info, osec, offset, loc_sec, loc_offset, encoded);
    }

    h = htab->root.hgot;

    if (!h || h->root.type != bfd_link_hash_defined) {
        return _bfd_elf_encode_eh_address(abfd, info, osec, offset, loc_sec, loc_offset, encoded);
    }

    if (sh_elf_osec_to_segment(abfd, osec) == sh_elf_osec_to_segment(abfd, loc_sec->output_section)) {
        return _bfd_elf_encode_eh_address(abfd, info, osec, offset, loc_sec, loc_offset, encoded);
    }

    if (sh_elf_osec_to_segment(abfd, osec) != sh_elf_osec_to_segment(abfd, h->root.u.def.section->output_section)) {
        return _bfd_elf_encode_eh_address(abfd, info, osec, offset, loc_sec, loc_offset, encoded);
    }

    *encoded = osec->vma + offset - (h->root.u.def.value + h->root.u.def.section->output_section->vma + h->root.u.def.section->output_offset);

    return DW_EH_PE_datarel | DW_EH_PE_sdata4;
}

#if !defined SH_TARGET_ALREADY_DEFINED
#define TARGET_BIG_SYM		sh_elf32_vec
#define TARGET_BIG_NAME		"elf32-sh"
#define TARGET_LITTLE_SYM	sh_elf32_le_vec
#define TARGET_LITTLE_NAME	"elf32-shl"
#endif

#define ELF_ARCH		bfd_arch_sh
#define ELF_TARGET_ID		SH_ELF_DATA
#define ELF_MACHINE_CODE	EM_SH
#ifdef __QNXTARGET__
#define ELF_MAXPAGESIZE		0x1000
#else
#define ELF_MAXPAGESIZE		0x80
#endif

#define elf_symbol_leading_char '_'

#define bfd_elf32_bfd_reloc_type_lookup	sh_elf_reloc_type_lookup
#define bfd_elf32_bfd_reloc_name_lookup \
					sh_elf_reloc_name_lookup
#define elf_info_to_howto		sh_elf_info_to_howto
#define bfd_elf32_bfd_relax_section	sh_elf_relax_section
#define elf_backend_relocate_section	sh_elf_relocate_section
#define bfd_elf32_bfd_get_relocated_section_contents \
					sh_elf_get_relocated_section_contents
#define bfd_elf32_mkobject		sh_elf_mkobject
#define elf_backend_object_p		sh_elf_object_p
#define bfd_elf32_bfd_copy_private_bfd_data \
					sh_elf_copy_private_data
#define bfd_elf32_bfd_merge_private_bfd_data \
					sh_elf_merge_private_data

#define elf_backend_gc_mark_hook	sh_elf_gc_mark_hook
#define elf_backend_check_relocs	sh_elf_check_relocs
#define elf_backend_copy_indirect_symbol \
					sh_elf_copy_indirect_symbol
#define elf_backend_create_dynamic_sections \
					sh_elf_create_dynamic_sections
#define bfd_elf32_bfd_link_hash_table_create \
					sh_elf_link_hash_table_create
#define elf_backend_adjust_dynamic_symbol \
					sh_elf_adjust_dynamic_symbol
#define elf_backend_early_size_sections	sh_elf_early_size_sections
#define elf_backend_late_size_sections	sh_elf_late_size_sections
#define elf_backend_omit_section_dynsym	sh_elf_omit_section_dynsym
#define elf_backend_finish_dynamic_symbol \
					sh_elf_finish_dynamic_symbol
#define elf_backend_finish_dynamic_sections \
					sh_elf_finish_dynamic_sections
#define elf_backend_reloc_type_class	sh_elf_reloc_type_class
#define elf_backend_plt_sym_val		sh_elf_plt_sym_val
#define elf_backend_can_make_relative_eh_frame \
					sh_elf_use_relative_eh_frame
#define elf_backend_can_make_lsda_relative_eh_frame \
					sh_elf_use_relative_eh_frame
#define elf_backend_encode_eh_address \
					sh_elf_encode_eh_address

#define elf_backend_stack_align		8
#define elf_backend_can_gc_sections	1
#define elf_backend_can_refcount	1
#define elf_backend_want_got_plt	1
#define elf_backend_plt_readonly	1
#define elf_backend_want_plt_sym	0
#define elf_backend_got_header_size	12
#define elf_backend_dtrel_excludes_plt	1

#define elf_backend_linux_prpsinfo32_ugid16	true

#if !defined SH_TARGET_ALREADY_DEFINED

#include "elf32-target.h"

/* NetBSD support.  */
#undef	TARGET_BIG_SYM
#define	TARGET_BIG_SYM			sh_elf32_nbsd_vec
#undef	TARGET_BIG_NAME
#define	TARGET_BIG_NAME			"elf32-sh-nbsd"
#undef	TARGET_LITTLE_SYM
#define	TARGET_LITTLE_SYM		sh_elf32_nbsd_le_vec
#undef	TARGET_LITTLE_NAME
#define	TARGET_LITTLE_NAME		"elf32-shl-nbsd"
#undef	ELF_MAXPAGESIZE
#define	ELF_MAXPAGESIZE			0x10000
#undef	ELF_COMMONPAGESIZE
#undef	elf_symbol_leading_char
#define	elf_symbol_leading_char		0
#undef	elf32_bed
#define	elf32_bed			elf32_sh_nbsd_bed

#include "elf32-target.h"


/* Linux support.  */
#undef	TARGET_BIG_SYM
#define	TARGET_BIG_SYM			sh_elf32_linux_be_vec
#undef	TARGET_BIG_NAME
#define	TARGET_BIG_NAME			"elf32-shbig-linux"
#undef	TARGET_LITTLE_SYM
#define	TARGET_LITTLE_SYM		sh_elf32_linux_vec
#undef	TARGET_LITTLE_NAME
#define	TARGET_LITTLE_NAME		"elf32-sh-linux"
#undef	ELF_COMMONPAGESIZE
#define	ELF_COMMONPAGESIZE		0x1000

#undef	elf_backend_grok_prstatus
#define	elf_backend_grok_prstatus	elf32_shlin_grok_prstatus
#undef	elf_backend_grok_psinfo
#define	elf_backend_grok_psinfo		elf32_shlin_grok_psinfo
#undef	elf32_bed
#define	elf32_bed			elf32_sh_lin_bed

#include "elf32-target.h"


/* FDPIC support.  */
#undef	TARGET_BIG_SYM
#define	TARGET_BIG_SYM			sh_elf32_fdpic_be_vec
#undef	TARGET_BIG_NAME
#define	TARGET_BIG_NAME			"elf32-shbig-fdpic"
#undef	TARGET_LITTLE_SYM
#define	TARGET_LITTLE_SYM		sh_elf32_fdpic_le_vec
#undef	TARGET_LITTLE_NAME
#define	TARGET_LITTLE_NAME		"elf32-sh-fdpic"

#undef	elf32_bed
#define	elf32_bed			elf32_sh_fd_bed

#include "elf32-target.h"

/* VxWorks support.  */
#undef	TARGET_BIG_SYM
#define	TARGET_BIG_SYM			sh_elf32_vxworks_vec
#undef	TARGET_BIG_NAME
#define	TARGET_BIG_NAME			"elf32-sh-vxworks"
#undef	TARGET_LITTLE_SYM
#define	TARGET_LITTLE_SYM		sh_elf32_vxworks_le_vec
#undef	TARGET_LITTLE_NAME
#define	TARGET_LITTLE_NAME		"elf32-shl-vxworks"
#undef	elf32_bed
#define	elf32_bed			elf32_sh_vxworks_bed

#undef	elf_backend_want_plt_sym
#define	elf_backend_want_plt_sym	1
#undef	elf_symbol_leading_char
#define	elf_symbol_leading_char		'_'
#define	elf_backend_want_got_underscore 1
#undef	elf_backend_grok_prstatus
#undef	elf_backend_grok_psinfo
#undef	elf_backend_add_symbol_hook
#define	elf_backend_add_symbol_hook	elf_vxworks_add_symbol_hook
#undef	elf_backend_link_output_symbol_hook
#define	elf_backend_link_output_symbol_hook \
					elf_vxworks_link_output_symbol_hook
#undef	elf_backend_emit_relocs
#define	elf_backend_emit_relocs		elf_vxworks_emit_relocs
#undef	elf_backend_final_write_processing
#define	elf_backend_final_write_processing \
					elf_vxworks_final_write_processing
#undef	ELF_MAXPAGESIZE
#define	ELF_MAXPAGESIZE			0x1000
#undef	ELF_COMMONPAGESIZE

#undef	ELF_TARGET_OS
#define	ELF_TARGET_OS			is_vxworks

#include "elf32-target.h"

#endif /* not SH_TARGET_ALREADY_DEFINED */
