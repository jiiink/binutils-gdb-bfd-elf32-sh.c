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

static bool
vxworks_object_p (bfd *abfd ATTRIBUTE_UNUSED)
{
#if !defined SH_TARGET_ALREADY_DEFINED
  extern const bfd_target sh_elf32_vxworks_le_vec;
  extern const bfd_target sh_elf32_vxworks_vec;

  return (abfd->xvec == &sh_elf32_vxworks_le_vec
	  || abfd->xvec == &sh_elf32_vxworks_vec);
#else
  return false;
#endif
}

/* Return true if OUTPUT_BFD is an FDPIC object.  */

static bool
fdpic_object_p (bfd *abfd ATTRIBUTE_UNUSED)
{
#if !defined SH_TARGET_ALREADY_DEFINED
  extern const bfd_target sh_elf32_fdpic_le_vec;
  extern const bfd_target sh_elf32_fdpic_be_vec;

  return (abfd->xvec == &sh_elf32_fdpic_le_vec
	  || abfd->xvec == &sh_elf32_fdpic_be_vec);
#else
  return false;
#endif
}

/* Return the howto table for ABFD.  */

static reloc_howto_type *
get_howto_table (bfd *abfd)
{
  if (vxworks_object_p (abfd))
    return sh_vxworks_howto_table;
  return sh_elf_howto_table;
}

static bfd_reloc_status_type
validate_relocation_address(bfd *input_bfd, asection *input_section, bfd_vma addr)
{
  if (addr > bfd_get_section_limit(input_bfd, input_section))
    return bfd_reloc_outofrange;
  return bfd_reloc_ok;
}

static bfd_reloc_status_type
handle_first_relocation(bfd_vma addr, asection *symbol_section,
                        bfd_vma *last_addr, asection **last_symbol_section)
{
  *last_addr = addr;
  *last_symbol_section = symbol_section;
  return bfd_reloc_ok;
}

static bfd_reloc_status_type
validate_consecutive_relocations(bfd_vma last_addr, bfd_vma addr,
                                asection *last_symbol_section, asection *symbol_section,
                                bfd_vma start, bfd_vma end)
{
  if (last_addr != addr)
    abort();
  
  if (!symbol_section || last_symbol_section != symbol_section || end < start)
    return bfd_reloc_outofrange;
  
  return bfd_reloc_ok;
}

static bfd_byte*
get_section_contents(bfd *input_bfd, asection *symbol_section, asection *input_section,
                    bfd_byte *contents, bfd_reloc_status_type *status)
{
  if (symbol_section == input_section)
    return contents;
  
  if (elf_section_data(symbol_section)->this_hdr.contents != NULL)
    return elf_section_data(symbol_section)->this_hdr.contents;
  
  bfd_byte *new_contents = NULL;
  if (!bfd_malloc_and_get_section(input_bfd, symbol_section, &new_contents))
  {
    free(new_contents);
    *status = bfd_reloc_outofrange;
    return NULL;
  }
  return new_contents;
}

#define IS_PPI(PTR) ((bfd_get_16(input_bfd, (PTR)) & 0xfc00) == 0xf800)
#define INSTRUCTION_SIZE 2
#define WORD_SIZE 4
#define OFFSET_ADJUSTMENT 4
#define MIN_SIGNED_BYTE -128
#define MAX_SIGNED_BYTE 127
#define INSN_MASK 0xff
#define INSN_END_FLAG 0x200

static int
calculate_cumulative_diff(bfd *input_bfd, bfd_byte *contents, bfd_vma start, bfd_vma end)
{
  int cum_diff = -6;
  bfd_byte *start_ptr = contents + start;
  bfd_byte *ptr = contents + end;
  
  while (cum_diff < 0 && ptr > start_ptr)
  {
    bfd_byte *last_ptr = ptr;
    ptr -= WORD_SIZE;
    
    while (ptr >= start_ptr && IS_PPI(ptr))
      ptr -= INSTRUCTION_SIZE;
    
    ptr += INSTRUCTION_SIZE;
    int diff = (last_ptr - ptr) >> 1;
    cum_diff += diff & 1;
    cum_diff += diff;
  }
  
  return cum_diff;
}

static void
adjust_start_end_positive_diff(int cum_diff, bfd_byte *ptr, bfd_byte *contents,
                               bfd_vma *start, bfd_vma *end)
{
  *start -= OFFSET_ADJUSTMENT;
  *end = (ptr + cum_diff * INSTRUCTION_SIZE) - contents;
}

static void
adjust_start_end_negative_diff(bfd *input_bfd, int cum_diff, bfd_byte *contents,
                               bfd_vma *start, bfd_vma *end)
{
  bfd_vma start0 = *start - OFFSET_ADJUSTMENT;
  
  while (start0 && IS_PPI(contents + start0))
    start0 -= INSTRUCTION_SIZE;
  
  start0 = *start - INSTRUCTION_SIZE - ((*start - start0) & INSTRUCTION_SIZE);
  *start = start0 - cum_diff - INSTRUCTION_SIZE;
  *end = start0;
}

static bfd_signed_vma
calculate_offset(bfd *input_bfd, bfd_byte *contents, bfd_vma addr,
                bfd_vma start, bfd_vma end,
                asection *input_section, asection *symbol_section)
{
  int insn = bfd_get_16(input_bfd, contents + addr);
  bfd_signed_vma x = (insn & INSN_END_FLAG ? end : start) - addr;
  
  if (input_section != symbol_section)
  {
    x += ((symbol_section->output_section->vma + symbol_section->output_offset)
          - (input_section->output_section->vma + input_section->output_offset));
  }
  
  return x >> 1;
}

static bfd_reloc_status_type
update_instruction(bfd *input_bfd, bfd_byte *contents, bfd_vma addr, bfd_signed_vma offset)
{
  if (offset < MIN_SIGNED_BYTE || offset > MAX_SIGNED_BYTE)
    return bfd_reloc_overflow;
  
  int insn = bfd_get_16(input_bfd, contents + addr);
  bfd_vma new_insn = (insn & ~INSN_MASK) | (offset & INSN_MASK);
  bfd_put_16(input_bfd, new_insn, contents + addr);
  
  return bfd_reloc_ok;
}

static bfd_reloc_status_type
sh_elf_reloc_loop(int r_type ATTRIBUTE_UNUSED, bfd *input_bfd,
                 asection *input_section, bfd_byte *contents,
                 bfd_vma addr, asection *symbol_section,
                 bfd_vma start, bfd_vma end)
{
  static bfd_vma last_addr;
  static asection *last_symbol_section;
  bfd_reloc_status_type status;
  
  status = validate_relocation_address(input_bfd, input_section, addr);
  if (status != bfd_reloc_ok)
    return status;
  
  if (!last_addr)
    return handle_first_relocation(addr, symbol_section, &last_addr, &last_symbol_section);
  
  status = validate_consecutive_relocations(last_addr, addr, last_symbol_section,
                                           symbol_section, start, end);
  last_addr = 0;
  if (status != bfd_reloc_ok)
    return status;
  
  bfd_byte *section_contents = get_section_contents(input_bfd, symbol_section,
                                                   input_section, contents, &status);
  if (!section_contents)
    return status;
  
  int cum_diff = calculate_cumulative_diff(input_bfd, section_contents, start, end);
  
  if (cum_diff >= 0)
  {
    bfd_byte *ptr = section_contents + end - ((-cum_diff - 6) * INSTRUCTION_SIZE);
    adjust_start_end_positive_diff(cum_diff, ptr, section_contents, &start, &end);
  }
  else
  {
    adjust_start_end_negative_diff(input_bfd, cum_diff, section_contents, &start, &end);
  }
  
  if (elf_section_data(symbol_section)->this_hdr.contents != section_contents)
    free(section_contents);
  
  bfd_signed_vma offset = calculate_offset(input_bfd, contents, addr, start, end,
                                          input_section, symbol_section);
  
  return update_instruction(input_bfd, contents, addr, offset);
}

/* This function is used for normal relocs.  This used to be like the COFF
   function, and is almost certainly incorrect for other ELF targets.  */

static bfd_reloc_status_type
handle_partial_linking(arelent *reloc_entry, asection *input_section)
{
  reloc_entry->address += input_section->output_offset;
  return bfd_reloc_ok;
}

static bfd_reloc_status_type
validate_relocation(bfd *abfd, asymbol *symbol_in, arelent *reloc_entry,
                    asection *input_section, bfd_size_type octets)
{
  if (symbol_in != NULL && bfd_is_und_section(symbol_in->section))
    return bfd_reloc_undefined;

  if (octets + bfd_get_reloc_size(reloc_entry->howto) >
      bfd_get_section_limit_octets(abfd, input_section))
    return bfd_reloc_outofrange;

  return bfd_reloc_ok;
}

static bfd_vma
calculate_symbol_value(asymbol *symbol_in)
{
  if (bfd_is_com_section(symbol_in->section))
    return 0;

  return symbol_in->value +
         symbol_in->section->output_section->vma +
         symbol_in->section->output_offset;
}

static bfd_reloc_status_type
process_dir32_reloc(bfd *abfd, bfd_byte *hit_data, bfd_vma sym_value,
                   arelent *reloc_entry)
{
  bfd_vma insn = bfd_get_32(abfd, hit_data);
  insn += sym_value + reloc_entry->addend;
  bfd_put_32(abfd, insn, hit_data);
  return bfd_reloc_ok;
}

#define SIGN_EXTEND_12BIT 0x800
#define IND12W_MASK 0xfff
#define IND12W_HIGH_MASK 0xf000
#define IND12W_RANGE 0x1000
#define IND12W_MAX_RANGE 0x2000
#define PC_OFFSET 4

static bfd_reloc_status_type
process_ind12w_reloc(bfd *abfd, bfd_byte *hit_data, bfd_vma sym_value,
                    arelent *reloc_entry, asection *input_section,
                    bfd_vma addr)
{
  bfd_vma insn = bfd_get_16(abfd, hit_data);
  
  sym_value += reloc_entry->addend;
  sym_value -= (input_section->output_section->vma +
                input_section->output_offset +
                addr + PC_OFFSET);
  
  sym_value += (((insn & IND12W_MASK) ^ SIGN_EXTEND_12BIT) - SIGN_EXTEND_12BIT) << 1;
  
  insn = (insn & IND12W_HIGH_MASK) | ((sym_value >> 1) & IND12W_MASK);
  bfd_put_16(abfd, insn, hit_data);
  
  if (sym_value + IND12W_RANGE >= IND12W_MAX_RANGE || (sym_value & 1) != 0)
    return bfd_reloc_overflow;
    
  return bfd_reloc_ok;
}

static bfd_reloc_status_type
sh_elf_reloc(bfd *abfd, arelent *reloc_entry, asymbol *symbol_in,
            void *data, asection *input_section, bfd *output_bfd,
            char **error_message ATTRIBUTE_UNUSED)
{
  enum elf_sh_reloc_type r_type;
  bfd_vma addr = reloc_entry->address;
  bfd_size_type octets = addr * OCTETS_PER_BYTE(abfd, input_section);
  bfd_byte *hit_data = (bfd_byte *)data + octets;
  bfd_reloc_status_type status;

  r_type = (enum elf_sh_reloc_type)reloc_entry->howto->type;

  if (output_bfd != NULL)
    return handle_partial_linking(reloc_entry, input_section);

  if (r_type == R_SH_IND12W && (symbol_in->flags & BSF_LOCAL) != 0)
    return bfd_reloc_ok;

  status = validate_relocation(abfd, symbol_in, reloc_entry, input_section, octets);
  if (status != bfd_reloc_ok)
    return status;

  bfd_vma sym_value = calculate_symbol_value(symbol_in);

  switch (r_type)
    {
    case R_SH_DIR32:
      return process_dir32_reloc(abfd, hit_data, sym_value, reloc_entry);
    case R_SH_IND12W:
      return process_ind12w_reloc(abfd, hit_data, sym_value, reloc_entry,
                                 input_section, addr);
    default:
      abort();
      break;
    }

  return bfd_reloc_ok;
}

/* This function is used for relocs which are only used for relaxing,
   which the linker should otherwise ignore.  */

static bfd_reloc_status_type
sh_elf_ignore_reloc (bfd *abfd ATTRIBUTE_UNUSED, arelent *reloc_entry,
		     asymbol *symbol ATTRIBUTE_UNUSED,
		     void *data ATTRIBUTE_UNUSED, asection *input_section,
		     bfd *output_bfd,
		     char **error_message ATTRIBUTE_UNUSED)
{
  if (output_bfd != NULL)
    reloc_entry->address += input_section->output_offset;
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

static reloc_howto_type *
sh_elf_reloc_type_lookup (bfd *abfd, bfd_reloc_code_real_type code)
{
  const size_t map_size = sizeof (sh_reloc_map) / sizeof (struct elf_reloc_map);
  
  for (unsigned int i = 0; i < map_size; i++)
    {
      if (sh_reloc_map[i].bfd_reloc_val == code)
	return get_howto_table (abfd) + (int) sh_reloc_map[i].elf_reloc_val;
    }

  return NULL;
}

static reloc_howto_type *
find_reloc_in_table(const reloc_howto_type *table, size_t table_size, const char *r_name)
{
  unsigned int i;
  
  for (i = 0; i < table_size; i++)
    if (table[i].name != NULL && strcasecmp(table[i].name, r_name) == 0)
      return (reloc_howto_type *)&table[i];
  
  return NULL;
}

static reloc_howto_type *
sh_elf_reloc_name_lookup (bfd *abfd, const char *r_name)
{
  if (vxworks_object_p (abfd))
    return find_reloc_in_table(sh_vxworks_howto_table,
                               sizeof(sh_vxworks_howto_table) / sizeof(sh_vxworks_howto_table[0]),
                               r_name);
  
  return find_reloc_in_table(sh_elf_howto_table,
                             sizeof(sh_elf_howto_table) / sizeof(sh_elf_howto_table[0]),
                             r_name);
}

/* Given an ELF reloc, fill in the howto field of a relent.  */

static bool is_relocation_type_invalid(unsigned int r)
{
  if (r >= R_SH_FIRST_INVALID_RELOC_6)
    return true;
  if (r >= R_SH_FIRST_INVALID_RELOC && r <= R_SH_LAST_INVALID_RELOC)
    return true;
  if (r >= R_SH_FIRST_INVALID_RELOC_2 && r <= R_SH_LAST_INVALID_RELOC_2)
    return true;
  if (r >= R_SH_FIRST_INVALID_RELOC_3 && r <= R_SH_LAST_INVALID_RELOC_3)
    return true;
  if (r >= R_SH_FIRST_INVALID_RELOC_4 && r <= R_SH_LAST_INVALID_RELOC_4)
    return true;
  if (r >= R_SH_FIRST_INVALID_RELOC_5 && r <= R_SH_LAST_INVALID_RELOC_5)
    return true;
  return false;
}

static bool handle_invalid_relocation(bfd *abfd, unsigned int r)
{
  _bfd_error_handler (_("%pB: unsupported relocation type %#x"), abfd, r);
  bfd_set_error (bfd_error_bad_value);
  return false;
}

static bool
sh_elf_info_to_howto (bfd *abfd, arelent *cache_ptr, Elf_Internal_Rela *dst)
{
  unsigned int r = ELF32_R_TYPE (dst->r_info);

  if (is_relocation_type_invalid(r))
    return handle_invalid_relocation(abfd, r);

  cache_ptr->howto = get_howto_table (abfd) + r;
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

#define JUMP_OFFSET_BASE 4
#define MOV_L_MASK 0xf000
#define MOV_L_INSTRUCTION 0xd000
#define DISPLACEMENT_MULTIPLIER 4
#define PC_ALIGNMENT_MASK 3
#define BRANCH_RANGE_MIN -0x1000
#define BRANCH_RANGE_MAX 0xff8
#define BSR_CALL_FLAG 0x0020
#define BSR_INSTRUCTION 0xa000
#define BRA_INSTRUCTION 0xb000
#define ADDEND_ADJUSTMENT -4
#define REGISTER_LOAD_SIZE 2
#define ADDRESS_SIZE 4

static bool should_skip_section(struct bfd_link_info *link_info, asection *sec)
{
    return bfd_link_relocatable(link_info)
        || (sec->flags & SEC_HAS_CONTENTS) == 0
        || (sec->flags & SEC_RELOC) == 0
        || sec->reloc_count == 0;
}

static bfd_byte *get_section_contents(bfd *abfd, asection *sec)
{
    if (elf_section_data(sec)->this_hdr.contents != NULL)
        return elf_section_data(sec)->this_hdr.contents;
    
    bfd_byte *contents = NULL;
    if (!bfd_malloc_and_get_section(abfd, sec, &contents))
        return NULL;
    
    return contents;
}

static bool validate_load_address(bfd *abfd, asection *sec, 
                                 Elf_Internal_Rela *irel, bfd_vma *laddr)
{
    *laddr = irel->r_offset + JUMP_OFFSET_BASE + irel->r_addend;
    if (*laddr >= sec->size)
    {
        _bfd_error_handler
            (_("%pB: %#" PRIx64 ": warning: bad R_SH_USES offset"),
             abfd, (uint64_t) irel->r_offset);
        return false;
    }
    return true;
}

static bool validate_mov_instruction(bfd *abfd, Elf_Internal_Rela *irel, 
                                    unsigned short insn)
{
    if ((insn & MOV_L_MASK) != MOV_L_INSTRUCTION)
    {
        _bfd_error_handler
            (_("%pB: %#" PRIx64 ": warning: "
               "R_SH_USES points to unrecognized insn 0x%x"),
             abfd, (uint64_t) irel->r_offset, insn);
        return false;
    }
    return true;
}

static bfd_vma calculate_paddr(unsigned short insn, bfd_vma laddr)
{
    bfd_vma paddr = insn & 0xff;
    paddr *= DISPLACEMENT_MULTIPLIER;
    paddr += (laddr + JUMP_OFFSET_BASE) &~ (bfd_vma) PC_ALIGNMENT_MASK;
    return paddr;
}

static Elf_Internal_Rela *find_dir32_reloc(Elf_Internal_Rela *internal_relocs,
                                          Elf_Internal_Rela *irelend, bfd_vma paddr)
{
    Elf_Internal_Rela *irelfn;
    for (irelfn = internal_relocs; irelfn < irelend; irelfn++)
        if (irelfn->r_offset == paddr
            && ELF32_R_TYPE(irelfn->r_info) == (int) R_SH_DIR32)
            break;
    return irelfn;
}

static Elf_Internal_Sym *load_symbols(bfd *abfd, Elf_Internal_Shdr *symtab_hdr)
{
    if (symtab_hdr->sh_info == 0)
        return NULL;
    
    Elf_Internal_Sym *isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;
    if (isymbuf == NULL)
        isymbuf = bfd_elf_get_elf_syms(abfd, symtab_hdr,
                                       symtab_hdr->sh_info, 0,
                                       NULL, NULL, NULL);
    return isymbuf;
}

static bool get_local_symbol_value(bfd *abfd, asection *sec, 
                                  Elf_Internal_Sym *isymbuf,
                                  Elf_Internal_Rela *irelfn,
                                  bfd_vma paddr, bfd_vma *symval)
{
    Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM(irelfn->r_info);
    if (isym->st_shndx != (unsigned int) _bfd_elf_section_from_bfd_section(abfd, sec))
    {
        _bfd_error_handler
            (_("%pB: %#" PRIx64 ": warning: symbol in unexpected section"),
             abfd, (uint64_t) paddr);
        return false;
    }
    
    *symval = isym->st_value + sec->output_section->vma + sec->output_offset;
    return true;
}

static bool get_global_symbol_value(bfd *abfd, Elf_Internal_Shdr *symtab_hdr,
                                   Elf_Internal_Rela *irelfn, bfd_vma *symval)
{
    unsigned long indx = ELF32_R_SYM(irelfn->r_info) - symtab_hdr->sh_info;
    struct elf_link_hash_entry *h = elf_sym_hashes(abfd)[indx];
    BFD_ASSERT(h != NULL);
    
    if (h->root.type != bfd_link_hash_defined
        && h->root.type != bfd_link_hash_defweak)
        return false;
    
    *symval = h->root.u.def.value
            + h->root.u.def.section->output_section->vma
            + h->root.u.def.section->output_offset;
    return true;
}

static bfd_vma get_symbol_value(bfd *abfd, asection *sec,
                               Elf_Internal_Shdr *symtab_hdr,
                               Elf_Internal_Sym *isymbuf,
                               Elf_Internal_Rela *irelfn,
                               bfd_vma paddr, bfd_byte *contents,
                               bool *success)
{
    bfd_vma symval = 0;
    *success = false;
    
    if (ELF32_R_SYM(irelfn->r_info) < symtab_hdr->sh_info)
    {
        if (!get_local_symbol_value(abfd, sec, isymbuf, irelfn, paddr, &symval))
            return 0;
    }
    else
    {
        if (!get_global_symbol_value(abfd, symtab_hdr, irelfn, &symval))
            return 0;
    }
    
    if (get_howto_table(abfd)[R_SH_DIR32].partial_inplace)
        symval += bfd_get_32(abfd, contents + paddr);
    else
        symval += irelfn->r_addend;
    
    *success = true;
    return symval;
}

static bool can_shorten_call(bfd_vma symval, Elf_Internal_Rela *irel, asection *sec)
{
    bfd_signed_vma foff = symval
                        - (irel->r_offset
                           + sec->output_section->vma
                           + sec->output_offset
                           + JUMP_OFFSET_BASE);
    return foff >= BRANCH_RANGE_MIN && foff < BRANCH_RANGE_MAX;
}

static void update_relocation(bfd *abfd, bfd_byte *contents,
                             Elf_Internal_Rela *irel,
                             Elf_Internal_Rela *irelfn,
                             bfd_vma paddr)
{
    irel->r_info = ELF32_R_INFO(ELF32_R_SYM(irelfn->r_info), R_SH_IND12W);
    
    if (bfd_get_16(abfd, contents + irel->r_offset) & BSR_CALL_FLAG)
        bfd_put_16(abfd, (bfd_vma) BSR_INSTRUCTION, contents + irel->r_offset);
    else
        bfd_put_16(abfd, (bfd_vma) BRA_INSTRUCTION, contents + irel->r_offset);
    
    irel->r_addend = ADDEND_ADJUSTMENT;
    irel->r_addend += bfd_get_32(abfd, contents + paddr);
}

static bool has_other_uses(Elf_Internal_Rela *internal_relocs,
                          Elf_Internal_Rela *irelend,
                          bfd_vma laddr)
{
    Elf_Internal_Rela *irelscan;
    for (irelscan = internal_relocs; irelscan < irelend; irelscan++)
        if (ELF32_R_TYPE(irelscan->r_info) == (int) R_SH_USES
            && laddr == irelscan->r_offset + JUMP_OFFSET_BASE + irelscan->r_addend)
            return true;
    return false;
}

static Elf_Internal_Rela *find_count_reloc(Elf_Internal_Rela *internal_relocs,
                                          Elf_Internal_Rela *irelend,
                                          bfd_vma paddr)
{
    Elf_Internal_Rela *irelcount;
    for (irelcount = internal_relocs; irelcount < irelend; irelcount++)
        if (irelcount->r_offset == paddr
            && ELF32_R_TYPE(irelcount->r_info) == (int) R_SH_COUNT)
            return irelcount;
    return NULL;
}

static bool handle_count_reloc(bfd *abfd, asection *sec,
                              Elf_Internal_Rela *irelcount,
                              Elf_Internal_Rela *irelfn,
                              bfd_vma paddr)
{
    if (irelcount->r_addend == 0)
    {
        _bfd_error_handler(_("%pB: %#" PRIx64 ": warning: bad count"),
                          abfd, (uint64_t) paddr);
        return true;
    }
    
    --irelcount->r_addend;
    
    if (irelcount->r_addend == 0)
    {
        if (!sh_elf_relax_delete_bytes(abfd, sec, irelfn->r_offset, ADDRESS_SIZE))
            return false;
    }
    return true;
}

static void cache_section_data(asection *sec, 
                              Elf_Internal_Rela *internal_relocs,
                              bfd_byte *contents,
                              Elf_Internal_Sym *isymbuf,
                              Elf_Internal_Shdr *symtab_hdr)
{
    elf_section_data(sec)->relocs = internal_relocs;
    elf_section_data(sec)->this_hdr.contents = contents;
    symtab_hdr->contents = (unsigned char *) isymbuf;
}

static bool process_uses_reloc(bfd *abfd, asection *sec,
                              struct bfd_link_info *link_info,
                              Elf_Internal_Rela *irel,
                              Elf_Internal_Rela *internal_relocs,
                              Elf_Internal_Rela *irelend,
                              bfd_byte **contents,
                              Elf_Internal_Sym **isymbuf,
                              Elf_Internal_Shdr *symtab_hdr,
                              bool *again)
{
    bfd_vma laddr;
    if (!validate_load_address(abfd, sec, irel, &laddr))
        return true;
    
    if (*contents == NULL)
    {
        *contents = get_section_contents(abfd, sec);
        if (*contents == NULL)
            return false;
    }
    
    unsigned short insn = bfd_get_16(abfd, *contents + laddr);
    if (!validate_mov_instruction(abfd, irel, insn))
        return true;
    
    bfd_vma paddr = calculate_paddr(insn, laddr);
    if (paddr >= sec->size)
    {
        _bfd_error_handler
            (_("%pB: %#" PRIx64 ": warning: bad R_SH_USES load offset"),
             abfd, (uint64_t) irel->r_offset);
        return true;
    }
    
    Elf_Internal_Rela *irelfn = find_dir32_reloc(internal_relocs, irelend, paddr);
    if (irelfn >= irelend)
    {
        _bfd_error_handler
            (_("%pB: %#" PRIx64 ": warning: could not find expected reloc"),
             abfd, (uint64_t) paddr);
        return true;
    }
    
    if (*isymbuf == NULL && symtab_hdr->sh_info != 0)
    {
        *isymbuf = load_symbols(abfd, symtab_hdr);
        if (*isymbuf == NULL)
            return false;
    }
    
    bool success;
    bfd_vma symval = get_symbol_value(abfd, sec, symtab_hdr, *isymbuf, 
                                     irelfn, paddr, *contents, &success);
    if (!success)
        return true;
    
    if (!can_shorten_call(symval, irel, sec))
        return true;
    
    cache_section_data(sec, internal_relocs, *contents, *isymbuf, symtab_hdr);
    
    update_relocation(abfd, *contents, irel, irelfn, paddr);
    
    if (has_other_uses(internal_relocs, irelend, laddr))
        return true;
    
    Elf_Internal_Rela *irelcount = find_count_reloc(internal_relocs, irelend, paddr);
    
    if (!sh_elf_relax_delete_bytes(abfd, sec, laddr, REGISTER_LOAD_SIZE))
        return false;
    
    *again = true;
    
    if (irelcount >= irelend)
    {
        _bfd_error_handler
            (_("%pB: %#" PRIx64 ": warning: "
               "could not find expected COUNT reloc"),
             abfd, (uint64_t) paddr);
        return true;
    }
    
    return handle_count_reloc(abfd, sec, irelcount, irelfn, paddr);
}

static bool process_align_optimization(bfd *abfd, asection *sec,
                                      Elf_Internal_Rela *internal_relocs,
                                      bfd_byte **contents,
                                      Elf_Internal_Sym *isymbuf,
                                      Elf_Internal_Shdr *symtab_hdr,
                                      bool have_code)
{
    if ((elf_elfheader(abfd)->e_flags & EF_SH_MACH_MASK) == EF_SH4 || !have_code)
        return true;
    
    bool swapped;
    
    if (*contents == NULL)
    {
        *contents = get_section_contents(abfd, sec);
        if (*contents == NULL)
            return false;
    }
    
    if (!sh_elf_align_loads(abfd, sec, internal_relocs, *contents, &swapped))
        return false;
    
    if (swapped)
        cache_section_data(sec, internal_relocs, *contents, isymbuf, symtab_hdr);
    
    return true;
}

static void cleanup_resources(struct bfd_link_info *link_info,
                             asection *sec,
                             Elf_Internal_Sym *isymbuf,
                             bfd_byte *contents,
                             Elf_Internal_Rela *internal_relocs,
                             Elf_Internal_Shdr *symtab_hdr)
{
    if (isymbuf != NULL && symtab_hdr->contents != (unsigned char *) isymbuf)
    {
        if (!link_info->keep_memory)
            free(isymbuf);
        else
            symtab_hdr->contents = (unsigned char *) isymbuf;
    }
    
    if (contents != NULL && elf_section_data(sec)->this_hdr.contents != contents)
    {
        if (!link_info->keep_memory)
            free(contents);
        else
            elf_section_data(sec)->this_hdr.contents = contents;
    }
    
    if (elf_section_data(sec)->relocs != internal_relocs)
        free(internal_relocs);
}

static void cleanup_on_error(asection *sec,
                            Elf_Internal_Sym *isymbuf,
                            bfd_byte *contents,
                            Elf_Internal_Rela *internal_relocs,
                            Elf_Internal_Shdr *symtab_hdr)
{
    if (symtab_hdr->contents != (unsigned char *) isymbuf)
        free(isymbuf);
    if (elf_section_data(sec)->this_hdr.contents != contents)
        free(contents);
    if (elf_section_data(sec)->relocs != internal_relocs)
        free(internal_relocs);
}

static bool
sh_elf_relax_section(bfd *abfd, asection *sec,
                    struct bfd_link_info *link_info, bool *again)
{
    Elf_Internal_Shdr *symtab_hdr;
    Elf_Internal_Rela *internal_relocs;
    bool have_code;
    Elf_Internal_Rela *irel, *irelend;
    bfd_byte *contents = NULL;
    Elf_Internal_Sym *isymbuf = NULL;
    
    *again = false;
    
    if (should_skip_section(link_info, sec))
        return true;
    
    symtab_hdr = &elf_symtab_hdr(abfd);
    
    internal_relocs = (_bfd_elf_link_read_relocs
                      (abfd, sec, NULL, (Elf_Internal_Rela *) NULL,
                       link_info->keep_memory));
    if (internal_relocs == NULL)
        goto error_return;
    
    have_code = false;
    
    irelend = internal_relocs + sec->reloc_count;
    for (irel = internal_relocs; irel < irelend; irel++)
    {
        if (ELF32_R_TYPE(irel->r_info) == (int) R_SH_CODE)
            have_code = true;
        
        if (ELF32_R_TYPE(irel->r_info) != (int) R_SH_USES)
            continue;
        
        if (!process_uses_reloc(abfd, sec, link_info, irel, internal_relocs,
                               irelend, &contents, &isymbuf, symtab_hdr, again))
            goto error_return;
    }
    
    if (!process_align_optimization(abfd, sec, internal_relocs, &contents,
                                   isymbuf, symtab_hdr, have_code))
        goto error_return;
    
    cleanup_resources(link_info, sec, isymbuf, contents, internal_relocs, symtab_hdr);
    return true;
    
error_return:
    cleanup_on_error(sec, isymbuf, contents, internal_relocs, symtab_hdr);
    return false;
}

/* Delete some bytes from a section while relaxing.  FIXME: There is a
   lot of duplication between this function and sh_relax_delete_bytes
   in coff-sh.c.  */

#define NOP_OPCODE 0x0009
#define SIGN_EXTEND_8BIT 0x80
#define SIGN_EXTEND_8BIT_MASK 0x100
#define SIGN_EXTEND_12BIT 0x800
#define SIGN_EXTEND_12BIT_MASK 0x1000
#define BYTE_MASK 0xff
#define WORD_MASK 0xfff
#define NIBBLE_MASK 0xf000
#define HIGH_BYTE_MASK 0xff00
#define INSTRUCTION_SIZE 2
#define WORD_SIZE 4
#define SWITCH8_MAX 0xff
#define SWITCH16_MIN -0x8000
#define SWITCH16_MAX 0x8000

static bfd_vma
find_alignment_boundary(asection *sec, bfd_vma addr, int count)
{
    Elf_Internal_Rela *irel, *irelend;
    
    irel = elf_section_data(sec)->relocs;
    irelend = irel + sec->reloc_count;
    
    for (; irel < irelend; irel++) {
        if (ELF32_R_TYPE(irel->r_info) == (int)R_SH_ALIGN &&
            irel->r_offset > addr &&
            count < (1 << irel->r_addend)) {
            return irel->r_offset;
        }
    }
    
    return sec->size;
}

static void
delete_bytes_from_contents(bfd *abfd, asection *sec, bfd_byte *contents,
                          bfd_vma addr, int count, bfd_vma toaddr,
                          Elf_Internal_Rela *irelalign)
{
    memmove(contents + addr, contents + addr + count,
            (size_t)(toaddr - addr - count));
    
    if (irelalign == NULL) {
        sec->size -= count;
    } else {
        int i;
        BFD_ASSERT((count & 1) == 0);
        for (i = 0; i < count; i += INSTRUCTION_SIZE) {
            bfd_put_16(abfd, (bfd_vma)NOP_OPCODE, contents + toaddr - count + i);
        }
    }
}

static bfd_vma
calculate_new_reloc_address(Elf_Internal_Rela *irel, bfd_vma addr,
                           bfd_vma toaddr, int count)
{
    bfd_vma nraddr = irel->r_offset;
    
    if ((irel->r_offset > addr && irel->r_offset < toaddr) ||
        (ELF32_R_TYPE(irel->r_info) == (int)R_SH_ALIGN && irel->r_offset == toaddr)) {
        nraddr -= count;
    }
    
    return nraddr;
}

static bool
should_delete_reloc(Elf_Internal_Rela *irel, bfd_vma addr, int count)
{
    int rtype = ELF32_R_TYPE(irel->r_info);
    
    return irel->r_offset >= addr &&
           irel->r_offset < addr + count &&
           rtype != (int)R_SH_ALIGN &&
           rtype != (int)R_SH_CODE &&
           rtype != (int)R_SH_DATA &&
           rtype != (int)R_SH_LABEL;
}

static void
get_reloc_start_and_insn(bfd *abfd, Elf_Internal_Rela *irel, bfd_byte *contents,
                         bfd_vma nraddr, bfd_vma *start, int *insn)
{
    switch ((enum elf_sh_reloc_type)ELF32_R_TYPE(irel->r_info)) {
    case R_SH_DIR8WPN:
    case R_SH_IND12W:
    case R_SH_DIR8WPZ:
    case R_SH_DIR8WPL:
        *start = irel->r_offset;
        *insn = bfd_get_16(abfd, contents + nraddr);
        break;
    default:
        break;
    }
}

static void
adjust_dir32_reloc(bfd *abfd, Elf_Internal_Rela *irel, bfd_byte *contents,
                  bfd_vma nraddr, bfd_vma addr, bfd_vma toaddr, int count,
                  unsigned int sec_shndx, Elf_Internal_Sym *isymbuf,
                  Elf_Internal_Shdr *symtab_hdr)
{
    if (ELF32_R_SYM(irel->r_info) < symtab_hdr->sh_info) {
        Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM(irel->r_info);
        if (isym->st_shndx == sec_shndx &&
            (isym->st_value <= addr || isym->st_value >= toaddr)) {
            bfd_vma val;
            
            if (get_howto_table(abfd)[R_SH_DIR32].partial_inplace) {
                val = bfd_get_32(abfd, contents + nraddr);
                val += isym->st_value;
                if (val > addr && val < toaddr) {
                    bfd_put_32(abfd, val - count, contents + nraddr);
                }
            } else {
                val = isym->st_value + irel->r_addend;
                if (val > addr && val < toaddr) {
                    irel->r_addend -= count;
                }
            }
        }
    }
}

static bfd_vma
calculate_stop_address(bfd_vma start, int insn, enum elf_sh_reloc_type rtype)
{
    int off;
    
    switch (rtype) {
    case R_SH_DIR8WPN:
        off = insn & BYTE_MASK;
        if (off & SIGN_EXTEND_8BIT)
            off -= SIGN_EXTEND_8BIT_MASK;
        return (bfd_vma)((bfd_signed_vma)start + WORD_SIZE + off * INSTRUCTION_SIZE);
        
    case R_SH_IND12W:
        off = insn & WORD_MASK;
        if (!off) {
            return start;
        }
        if (off & SIGN_EXTEND_12BIT)
            off -= SIGN_EXTEND_12BIT_MASK;
        return (bfd_vma)((bfd_signed_vma)start + WORD_SIZE + off * INSTRUCTION_SIZE);
        
    case R_SH_DIR8WPZ:
        off = insn & BYTE_MASK;
        return start + WORD_SIZE + off * INSTRUCTION_SIZE;
        
    case R_SH_DIR8WPL:
        off = insn & BYTE_MASK;
        return (start & ~(bfd_vma)3) + WORD_SIZE + off * WORD_SIZE;
        
    default:
        return start;
    }
}

static void
handle_switch_reloc(bfd *abfd, Elf_Internal_Rela *irel, bfd_byte *contents,
                   bfd_vma nraddr, bfd_vma addr, bfd_vma toaddr, int count,
                   bfd_vma *start, bfd_vma *stop, bfd_signed_vma *voff)
{
    *stop = irel->r_offset;
    *start = (bfd_vma)((bfd_signed_vma)*stop - (long)irel->r_addend);
    
    if (*start > addr && *start < toaddr && (*stop <= addr || *stop >= toaddr)) {
        irel->r_addend += count;
    } else if (*stop > addr && *stop < toaddr && (*start <= addr || *start >= toaddr)) {
        irel->r_addend -= count;
    }
    
    if (ELF32_R_TYPE(irel->r_info) == (int)R_SH_SWITCH16) {
        *voff = bfd_get_signed_16(abfd, contents + nraddr);
    } else if (ELF32_R_TYPE(irel->r_info) == (int)R_SH_SWITCH8) {
        *voff = bfd_get_8(abfd, contents + nraddr);
    } else {
        *voff = bfd_get_signed_32(abfd, contents + nraddr);
    }
    
    *stop = (bfd_vma)((bfd_signed_vma)*start + *voff);
}

static int
calculate_adjustment(bfd_vma start, bfd_vma stop, bfd_vma addr,
                    bfd_vma toaddr, int count)
{
    if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr))
        return count;
    if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))
        return -count;
    return 0;
}

static bool
apply_reloc_adjustment(bfd *abfd, Elf_Internal_Rela *irel, bfd_byte *contents,
                       bfd_vma nraddr, int adjust, int count, int insn,
                       bfd_signed_vma voff)
{
    int oinsn = insn;
    bool overflow = false;
    
    switch ((enum elf_sh_reloc_type)ELF32_R_TYPE(irel->r_info)) {
    case R_SH_DIR8WPN:
    case R_SH_DIR8WPZ:
        insn += adjust / INSTRUCTION_SIZE;
        if ((oinsn & HIGH_BYTE_MASK) != (insn & HIGH_BYTE_MASK))
            overflow = true;
        bfd_put_16(abfd, (bfd_vma)insn, contents + nraddr);
        break;
        
    case R_SH_IND12W:
        insn += adjust / INSTRUCTION_SIZE;
        if ((oinsn & NIBBLE_MASK) != (insn & NIBBLE_MASK))
            overflow = true;
        bfd_put_16(abfd, (bfd_vma)insn, contents + nraddr);
        break;
        
    case R_SH_DIR8WPL:
        BFD_ASSERT(adjust == count || count >= WORD_SIZE);
        if (count >= WORD_SIZE) {
            insn += adjust / WORD_SIZE;
        } else {
            if ((irel->r_offset & 3) == 0)
                ++insn;
        }
        if ((oinsn & HIGH_BYTE_MASK) != (insn & HIGH_BYTE_MASK))
            overflow = true;
        bfd_put_16(abfd, (bfd_vma)insn, contents + nraddr);
        break;
        
    case R_SH_SWITCH8:
        voff += adjust;
        if (voff < 0 || voff >= SWITCH8_MAX)
            overflow = true;
        bfd_put_8(abfd, voff, contents + nraddr);
        break;
        
    case R_SH_SWITCH16:
        voff += adjust;
        if (voff < SWITCH16_MIN || voff >= SWITCH16_MAX)
            overflow = true;
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
        break;
    }
    
    return overflow;
}

static bool
adjust_single_reloc(bfd *abfd, Elf_Internal_Rela *irel, bfd_byte *contents,
                   bfd_vma addr, bfd_vma toaddr, int count, unsigned int sec_shndx,
                   Elf_Internal_Sym *isymbuf, Elf_Internal_Shdr *symtab_hdr)
{
    bfd_vma nraddr, start = 0, stop;
    int insn = 0, adjust;
    bfd_signed_vma voff = 0;
    enum elf_sh_reloc_type rtype;
    
    nraddr = calculate_new_reloc_address(irel, addr, toaddr, count);
    
    if (should_delete_reloc(irel, addr, count)) {
        irel->r_info = ELF32_R_INFO(ELF32_R_SYM(irel->r_info), (int)R_SH_NONE);
    }
    
    get_reloc_start_and_insn(abfd, irel, contents, nraddr, &start, &insn);
    
    rtype = (enum elf_sh_reloc_type)ELF32_R_TYPE(irel->r_info);
    
    switch (rtype) {
    case R_SH_DIR32:
        adjust_dir32_reloc(abfd, irel, contents, nraddr, addr, toaddr, count,
                          sec_shndx, isymbuf, symtab_hdr);
        stop = addr;
        break;
        
    case R_SH_SWITCH8:
    case R_SH_SWITCH16:
    case R_SH_SWITCH32:
        handle_switch_reloc(abfd, irel, contents, nraddr, addr, toaddr, count,
                           &start, &stop, &voff);
        break;
        
    case R_SH_USES:
        start = irel->r_offset;
        stop = (bfd_vma)((bfd_signed_vma)start + (long)irel->r_addend + WORD_SIZE);
        break;
        
    case R_SH_IND12W:
        stop = calculate_stop_address(start, insn, rtype);
        if (stop != start && stop > addr && stop < toaddr) {
            irel->r_addend -= count;
        }
        break;
        
    case R_SH_DIR8WPN:
    case R_SH_DIR8WPZ:
    case R_SH_DIR8WPL:
        stop = calculate_stop_address(start, insn, rtype);
        break;
        
    default:
        stop = addr;
        break;
    }
    
    adjust = calculate_adjustment(start, stop, addr, toaddr, count);
    
    if (adjust != 0) {
        bool overflow = apply_reloc_adjustment(abfd, irel, contents, nraddr,
                                              adjust, count, insn, voff);
        if (overflow) {
            _bfd_error_handler(
                _("%pB: %#" PRIx64 ": fatal: reloc overflow while relaxing"),
                abfd, (uint64_t)irel->r_offset);
            bfd_set_error(bfd_error_bad_value);
            return false;
        }
    }
    
    irel->r_offset = nraddr;
    return true;
}

static bool
load_section_contents(bfd *abfd, asection *o, bfd_byte **ocontents)
{
    if (*ocontents != NULL)
        return true;
        
    if (elf_section_data(o)->this_hdr.contents != NULL) {
        *ocontents = elf_section_data(o)->this_hdr.contents;
    } else {
        if (!bfd_malloc_and_get_section(abfd, o, ocontents)) {
            free(*ocontents);
            return false;
        }
        elf_section_data(o)->this_hdr.contents = *ocontents;
    }
    
    return true;
}

static void
adjust_switch32_in_section(bfd *abfd, asection *o, bfd_vma addr, bfd_vma toaddr,
                          int count, bfd_byte *ocontents)
{
    bfd_vma start, stop;
    bfd_signed_vma voff;
    Elf_Internal_Rela *irelscan, *irelscanend;
    Elf_Internal_Rela *internal_relocs;
    
    internal_relocs = elf_section_data(o)->relocs;
    irelscanend = internal_relocs + o->reloc_count;
    
    for (irelscan = internal_relocs; irelscan < irelscanend; irelscan++) {
        if (ELF32_R_TYPE(irelscan->r_info) != (int)R_SH_SWITCH32)
            continue;
            
        stop = irelscan->r_offset;
        start = (bfd_vma)((bfd_signed_vma)stop - (long)irelscan->r_addend);
        
        if (start > addr && start < toaddr)
            irelscan->r_addend += count;
            
        voff = bfd_get_signed_32(abfd, ocontents + irelscan->r_offset);
        stop = (bfd_vma)((bfd_signed_vma)start + voff);
        
        if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr)) {
            bfd_put_signed_32(abfd, (bfd_vma)voff + count,
                            ocontents + irelscan->r_offset);
        } else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr)) {
            bfd_put_signed_32(abfd, (bfd_vma)voff - count,
                            ocontents + irelscan->r_offset);
        }
    }
}

static void
adjust_dir32_in_section(bfd *abfd, asection *o, bfd_vma addr, bfd_vma toaddr,
                       int count, unsigned int sec_shndx, Elf_Internal_Sym *isymbuf,
                       Elf_Internal_Shdr *symtab_hdr, bfd_byte *ocontents)
{
    Elf_Internal_Rela *irelscan, *irelscanend;
    Elf_Internal_Rela *internal_relocs;
    
    internal_relocs = elf_section_data(o)->relocs;
    irelscanend = internal_relocs + o->reloc_count;
    
    for (irelscan = internal_relocs; irelscan < irelscanend; irelscan++) {
        if (ELF32_R_TYPE(irelscan->r_info) != (int)R_SH_DIR32)
            continue;
            
        if (ELF32_R_SYM(irelscan->r_info) >= symtab_hdr->sh_info)
            continue;
            
        Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM(irelscan->r_info);
        if (isym->st_shndx == sec_shndx &&
            (isym->st_value <= addr || isym->st_value >= toaddr)) {
            bfd_vma val = bfd_get_32(abfd, ocontents + irelscan->r_offset);
            val += isym->st_value;
            if (val > addr && val < toaddr) {
                bfd_put_32(abfd, val - count, ocontents + irelscan->r_offset);
            }
        }
    }
}

static bool
adjust_other_sections(bfd *abfd, asection *sec, bfd_vma addr, bfd_vma toaddr,
                     int count, unsigned int sec_shndx, Elf_Internal_Sym *isymbuf,
                     Elf_Internal_Shdr *symtab_hdr)
{
    asection *o;
    
    for (o = abfd->sections; o != NULL; o = o->next) {
        Elf_Internal_Rela *internal_relocs;
        bfd_byte *ocontents = NULL;
        
        if (o == sec || (o->flags & SEC_HAS_CONTENTS) == 0 ||
            (o->flags & SEC_RELOC) == 0 || o->reloc_count == 0)
            continue;
            
        internal_relocs = _bfd_elf_link_read_relocs(abfd, o, NULL, NULL, true);
        if (internal_relocs == NULL)
            return false;
            
        Elf_Internal_Rela *irelscan, *irelscanend = internal_relocs + o->reloc_count;
        
        for (irelscan = internal_relocs; irelscan < irelscanend; irelscan++) {
            if (ELF32_R_TYPE(irelscan->r_info) == (int)R_SH_SWITCH32) {
                if (!load_section_contents(abfd, o, &ocontents))
                    return false;
                adjust_switch32_in_section(abfd, o, addr, toaddr, count, ocontents);
                break;
            }
        }
        
        for (irelscan = internal_relocs; irelscan < irelscanend; irelscan++) {
            if (ELF32_R_TYPE(irelscan->r_info) == (int)R_SH_DIR32 &&
                ELF32_R_SYM(irelscan->r_info) < symtab_hdr->sh_info) {
                if (!load_section_contents(abfd, o, &ocontents))
                    return false;
                adjust_dir32_in_section(abfd, o, addr, toaddr, count, sec_shndx,
                                      isymbuf, symtab_hdr, ocontents);
                break;
            }
        }
    }
    
    return true;
}

static void
adjust_local_symbols(Elf_Internal_Sym *isymbuf, Elf_Internal_Shdr *symtab_hdr,
                    unsigned int sec_shndx, bfd_vma addr, bfd_vma toaddr, int count)
{
    Elf_Internal_Sym *isym, *isymend;
    
    isymend = isymbuf + symtab_hdr->sh_info;
    for (isym = isymbuf; isym < isymend; isym++) {
        if (isym->st_shndx == sec_shndx && isym->st_value > addr &&
            isym->st_value < toaddr) {
            isym->st_value -= count;
        }
    }
}

static void
adjust_global_symbols(bfd *abfd, asection *sec, bfd_vma addr, bfd_vma toaddr,
                     int count, Elf_Internal_Shdr *symtab_hdr)
{
    unsigned int symcount;
    struct elf_link_hash_entry **sym_hashes, **end_hashes;
    
    symcount = (symtab_hdr->sh_size / sizeof(Elf32_External_Sym) -
                symtab_hdr->sh_info);
    sym_hashes = elf_sym_hashes(abfd);
    end_hashes = sym_hashes + symcount;
    
    for (; sym_hashes < end_hashes; sym_hashes++) {
        struct elf_link_hash_entry *sym_hash = *sym_hashes;
        if ((sym_hash->root.type == bfd_link_hash_defined ||
             sym_hash->root.type == bfd_link_hash_defweak) &&
            sym_hash->root.u.def.section == sec &&
            sym_hash->root.u.def.value > addr &&
            sym_hash->root.u.def.value < toaddr) {
            sym_hash->root.u.def.value -= count;
        }
    }
}

static bool
sh_elf_relax_delete_bytes(bfd *abfd, asection *sec, bfd_vma addr, int count)
{
    Elf_Internal_Shdr *symtab_hdr;
    unsigned int sec_shndx;
    bfd_byte *contents;
    Elf_Internal_Rela *irel, *irelend;
    Elf_Internal_Rela *irelalign = NULL;
    bfd_vma toaddr;
    Elf_Internal_Sym *isymbuf;
    
    symtab_hdr = &elf_symtab_hdr(abfd);
    isymbuf = (Elf_Internal_Sym *)symtab_hdr->contents;
    sec_shndx = _bfd_elf_section_from_bfd_section(abfd, sec);
    contents = elf_section_data(sec)->this_hdr.contents;
    
    toaddr = find_alignment_boundary(sec, addr, count);
    
    irel = elf_section_data(sec)->relocs;
    irelend = irel + sec->reloc_count;
    for (; irel < irelend; irel++) {
        if (ELF32_R_TYPE(irel->r_info) == (int)R_SH_ALIGN &&
            irel->r_offset == toaddr) {
            irelalign = irel;
            break;
        }
    }
    
    delete_bytes_from_contents(abfd, sec, contents, addr, count, toaddr, irelalign);
    
    for (irel = elf_section_data(sec)->relocs; irel < irelend; irel++) {
        if (!adjust_single_reloc(abfd, irel, contents, addr, toaddr, count,
                                sec_shndx, isymbuf, symtab_hdr)) {
            return false;
        }
    }
    
    if (!adjust_other_sections(abfd, sec, addr, toaddr, count, sec_shndx,
                              isymbuf, symtab_hdr)) {
        return false;
    }
    
    adjust_local_symbols(isymbuf, symtab_hdr, sec_shndx, addr, toaddr, count);
    adjust_global_symbols(abfd, sec, addr, toaddr, count, symtab_hdr);
    
    if (irelalign != NULL) {
        bfd_vma alignto = BFD_ALIGN(toaddr, 1 << irelalign->r_addend);
        bfd_vma alignaddr = BFD_ALIGN(irelalign->r_offset, 1 << irelalign->r_addend);
        if (alignto != alignaddr) {
            return sh_elf_relax_delete_bytes(abfd, sec, alignaddr,
                                            (int)(alignto - alignaddr));
        }
    }
    
    return true;
}

/* Look for loads and stores which we can align to four byte
   boundaries.  This is like sh_align_loads in coff-sh.c.  */

static bool
sh_elf_align_loads (bfd *abfd ATTRIBUTE_UNUSED, asection *sec,
		    Elf_Internal_Rela *internal_relocs,
		    bfd_byte *contents ATTRIBUTE_UNUSED,
		    bool *pswapped)
{
  bfd_vma *labels = NULL;
  bfd_vma *label, *label_end;
  bool result;

  *pswapped = false;

  labels = collect_label_addresses(internal_relocs, sec->reloc_count, &label_end);
  if (labels == NULL)
    return false;

  label = labels;
  result = process_code_sections(abfd, sec, contents, internal_relocs,
                                 sec->reloc_count, &label, label_end, pswapped);

  free(labels);
  return result;
}

static bfd_vma *
collect_label_addresses(Elf_Internal_Rela *internal_relocs, 
                        unsigned int reloc_count,
                        bfd_vma **label_end)
{
  Elf_Internal_Rela *irel, *irelend;
  bfd_size_type amt;
  bfd_vma *labels;

  amt = reloc_count * sizeof(bfd_vma);
  labels = (bfd_vma *) bfd_malloc(amt);
  if (labels == NULL)
    return NULL;

  irelend = internal_relocs + reloc_count;
  *label_end = labels;

  for (irel = internal_relocs; irel < irelend; irel++)
    {
      if (is_label_reloc(irel))
        {
          **label_end = irel->r_offset;
          (*label_end)++;
        }
    }

  return labels;
}

static bool
is_label_reloc(Elf_Internal_Rela *irel)
{
  return ELF32_R_TYPE(irel->r_info) == (int) R_SH_LABEL;
}

static bool
is_code_reloc(Elf_Internal_Rela *irel)
{
  return ELF32_R_TYPE(irel->r_info) == (int) R_SH_CODE;
}

static bool
is_data_reloc(Elf_Internal_Rela *irel)
{
  return ELF32_R_TYPE(irel->r_info) == (int) R_SH_DATA;
}

static bfd_vma
find_section_stop(Elf_Internal_Rela *irel, Elf_Internal_Rela *irelend,
                  bfd_size_type section_size)
{
  for (irel++; irel < irelend; irel++)
    if (is_data_reloc(irel))
      return irel->r_offset;
  
  return section_size;
}

static bool
process_code_sections(bfd *abfd, asection *sec, bfd_byte *contents,
                     Elf_Internal_Rela *internal_relocs,
                     unsigned int reloc_count,
                     bfd_vma **label, bfd_vma *label_end,
                     bool *pswapped)
{
  Elf_Internal_Rela *irel, *irelend;
  bfd_vma start, stop;

  irelend = internal_relocs + reloc_count;

  for (irel = internal_relocs; irel < irelend; irel++)
    {
      if (!is_code_reloc(irel))
        continue;

      start = irel->r_offset;
      stop = find_section_stop(irel, irelend, sec->size);

      if (!_bfd_sh_align_load_span(abfd, sec, contents, sh_elf_swap_insns,
                                   internal_relocs, label,
                                   label_end, start, stop, pswapped))
        return false;
    }

  return true;
}

/* Swap two SH instructions.  This is like sh_swap_insns in coff-sh.c.  */

static bool is_special_reloc_type(enum elf_sh_reloc_type type)
{
  return type == R_SH_ALIGN || type == R_SH_CODE || 
         type == R_SH_DATA || type == R_SH_LABEL;
}

static void swap_instruction_bytes(bfd *abfd, bfd_byte *contents, bfd_vma addr)
{
  unsigned short i1 = bfd_get_16(abfd, contents + addr);
  unsigned short i2 = bfd_get_16(abfd, contents + addr + 2);
  bfd_put_16(abfd, (bfd_vma)i2, contents + addr);
  bfd_put_16(abfd, (bfd_vma)i1, contents + addr + 2);
}

static void adjust_uses_reloc(Elf_Internal_Rela *irel, bfd_vma addr)
{
  bfd_vma off = irel->r_offset + 4 + irel->r_addend;
  if (off == addr)
    irel->r_addend += 2;
  else if (off == addr + 2)
    irel->r_addend -= 2;
}

static int adjust_reloc_offset(Elf_Internal_Rela *irel, bfd_vma addr)
{
  if (irel->r_offset == addr)
  {
    irel->r_offset += 2;
    return -2;
  }
  if (irel->r_offset == addr + 2)
  {
    irel->r_offset -= 2;
    return 2;
  }
  return 0;
}

static bool update_instruction_with_overflow_check(bfd *abfd, bfd_byte *loc, 
                                                   int add, unsigned short mask)
{
  unsigned short insn = bfd_get_16(abfd, loc);
  unsigned short oinsn = insn;
  insn += add / 2;
  if ((oinsn & mask) != (insn & mask))
    return true;
  bfd_put_16(abfd, (bfd_vma)insn, loc);
  return false;
}

static bool handle_reloc_adjustment(bfd *abfd, bfd_byte *contents, 
                                    Elf_Internal_Rela *irel, int add, 
                                    enum elf_sh_reloc_type type, bfd_vma addr)
{
  #define ADDR_BOUNDARY_MASK 3
  #define HIGH_BYTE_MASK 0xff00
  #define HIGH_NIBBLE_MASK 0xf000
  
  bfd_byte *loc = contents + irel->r_offset;
  bool overflow = false;

  switch (type)
  {
  case R_SH_DIR8WPN:
  case R_SH_DIR8WPZ:
    overflow = update_instruction_with_overflow_check(abfd, loc, add, HIGH_BYTE_MASK);
    break;

  case R_SH_IND12W:
    overflow = update_instruction_with_overflow_check(abfd, loc, add, HIGH_NIBBLE_MASK);
    break;

  case R_SH_DIR8WPL:
    if ((addr & ADDR_BOUNDARY_MASK) != 0)
      overflow = update_instruction_with_overflow_check(abfd, loc, add, HIGH_BYTE_MASK);
    break;

  default:
    break;
  }

  if (overflow)
  {
    _bfd_error_handler(
      (_("%pB: %#" PRIx64 ": fatal: reloc overflow while relaxing"),
       abfd, (uint64_t)irel->r_offset);
    bfd_set_error(bfd_error_bad_value);
    return false;
  }
  
  return true;
}

static bool process_single_reloc(bfd *abfd, bfd_byte *contents, 
                                 Elf_Internal_Rela *irel, bfd_vma addr)
{
  enum elf_sh_reloc_type type = (enum elf_sh_reloc_type)ELF32_R_TYPE(irel->r_info);
  
  if (is_special_reloc_type(type))
    return true;

  if (type == R_SH_USES)
    adjust_uses_reloc(irel, addr);

  int add = adjust_reloc_offset(irel, addr);
  
  if (add != 0)
    return handle_reloc_adjustment(abfd, contents, irel, add, type, addr);
    
  return true;
}

static bool sh_elf_swap_insns(bfd *abfd, asection *sec, void *relocs,
                              bfd_byte *contents, bfd_vma addr)
{
  Elf_Internal_Rela *internal_relocs = (Elf_Internal_Rela *)relocs;
  
  swap_instruction_bytes(abfd, contents, addr);

  Elf_Internal_Rela *irelend = internal_relocs + sec->reloc_count;
  for (Elf_Internal_Rela *irel = internal_relocs; irel < irelend; irel++)
  {
    if (!process_single_reloc(abfd, contents, irel, addr))
      return false;
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

static const struct elf_sh_plt_info *
get_fdpic_plt_info(bfd *abfd)
{
    int endian_index = !bfd_big_endian(abfd);
    
    if (sh_get_arch_from_bfd_mach(bfd_get_mach(abfd)) & arch_sh2a_base)
        return &fdpic_sh2a_plts[endian_index];
    
    return &fdpic_sh_plts[endian_index];
}

static const struct elf_sh_plt_info *
get_plt_info(bfd *abfd, bool pic_p)
{
    int endian_index = !bfd_big_endian(abfd);
    
    if (fdpic_object_p(abfd))
        return get_fdpic_plt_info(abfd);
    
    if (vxworks_object_p(abfd))
        return &vxworks_sh_plts[pic_p][endian_index];
    
    return &elf_sh_plts[pic_p][endian_index];
}

/* Install a 32-bit PLT field starting at ADDR, which occurs in OUTPUT_BFD.
   VALUE is the field's value and CODE_P is true if VALUE refers to code,
   not data.  */

inline static void
install_plt_field (bfd *output_bfd, bool code_p ATTRIBUTE_UNUSED,
		   unsigned long value, bfd_byte *addr)
{
  bfd_put_32 (output_bfd, value, addr);
}

/* The number of PLT entries which can use a shorter PLT, if any.
   Currently always 64K, since only SH-2A FDPIC uses this; a
   20-bit movi20 can address that many function descriptors below
   _GLOBAL_OFFSET_TABLE_.  */
#define MAX_SHORT_PLT 65536

/* Return the index of the PLT entry at byte offset OFFSET.  */

static bfd_vma calculate_short_plt_offset(const struct elf_sh_plt_info *info, bfd_vma offset, bfd_vma *plt_index)
{
    bfd_vma short_plt_size = MAX_SHORT_PLT * info->short_plt->symbol_entry_size;
    
    if (offset > short_plt_size) {
        *plt_index = MAX_SHORT_PLT;
        return offset - short_plt_size;
    }
    
    return offset;
}

static const struct elf_sh_plt_info* get_effective_plt_info(const struct elf_sh_plt_info *info, bfd_vma offset)
{
    if (info->short_plt == NULL) {
        return info;
    }
    
    bfd_vma short_plt_size = MAX_SHORT_PLT * info->short_plt->symbol_entry_size;
    
    if (offset <= short_plt_size) {
        return info->short_plt;
    }
    
    return info;
}

static bfd_vma get_plt_index(const struct elf_sh_plt_info *info, bfd_vma offset)
{
    bfd_vma plt_index = 0;
    
    offset -= info->plt0_entry_size;
    
    if (info->short_plt != NULL) {
        offset = calculate_short_plt_offset(info, offset, &plt_index);
        info = get_effective_plt_info(info, offset + plt_index * info->short_plt->symbol_entry_size);
    }
    
    return plt_index + offset / info->symbol_entry_size;
}

/* Do the inverse operation.  */

static bfd_vma
calculate_short_plt_offset(const struct elf_sh_plt_info *info, bfd_vma plt_index)
{
    if (plt_index <= MAX_SHORT_PLT)
        return 0;
    
    return MAX_SHORT_PLT * info->short_plt->symbol_entry_size;
}

static bfd_vma
adjust_plt_index_for_short(bfd_vma plt_index)
{
    if (plt_index <= MAX_SHORT_PLT)
        return plt_index;
    
    return plt_index - MAX_SHORT_PLT;
}

static const struct elf_sh_plt_info *
select_plt_info(const struct elf_sh_plt_info *info, bfd_vma plt_index)
{
    if (info->short_plt == NULL)
        return info;
    
    if (plt_index <= MAX_SHORT_PLT)
        return info->short_plt;
    
    return info;
}

static bfd_vma
calculate_plt_entry_offset(const struct elf_sh_plt_info *info, bfd_vma plt_index)
{
    return info->plt0_entry_size + (plt_index * info->symbol_entry_size);
}

static bfd_vma
get_plt_offset(const struct elf_sh_plt_info *info, bfd_vma plt_index)
{
    bfd_vma offset = 0;
    
    if (info->short_plt != NULL)
    {
        offset = calculate_short_plt_offset(info, plt_index);
        plt_index = adjust_plt_index_for_short(plt_index);
        info = select_plt_info(info, plt_index + offset / (info->short_plt->symbol_entry_size));
    }
    
    return offset + calculate_plt_entry_offset(info, plt_index);
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

static bool sh_elf_mkobject(bfd *abfd)
{
    return bfd_elf_allocate_object(abfd, sizeof(struct sh_elf_obj_tdata));
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

static struct bfd_hash_entry *
sh_elf_link_hash_newfunc (struct bfd_hash_entry *entry,
			  struct bfd_hash_table *table,
			  const char *string)
{
  struct elf_sh_link_hash_entry *ret =
    (struct elf_sh_link_hash_entry *) entry;

  if (ret == NULL)
    ret = ((struct elf_sh_link_hash_entry *)
	   bfd_hash_allocate (table,
			      sizeof (struct elf_sh_link_hash_entry)));
  if (ret == NULL)
    return NULL;

  ret = ((struct elf_sh_link_hash_entry *)
	 _bfd_elf_link_hash_newfunc ((struct bfd_hash_entry *) ret,
				     table, string));
  if (ret != NULL)
    {
      ret->gotplt_refcount = 0;
      ret->funcdesc.refcount = 0;
      ret->abs_funcdesc_refcount = 0;
      ret->got_type = GOT_UNKNOWN;
    }

  return (struct bfd_hash_entry *) ret;
}

/* Create an sh ELF linker hash table.  */

static struct bfd_link_hash_table *
sh_elf_link_hash_table_create (bfd *abfd)
{
  struct elf_sh_link_hash_table *ret;
  size_t amt = sizeof (struct elf_sh_link_hash_table);

  ret = (struct elf_sh_link_hash_table *) bfd_zmalloc (amt);
  if (ret == NULL)
    return NULL;

  if (!_bfd_elf_link_hash_table_init (&ret->root, abfd,
				      sh_elf_link_hash_newfunc,
				      sizeof (struct elf_sh_link_hash_entry)))
    {
      free (ret);
      return NULL;
    }

  if (fdpic_object_p (abfd))
    {
      ret->root.dt_pltgot_required = true;
      ret->fdpic_p = true;
    }

  return &ret->root.root;
}

static bool
sh_elf_omit_section_dynsym (bfd *output_bfd ATTRIBUTE_UNUSED,
			    struct bfd_link_info *info, asection *p)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);

  if (!htab->fdpic_p)
    return true;

  switch (elf_section_data (p)->this_hdr.sh_type)
    {
    case SHT_PROGBITS:
    case SHT_NOBITS:
    case SHT_NULL:
      return false;
    default:
      return true;
    }
}

/* Create .got, .gotplt, and .rela.got sections in DYNOBJ, and set up
   shortcuts to them in our hash table.  */

static bool
create_section_with_alignment(bfd *dynobj, asection **section_ptr, 
                              const char *name, flagword flags)
{
    *section_ptr = bfd_make_section_anyway_with_flags(dynobj, name, flags);
    if (*section_ptr == NULL || !bfd_set_section_alignment(*section_ptr, 2))
        return false;
    return true;
}

static bool
create_got_section(bfd *dynobj, struct bfd_link_info *info)
{
    struct elf_sh_link_hash_table *htab;
    
    if (!_bfd_elf_create_got_section(dynobj, info))
        return false;
    
    htab = sh_elf_hash_table(info);
    if (htab == NULL)
        return false;
    
    const flagword funcdesc_flags = SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS 
                                   | SEC_IN_MEMORY | SEC_LINKER_CREATED;
    const flagword readonly_flags = funcdesc_flags | SEC_READONLY;
    
    if (!create_section_with_alignment(dynobj, &htab->sfuncdesc, 
                                       ".got.funcdesc", funcdesc_flags))
        return false;
    
    if (!create_section_with_alignment(dynobj, &htab->srelfuncdesc,
                                       ".rela.got.funcdesc", readonly_flags))
        return false;
    
    if (!create_section_with_alignment(dynobj, &htab->srofixup,
                                       ".rofixup", readonly_flags))
        return false;
    
    return true;
}

/* Create dynamic sections when linking against a dynamic object.  */

static int get_pointer_alignment(const struct elf_backend_data *bed)
{
  switch (bed->s->arch_size)
    {
    case 32:
      return 2;
    case 64:
      return 3;
    default:
      bfd_set_error (bfd_error_bad_value);
      return -1;
    }
}

static flagword get_plt_flags(const struct elf_backend_data *bed)
{
  flagword flags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS | SEC_IN_MEMORY
                   | SEC_LINKER_CREATED | SEC_CODE);
  
  if (bed->plt_not_loaded)
    flags &= ~ (SEC_LOAD | SEC_HAS_CONTENTS);
  if (bed->plt_readonly)
    flags |= SEC_READONLY;
  
  return flags;
}

static bool create_section_with_alignment(bfd *abfd, const char *name,
                                         flagword flags, int alignment,
                                         asection **section_ptr)
{
  asection *s = bfd_make_section_anyway_with_flags(abfd, name, flags);
  *section_ptr = s;
  return s != NULL && bfd_set_section_alignment(s, alignment);
}

static bool create_procedure_linkage_symbol(bfd *abfd, struct bfd_link_info *info,
                                           struct elf_sh_link_hash_table *htab,
                                           asection *plt_section)
{
  struct bfd_link_hash_entry *bh = NULL;
  
  if (!_bfd_generic_link_add_one_symbol(info, abfd, "_PROCEDURE_LINKAGE_TABLE_",
                                        BSF_GLOBAL, plt_section, (bfd_vma) 0,
                                        NULL, false,
                                        get_elf_backend_data(abfd)->collect, &bh))
    return false;
  
  struct elf_link_hash_entry *h = (struct elf_link_hash_entry *) bh;
  h->def_regular = 1;
  h->type = STT_OBJECT;
  htab->root.hplt = h;
  
  return !bfd_link_pic(info) || bfd_elf_link_record_dynamic_symbol(info, h);
}

static bool create_plt_sections(bfd *abfd, struct bfd_link_info *info,
                               struct elf_sh_link_hash_table *htab,
                               const struct elf_backend_data *bed,
                               int ptralign)
{
  flagword base_flags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS | SEC_IN_MEMORY
                         | SEC_LINKER_CREATED);
  flagword pltflags = get_plt_flags(bed);
  
  if (!create_section_with_alignment(abfd, ".plt", pltflags, 
                                     bed->plt_alignment, &htab->root.splt))
    return false;
  
  if (bed->want_plt_sym && 
      !create_procedure_linkage_symbol(abfd, info, htab, htab->root.splt))
    return false;
  
  const char *rel_name = bed->default_use_rela_p ? ".rela.plt" : ".rel.plt";
  if (!create_section_with_alignment(abfd, rel_name, 
                                     base_flags | SEC_READONLY, 
                                     ptralign, &htab->root.srelplt))
    return false;
  
  return true;
}

static bool create_dynbss_sections(bfd *abfd, struct bfd_link_info *info,
                                   struct elf_sh_link_hash_table *htab,
                                   const struct elf_backend_data *bed,
                                   int ptralign)
{
  flagword base_flags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS | SEC_IN_MEMORY
                         | SEC_LINKER_CREATED);
  
  asection *s = bfd_make_section_anyway_with_flags(abfd, ".dynbss",
                                                   SEC_ALLOC | SEC_LINKER_CREATED);
  htab->root.sdynbss = s;
  if (s == NULL)
    return false;
  
  if (bfd_link_pic(info))
    return true;
  
  const char *rel_name = bed->default_use_rela_p ? ".rela.bss" : ".rel.bss";
  return create_section_with_alignment(abfd, rel_name,
                                       base_flags | SEC_READONLY,
                                       ptralign, &htab->root.srelbss);
}

static bool
sh_elf_create_dynamic_sections (bfd *abfd, struct bfd_link_info *info)
{
  const struct elf_backend_data *bed = get_elf_backend_data (abfd);
  int ptralign = get_pointer_alignment(bed);
  
  if (ptralign < 0)
    return false;
  
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;
  
  if (htab->root.dynamic_sections_created)
    return true;
  
  if (!create_plt_sections(abfd, info, htab, bed, ptralign))
    return false;
  
  if (htab->root.sgot == NULL && !create_got_section(abfd, info))
    return false;
  
  if (bed->want_dynbss && !create_dynbss_sections(abfd, info, htab, bed, ptralign))
    return false;
  
  if (htab->root.target_os == is_vxworks &&
      !elf_vxworks_create_dynamic_sections(abfd, info, &htab->srelplt2))
    return false;
  
  return true;
}

/* Adjust a symbol defined by a dynamic object and referenced by a
   regular object.  The current definition is in some section of the
   dynamic object, but we're not including those sections.  We have to
   change the definition to something the rest of the link can
   understand.  */

static bool
should_skip_plt_entry(struct elf_link_hash_entry *h, struct bfd_link_info *info)
{
    return h->plt.refcount <= 0
           || SYMBOL_CALLS_LOCAL(info, h)
           || (ELF_ST_VISIBILITY(h->other) != STV_DEFAULT
               && h->root.type == bfd_link_hash_undefweak);
}

static void
clear_plt_entry(struct elf_link_hash_entry *h)
{
    h->plt.offset = (bfd_vma) -1;
    h->needs_plt = 0;
}

static bool
handle_function_symbol(struct elf_link_hash_entry *h, struct bfd_link_info *info)
{
    if (should_skip_plt_entry(h, info))
    {
        clear_plt_entry(h);
    }
    return true;
}

static bool
handle_weak_alias(struct elf_link_hash_entry *h, struct bfd_link_info *info)
{
    struct elf_link_hash_entry *def = weakdef(h);
    BFD_ASSERT(def->root.type == bfd_link_hash_defined);
    h->root.u.def.section = def->root.u.def.section;
    h->root.u.def.value = def->root.u.def.value;
    if (info->nocopyreloc)
        h->non_got_ref = def->non_got_ref;
    return true;
}

static bool
should_skip_copy_reloc(struct elf_link_hash_entry *h, struct bfd_link_info *info)
{
    if (bfd_link_pic(info))
        return true;
    
    if (!h->non_got_ref)
        return true;
    
    if (0 && info->nocopyreloc)
    {
        h->non_got_ref = 0;
        return true;
    }
    
    if (0 && !_bfd_elf_readonly_dynrelocs(h))
    {
        h->non_got_ref = 0;
        return true;
    }
    
    return false;
}

static void
allocate_copy_reloc(struct elf_link_hash_entry *h, struct elf_sh_link_hash_table *htab)
{
    if ((h->root.u.def.section->flags & SEC_ALLOC) != 0 && h->size != 0)
    {
        asection *srel = htab->root.srelbss;
        BFD_ASSERT(srel != NULL);
        srel->size += sizeof(Elf32_External_Rela);
        h->needs_copy = 1;
    }
}

static bool
sh_elf_adjust_dynamic_symbol(struct bfd_link_info *info,
                             struct elf_link_hash_entry *h)
{
    struct elf_sh_link_hash_table *htab;
    asection *s;

    htab = sh_elf_hash_table(info);
    if (htab == NULL)
        return false;

    BFD_ASSERT(htab->root.dynobj != NULL
               && (h->needs_plt
                   || h->is_weakalias
                   || (h->def_dynamic
                       && h->ref_regular
                       && !h->def_regular)));

    if (h->type == STT_FUNC || h->needs_plt)
    {
        return handle_function_symbol(h, info);
    }
    
    h->plt.offset = (bfd_vma) -1;

    if (h->is_weakalias)
    {
        return handle_weak_alias(h, info);
    }

    if (should_skip_copy_reloc(h, info))
    {
        return true;
    }

    s = htab->root.sdynbss;
    BFD_ASSERT(s != NULL);

    allocate_copy_reloc(h, htab);

    return _bfd_elf_adjust_dynamic_copy(info, h, s);
}

/* Allocate space in .plt, .got and associated reloc sections for
   dynamic relocs.  */

static bool
ensure_dynamic_symbol(struct bfd_link_info *info, struct elf_link_hash_entry *h)
{
  if (h->dynindx == -1 && !h->forced_local)
    return bfd_elf_link_record_dynamic_symbol(info, h);
  return true;
}

static void
adjust_gotplt_refs(struct elf_link_hash_entry *h, struct elf_sh_link_hash_entry *eh)
{
  if ((h->got.refcount > 0 || h->forced_local) && eh->gotplt_refcount > 0)
    {
      h->got.refcount += eh->gotplt_refcount;
      if (h->plt.refcount >= eh->gotplt_refcount)
        h->plt.refcount -= eh->gotplt_refcount;
    }
}

static bool
is_symbol_visible_or_defined(struct elf_link_hash_entry *h)
{
  return ELF_ST_VISIBILITY(h->other) == STV_DEFAULT || 
         h->root.type != bfd_link_hash_undefweak;
}

static void
allocate_plt_entry(struct elf_link_hash_entry *h, 
                   struct elf_sh_link_hash_table *htab,
                   struct bfd_link_info *info)
{
  asection *s = htab->root.splt;
  const struct elf_sh_plt_info *plt_info = htab->plt_info;

  if (s->size == 0)
    s->size += htab->plt_info->plt0_entry_size;

  h->plt.offset = s->size;

  if (!htab->fdpic_p && !bfd_link_pic(info) && !h->def_regular)
    {
      h->root.u.def.section = s;
      h->root.u.def.value = h->plt.offset;
    }

  if (plt_info->short_plt != NULL && 
      get_plt_index(plt_info->short_plt, s->size) < MAX_SHORT_PLT)
    plt_info = plt_info->short_plt;

  s->size += plt_info->symbol_entry_size;

  if (!htab->fdpic_p)
    htab->root.sgotplt->size += 4;
  else
    htab->root.sgotplt->size += 8;

  htab->root.srelplt->size += sizeof(Elf32_External_Rela);
}

static void
allocate_vxworks_plt_relocs(struct elf_link_hash_entry *h,
                           struct elf_sh_link_hash_table *htab)
{
  if (h->plt.offset == htab->plt_info->plt0_entry_size)
    htab->srelplt2->size += sizeof(Elf32_External_Rela);
  
  htab->srelplt2->size += sizeof(Elf32_External_Rela) * 2;
}

static bool
handle_plt_allocation(struct elf_link_hash_entry *h,
                      struct elf_sh_link_hash_table *htab,
                      struct bfd_link_info *info)
{
  if (!htab->root.dynamic_sections_created || h->plt.refcount <= 0 ||
      !is_symbol_visible_or_defined(h))
    {
      h->plt.offset = (bfd_vma)-1;
      h->needs_plt = 0;
      return true;
    }

  if (!ensure_dynamic_symbol(info, h))
    return false;

  if (bfd_link_pic(info) || WILL_CALL_FINISH_DYNAMIC_SYMBOL(1, 0, h))
    {
      allocate_plt_entry(h, htab, info);
      
      if (htab->root.target_os == is_vxworks && !bfd_link_pic(info))
        allocate_vxworks_plt_relocs(h, htab);
    }
  else
    {
      h->plt.offset = (bfd_vma)-1;
      h->needs_plt = 0;
    }

  return true;
}

static void
allocate_got_space(struct elf_link_hash_entry *h,
                   struct elf_sh_link_hash_table *htab,
                   enum got_type got_type)
{
  asection *s = htab->root.sgot;
  h->got.offset = s->size;
  s->size += 4;
  
  if (got_type == GOT_TLS_GD)
    s->size += 4;
}

#define RELA_SIZE sizeof(Elf32_External_Rela)

static void
allocate_got_dynamic_relocs(struct elf_link_hash_entry *h,
                           struct elf_sh_link_hash_table *htab,
                           struct bfd_link_info *info,
                           enum got_type got_type,
                           bool dyn)
{
  if (!dyn)
    {
      if (htab->fdpic_p && !bfd_link_pic(info) &&
          h->root.type != bfd_link_hash_undefweak &&
          (got_type == GOT_NORMAL || got_type == GOT_FUNCDESC))
        htab->srofixup->size += 4;
      return;
    }

  if (got_type == GOT_TLS_IE && !h->def_dynamic && !bfd_link_pic(info))
    return;

  if ((got_type == GOT_TLS_GD && h->dynindx == -1) || got_type == GOT_TLS_IE)
    htab->root.srelgot->size += RELA_SIZE;
  else if (got_type == GOT_TLS_GD)
    htab->root.srelgot->size += 2 * RELA_SIZE;
  else if (got_type == GOT_FUNCDESC)
    {
      if (!bfd_link_pic(info) && SYMBOL_FUNCDESC_LOCAL(info, h))
        htab->srofixup->size += 4;
      else
        htab->root.srelgot->size += RELA_SIZE;
    }
  else if (is_symbol_visible_or_defined(h) &&
           (bfd_link_pic(info) || WILL_CALL_FINISH_DYNAMIC_SYMBOL(dyn, 0, h)))
    htab->root.srelgot->size += RELA_SIZE;
  else if (htab->fdpic_p && !bfd_link_pic(info) && got_type == GOT_NORMAL &&
           is_symbol_visible_or_defined(h))
    htab->srofixup->size += 4;
}

static bool
handle_got_allocation(struct elf_link_hash_entry *h,
                      struct elf_sh_link_hash_table *htab,
                      struct bfd_link_info *info)
{
  if (h->got.refcount <= 0)
    {
      h->got.offset = (bfd_vma)-1;
      return true;
    }

  enum got_type got_type = sh_elf_hash_entry(h)->got_type;
  
  if (!ensure_dynamic_symbol(info, h))
    return false;

  allocate_got_space(h, htab, got_type);
  
  bool dyn = htab->root.dynamic_sections_created;
  allocate_got_dynamic_relocs(h, htab, info, got_type, dyn);

  return true;
}

static void
allocate_funcdesc_relocs(struct elf_sh_link_hash_entry *eh,
                        struct elf_sh_link_hash_table *htab,
                        struct bfd_link_info *info,
                        struct elf_link_hash_entry *h)
{
  if (eh->abs_funcdesc_refcount > 0 &&
      (h->root.type != bfd_link_hash_undefweak ||
       (htab->root.dynamic_sections_created && !SYMBOL_CALLS_LOCAL(info, h))))
    {
      if (!bfd_link_pic(info) && SYMBOL_FUNCDESC_LOCAL(info, h))
        htab->srofixup->size += eh->abs_funcdesc_refcount * 4;
      else
        htab->root.srelgot->size += eh->abs_funcdesc_refcount * RELA_SIZE;
    }

  if ((eh->funcdesc.refcount > 0 ||
       (h->got.offset != MINUS_ONE && eh->got_type == GOT_FUNCDESC)) &&
      h->root.type != bfd_link_hash_undefweak &&
      SYMBOL_FUNCDESC_LOCAL(info, h))
    {
      eh->funcdesc.offset = htab->sfuncdesc->size;
      htab->sfuncdesc->size += 8;

      if (!bfd_link_pic(info) && SYMBOL_CALLS_LOCAL(info, h))
        htab->srofixup->size += 8;
      else
        htab->srelfuncdesc->size += RELA_SIZE;
    }
}

static void
remove_pc_relative_relocs(struct elf_dyn_relocs **pp)
{
  struct elf_dyn_relocs *p;
  
  while ((p = *pp) != NULL)
    {
      p->count -= p->pc_count;
      p->pc_count = 0;
      if (p->count == 0)
        *pp = p->next;
      else
        pp = &p->next;
    }
}

static void
remove_tls_vars_relocs(struct elf_dyn_relocs **pp)
{
  struct elf_dyn_relocs *p;
  
  while ((p = *pp) != NULL)
    {
      if (strcmp(p->sec->output_section->name, ".tls_vars") == 0)
        *pp = p->next;
      else
        pp = &p->next;
    }
}

static bool
handle_shared_relocs(struct elf_link_hash_entry *h,
                    struct elf_sh_link_hash_table *htab,
                    struct bfd_link_info *info)
{
  if (SYMBOL_CALLS_LOCAL(info, h))
    remove_pc_relative_relocs(&h->dyn_relocs);

  if (htab->root.target_os == is_vxworks)
    remove_tls_vars_relocs(&h->dyn_relocs);

  if (h->dyn_relocs != NULL && h->root.type == bfd_link_hash_undefweak)
    {
      if (ELF_ST_VISIBILITY(h->other) != STV_DEFAULT ||
          UNDEFWEAK_NO_DYNAMIC_RELOC(info, h))
        h->dyn_relocs = NULL;
      else if (!ensure_dynamic_symbol(info, h))
        return false;
    }

  return true;
}

static bool
handle_non_shared_relocs(struct elf_link_hash_entry *h,
                        struct elf_sh_link_hash_table *htab,
                        struct bfd_link_info *info)
{
  if (!h->non_got_ref &&
      ((h->def_dynamic && !h->def_regular) ||
       (htab->root.dynamic_sections_created &&
        (h->root.type == bfd_link_hash_undefweak ||
         h->root.type == bfd_link_hash_undefined))))
    {
      if (!ensure_dynamic_symbol(info, h))
        return false;
      
      if (h->dynindx == -1)
        h->dyn_relocs = NULL;
    }
  else
    {
      h->dyn_relocs = NULL;
    }

  return true;
}

static void
allocate_dyn_relocs_space(struct elf_link_hash_entry *h,
                         struct elf_sh_link_hash_table *htab,
                         struct bfd_link_info *info)
{
  struct elf_dyn_relocs *p;
  
  for (p = h->dyn_relocs; p != NULL; p = p->next)
    {
      asection *sreloc = elf_section_data(p->sec)->sreloc;
      sreloc->size += p->count * RELA_SIZE;

      if (htab->fdpic_p && !bfd_link_pic(info))
        htab->srofixup->size -= 4 * (p->count - p->pc_count);
    }
}

static bool
allocate_dynrelocs(struct elf_link_hash_entry *h, void *inf)
{
  if (h->root.type == bfd_link_hash_indirect)
    return true;

  struct bfd_link_info *info = (struct bfd_link_info *)inf;
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table(info);
  
  if (htab == NULL)
    return false;

  struct elf_sh_link_hash_entry *eh = (struct elf_sh_link_hash_entry *)h;
  
  adjust_gotplt_refs(h, eh);

  if (!handle_plt_allocation(h, htab, info))
    return false;

  if (!handle_got_allocation(h, htab, info))
    return false;

  allocate_funcdesc_relocs(eh, htab, info, h);

  if (h->dyn_relocs == NULL)
    return true;

  if (bfd_link_pic(info))
    {
      if (!handle_shared_relocs(h, htab, info))
        return false;
    }
  else
    {
      if (!handle_non_shared_relocs(h, htab, info))
        return false;
    }

  allocate_dyn_relocs_space(h, htab, info);

  return true;
}

/* This function is called after all the input files have been read,
   and the input sections have been assigned to output sections.
   It's a convenient place to determine the PLT style.  */

static bool
sh_elf_early_size_sections (bfd *output_bfd, struct bfd_link_info *info)
{
  sh_elf_hash_table (info)->plt_info = get_plt_info (output_bfd,
						     bfd_link_pic (info));

  if (sh_elf_hash_table (info)->fdpic_p && !bfd_link_relocatable (info)
      && !bfd_elf_stack_segment_size (output_bfd, info,
				      "__stacksize", DEFAULT_STACK_SIZE))
    return false;
  return true;
}

/* Set the sizes of the dynamic sections.  */

static bool
setup_interp_section(bfd *dynobj, struct bfd_link_info *info)
{
  asection *s;
  
  if (!bfd_link_executable(info) || info->nointerp)
    return true;
    
  s = bfd_get_linker_section(dynobj, ".interp");
  BFD_ASSERT(s != NULL);
  s->size = sizeof ELF_DYNAMIC_INTERPRETER;
  s->contents = (unsigned char *) ELF_DYNAMIC_INTERPRETER;
  s->alloced = 1;
  
  return true;
}

static void
process_local_dynrel(struct elf_dyn_relocs *p, 
                     struct elf_sh_link_hash_table *htab,
                     struct bfd_link_info *info)
{
  asection *srel;
  
  if (!bfd_is_abs_section(p->sec) && bfd_is_abs_section(p->sec->output_section))
    return;
    
  if (htab->root.target_os == is_vxworks && 
      strcmp(p->sec->output_section->name, ".tls_vars") == 0)
    return;
    
  if (p->count == 0)
    return;
    
  srel = elf_section_data(p->sec)->sreloc;
  srel->size += p->count * sizeof(Elf32_External_Rela);
  
  if ((p->sec->output_section->flags & SEC_READONLY) != 0) {
    info->flags |= DF_TEXTREL;
    info->callbacks->minfo(_("%pB: dynamic relocation in read-only section `%pA'\n"),
                          p->sec->owner, p->sec);
  }
  
  if (htab->fdpic_p && !bfd_link_pic(info))
    htab->srofixup->size -= 4 * (p->count - p->pc_count);
}

static void
process_section_dynrels(bfd *ibfd, struct elf_sh_link_hash_table *htab,
                        struct bfd_link_info *info)
{
  asection *s;
  struct elf_dyn_relocs *p;
  
  for (s = ibfd->sections; s != NULL; s = s->next) {
    for (p = ((struct elf_dyn_relocs *)
              elf_section_data(s)->local_dynrel);
         p != NULL;
         p = p->next) {
      process_local_dynrel(p, htab, info);
    }
  }
}

static bool
allocate_local_funcdesc(bfd *ibfd, bfd_size_type locsymcount,
                       union gotref **local_funcdesc,
                       bfd_signed_vma *local_got,
                       bfd_signed_vma *elf_got_base)
{
  bfd_size_type size;
  
  if (*local_funcdesc != NULL)
    return true;
    
  size = locsymcount * sizeof(union gotref);
  *local_funcdesc = (union gotref *) bfd_zalloc(ibfd, size);
  
  if (*local_funcdesc == NULL)
    return false;
    
  sh_elf_local_funcdesc(ibfd) = *local_funcdesc;
  *local_funcdesc += (local_got - elf_got_base);
  
  return true;
}

static bool
process_local_got_entry(bfd *ibfd, bfd_signed_vma *local_got,
                       char *local_got_type, union gotref **local_funcdesc,
                       struct elf_sh_link_hash_table *htab,
                       struct bfd_link_info *info,
                       bfd_size_type locsymcount)
{
  asection *s = htab->root.sgot;
  asection *srel = htab->root.srelgot;
  
  if (*local_got <= 0) {
    *local_got = (bfd_vma) -1;
    return true;
  }
  
  *local_got = s->size;
  s->size += 4;
  
  if (*local_got_type == GOT_TLS_GD)
    s->size += 4;
    
  if (bfd_link_pic(info))
    srel->size += sizeof(Elf32_External_Rela);
  else
    htab->srofixup->size += 4;
    
  if (*local_got_type == GOT_FUNCDESC) {
    if (!allocate_local_funcdesc(ibfd, locsymcount, local_funcdesc,
                                 local_got, elf_local_got_refcounts(ibfd)))
      return false;
    (*local_funcdesc)->refcount++;
    ++(*local_funcdesc);
  }
  
  return true;
}

static bool
process_local_got(bfd *ibfd, struct elf_sh_link_hash_table *htab,
                 struct bfd_link_info *info)
{
  bfd_signed_vma *local_got, *end_local_got;
  union gotref *local_funcdesc;
  char *local_got_type;
  bfd_size_type locsymcount;
  Elf_Internal_Shdr *symtab_hdr;
  
  symtab_hdr = &elf_symtab_hdr(ibfd);
  locsymcount = symtab_hdr->sh_info;
  
  local_got = elf_local_got_refcounts(ibfd);
  if (!local_got)
    return true;
    
  end_local_got = local_got + locsymcount;
  local_got_type = sh_elf_local_got_type(ibfd);
  local_funcdesc = sh_elf_local_funcdesc(ibfd);
  
  for (; local_got < end_local_got; ++local_got, ++local_got_type) {
    if (!process_local_got_entry(ibfd, local_got, local_got_type,
                                 &local_funcdesc, htab, info, locsymcount))
      return false;
  }
  
  return true;
}

static void
process_local_funcdesc_entry(union gotref *local_funcdesc,
                            struct elf_sh_link_hash_table *htab,
                            struct bfd_link_info *info)
{
  if (local_funcdesc->refcount <= 0) {
    local_funcdesc->offset = MINUS_ONE;
    return;
  }
  
  local_funcdesc->offset = htab->sfuncdesc->size;
  htab->sfuncdesc->size += 8;
  
  if (!bfd_link_pic(info))
    htab->srofixup->size += 8;
  else
    htab->srelfuncdesc->size += sizeof(Elf32_External_Rela);
}

static void
process_local_funcdescs(bfd *ibfd, struct elf_sh_link_hash_table *htab,
                       struct bfd_link_info *info)
{
  union gotref *local_funcdesc, *end_local_funcdesc;
  Elf_Internal_Shdr *symtab_hdr;
  bfd_size_type locsymcount;
  
  local_funcdesc = sh_elf_local_funcdesc(ibfd);
  if (!local_funcdesc)
    return;
    
  symtab_hdr = &elf_symtab_hdr(ibfd);
  locsymcount = symtab_hdr->sh_info;
  end_local_funcdesc = local_funcdesc + locsymcount;
  
  for (; local_funcdesc < end_local_funcdesc; ++local_funcdesc) {
    process_local_funcdesc_entry(local_funcdesc, htab, info);
  }
}

static bool
process_input_bfd(bfd *ibfd, struct elf_sh_link_hash_table *htab,
                 struct bfd_link_info *info)
{
  if (!is_sh_elf(ibfd))
    return true;
    
  process_section_dynrels(ibfd, htab, info);
  
  if (!process_local_got(ibfd, htab, info))
    return false;
    
  process_local_funcdescs(ibfd, htab, info);
  
  return true;
}

static void
setup_tls_ldm_got(struct elf_sh_link_hash_table *htab)
{
  if (htab->tls_ldm_got.refcount <= 0) {
    htab->tls_ldm_got.offset = -1;
    return;
  }
  
  htab->tls_ldm_got.offset = htab->root.sgot->size;
  htab->root.sgot->size += 8;
  htab->root.srelgot->size += sizeof(Elf32_External_Rela);
}

static void
handle_fdpic_got_plt(struct elf_sh_link_hash_table *htab)
{
  if (!htab->fdpic_p)
    return;
    
  BFD_ASSERT(htab->root.sgotplt && htab->root.sgotplt->size == 12);
  htab->root.sgotplt->size = 0;
}

static void
finalize_fdpic_got_plt(struct elf_sh_link_hash_table *htab)
{
  if (!htab->fdpic_p)
    return;
    
  htab->root.hgot->root.u.def.value = htab->root.sgotplt->size;
  htab->root.sgotplt->size += 12;
  
  if (htab->srofixup != NULL)
    htab->srofixup->size += 4;
}

static bool
is_dynamic_section(asection *s, struct elf_sh_link_hash_table *htab)
{
  return (s == htab->root.splt ||
          s == htab->root.sgot ||
          s == htab->root.sgotplt ||
          s == htab->sfuncdesc ||
          s == htab->srofixup ||
          s == htab->root.sdynbss);
}

static bool
allocate_section_contents(asection *s, bfd *dynobj)
{
  if ((s->flags & SEC_HAS_CONTENTS) == 0)
    return true;
    
  s->contents = (bfd_byte *) bfd_zalloc(dynobj, s->size);
  if (s->contents == NULL)
    return false;
    
  s->alloced = 1;
  return true;
}

static bool
process_dynamic_section(asection *s, bfd *dynobj,
                       struct elf_sh_link_hash_table *htab,
                       bool *relocs)
{
  if ((s->flags & SEC_LINKER_CREATED) == 0)
    return true;
    
  if (!is_dynamic_section(s, htab) && 
      !startswith(bfd_section_name(s), ".rela")) {
    return true;
  }
  
  if (startswith(bfd_section_name(s), ".rela")) {
    if (s->size != 0 && s != htab->root.srelplt && s != htab->srelplt2)
      *relocs = true;
    s->reloc_count = 0;
  }
  
  if (s->size == 0) {
    s->flags |= SEC_EXCLUDE;
    return true;
  }
  
  return allocate_section_contents(s, dynobj);
}

static bool
sh_elf_late_size_sections(bfd *output_bfd ATTRIBUTE_UNUSED,
                          struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab;
  bfd *dynobj;
  asection *s;
  bool relocs;
  bfd *ibfd;
  
  htab = sh_elf_hash_table(info);
  if (htab == NULL)
    return false;
    
  dynobj = htab->root.dynobj;
  if (dynobj == NULL)
    return true;
    
  if (htab->root.dynamic_sections_created) {
    if (!setup_interp_section(dynobj, info))
      return false;
  }
  
  for (ibfd = info->input_bfds; ibfd != NULL; ibfd = ibfd->link.next) {
    if (!process_input_bfd(ibfd, htab, info))
      return false;
  }
  
  setup_tls_ldm_got(htab);
  handle_fdpic_got_plt(htab);
  
  elf_link_hash_traverse(&htab->root, allocate_dynrelocs, info);
  
  finalize_fdpic_got_plt(htab);
  
  relocs = false;
  for (s = dynobj->sections; s != NULL; s = s->next) {
    if (!process_dynamic_section(s, dynobj, htab, &relocs))
      return false;
  }
  
  return _bfd_elf_maybe_vxworks_add_dynamic_tags(output_bfd, info, relocs);
}

/* Add a dynamic relocation to the SRELOC section.  */

inline static bfd_vma
sh_elf_add_dyn_reloc (bfd *output_bfd, asection *sreloc, bfd_vma offset,
		      int reloc_type, long dynindx, bfd_vma addend)
{
  Elf_Internal_Rela outrel;
  bfd_vma reloc_offset;

  outrel.r_offset = offset;
  outrel.r_info = ELF32_R_INFO (dynindx, reloc_type);
  outrel.r_addend = addend;

  reloc_offset = sreloc->reloc_count * sizeof (Elf32_External_Rela);
  BFD_ASSERT (reloc_offset < sreloc->size);
  bfd_elf32_swap_reloca_out (output_bfd, &outrel,
			     sreloc->contents + reloc_offset);
  sreloc->reloc_count++;

  return reloc_offset;
}

/* Add an FDPIC read-only fixup.  */

inline static void
sh_elf_add_rofixup (bfd *output_bfd, asection *srofixup, bfd_vma offset)
{
  const size_t FIXUP_ENTRY_SIZE = 4;
  bfd_vma fixup_offset;

  fixup_offset = srofixup->reloc_count++ * FIXUP_ENTRY_SIZE;
  BFD_ASSERT (fixup_offset < srofixup->size);
  bfd_put_32 (output_bfd, offset, srofixup->contents + fixup_offset);
}

/* Return the offset of the generated .got section from the
   _GLOBAL_OFFSET_TABLE_ symbol.  */

static bfd_signed_vma
sh_elf_got_offset (struct elf_sh_link_hash_table *htab)
{
  return (htab->root.sgot->output_offset - htab->root.sgotplt->output_offset
	  - htab->root.hgot->root.u.def.value);
}

/* Find the segment number in which OSEC, and output section, is
   located.  */

static unsigned
sh_elf_osec_to_segment (bfd *output_bfd, asection *osec)
{
  Elf_Internal_Phdr *p = NULL;

  if (output_bfd->xvec->flavour == bfd_target_elf_flavour
      && output_bfd->direction != read_direction)
    p = _bfd_elf_find_segment_containing_section (output_bfd, osec);

  return (p != NULL) ? p - elf_tdata (output_bfd)->phdr : -1;
}

static bool
sh_elf_osec_readonly_p (bfd *output_bfd, asection *osec)
{
  const unsigned INVALID_SEGMENT = (unsigned) -1;
  unsigned seg = sh_elf_osec_to_segment (output_bfd, osec);

  if (seg == INVALID_SEGMENT) {
    return false;
  }

  return !(elf_tdata (output_bfd)->phdr[seg].p_flags & PF_W);
}

/* Generate the initial contents of a local function descriptor, along
   with any relocations or fixups required.  */
static void update_section_and_value(struct elf_link_hash_entry *h,
                                     asection **section,
                                     bfd_vma *value)
{
    *section = h->root.u.def.section;
    *value = h->root.u.def.value;
}

static void compute_local_symbol_values(asection *section,
                                        bfd_vma value,
                                        bfd *output_bfd,
                                        int *dynindx,
                                        bfd_vma *addr,
                                        bfd_vma *seg)
{
    *dynindx = elf_section_data (section->output_section)->dynindx;
    *addr = value + section->output_offset;
    *seg = sh_elf_osec_to_segment (output_bfd, section->output_section);
}

static void compute_external_symbol_values(struct elf_link_hash_entry *h,
                                           int *dynindx,
                                           bfd_vma *addr,
                                           bfd_vma *seg)
{
    BFD_ASSERT (h->dynindx != -1);
    *dynindx = h->dynindx;
    *addr = 0;
    *seg = 0;
}

static bfd_vma calculate_funcdesc_address(struct elf_sh_link_hash_table *htab,
                                          bfd_vma offset)
{
    return offset + htab->sfuncdesc->output_section->vma + htab->sfuncdesc->output_offset;
}

static void add_rofixup_entries(bfd *output_bfd,
                                struct elf_sh_link_hash_table *htab,
                                bfd_vma offset)
{
    bfd_vma base_addr = calculate_funcdesc_address(htab, offset);
    
    sh_elf_add_rofixup (output_bfd, htab->srofixup, base_addr);
    sh_elf_add_rofixup (output_bfd, htab->srofixup, base_addr + 4);
}

static bfd_vma calculate_gp_value(struct elf_sh_link_hash_table *htab)
{
    return htab->root.hgot->root.u.def.value
           + htab->root.hgot->root.u.def.section->output_section->vma
           + htab->root.hgot->root.u.def.section->output_offset;
}

static bool should_add_rofixup(struct elf_link_hash_entry *h)
{
    return h == NULL || h->root.type != bfd_link_hash_undefweak;
}

static void handle_static_relocation(bfd *output_bfd,
                                     struct bfd_link_info *info,
                                     struct elf_link_hash_entry *h,
                                     struct elf_sh_link_hash_table *htab,
                                     bfd_vma offset,
                                     asection *section,
                                     bfd_vma *addr,
                                     bfd_vma *seg)
{
    if (should_add_rofixup(h))
    {
        add_rofixup_entries(output_bfd, htab, offset);
    }
    
    *addr += section->output_section->vma;
    *seg = calculate_gp_value(htab);
}

static void handle_dynamic_relocation(bfd *output_bfd,
                                      struct elf_sh_link_hash_table *htab,
                                      bfd_vma offset,
                                      int dynindx)
{
    sh_elf_add_dyn_reloc (output_bfd, htab->srelfuncdesc,
                         calculate_funcdesc_address(htab, offset),
                         R_SH_FUNCDESC_VALUE, dynindx, 0);
}

static bool
sh_elf_initialize_funcdesc (bfd *output_bfd,
                           struct bfd_link_info *info,
                           struct elf_link_hash_entry *h,
                           bfd_vma offset,
                           asection *section,
                           bfd_vma value)
{
    struct elf_sh_link_hash_table *htab;
    int dynindx;
    bfd_vma addr, seg;
    
    htab = sh_elf_hash_table (info);
    
    if (h != NULL && SYMBOL_CALLS_LOCAL (info, h))
    {
        update_section_and_value(h, &section, &value);
    }
    
    if (h == NULL || SYMBOL_CALLS_LOCAL (info, h))
    {
        compute_local_symbol_values(section, value, output_bfd, &dynindx, &addr, &seg);
    }
    else
    {
        compute_external_symbol_values(h, &dynindx, &addr, &seg);
    }
    
    if (!bfd_link_pic (info) && SYMBOL_CALLS_LOCAL (info, h))
    {
        handle_static_relocation(output_bfd, info, h, htab, offset, section, &addr, &seg);
    }
    else
    {
        handle_dynamic_relocation(output_bfd, htab, offset, dynindx);
    }
    
    bfd_put_32 (output_bfd, addr, htab->sfuncdesc->contents + offset);
    bfd_put_32 (output_bfd, seg, htab->sfuncdesc->contents + offset + 4);
    
    return true;
}

/* Install a 20-bit movi20 field starting at ADDR, which occurs in OUTPUT_BFD.
   VALUE is the field's value.  Return bfd_reloc_ok if successful or an error
   otherwise.  */

static bfd_reloc_status_type
check_section_bounds(bfd *input_bfd, asection *input_section, bfd_vma offset)
{
  if (offset > bfd_get_section_limit(input_bfd, input_section))
    return bfd_reloc_outofrange;
  return bfd_reloc_ok;
}

static bfd_reloc_status_type
check_relocation_overflow(bfd *input_bfd, unsigned long relocation)
{
  return bfd_check_overflow(complain_overflow_signed, 20, 0,
                           bfd_arch_bits_per_address(input_bfd), relocation);
}

static void
write_movi20_instruction(bfd *output_bfd, bfd_byte *addr, unsigned long relocation)
{
  #define MOVI20_HIGH_MASK 0xf0000
  #define MOVI20_HIGH_SHIFT 12
  #define MOVI20_LOW_MASK 0xffff
  
  unsigned long cur_val = bfd_get_16(output_bfd, addr);
  unsigned long high_part = (relocation & MOVI20_HIGH_MASK) >> MOVI20_HIGH_SHIFT;
  unsigned long low_part = relocation & MOVI20_LOW_MASK;
  
  bfd_put_16(output_bfd, cur_val | high_part, addr);
  bfd_put_16(output_bfd, low_part, addr + 2);
}

static bfd_reloc_status_type
install_movi20_field(bfd *output_bfd, unsigned long relocation,
                    bfd *input_bfd, asection *input_section,
                    bfd_byte *contents, bfd_vma offset)
{
  bfd_reloc_status_type status;
  
  status = check_section_bounds(input_bfd, input_section, offset);
  if (status != bfd_reloc_ok)
    return status;
  
  status = check_relocation_overflow(input_bfd, relocation);
  if (status != bfd_reloc_ok)
    return status;
  
  write_movi20_instruction(output_bfd, contents + offset, relocation);
  
  return bfd_reloc_ok;
}

/* Relocate an SH ELF section.  */

static bool is_reloc_type_to_skip(int r_type)
{
  return (r_type >= (int) R_SH_GNU_VTINHERIT && r_type <= (int) R_SH_LABEL) || 
         (r_type == (int) R_SH_NONE);
}

static bool is_invalid_reloc_type(int r_type)
{
  return r_type < 0 || r_type >= R_SH_max ||
         (r_type >= (int) R_SH_FIRST_INVALID_RELOC && r_type <= (int) R_SH_LAST_INVALID_RELOC) ||
         (r_type >= (int) R_SH_FIRST_INVALID_RELOC_2 && r_type <= (int) R_SH_LAST_INVALID_RELOC_2) ||
         (r_type >= (int) R_SH_FIRST_INVALID_RELOC_3 && r_type <= (int) R_SH_LAST_INVALID_RELOC_3) ||
         (r_type >= (int) R_SH_FIRST_INVALID_RELOC_4 && r_type <= (int) R_SH_LAST_INVALID_RELOC_4) ||
         (r_type >= (int) R_SH_FIRST_INVALID_RELOC_5 && r_type <= (int) R_SH_LAST_INVALID_RELOC_5) ||
         (r_type >= (int) R_SH_FIRST_INVALID_RELOC_6 && r_type <= (int) R_SH_LAST_INVALID_RELOC_6);
}

static bool needs_relocation_override(int r_type, struct elf_link_hash_entry *h, 
                                      struct elf_sh_link_hash_table *htab, 
                                      struct bfd_link_info *info, bool dyn)
{
  if (r_type == R_SH_GOTPC || r_type == R_SH_GOTPC_LOW16 || 
      r_type == R_SH_GOTPC_MEDLOW16 || r_type == R_SH_GOTPC_MEDHI16 || 
      r_type == R_SH_GOTPC_HI16)
    return true;
    
  if ((r_type == R_SH_PLT32 || r_type == R_SH_PLT_LOW16 || 
       r_type == R_SH_PLT_MEDLOW16 || r_type == R_SH_PLT_MEDHI16 || 
       r_type == R_SH_PLT_HI16) && h->plt.offset != (bfd_vma) -1)
    return true;
    
  if ((r_type == R_SH_GOT32 || r_type == R_SH_GOT20 || 
       r_type == R_SH_GOTFUNCDESC || r_type == R_SH_GOTFUNCDESC20 || 
       r_type == R_SH_GOTOFFFUNCDESC || r_type == R_SH_GOTOFFFUNCDESC20 || 
       r_type == R_SH_FUNCDESC || r_type == R_SH_GOT_LOW16 || 
       r_type == R_SH_GOT_MEDLOW16 || r_type == R_SH_GOT_MEDHI16 || 
       r_type == R_SH_GOT_HI16) && 
      WILL_CALL_FINISH_DYNAMIC_SYMBOL(dyn, bfd_link_pic(info), h) &&
      (!bfd_link_pic(info) || (!info->symbolic && h->dynindx != -1) || !h->def_regular))
    return true;
    
  return false;
}

static bool needs_dynamic_relocation(int r_type, struct elf_link_hash_entry *h, 
                                     struct bfd_link_info *info, asection *input_section)
{
  if (!bfd_link_pic(info))
    return false;
    
  if ((!info->symbolic && h->dynindx != -1) || !h->def_regular) {
    if ((r_type == R_SH_DIR32 && !h->forced_local) || 
        (r_type == R_SH_REL32 && !SYMBOL_CALLS_LOCAL(info, h))) {
      if ((input_section->flags & SEC_ALLOC) != 0)
        return true;
      if ((input_section->flags & SEC_DEBUGGING) != 0 && h->def_dynamic)
        return true;
    }
  }
  
  return false;
}

static bool process_local_symbol(Elf_Internal_Sym *sym, asection **sec, 
                                 bfd_vma *relocation, asection **local_sections, 
                                 unsigned long r_symndx, bfd *input_bfd, 
                                 struct bfd_link_info *info, 
                                 Elf_Internal_Shdr *symtab_hdr, 
                                 Elf_Internal_Rela *rel, reloc_howto_type *howto, 
                                 bfd_byte *contents, bfd_vma *addend)
{
  *sec = local_sections[r_symndx];
  *relocation = (*sec)->output_section->vma + (*sec)->output_offset + sym->st_value;
  
  if (discarded_section(*sec))
    return true;
    
  if (bfd_link_relocatable(info)) {
    if (ELF_ST_TYPE(sym->st_info) == STT_SECTION) {
      if (!howto->partial_inplace) {
        rel->r_addend += (*sec)->output_offset;
      } else {
        _bfd_relocate_contents(howto, input_bfd, 
                              (*sec)->output_offset + sym->st_value,
                              contents + rel->r_offset);
      }
    }
    return false;
  }
  
  if (!howto->partial_inplace) {
    *relocation = _bfd_elf_rela_local_sym(input_bfd, sym, sec, rel);
    *addend = rel->r_addend;
  } else if (((*sec)->flags & SEC_MERGE) && ELF_ST_TYPE(sym->st_info) == STT_SECTION) {
    asection *msec = *sec;
    *addend = bfd_get_32(input_bfd, contents + rel->r_offset);
    *addend = _bfd_elf_rel_local_sym(input_bfd, sym, &msec, *addend) - *relocation;
    *addend += msec->output_section->vma + msec->output_offset;
    bfd_put_32(input_bfd, *addend, contents + rel->r_offset);
    *addend = 0;
  }
  
  return true;
}

static void process_global_symbol(struct elf_link_hash_entry **h, bfd_vma *relocation,
                                  struct elf_link_hash_entry **sym_hashes, 
                                  unsigned long r_symndx, 
                                  Elf_Internal_Shdr *symtab_hdr, 
                                  asection **sec, struct elf_sh_link_hash_table *htab,
                                  int r_type, struct bfd_link_info *info,
                                  bfd *output_bfd, bfd *input_bfd, 
                                  asection *input_section, Elf_Internal_Rela *rel,
                                  reloc_howto_type *howto)
{
  *h = sym_hashes[r_symndx - symtab_hdr->sh_info];
  
  while ((*h)->root.type == bfd_link_hash_indirect || 
         (*h)->root.type == bfd_link_hash_warning)
    *h = (struct elf_link_hash_entry *) (*h)->root.u.i.link;
    
  if ((*h)->root.type == bfd_link_hash_defined || 
      (*h)->root.type == bfd_link_hash_defweak) {
    bool dyn = htab ? htab->root.dynamic_sections_created : false;
    *sec = (*h)->root.u.def.section;
    
    if (!needs_relocation_override(r_type, *h, htab, info, dyn) &&
        !needs_dynamic_relocation(r_type, *h, info, input_section) &&
        (*sec)->output_section != NULL &&
        !((*sec)->output_section == NULL && 
          ((input_section->flags & SEC_DEBUGGING) != 0 && (*h)->def_dynamic)) &&
        !((*sec)->output_section == NULL && 
          (sh_elf_hash_entry(*h)->got_type == GOT_TLS_IE || 
           sh_elf_hash_entry(*h)->got_type == GOT_TLS_GD))) {
      *relocation = (*h)->root.u.def.value + 
                   (*sec)->output_section->vma + 
                   (*sec)->output_offset;
    } else if (!bfd_link_relocatable(info) && (*sec)->output_section == NULL &&
               _bfd_elf_section_offset(output_bfd, info, input_section, 
                                      rel->r_offset) != (bfd_vma)-1) {
      _bfd_error_handler(_("%pB(%pA+%#" PRIx64 "): unresolvable %s relocation against symbol `%s'"),
                        input_bfd, input_section, (uint64_t) rel->r_offset,
                        howto->name, (*h)->root.root.string);
    }
  }
}

static bool check_alignment(bfd *input_bfd, asection *input_section, 
                           Elf_Internal_Rela *rel, bfd_vma relocation, 
                           reloc_howto_type *howto, int alignment_mask)
{
  if (relocation & alignment_mask) {
    _bfd_error_handler(_("%pB: %#" PRIx64 ": fatal: unaligned %s relocation %#" PRIx64),
                      input_section->owner, (uint64_t) rel->r_offset,
                      howto->name, (uint64_t) relocation);
    bfd_set_error(bfd_error_bad_value);
    return false;
  }
  return true;
}

static bool check_range(bfd *input_bfd, asection *input_section, 
                       Elf_Internal_Rela *rel, bfd_vma relocation, 
                       const char *reloc_name, int min_val, int max_val)
{
  if ((signed int)relocation < min_val || (signed int)relocation > max_val) {
    _bfd_error_handler(_("%pB: %#" PRIx64 ": fatal: %s relocation %" PRId64 " not in range -32..32"),
                      input_section->owner, (uint64_t) rel->r_offset,
                      reloc_name, (int64_t) relocation);
    bfd_set_error(bfd_error_bad_value);
    return false;
  }
  return true;
}

static bool emit_dynamic_relocation(bfd *output_bfd, asection *sreloc, 
                                   asection *input_section, 
                                   Elf_Internal_Rela *rel, 
                                   struct elf_link_hash_entry *h, 
                                   bfd_vma relocation, bfd_vma addend, 
                                   struct bfd_link_info *info, bool fdpic_p,
                                   reloc_howto_type *howto, asection *sec,
                                   int r_type)
{
  Elf_Internal_Rela outrel;
  bfd_byte *loc;
  bool skip = false, relocate = false;
  
  outrel.r_offset = _bfd_elf_section_offset(output_bfd, info, input_section, 
                                           rel->r_offset);
  if (outrel.r_offset == (bfd_vma) -1)
    skip = true;
  else if (outrel.r_offset == (bfd_vma) -2) {
    skip = true;
    relocate = true;
  }
  
  outrel.r_offset += input_section->output_section->vma + input_section->output_offset;
  
  if (skip)
    memset(&outrel, 0, sizeof outrel);
  else if (r_type == R_SH_REL32) {
    BFD_ASSERT(h != NULL && h->dynindx != -1);
    outrel.r_info = ELF32_R_INFO(h->dynindx, R_SH_REL32);
    outrel.r_addend = howto->partial_inplace ? 
                     bfd_get_32(output_bfd, ((bfd_byte*)NULL) + rel->r_offset) : addend;
  } else if (fdpic_p && (h == NULL || ((info->symbolic || h->dynindx == -1) && h->def_regular))) {
    int dynindx = elf_section_data(sec->output_section)->dynindx;
    outrel.r_info = ELF32_R_INFO(dynindx, R_SH_DIR32);
    outrel.r_addend = relocation + (howto->partial_inplace ? 
                                   bfd_get_32(output_bfd, ((bfd_byte*)NULL) + rel->r_offset) : addend);
    outrel.r_addend -= sec->output_section->vma;
  } else {
    if (h == NULL || ((info->symbolic || h->dynindx == -1) && h->def_regular)) {
      relocate = howto->partial_inplace;
      outrel.r_info = ELF32_R_INFO(0, R_SH_RELATIVE);
    } else {
      BFD_ASSERT(h->dynindx != -1);
      outrel.r_info = ELF32_R_INFO(h->dynindx, R_SH_DIR32);
    }
    outrel.r_addend = relocation + (howto->partial_inplace ? 
                                   bfd_get_32(output_bfd, ((bfd_byte*)NULL) + rel->r_offset) : addend);
  }
  
  loc = sreloc->contents + sreloc->reloc_count++ * sizeof(Elf32_External_Rela);
  bfd_elf32_swap_reloca_out(output_bfd, &outrel, loc);
  
  return !relocate;
}

static bfd_reloc_status_type process_got_relocation(bfd *output_bfd, 
                                                   struct bfd_link_info *info,
                                                   struct elf_link_hash_entry *h,
                                                   bfd_vma *local_got_offsets,
                                                   unsigned long r_symndx,
                                                   struct elf_sh_link_hash_table *htab,
                                                   asection *sgot, asection *srelgot,
                                                   bfd_vma relocation, bfd_vma addend,
                                                   bfd *input_bfd, asection *input_section,
                                                   bfd_byte *contents, Elf_Internal_Rela *rel,
                                                   asection *sec, bool fdpic_p, int r_type)
{
  bfd_vma off;
  
  if (h != NULL) {
    off = h->got.offset;
    BFD_ASSERT(off != (bfd_vma) -1);
    
    bool dyn = htab->root.dynamic_sections_created;
    if (!WILL_CALL_FINISH_DYNAMIC_SYMBOL(dyn, bfd_link_pic(info), h) ||
        (bfd_link_pic(info) && SYMBOL_REFERENCES_LOCAL(info, h)) ||
        ((ELF_ST_VISIBILITY(h->other) || UNDEFWEAK_NO_DYNAMIC_RELOC(info, h)) && 
         h->root.type == bfd_link_hash_undefweak)) {
      if ((off & 1) == 0) {
        bfd_put_32(output_bfd, relocation, sgot->contents + off);
        h->got.offset |= 1;
        
        if (fdpic_p && !bfd_link_pic(info) && 
            sh_elf_hash_entry(h)->got_type == GOT_NORMAL &&
            (ELF_ST_VISIBILITY(h->other) == STV_DEFAULT || 
             h->root.type != bfd_link_hash_undefweak))
          sh_elf_add_rofixup(output_bfd, htab->srofixup,
                            sgot->output_section->vma + sgot->output_offset + off);
      } else {
        off &= ~1;
      }
    }
    relocation = sh_elf_got_offset(htab) + off;
  } else {
    BFD_ASSERT(local_got_offsets != NULL && local_got_offsets[r_symndx] != (bfd_vma) -1);
    off = local_got_offsets[r_symndx];
    
    if ((off & 1) == 0) {
      bfd_put_32(output_bfd, relocation, sgot->contents + off);
      
      if (bfd_link_pic(info)) {
        Elf_Internal_Rela outrel;
        bfd_byte *loc;
        
        outrel.r_offset = sgot->output_section->vma + sgot->output_offset + off;
        if (fdpic_p) {
          int dynindx = elf_section_data(sec->output_section)->dynindx;
          outrel.r_info = ELF32_R_INFO(dynindx, R_SH_DIR32);
          outrel.r_addend = relocation - sec->output_section->vma;
        } else {
          outrel.r_info = ELF32_R_INFO(0, R_SH_RELATIVE);
          outrel.r_addend = relocation;
        }
        loc = srelgot->contents + srelgot->reloc_count++ * sizeof(Elf32_External_Rela);
        bfd_elf32_swap_reloca_out(output_bfd, &outrel, loc);
      } else if (fdpic_p && sh_elf_local_got_type(input_bfd)[r_symndx] == GOT_NORMAL) {
        sh_elf_add_rofixup(output_bfd, htab->srofixup,
                          sgot->output_section->vma + sgot->output_offset + off);
      }
      
      local_got_offsets[r_symndx] |= 1;
    } else {
      off &= ~1;
    }
    
    relocation = sh_elf_got_offset(htab) + off;
  }
  
#ifdef GOT_BIAS
  relocation -= GOT_BIAS;
#endif
  
  if (r_type == R_SH_GOT20)
    return install_movi20_field(output_bfd, relocation + addend, input_bfd, 
                               input_section, contents, rel->r_offset);
  
  return _bfd_final_link_relocate(get_howto_table(output_bfd) + r_type, 
                                  input_bfd, input_section, contents, 
                                  rel->r_offset, relocation, addend);
}

static int sh_elf_relocate_section(bfd *output_bfd, struct bfd_link_info *info,
                                   bfd *input_bfd, asection *input_section,
                                   bfd_byte *contents, Elf_Internal_Rela *relocs,
                                   Elf_Internal_Sym *local_syms,
                                   asection **local_sections)
{
  struct elf_sh_link_hash_table *htab;
  Elf_Internal_Shdr *symtab_hdr;
  struct elf_link_hash_entry **sym_hashes;
  Elf_Internal_Rela *rel, *relend;
  bfd_vma *local_got_offsets;
  asection *sgot = NULL;
  asection *sgotplt = NULL;
  asection *splt = NULL;
  asection *sreloc = NULL;
  asection *srelgot = NULL;
  bool is_vxworks_tls;
  unsigned isec_segment, got_segment, plt_segment, check_segment[2];
  bool fdpic_p = false;
  
  if (!is_sh_elf(input_bfd)) {
    bfd_set_error(bfd_error_wrong_format);
    return false;
  }
  
  htab = sh_elf_hash_table(info);
  if (htab != NULL) {
    sgot = htab->root.sgot;
    sgotplt = htab->root.sgotplt;
    srelgot = htab->root.srelgot;
    splt = htab->root.splt;
    fdpic_p = htab->fdpic_p;
  }
  
  symtab_hdr = &elf_symtab_hdr(input_bfd);
  sym_hashes = elf_sym_hashes(input_bfd);
  local_got_offsets = elf_local_got_offsets(input_bfd);
  
  isec_segment = sh_elf_osec_to_segment(output_bfd, input_section->output_section);
  got_segment = (fdpic_p && sgot) ? 
                sh_elf_osec_to_segment(output_bfd, sgot->output_section) : -1;
  plt_segment = (fdpic_p && splt) ? 
                sh_elf_osec_to_segment(output_bfd, splt->output_section) : -1;
  
  is_vxworks_tls = (htab && htab->root.target_os == is_vxworks && 
                    bfd_link_pic(info) && 
                    !strcmp(input_section->output_section->name, ".tls_vars"));
  
  relend = relocs + input_section->reloc_count;
  for (rel = relocs; rel < relend; rel++) {
    int r_type;
    reloc_howto_type *howto;
    unsigned long r_symndx;
    Elf_Internal_Sym *sym;
    asection *sec;
    struct elf_link_hash_entry *h;
    bfd_vma relocation;
    bfd_vma addend = 0;
    bfd_reloc_status_type r;
    bfd_vma off;
    enum got_type got_type;
    const char *symname = NULL;
    bool resolved_to_zero;
    
    r_symndx = ELF32_R_SYM(rel->r_info);
    r_type = ELF32_R_TYPE(rel->r_info);
    
    if (is_reloc_type_to_skip(r_type))
      continue;
      
    if (is_invalid_reloc_type(r_type)) {
      bfd_set_error(bfd_error_bad_value);
      return false;
    }
    
    howto = get_howto_table(output_bfd) + r_type;
    
    if (!howto->partial_inplace)
      addend = rel->r_addend;
      
    resolved_to_zero = false;
    h = NULL;
    sym = NULL;
    sec = NULL;
    check_segment[0] = -1;
    check_segment[1] = -1;
    
    if (r_symndx < symtab_hdr->sh_info) {
      sym = local_syms + r_symndx;
      symname = bfd_elf_string_from_elf_section(input_bfd, symtab_hdr->sh_link, sym->st_name);
      if (symname == NULL || *symname == '\0')
        symname = bfd_section_name(local_sections[r_symndx]);
        
      if (!process_local_symbol(sym, &sec, &relocation, local_sections, r_symndx,
                               input_bfd, info, symtab_hdr, rel, howto, contents, &addend))
        continue;
    } else {
      relocation = 0;
      symname = sym_hashes[r_symndx - symtab_hdr->sh_info]->root.root.string;
      process_global_symbol(&h, &relocation, sym_hashes, r_symndx, symtab_hdr, 
                           &sec, htab, r_type, info, output_bfd, input_bfd, 
                           input_section, rel, howto);
                           
      if (h->root.type == bfd_link_hash_undefweak)
        resolved_to_zero = UNDEFWEAK_NO_DYNAMIC_RELOC(info, h);
      else if (info->unresolved_syms_in_objects == RM_IGNORE && 
               ELF_ST_VISIBILITY(h->other) == STV_DEFAULT)
        ;
      else if (!bfd_link_relocatable(info))
        info->callbacks->undefined_symbol(info, h->root.root.string, input_bfd, 
                                         input_section, rel->r_offset,
                                         (info->unresolved_syms_in_objects == RM_DIAGNOSE && 
                                          !info->warn_unresolved_syms) || 
                                         ELF_ST_VISIBILITY(h->other));
    }
    
    if (sec != NULL && discarded_section(sec))
      RELOC_AGAINST_DISCARDED_SECTION(info, input_bfd, input_section, rel, 1, 
                                     relend, R_SH_NONE, howto, 0, contents);
                                     
    if (bfd_link_relocatable(info))
      continue;
      
    check_segment[0] = isec_segment;
    check_segment[1] = (sec != NULL) ? 
                      sh_elf_osec_to_segment(output_bfd, sec->output_section) : -1;
                      
    switch (r_type) {
    case R_SH_IND12W:
    case R_SH_DIR16:
    case R_SH_DIR8:
    case R_SH_DIR8U:
    case R_SH_DIR8S:
    case R_SH_DIR4U:
      r = _bfd_final_link_relocate(howto, input_bfd, input_section, contents,
                                   rel->r_offset, relocation, addend);
      break;
      
    case R_SH_DIR8WPN:
    case R_SH_DIR8WPZ:
    case R_SH_DIR8WPL:
      if (input_section->output_section->vma + input_section->output_offset != relocation) {
        int disp = relocation - input_section->output_section->vma - 
                  input_section->output_offset - rel->r_offset;
        int mask = (r_type == R_SH_DIR8WPL) ? 3 : 1;
        if (disp & mask) {
          _bfd_error_handler(_("%pB: %#" PRIx64 ": fatal: unaligned branch target for relax-support relocation"),
                           input_section->owner, (uint64_t) rel->r_offset);
          bfd_set_error(bfd_error_bad_value);
          return false;
        }
        relocation -= 4;
        r = _bfd_final_link_relocate(howto, input_bfd, input_section, contents,
                                     rel->r_offset, relocation, addend);
      } else {
        r = bfd_reloc_ok;
      }
      break;
      
    case R_SH_DIR8UL:
    case R_SH_DIR4UL:
      if (!check_alignment(input_bfd, input_section, rel, relocation, howto, 3))
        return false;
      r = _bfd_final_link_relocate(howto, input_bfd, input_section, contents,
                                   rel->r_offset, relocation, addend);
      break;
      
    case R_SH_DIR8UW:
    case R_SH_DIR8SW:
    case R_SH_DIR4UW:
      if (!check_alignment(input_bfd, input_section, rel, relocation, howto, 1))
        return false;
      r = _bfd_final_link_relocate(howto, input_bfd, input_section, contents,
                                   rel->r_offset, relocation, addend);
      break;
      
    case R_SH_PSHA:
      if (!check_range(input_bfd, input_section, rel, relocation, "R_SH_PSHA", -32, 32))
        return false;
      r = _bfd_final_link_relocate(howto, input_bfd, input_section, contents,
                                   rel->r_offset, relocation, addend);
      break;
      
    case R_SH_PSHL:
      if (!check_range(input_bfd, input_section, rel, relocation, "R_SH_PSHL", -16, 16))
        return false;
      r = _bfd_final_link_relocate(howto, input_bfd, input_section, contents,
                                   rel->r_offset, relocation, addend);
      break;
      
    case R_SH_DIR32:
    case R_SH_REL32:
      if (bfd_link_pic(info) && (h == NULL || (ELF_ST_VISIBILITY(h->other) == STV_DEFAULT && 
          !resolved_to_zero) || h->root.type != bfd_link_hash_undefweak) && 
          r_symndx != STN_UNDEF && (input_section->flags & SEC_ALLOC) != 0 && 
          !is_vxworks_tls && (r_type == R_SH_DIR32 || !SYMBOL_CALLS_LOCAL(info, h))) {
        if (sreloc == NULL) {
          sreloc = _bfd_elf_get_dynamic_reloc_section(input_bfd, input_section, true);
          if (sreloc == NULL)
            return false;
        }
        if (!emit_dynamic_relocation(output_bfd, sreloc, input_section, rel, h, 
                                    relocation, addend, info, fdpic_p, howto, sec, r_type))
          continue;
        check_segment[0] = check_segment[1] = -1;
      } else if

/* This is a version of bfd_generic_get_relocated_section_contents
   which uses sh_elf_relocate_section.  */

static bfd_byte *allocate_and_copy_section_data(asection *input_section, bfd_byte *data)
{
  if (data == NULL)
    {
      data = bfd_malloc(input_section->size);
      if (data == NULL)
        return NULL;
    }
  memcpy(data, elf_section_data(input_section)->this_hdr.contents,
         (size_t)input_section->size);
  return data;
}

static Elf_Internal_Sym *get_symbol_buffer(bfd *input_bfd, Elf_Internal_Shdr *symtab_hdr)
{
  if (symtab_hdr->sh_info == 0)
    return NULL;
    
  Elf_Internal_Sym *isymbuf = (Elf_Internal_Sym *)symtab_hdr->contents;
  if (isymbuf == NULL)
    {
      isymbuf = bfd_elf_get_elf_syms(input_bfd, symtab_hdr,
                                      symtab_hdr->sh_info, 0,
                                      NULL, NULL, NULL);
    }
  return isymbuf;
}

static asection **allocate_section_array(Elf_Internal_Shdr *symtab_hdr)
{
  bfd_size_type amt = symtab_hdr->sh_info;
  amt *= sizeof(asection *);
  if (amt == 0)
    return NULL;
  return (asection **)bfd_malloc(amt);
}

static asection *get_section_from_symbol(bfd *input_bfd, Elf_Internal_Sym *isym)
{
  if (isym->st_shndx == SHN_UNDEF)
    return bfd_und_section_ptr;
  if (isym->st_shndx == SHN_ABS)
    return bfd_abs_section_ptr;
  if (isym->st_shndx == SHN_COMMON)
    return bfd_com_section_ptr;
  return bfd_section_from_elf_index(input_bfd, isym->st_shndx);
}

static void populate_sections_array(bfd *input_bfd, Elf_Internal_Sym *isymbuf,
                                    asection **sections, Elf_Internal_Shdr *symtab_hdr)
{
  Elf_Internal_Sym *isymend = isymbuf + symtab_hdr->sh_info;
  asection **secpp = sections;
  
  for (Elf_Internal_Sym *isym = isymbuf; isym < isymend; ++isym, ++secpp)
    {
      *secpp = get_section_from_symbol(input_bfd, isym);
    }
}

static void cleanup_resources(asection **sections, Elf_Internal_Sym *isymbuf,
                              Elf_Internal_Rela *internal_relocs,
                              Elf_Internal_Shdr *symtab_hdr, asection *input_section)
{
  free(sections);
  if (symtab_hdr->contents != (unsigned char *)isymbuf)
    free(isymbuf);
  if (elf_section_data(input_section)->relocs != internal_relocs)
    free(internal_relocs);
}

static bool has_relocations(asection *input_section)
{
  return (input_section->flags & SEC_RELOC) != 0 && input_section->reloc_count > 0;
}

static bfd_byte *process_relocations(bfd *output_bfd, struct bfd_link_info *link_info,
                                     bfd *input_bfd, asection *input_section,
                                     bfd_byte *data, Elf_Internal_Shdr *symtab_hdr,
                                     bfd_byte *orig_data)
{
  Elf_Internal_Rela *internal_relocs = NULL;
  Elf_Internal_Sym *isymbuf = NULL;
  asection **sections = NULL;

  internal_relocs = _bfd_elf_link_read_relocs(input_bfd, input_section, NULL,
                                              (Elf_Internal_Rela *)NULL, false);
  if (internal_relocs == NULL)
    goto error_return;

  isymbuf = get_symbol_buffer(input_bfd, symtab_hdr);
  if (symtab_hdr->sh_info != 0 && isymbuf == NULL)
    goto error_return;

  sections = allocate_section_array(symtab_hdr);
  if (sections == NULL && symtab_hdr->sh_info != 0)
    goto error_return;

  if (isymbuf != NULL && sections != NULL)
    populate_sections_array(input_bfd, isymbuf, sections, symtab_hdr);

  if (!sh_elf_relocate_section(output_bfd, link_info, input_bfd,
                               input_section, data, internal_relocs,
                               isymbuf, sections))
    goto error_return;

  cleanup_resources(sections, isymbuf, internal_relocs, symtab_hdr, input_section);
  return data;

error_return:
  cleanup_resources(sections, isymbuf, internal_relocs, symtab_hdr, input_section);
  if (orig_data == NULL)
    free(data);
  return NULL;
}

static bfd_byte *
sh_elf_get_relocated_section_contents(bfd *output_bfd,
                                      struct bfd_link_info *link_info,
                                      struct bfd_link_order *link_order,
                                      bfd_byte *data,
                                      bool relocatable,
                                      asymbol **symbols)
{
  asection *input_section = link_order->u.indirect.section;
  bfd *input_bfd = input_section->owner;

  if (relocatable || elf_section_data(input_section)->this_hdr.contents == NULL)
    return bfd_generic_get_relocated_section_contents(output_bfd, link_info,
                                                      link_order, data,
                                                      relocatable, symbols);

  Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr(input_bfd);
  bfd_byte *orig_data = data;
  
  data = allocate_and_copy_section_data(input_section, data);
  if (data == NULL)
    return NULL;

  if (has_relocations(input_section))
    return process_relocations(output_bfd, link_info, input_bfd, input_section,
                               data, symtab_hdr, orig_data);

  return data;
}

/* Return the base VMA address which should be subtracted from real addresses
   when resolving @dtpoff relocation.
   This is PT_TLS segment p_vaddr.  */

static bfd_vma
dtpoff_base (struct bfd_link_info *info)
{
  struct elf_link_hash_table *hash_table = elf_hash_table (info);
  
  if (hash_table->tls_sec == NULL)
    return 0;
    
  return hash_table->tls_sec->vma;
}

/* Return the relocation value for R_SH_TLS_TPOFF32..  */

static bfd_vma
tpoff (struct bfd_link_info *info, bfd_vma address)
{
  #define TCBHEAD_SIZE 8
  
  struct elf_link_hash_table *htab = elf_hash_table (info);
  
  if (htab->tls_sec == NULL)
    return 0;
    
  bfd_vma tls_offset = address - htab->tls_sec->vma;
  bfd_vma alignment_offset = align_power ((bfd_vma) TCBHEAD_SIZE, 
                                           htab->tls_sec->alignment_power);
  
  return tls_offset + alignment_offset;
}

static asection *
sh_elf_gc_mark_hook (asection *sec,
		     struct bfd_link_info *info,
		     Elf_Internal_Rela *rel,
		     struct elf_link_hash_entry *h,
		     Elf_Internal_Sym *sym)
{
  if (h != NULL)
    {
      unsigned int r_type = ELF32_R_TYPE (rel->r_info);
      if (r_type == R_SH_GNU_VTINHERIT || r_type == R_SH_GNU_VTENTRY)
	return NULL;
    }

  return _bfd_elf_gc_mark_hook (sec, info, rel, h, sym);
}

/* Copy the extra info we tack onto an elf_link_hash_entry.  */

static void
transfer_refcounts(struct elf_sh_link_hash_entry *edir,
                   struct elf_sh_link_hash_entry *eind)
{
  edir->gotplt_refcount = eind->gotplt_refcount;
  eind->gotplt_refcount = 0;
  edir->funcdesc.refcount += eind->funcdesc.refcount;
  eind->funcdesc.refcount = 0;
  edir->abs_funcdesc_refcount += eind->abs_funcdesc_refcount;
  eind->abs_funcdesc_refcount = 0;
}

static void
transfer_got_type(struct elf_sh_link_hash_entry *edir,
                  struct elf_sh_link_hash_entry *eind,
                  struct elf_link_hash_entry *dir,
                  struct elf_link_hash_entry *ind)
{
  if (ind->root.type == bfd_link_hash_indirect && dir->got.refcount <= 0)
    {
      edir->got_type = eind->got_type;
      eind->got_type = GOT_UNKNOWN;
    }
}

static void
transfer_dynamic_flags(struct elf_link_hash_entry *dir,
                       struct elf_link_hash_entry *ind)
{
  if (dir->versioned != versioned_hidden)
    dir->ref_dynamic |= ind->ref_dynamic;
  dir->ref_regular |= ind->ref_regular;
  dir->ref_regular_nonweak |= ind->ref_regular_nonweak;
  dir->needs_plt |= ind->needs_plt;
}

static void
sh_elf_copy_indirect_symbol (struct bfd_link_info *info,
                              struct elf_link_hash_entry *dir,
                              struct elf_link_hash_entry *ind)
{
  struct elf_sh_link_hash_entry *edir, *eind;

  edir = (struct elf_sh_link_hash_entry *) dir;
  eind = (struct elf_sh_link_hash_entry *) ind;

  transfer_refcounts(edir, eind);
  transfer_got_type(edir, eind, dir, ind);

  if (ind->root.type != bfd_link_hash_indirect && dir->dynamic_adjusted)
    {
      transfer_dynamic_flags(dir, ind);
    }
  else
    {
      _bfd_elf_link_hash_copy_indirect (info, dir, ind);
    }
}

static int get_local_tls_reloc(int r_type)
{
    switch (r_type)
    {
    case R_SH_TLS_GD_32:
    case R_SH_TLS_IE_32:
    case R_SH_TLS_LD_32:
        return R_SH_TLS_LE_32;
    }
    return r_type;
}

static int get_non_local_tls_reloc(int r_type)
{
    switch (r_type)
    {
    case R_SH_TLS_GD_32:
        return R_SH_TLS_IE_32;
    }
    return r_type;
}

static int
sh_elf_optimized_tls_reloc (struct bfd_link_info *info, int r_type,
			    int is_local)
{
    if (bfd_link_pic (info))
        return r_type;

    if (is_local)
        return get_local_tls_reloc(r_type);
    
    return get_non_local_tls_reloc(r_type);
}

/* Look through the relocs for a section during the first phase.
   Since we don't do .gots or .plts, we just need to consider the
   virtual table relocs for gc.  */

static bool
sh_elf_check_relocs (bfd *abfd, struct bfd_link_info *info, asection *sec,
		     const Elf_Internal_Rela *relocs)
{
  Elf_Internal_Shdr *symtab_hdr;
  struct elf_link_hash_entry **sym_hashes;
  struct elf_sh_link_hash_table *htab;
  const Elf_Internal_Rela *rel;
  const Elf_Internal_Rela *rel_end;
  asection *sreloc;

  sreloc = NULL;

  if (bfd_link_relocatable (info))
    return true;

  BFD_ASSERT (is_sh_elf (abfd));

  symtab_hdr = &elf_symtab_hdr (abfd);
  sym_hashes = elf_sym_hashes (abfd);

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  rel_end = relocs + sec->reloc_count;
  for (rel = relocs; rel < rel_end; rel++)
    {
      if (!process_relocation(abfd, info, sec, rel, symtab_hdr, sym_hashes, 
                             htab, &sreloc))
        return false;
    }

  return true;
}

static struct elf_link_hash_entry *
get_hash_entry(const Elf_Internal_Rela *rel, Elf_Internal_Shdr *symtab_hdr,
              struct elf_link_hash_entry **sym_hashes)
{
  unsigned long r_symndx = ELF32_R_SYM (rel->r_info);
  struct elf_link_hash_entry *h;
  
  if (r_symndx < symtab_hdr->sh_info)
    return NULL;
    
  h = sym_hashes[r_symndx - symtab_hdr->sh_info];
  while (h->root.type == bfd_link_hash_indirect
         || h->root.type == bfd_link_hash_warning)
    h = (struct elf_link_hash_entry *) h->root.u.i.link;
    
  return h;
}

static unsigned int
optimize_tls_reloc(struct bfd_link_info *info, unsigned int r_type,
                   struct elf_link_hash_entry *h)
{
  r_type = sh_elf_optimized_tls_reloc (info, r_type, h == NULL);
  
  if (!bfd_link_pic (info)
      && r_type == R_SH_TLS_IE_32
      && h != NULL
      && h->root.type != bfd_link_hash_undefined
      && h->root.type != bfd_link_hash_undefweak
      && (h->dynindx == -1 || h->def_regular))
    r_type = R_SH_TLS_LE_32;
    
  return r_type;
}

static void
handle_fdpic_funcdesc(struct elf_sh_link_hash_table *htab,
                     struct elf_link_hash_entry *h, struct bfd_link_info *info,
                     unsigned int r_type)
{
  if (!htab->fdpic_p)
    return;
    
  switch (r_type)
    {
    case R_SH_GOTOFFFUNCDESC:
    case R_SH_GOTOFFFUNCDESC20:
    case R_SH_FUNCDESC:
    case R_SH_GOTFUNCDESC:
    case R_SH_GOTFUNCDESC20:
      if (h != NULL && h->dynindx == -1)
        {
          switch (ELF_ST_VISIBILITY (h->other))
            {
            case STV_INTERNAL:
            case STV_HIDDEN:
              break;
            default:
              bfd_elf_link_record_dynamic_symbol (info, h);
              break;
            }
        }
      break;
    }
}

static bool
ensure_got_exists(struct elf_sh_link_hash_table *htab, bfd *abfd,
                 struct bfd_link_info *info, unsigned int r_type)
{
  if (htab->root.sgot != NULL)
    return true;
    
  switch (r_type)
    {
    case R_SH_DIR32:
      if (!htab->fdpic_p)
        break;
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
      if (htab->root.dynobj == NULL)
        htab->root.dynobj = abfd;
      if (!create_got_section (htab->root.dynobj, info))
        return false;
      break;
    default:
      break;
    }
  return true;
}

static enum got_type
get_got_type(unsigned int r_type)
{
  switch (r_type)
    {
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

static bfd_signed_vma *
ensure_local_got_refcounts(bfd *abfd, Elf_Internal_Shdr *symtab_hdr)
{
  bfd_signed_vma *local_got_refcounts = elf_local_got_refcounts (abfd);
  
  if (local_got_refcounts == NULL)
    {
      bfd_size_type size;
      
      size = symtab_hdr->sh_info;
      size *= sizeof (bfd_signed_vma);
      size += symtab_hdr->sh_info;
      local_got_refcounts = ((bfd_signed_vma *)
                            bfd_zalloc (abfd, size));
      if (local_got_refcounts == NULL)
        return NULL;
      elf_local_got_refcounts (abfd) = local_got_refcounts;
      sh_elf_local_got_type (abfd)
        = (char *) (local_got_refcounts + symtab_hdr->sh_info);
    }
  return local_got_refcounts;
}

static bool
validate_got_type_combination(enum got_type old_got_type, enum got_type got_type,
                              bfd *abfd, struct elf_link_hash_entry *h)
{
  if (old_got_type == got_type || old_got_type == GOT_UNKNOWN)
    return true;
    
  if (old_got_type == GOT_TLS_GD && got_type == GOT_TLS_IE)
    return true;
    
  if ((old_got_type == GOT_FUNCDESC || got_type == GOT_FUNCDESC)
      && (old_got_type == GOT_NORMAL || got_type == GOT_NORMAL))
    {
      _bfd_error_handler
        (_("%pB: `%s' accessed both as normal and FDPIC symbol"),
         abfd, h->root.root.string);
    }
  else if (old_got_type == GOT_FUNCDESC || got_type == GOT_FUNCDESC)
    {
      _bfd_error_handler
        (_("%pB: `%s' accessed both as FDPIC and thread local symbol"),
         abfd, h->root.root.string);
    }
  else
    {
      _bfd_error_handler
        (_("%pB: `%s' accessed both as normal and thread local symbol"),
         abfd, h->root.root.string);
    }
  return false;
}

static bool
handle_got_relocs(bfd *abfd, struct elf_link_hash_entry *h,
                 unsigned long r_symndx, enum got_type got_type,
                 Elf_Internal_Shdr *symtab_hdr)
{
  enum got_type old_got_type;
  
  if (h != NULL)
    {
      h->got.refcount += 1;
      old_got_type = sh_elf_hash_entry (h)->got_type;
    }
  else
    {
      bfd_signed_vma *local_got_refcounts;
      
      local_got_refcounts = ensure_local_got_refcounts(abfd, symtab_hdr);
      if (local_got_refcounts == NULL)
        return false;
        
      local_got_refcounts[r_symndx] += 1;
      old_got_type = sh_elf_local_got_type (abfd) [r_symndx];
    }
  
  if (old_got_type == GOT_TLS_IE && got_type == GOT_TLS_GD)
    got_type = GOT_TLS_IE;
  else if (!validate_got_type_combination(old_got_type, got_type, abfd, h))
    return false;
    
  if (old_got_type != got_type)
    {
      if (h != NULL)
        sh_elf_hash_entry (h)->got_type = got_type;
      else
        sh_elf_local_got_type (abfd) [r_symndx] = got_type;
    }
    
  return true;
}

static union gotref *
ensure_local_funcdesc(bfd *abfd, Elf_Internal_Shdr *symtab_hdr)
{
  union gotref *local_funcdesc = sh_elf_local_funcdesc (abfd);
  
  if (local_funcdesc == NULL)
    {
      bfd_size_type size = symtab_hdr->sh_info * sizeof (union gotref);
      local_funcdesc = (union gotref *) bfd_zalloc (abfd, size);
      if (local_funcdesc == NULL)
        return NULL;
      sh_elf_local_funcdesc (abfd) = local_funcdesc;
    }
  return local_funcdesc;
}

static bool
handle_funcdesc_relocs(bfd *abfd, struct elf_link_hash_entry *h,
                      const Elf_Internal_Rela *rel, unsigned long r_symndx,
                      unsigned int r_type, struct elf_sh_link_hash_table *htab,
                      struct bfd_link_info *info, Elf_Internal_Shdr *symtab_hdr)
{
  if (rel->r_addend)
    {
      _bfd_error_handler
        (_("%pB: Function descriptor relocation with non-zero addend"), abfd);
      return false;
    }
  
  if (h == NULL)
    {
      union gotref *local_funcdesc = ensure_local_funcdesc(abfd, symtab_hdr);
      if (local_funcdesc == NULL)
        return false;
        
      local_funcdesc[r_symndx].refcount += 1;
      
      if (r_type == R_SH_FUNCDESC)
        {
          if (!bfd_link_pic (info))
            htab->srofixup->size += 4;
          else
            htab->root.srelgot->size += sizeof (Elf32_External_Rela);
        }
    }
  else
    {
      enum got_type old_got_type;
      
      sh_elf_hash_entry (h)->funcdesc.refcount++;
      if (r_type == R_SH_FUNCDESC)
        sh_elf_hash_entry (h)->abs_funcdesc_refcount++;
        
      old_got_type = sh_elf_hash_entry (h)->got_type;
      if (old_got_type != GOT_FUNCDESC && old_got_type != GOT_UNKNOWN)
        {
          if (old_got_type == GOT_NORMAL)
            _bfd_error_handler
              (_("%pB: `%s' accessed both as normal and FDPIC symbol"),
               abfd, h->root.root.string);
          else
            _bfd_error_handler
              (_("%pB: `%s' accessed both as FDPIC and thread local symbol"),
               abfd, h->root.root.string);
        }
    }
  return true;
}

static struct elf_dyn_relocs **
get_dyn_relocs_head(struct elf_link_hash_entry *h, bfd *abfd,
                   unsigned long r_symndx, asection *sec,
                   struct elf_sh_link_hash_table *htab)
{
  if (h != NULL)
    return &h->dyn_relocs;
    
  asection *s;
  void *vpp;
  Elf_Internal_Sym *isym;
  
  isym = bfd_sym_from_r_symndx (&htab->root.sym_cache, abfd, r_symndx);
  if (isym == NULL)
    return NULL;
    
  s = bfd_section_from_elf_index (abfd, isym->st_shndx);
  if (s == NULL)
    s = sec;
    
  vpp = &elf_section_data (s)->local_dynrel;
  return (struct elf_dyn_relocs **) vpp;
}

static bool
allocate_dyn_relocs(bfd *abfd, asection *sec, struct elf_link_hash_entry *h,
                   unsigned long r_symndx, unsigned int r_type,
                   struct elf_sh_link_hash_table *htab, asection **sreloc)
{
  struct elf_dyn_relocs *p;
  struct elf_dyn_relocs **head;
  
  if (htab->root.dynobj == NULL)
    htab->root.dynobj = abfd;
    
  if (*sreloc == NULL)
    {
      *sreloc = _bfd_elf_make_dynamic_reloc_section
        (sec, htab->root.dynobj, 2, abfd, true);
      if (*sreloc == NULL)
        return false;
    }
  
  head = get_dyn_relocs_head(h, abfd, r_symndx, sec, htab);
  if (head == NULL)
    return false;
    
  p = *head;
  if (p == NULL || p->sec != sec)
    {
      size_t amt = sizeof (*p);
      p = bfd_alloc (htab->root.dynobj, amt);
      if (p == NULL)
        return false;
      p->next = *head;
      *head = p;
      p->sec = sec;
      p->count = 0;
      p->pc_count = 0;
    }
  
  p->count += 1;
  if (r_type == R_SH_REL32)
    p->pc_count += 1;
    
  return true;
}

static bool
needs_dyn_reloc(struct bfd_link_info *info, asection *sec,
               struct elf_link_hash_entry *h, unsigned int r_type)
{
  if ((sec->flags & SEC_ALLOC) == 0)
    return false;
    
  if (bfd_link_pic (info))
    {
      if (r_type == R_SH_REL32 && h == NULL)
        return false;
      if (h != NULL && info->symbolic && h->def_regular
          && h->root.type != bfd_link_hash_defweak)
        return false;
      return true;
    }
  
  return h != NULL && (h->root.type == bfd_link_hash_defweak || !h->def_regular);
}

static bool
process_relocation(bfd *abfd, struct bfd_link_info *info, asection *sec,
                  const Elf_Internal_Rela *rel, Elf_Internal_Shdr *symtab_hdr,
                  struct elf_link_hash_entry **sym_hashes,
                  struct elf_sh_link_hash_table *htab, asection **sreloc)
{
  struct elf_link_hash_entry *h;
  unsigned long r_symndx;
  unsigned int r_type;
  enum got_type got_type;
  
  r_symndx = ELF32_R_SYM (rel->r_info);
  r_type = ELF32_R_TYPE (rel->r_info);
  
  h = get_hash_entry(rel, symtab_hdr, sym_hashes);
  r_type = optimize_tls_reloc(info, r_type, h);
  
  handle_fdpic_funcdesc(htab, h, info, r_type);
  
  if (!ensure_got_exists(htab, abfd, info, r_type))
    return false;
    
  switch (r_type)
    {
    case R_SH_GNU_VTINHERIT:
      if (!bfd_elf_gc_record_vtinherit (abfd, sec, h, rel->r_offset))
        return false;
      break;
      
    case R_SH_GNU_VTENTRY:
      if (!bfd_elf_gc_record_vtentry (abfd, sec, h, rel->r_addend))
        return false;
      break;
      
    case R_SH_TLS_IE_32:
      if (bfd_link_pic (info))
        info->flags |= DF_STATIC_TLS;
    case R_SH_TLS_GD_32:
    case R_SH_GOT32:
    case R_SH_GOT20:
    case R_SH_GOTFUNCDESC:
    case R_SH_GOTFUNCDESC20:
      got_type = get_got_type(r_type);
      if (!handle_got_relocs(abfd, h, r_symndx, got_type, symtab_hdr))
        return false;
      break;
      
    case R_SH_TLS_LD_32:
      sh_elf_hash_table(info)->tls_ldm_got.refcount += 1;
      break;
      
    case R_SH_FUNCDESC:
    case R_SH_GOTOFFFUNCDESC:
    case R_SH_GOTOFFFUNCDESC20:
      if (!handle_funcdesc_relocs(abfd, h, rel, r_symndx, r_type, htab, info, symtab_hdr))
        return false;
      break;
      
    case R_SH_GOTPLT32:
      if (h == NULL || h->forced_local || !bfd_link_pic (info)
          || info->symbolic || h->dynindx == -1)
        {
          got_type = get_got_type(r_type);
          if (!handle_got_relocs(abfd, h, r_symndx, got_type, symtab_hdr))
            return false;
        }
      else
        {
          h->needs_plt = 1;
          h->plt.refcount += 1;
          ((struct elf_sh_link_hash_entry *) h)->gotplt_refcount += 1;
        }
      break;
      
    case R_SH_PLT32:
      if (h == NULL)
        break;
      if (h->forced_local)
        break;
      h->needs_plt = 1;
      h->plt.refcount += 1;
      break;
      
    case R_SH_DIR32:
    case R_SH_REL32:
      if (h != NULL && !bfd_link_pic (info))
        {
          h->non_got_ref = 1;
          h->plt.refcount += 1;
        }
        
      if (needs_dyn_reloc(info, sec, h, r_type))
        {
          if (!allocate_dyn_relocs(abfd, sec, h, r_symndx, r_type, htab, sreloc))
            return false;
        }
        
      if (htab->fdpic_p && !bfd_link_pic (info) && r_type == R_SH_DIR32
          && (sec->flags & SEC_ALLOC) != 0)
        htab->srofixup->size += 4;
      break;
      
    case R_SH_TLS_LE_32:
      if (bfd_link_dll (info))
        {
          _bfd_error_handler
            (_("%pB: TLS local exec code cannot be linked into shared objects"),
             abfd);
          return false;
        }
      break;
      
    case R_SH_TLS_LDO_32:
      break;
      
    default:
      break;
    }
    
  return true;
}

#ifndef sh_elf_set_mach_from_flags
static unsigned int sh_ef_bfd_table[] = { EF_SH_BFD_TABLE };

static bool
sh_elf_set_mach_from_flags (bfd *abfd)
{
  flagword flags = elf_elfheader (abfd)->e_flags & EF_SH_MACH_MASK;

  if (flags >= ARRAY_SIZE (sh_ef_bfd_table))
    return false;

  if (sh_ef_bfd_table[flags] == 0)
    return false;

  bfd_default_set_arch_mach (abfd, bfd_arch_sh, sh_ef_bfd_table[flags]);

  return true;
}


/* Reverse table lookup for sh_ef_bfd_table[].
   Given a bfd MACH value from archures.c
   return the equivalent ELF flags from the table.
   Return -1 if no match is found.  */

int
sh_elf_get_flags_from_mach (unsigned long mach)
{
  int i = ARRAY_SIZE (sh_ef_bfd_table) - 1;

  for (; i > 0; i--)
    if (sh_ef_bfd_table[i] == mach)
      return i;

  BFD_FAIL();
  return -1;
}
#endif /* not sh_elf_set_mach_from_flags */

#ifndef sh_elf_copy_private_data
/* Copy backend specific data from one object module to another */

static bool
sh_elf_copy_private_data (bfd * ibfd, bfd * obfd)
{
  if (! is_sh_elf (ibfd) || ! is_sh_elf (obfd))
    return true;

  if (! _bfd_elf_copy_private_bfd_data (ibfd, obfd))
    return false;

  return sh_elf_set_mach_from_flags (obfd);
}
#endif /* not sh_elf_copy_private_data */

#ifndef sh_elf_merge_private_data

/* This function returns the ELF architecture number that
   corresponds to the given arch_sh* flags.  */

int sh_find_elf_flags(unsigned int arch_set)
{
    extern unsigned long sh_get_bfd_mach_from_arch_set(unsigned int);
    unsigned long bfd_mach = sh_get_bfd_mach_from_arch_set(arch_set);
    return sh_elf_get_flags_from_mach(bfd_mach);
}

/* Merge the architecture type of two BFD files, such that the
   resultant architecture supports all the features required
   by the two input BFDs.
   If the input BFDs are multually incompatible - i.e. one uses
   DSP while the other uses FPU - or there is no known architecture
   that fits the requirements then an error is emitted.  */

static bool
sh_merge_bfd_arch (bfd *ibfd, struct bfd_link_info *info)
{
  bfd *obfd = info->output_bfd;
  unsigned int old_arch, new_arch, merged_arch;

  if (! _bfd_generic_verify_endian_match (ibfd, info))
    return false;

  old_arch = sh_get_arch_up_from_bfd_mach (bfd_get_mach (obfd));
  new_arch = sh_get_arch_up_from_bfd_mach (bfd_get_mach (ibfd));

  merged_arch = SH_MERGE_ARCH_SET (old_arch, new_arch);

  if (!SH_VALID_CO_ARCH_SET (merged_arch))
    {
      const char *new_inst_type = SH_ARCH_SET_HAS_DSP (new_arch) ? "dsp" : "floating point";
      const char *old_inst_type = SH_ARCH_SET_HAS_DSP (new_arch) ? "floating point" : "dsp";
      
      _bfd_error_handler
	(_("%pB: uses %s instructions while previous modules "
	   "use %s instructions"),
	 ibfd,
	 new_inst_type,
	 old_inst_type);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  
  if (!SH_VALID_ARCH_SET (merged_arch))
    {
      _bfd_error_handler
	(_("internal error: merge of architecture '%s' with "
	   "architecture '%s' produced unknown architecture"),
	 bfd_printable_name (obfd),
	 bfd_printable_name (ibfd));
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  bfd_default_set_arch_mach (obfd, bfd_arch_sh,
			     sh_get_bfd_mach_from_arch_set (merged_arch));

  return true;
}

/* This routine initialises the elf flags when required and
   calls sh_merge_bfd_arch() to check dsp/fpu compatibility.  */

static bool is_dynamic_or_non_sh_elf(bfd *ibfd, bfd *obfd)
{
    return (ibfd->flags & DYNAMIC) != 0 || !is_sh_elf(ibfd) || !is_sh_elf(obfd);
}

static void initialize_output_elf_flags(bfd *obfd, bfd *ibfd)
{
    elf_flags_init(obfd) = true;
    elf_elfheader(obfd)->e_flags = elf_elfheader(ibfd)->e_flags;
    sh_elf_set_mach_from_flags(obfd);
    if (elf_elfheader(obfd)->e_flags & EF_SH_FDPIC)
        elf_elfheader(obfd)->e_flags &= ~EF_SH_PIC;
}

static bool check_instruction_compatibility(bfd *ibfd, struct bfd_link_info *info)
{
    if (!sh_merge_bfd_arch(ibfd, info))
    {
        _bfd_error_handler(_("%pB: uses instructions which are incompatible "
                           "with instructions used in previous modules"),
                         ibfd);
        bfd_set_error(bfd_error_bad_value);
        return false;
    }
    return true;
}

static void update_machine_flags(bfd *obfd)
{
    elf_elfheader(obfd)->e_flags &= ~EF_SH_MACH_MASK;
    elf_elfheader(obfd)->e_flags |= sh_elf_get_flags_from_mach(bfd_get_mach(obfd));
}

static bool check_fdpic_compatibility(bfd *ibfd, bfd *obfd)
{
    if (fdpic_object_p(ibfd) != fdpic_object_p(obfd))
    {
        _bfd_error_handler(_("%pB: attempt to mix FDPIC and non-FDPIC objects"),
                         ibfd);
        bfd_set_error(bfd_error_bad_value);
        return false;
    }
    return true;
}

static bool
sh_elf_merge_private_data(bfd *ibfd, struct bfd_link_info *info)
{
    bfd *obfd = info->output_bfd;

    if (is_dynamic_or_non_sh_elf(ibfd, obfd))
        return true;

    if (!elf_flags_init(obfd))
        initialize_output_elf_flags(obfd, ibfd);

    if (!check_instruction_compatibility(ibfd, info))
        return false;

    update_machine_flags(obfd);

    if (!check_fdpic_compatibility(ibfd, obfd))
        return false;

    return true;
}
#endif /* not sh_elf_merge_private_data */

/* Override the generic function because we need to store sh_elf_obj_tdata
   as the specific tdata.  We set also the machine architecture from flags
   here.  */

static bool
sh_elf_object_p (bfd *abfd)
{
  if (!sh_elf_set_mach_from_flags (abfd))
    return false;

  bool has_fdpic_flag = (elf_elfheader (abfd)->e_flags & EF_SH_FDPIC) != 0;
  bool is_fdpic = fdpic_object_p (abfd);
  
  return has_fdpic_flag == is_fdpic;
}

/* Finish up dynamic symbol handling.  We set the contents of various
   dynamic sections here.  */

static void handle_plt_entry(bfd *output_bfd, struct bfd_link_info *info,
                             struct elf_link_hash_entry *h,
                             struct elf_sh_link_hash_table *htab,
                             Elf_Internal_Sym *sym);
static void handle_got_entry(bfd *output_bfd, struct bfd_link_info *info,
                             struct elf_link_hash_entry *h,
                             struct elf_sh_link_hash_table *htab);
static void handle_copy_reloc(bfd *output_bfd, struct elf_link_hash_entry *h,
                              struct elf_sh_link_hash_table *htab);
static void fill_plt_entry(bfd *output_bfd, struct bfd_link_info *info,
                           struct elf_link_hash_entry *h,
                           struct elf_sh_link_hash_table *htab,
                           const struct elf_sh_plt_info *plt_info,
                           bfd_vma plt_index, bfd_vma got_offset);
static void create_vxworks_plt_relocs(bfd *output_bfd, struct bfd_link_info *info,
                                      struct elf_link_hash_entry *h,
                                      struct elf_sh_link_hash_table *htab,
                                      bfd_vma plt_index, bfd_vma got_offset,
                                      const struct elf_sh_plt_info *plt_info);
static void create_plt_relocation(bfd *output_bfd, struct elf_link_hash_entry *h,
                                  struct elf_sh_link_hash_table *htab,
                                  bfd_vma plt_index, bfd_vma got_offset);
static bfd_vma calculate_got_offset(struct elf_sh_link_hash_table *htab,
                                    bfd_vma plt_index, asection *sgotplt,
                                    struct bfd_link_info *info);

#define INVALID_OFFSET ((bfd_vma) -1)
#define GOT_ENTRY_SIZE 4
#define GOT_RESERVED_ENTRIES 3
#define FDPIC_GOT_ENTRY_SIZE 8
#define FDPIC_GOT_OFFSET 12
#define PLT_GROUP_SIZE 4096
#define BRA_OPCODE_BASE 0xa000
#define BRA_OFFSET_MASK 0x0fff

static bool
sh_elf_finish_dynamic_symbol (bfd *output_bfd, struct bfd_link_info *info,
                              struct elf_link_hash_entry *h,
                              Elf_Internal_Sym *sym)
{
  struct elf_sh_link_hash_table *htab;

  htab = sh_elf_hash_table (info);

  if (h->plt.offset != INVALID_OFFSET)
    handle_plt_entry(output_bfd, info, h, htab, sym);

  if (h->got.offset != INVALID_OFFSET
      && sh_elf_hash_entry (h)->got_type != GOT_TLS_GD
      && sh_elf_hash_entry (h)->got_type != GOT_TLS_IE
      && sh_elf_hash_entry (h)->got_type != GOT_FUNCDESC)
    handle_got_entry(output_bfd, info, h, htab);

  if (h->needs_copy)
    handle_copy_reloc(output_bfd, h, htab);

  if (h == htab->root.hdynamic
      || (htab->root.target_os != is_vxworks && h == htab->root.hgot))
    sym->st_shndx = SHN_ABS;

  return true;
}

static void handle_plt_entry(bfd *output_bfd, struct bfd_link_info *info,
                             struct elf_link_hash_entry *h,
                             struct elf_sh_link_hash_table *htab,
                             Elf_Internal_Sym *sym)
{
  asection *splt;
  asection *sgotplt;
  asection *srelplt;
  bfd_vma plt_index;
  bfd_vma got_offset;
  const struct elf_sh_plt_info *plt_info;

  BFD_ASSERT (h->dynindx != -1);

  splt = htab->root.splt;
  sgotplt = htab->root.sgotplt;
  srelplt = htab->root.srelplt;
  BFD_ASSERT (splt != NULL && sgotplt != NULL && srelplt != NULL);

  plt_index = get_plt_index (htab->plt_info, h->plt.offset);

  plt_info = htab->plt_info;
  if (plt_info->short_plt != NULL && plt_index <= MAX_SHORT_PLT)
    plt_info = plt_info->short_plt;

  got_offset = calculate_got_offset(htab, plt_index, sgotplt, info);

  fill_plt_entry(output_bfd, info, h, htab, plt_info, plt_index, got_offset);

#ifdef GOT_BIAS
  if (bfd_link_pic (info))
    got_offset += GOT_BIAS;
#endif
  if (htab->fdpic_p)
    got_offset = plt_index * FDPIC_GOT_ENTRY_SIZE;

  if (plt_info->symbol_fields.reloc_offset != MINUS_ONE)
    install_plt_field (output_bfd, false,
                      plt_index * sizeof (Elf32_External_Rela),
                      (splt->contents
                       + h->plt.offset
                       + plt_info->symbol_fields.reloc_offset));

  bfd_put_32 (output_bfd,
              (splt->output_section->vma
               + splt->output_offset
               + h->plt.offset
               + plt_info->symbol_resolve_offset),
              sgotplt->contents + got_offset);
  if (htab->fdpic_p)
    bfd_put_32 (output_bfd,
                sh_elf_osec_to_segment (output_bfd, splt->output_section),
                sgotplt->contents + got_offset + 4);

  create_plt_relocation(output_bfd, h, htab, plt_index, got_offset);

  if (htab->root.target_os == is_vxworks && !bfd_link_pic (info))
    create_vxworks_plt_relocs(output_bfd, info, h, htab, plt_index, got_offset, plt_info);

  if (!h->def_regular)
    sym->st_shndx = SHN_UNDEF;
}

static bfd_vma calculate_got_offset(struct elf_sh_link_hash_table *htab,
                                    bfd_vma plt_index, asection *sgotplt,
                                    struct bfd_link_info *info)
{
  bfd_vma got_offset;
  
  if (htab->fdpic_p)
    got_offset = plt_index * FDPIC_GOT_ENTRY_SIZE + FDPIC_GOT_OFFSET - sgotplt->size;
  else
    got_offset = (plt_index + GOT_RESERVED_ENTRIES) * GOT_ENTRY_SIZE;

#ifdef GOT_BIAS
  if (bfd_link_pic (info))
    got_offset -= GOT_BIAS;
#endif

  return got_offset;
}

static void fill_plt_entry(bfd *output_bfd, struct bfd_link_info *info,
                           struct elf_link_hash_entry *h,
                           struct elf_sh_link_hash_table *htab,
                           const struct elf_sh_plt_info *plt_info,
                           bfd_vma plt_index, bfd_vma got_offset)
{
  asection *splt = htab->root.splt;
  asection *sgotplt = htab->root.sgotplt;

  memcpy (splt->contents + h->plt.offset,
          plt_info->symbol_entry,
          plt_info->symbol_entry_size);

  if (bfd_link_pic (info) || htab->fdpic_p)
    {
      if (plt_info->symbol_fields.got20)
        {
          bfd_reloc_status_type r;
          r = install_movi20_field (output_bfd, got_offset,
                                   splt->owner, splt, splt->contents,
                                   h->plt.offset
                                   + plt_info->symbol_fields.got_entry);
          BFD_ASSERT (r == bfd_reloc_ok);
        }
      else
        install_plt_field (output_bfd, false, got_offset,
                          (splt->contents
                           + h->plt.offset
                           + plt_info->symbol_fields.got_entry));
    }
  else
    {
      BFD_ASSERT (!plt_info->symbol_fields.got20);

      install_plt_field (output_bfd, false,
                        (sgotplt->output_section->vma
                         + sgotplt->output_offset
                         + got_offset),
                        (splt->contents
                         + h->plt.offset
                         + plt_info->symbol_fields.got_entry));
      
      if (htab->root.target_os == is_vxworks)
        {
          unsigned int reachable_plts, plts_per_4k;
          int distance;

          reachable_plts = ((PLT_GROUP_SIZE
                            - plt_info->plt0_entry_size
                            - (plt_info->symbol_fields.plt + 4))
                           / plt_info->symbol_entry_size) + 1;
          plts_per_4k = (PLT_GROUP_SIZE / plt_info->symbol_entry_size);
          
          if (plt_index < reachable_plts)
            distance = -(h->plt.offset + plt_info->symbol_fields.plt);
          else
            distance = -(((plt_index - reachable_plts) % plts_per_4k + 1)
                        * plt_info->symbol_entry_size);

          bfd_put_16 (output_bfd,
                     BRA_OPCODE_BASE | (BRA_OFFSET_MASK & ((distance - 4) / 2)),
                     (splt->contents
                      + h->plt.offset
                      + plt_info->symbol_fields.plt));
        }
      else
        install_plt_field (output_bfd, true,
                          splt->output_section->vma + splt->output_offset,
                          (splt->contents
                           + h->plt.offset
                           + plt_info->symbol_fields.plt));
    }
}

static void create_plt_relocation(bfd *output_bfd, struct elf_link_hash_entry *h,
                                  struct elf_sh_link_hash_table *htab,
                                  bfd_vma plt_index, bfd_vma got_offset)
{
  Elf_Internal_Rela rel;
  bfd_byte *loc;
  asection *sgotplt = htab->root.sgotplt;
  asection *srelplt = htab->root.srelplt;

  rel.r_offset = (sgotplt->output_section->vma
                 + sgotplt->output_offset
                 + got_offset);
  if (htab->fdpic_p)
    rel.r_info = ELF32_R_INFO (h->dynindx, R_SH_FUNCDESC_VALUE);
  else
    rel.r_info = ELF32_R_INFO (h->dynindx, R_SH_JMP_SLOT);
  rel.r_addend = 0;
#ifdef GOT_BIAS
  rel.r_addend = GOT_BIAS;
#endif
  loc = srelplt->contents + plt_index * sizeof (Elf32_External_Rela);
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
}

static void create_vxworks_plt_relocs(bfd *output_bfd, struct bfd_link_info *info,
                                      struct elf_link_hash_entry *h,
                                      struct elf_sh_link_hash_table *htab,
                                      bfd_vma plt_index, bfd_vma got_offset,
                                      const struct elf_sh_plt_info *plt_info)
{
  Elf_Internal_Rela rel;
  bfd_byte *loc;
  asection *splt = htab->root.splt;
  asection *sgotplt = htab->root.sgotplt;

  loc = (htab->srelplt2->contents
         + (plt_index * 2 + 1) * sizeof (Elf32_External_Rela));

  rel.r_offset = (splt->output_section->vma
                 + splt->output_offset
                 + h->plt.offset
                 + plt_info->symbol_fields.got_entry);
  rel.r_info = ELF32_R_INFO (htab->root.hgot->indx, R_SH_DIR32);
  rel.r_addend = got_offset;
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
  loc += sizeof (Elf32_External_Rela);

  rel.r_offset = (sgotplt->output_section->vma
                 + sgotplt->output_offset
                 + got_offset);
  rel.r_info = ELF32_R_INFO (htab->root.hplt->indx, R_SH_DIR32);
  rel.r_addend = 0;
  bfd_elf32_swap_reloc_out (output_bfd, &rel, loc);
}

static void handle_got_entry(bfd *output_bfd, struct bfd_link_info *info,
                             struct elf_link_hash_entry *h,
                             struct elf_sh_link_hash_table *htab)
{
  asection *sgot;
  asection *srelgot;
  Elf_Internal_Rela rel;
  bfd_byte *loc;

  sgot = htab->root.sgot;
  srelgot = htab->root.srelgot;
  BFD_ASSERT (sgot != NULL && srelgot != NULL);

  rel.r_offset = (sgot->output_section->vma
                 + sgot->output_offset
                 + (h->got.offset &~ (bfd_vma) 1));

  if (bfd_link_pic (info)
      && (h->root.type == bfd_link_hash_defined
          || h->root.type == bfd_link_hash_defweak)
      && SYMBOL_REFERENCES_LOCAL (info, h))
    {
      if (htab->fdpic_p)
        {
          asection *sec = h->root.u.def.section;
          int dynindx = elf_section_data (sec->output_section)->dynindx;

          rel.r_info = ELF32_R_INFO (dynindx, R_SH_DIR32);
          rel.r_addend = (h->root.u.def.value
                         + h->root.u.def.section->output_offset);
        }
      else
        {
          rel.r_info = ELF32_R_INFO (0, R_SH_RELATIVE);
          rel.r_addend = (h->root.u.def.value
                         + h->root.u.def.section->output_section->vma
                         + h->root.u.def.section->output_offset);
        }
    }
  else
    {
      bfd_put_32 (output_bfd, (bfd_vma) 0, sgot->contents + h->got.offset);
      rel.r_info = ELF32_R_INFO (h->dynindx, R_SH_GLOB_DAT);
      rel.r_addend = 0;
    }

  loc = srelgot->contents;
  loc += srelgot->reloc_count++ * sizeof (Elf32_External_Rela);
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
}

static void handle_copy_reloc(bfd *output_bfd, struct elf_link_hash_entry *h,
                              struct elf_sh_link_hash_table *htab)
{
  asection *s;
  Elf_Internal_Rela rel;
  bfd_byte *loc;

  BFD_ASSERT (h->dynindx != -1
              && (h->root.type == bfd_link_hash_defined
                  || h->root.type == bfd_link_hash_defweak));

  s = bfd_get_linker_section (htab->root.dynobj, ".rela.bss");
  BFD_ASSERT (s != NULL);

  rel.r_offset = (h->root.u.def.value
                 + h->root.u.def.section->output_section->vma
                 + h->root.u.def.section->output_offset);
  rel.r_info = ELF32_R_INFO (h->dynindx, R_SH_COPY);
  rel.r_addend = 0;
  loc = s->contents + s->reloc_count++ * sizeof (Elf32_External_Rela);
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
}

/* Finish up the dynamic sections.  */

static bool
process_dynamic_entry(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                     Elf32_External_Dyn *dyncon)
{
    Elf_Internal_Dyn dyn;
    asection *s;

    bfd_elf32_swap_dyn_in(htab->root.dynobj, dyncon, &dyn);

    switch (dyn.d_tag)
    {
    default:
        if (htab->root.target_os == is_vxworks
            && elf_vxworks_finish_dynamic_entry(output_bfd, &dyn))
            bfd_elf32_swap_dyn_out(output_bfd, &dyn, dyncon);
        break;

    case DT_PLTGOT:
        BFD_ASSERT(htab->root.hgot != NULL);
        s = htab->root.hgot->root.u.def.section;
        dyn.d_un.d_ptr = htab->root.hgot->root.u.def.value
            + s->output_section->vma + s->output_offset;
        bfd_elf32_swap_dyn_out(output_bfd, &dyn, dyncon);
        break;

    case DT_JMPREL:
        s = htab->root.srelplt;
        dyn.d_un.d_ptr = s->output_section->vma + s->output_offset;
        bfd_elf32_swap_dyn_out(output_bfd, &dyn, dyncon);
        break;

    case DT_PLTRELSZ:
        s = htab->root.srelplt;
        dyn.d_un.d_val = s->size;
        bfd_elf32_swap_dyn_out(output_bfd, &dyn, dyncon);
        break;
    }

    return true;
}

static void
fill_plt0_entry(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
               asection *splt, asection *sgotplt)
{
    unsigned int i;

    memcpy(splt->contents,
           htab->plt_info->plt0_entry,
           htab->plt_info->plt0_entry_size);

    for (i = 0; i < ARRAY_SIZE(htab->plt_info->plt0_got_fields); i++)
    {
        if (htab->plt_info->plt0_got_fields[i] != MINUS_ONE)
        {
            install_plt_field(output_bfd, false,
                            (sgotplt->output_section->vma
                             + sgotplt->output_offset
                             + (i * 4)),
                            (splt->contents
                             + htab->plt_info->plt0_got_fields[i]));
        }
    }
}

static void
create_first_plt_relocation(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                           asection *splt)
{
    Elf_Internal_Rela rel;
    bfd_byte *loc;

    loc = htab->srelplt2->contents;
    rel.r_offset = (splt->output_section->vma
                   + splt->output_offset
                   + htab->plt_info->plt0_got_fields[2]);
    rel.r_info = ELF32_R_INFO(htab->root.hgot->indx, R_SH_DIR32);
    rel.r_addend = 8;
    bfd_elf32_swap_reloca_out(output_bfd, &rel, loc);
}

static void
fix_plt_unloaded_relocation(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                           bfd_byte *loc)
{
    Elf_Internal_Rela rel;

    bfd_elf32_swap_reloc_in(output_bfd, loc, &rel);
    rel.r_info = ELF32_R_INFO(htab->root.hgot->indx, R_SH_DIR32);
    bfd_elf32_swap_reloc_out(output_bfd, &rel, loc);
    loc += sizeof(Elf32_External_Rela);

    bfd_elf32_swap_reloc_in(output_bfd, loc, &rel);
    rel.r_info = ELF32_R_INFO(htab->root.hplt->indx, R_SH_DIR32);
    bfd_elf32_swap_reloc_out(output_bfd, &rel, loc);
}

static void
finalize_vxworks_plt(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                     asection *splt)
{
    bfd_byte *loc;

    create_first_plt_relocation(output_bfd, htab, splt);
    
    loc = htab->srelplt2->contents + sizeof(Elf32_External_Rela);
    while (loc < htab->srelplt2->contents + htab->srelplt2->size)
    {
        fix_plt_unloaded_relocation(output_bfd, htab, loc);
        loc += 2 * sizeof(Elf32_External_Rela);
    }
}

static void
process_dynamic_sections(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                        asection *sgotplt, asection *sdyn)
{
    Elf32_External_Dyn *dyncon, *dynconend;
    asection *splt;

    BFD_ASSERT(sgotplt != NULL && sdyn != NULL);

    dyncon = (Elf32_External_Dyn *) sdyn->contents;
    dynconend = (Elf32_External_Dyn *) (sdyn->contents + sdyn->size);
    
    for (; dyncon < dynconend; dyncon++)
        process_dynamic_entry(output_bfd, htab, dyncon);

    splt = htab->root.splt;
    if (splt && splt->size > 0 && htab->plt_info->plt0_entry)
    {
        fill_plt0_entry(output_bfd, htab, splt, sgotplt);

        if (htab->root.target_os == is_vxworks)
            finalize_vxworks_plt(output_bfd, htab, splt);

        elf_section_data(splt->output_section)->this_hdr.sh_entsize = 4;
    }
}

static void
fill_got_entries(bfd *output_bfd, asection *sgotplt, asection *sdyn)
{
    if (sdyn == NULL)
        bfd_put_32(output_bfd, (bfd_vma) 0, sgotplt->contents);
    else
        bfd_put_32(output_bfd,
                  sdyn->output_section->vma + sdyn->output_offset,
                  sgotplt->contents);
    
    bfd_put_32(output_bfd, (bfd_vma) 0, sgotplt->contents + 4);
    bfd_put_32(output_bfd, (bfd_vma) 0, sgotplt->contents + 8);
}

static void
finalize_fdpic_got(bfd *output_bfd, struct elf_sh_link_hash_table *htab)
{
    struct elf_link_hash_entry *hgot = htab->root.hgot;
    bfd_vma got_value = hgot->root.u.def.value
        + hgot->root.u.def.section->output_section->vma
        + hgot->root.u.def.section->output_offset;

    sh_elf_add_rofixup(output_bfd, htab->srofixup, got_value);
    BFD_ASSERT(htab->srofixup->reloc_count * 4 == htab->srofixup->size);
}

static bool
sh_elf_finish_dynamic_sections(bfd *output_bfd, struct bfd_link_info *info)
{
    struct elf_sh_link_hash_table *htab;
    asection *sgotplt;
    asection *sdyn;

    htab = sh_elf_hash_table(info);
    if (htab == NULL)
        return false;

    sgotplt = htab->root.sgotplt;
    sdyn = bfd_get_linker_section(htab->root.dynobj, ".dynamic");

    if (htab->root.dynamic_sections_created)
        process_dynamic_sections(output_bfd, htab, sgotplt, sdyn);

    if (sgotplt && sgotplt->size > 0 && !htab->fdpic_p)
        fill_got_entries(output_bfd, sgotplt, sdyn);

    if (sgotplt && sgotplt->size > 0)
        elf_section_data(sgotplt->output_section)->this_hdr.sh_entsize = 4;

    if (htab->fdpic_p && htab->srofixup != NULL)
        finalize_fdpic_got(output_bfd, htab);

    if (htab->srelfuncdesc)
        BFD_ASSERT(htab->srelfuncdesc->reloc_count * sizeof(Elf32_External_Rela)
                  == htab->srelfuncdesc->size);

    if (htab->root.srelgot)
        BFD_ASSERT(htab->root.srelgot->reloc_count * sizeof(Elf32_External_Rela)
                  == htab->root.srelgot->size);

    return true;
}

static enum elf_reloc_type_class
sh_elf_reloc_type_class (const struct bfd_link_info *info ATTRIBUTE_UNUSED,
			 const asection *rel_sec ATTRIBUTE_UNUSED,
			 const Elf_Internal_Rela *rela)
{
  switch ((int) ELF32_R_TYPE (rela->r_info))
    {
    case R_SH_RELATIVE:
      return reloc_class_relative;
    case R_SH_JMP_SLOT:
      return reloc_class_plt;
    case R_SH_COPY:
      return reloc_class_copy;
    default:
      return reloc_class_normal;
    }
}

#if !defined SH_TARGET_ALREADY_DEFINED
/* Support for Linux core dump NOTE sections.  */

static bool
elf32_shlin_grok_prstatus (bfd *abfd, Elf_Internal_Note *note)
{
  #define LINUX_SH_PRSTATUS_SIZE 168
  #define SIGNAL_OFFSET 12
  #define LWPID_OFFSET 24
  #define REG_OFFSET 72
  #define REG_SIZE 92

  if (note->descsz != LINUX_SH_PRSTATUS_SIZE)
    return false;

  elf_tdata (abfd)->core->signal = bfd_get_16 (abfd, note->descdata + SIGNAL_OFFSET);
  elf_tdata (abfd)->core->lwpid = bfd_get_32 (abfd, note->descdata + LWPID_OFFSET);

  return _bfd_elfcore_make_pseudosection (abfd, ".reg",
                                          REG_SIZE, note->descpos + REG_OFFSET);
}

static bool
elf32_shlin_grok_psinfo (bfd *abfd, Elf_Internal_Note *note)
{
  #define LINUX_SH_PRPSINFO_SIZE 124
  #define PROGRAM_NAME_OFFSET 28
  #define PROGRAM_NAME_LENGTH 16
  #define COMMAND_OFFSET 44
  #define COMMAND_LENGTH 80

  if (note->descsz != LINUX_SH_PRPSINFO_SIZE)
    return false;

  elf_tdata (abfd)->core->program
    = _bfd_elfcore_strndup (abfd, note->descdata + PROGRAM_NAME_OFFSET, PROGRAM_NAME_LENGTH);
  elf_tdata (abfd)->core->command
    = _bfd_elfcore_strndup (abfd, note->descdata + COMMAND_OFFSET, COMMAND_LENGTH);

  char *command = elf_tdata (abfd)->core->command;
  int n = strlen (command);

  if (n > 0 && command[n - 1] == ' ')
    command[n - 1] = '\0';

  return true;
}
#endif /* not SH_TARGET_ALREADY_DEFINED */


/* Return address for Ith PLT stub in section PLT, for relocation REL
   or (bfd_vma) -1 if it should not be included.  */

static bfd_vma
sh_elf_plt_sym_val (bfd_vma i, const asection *plt,
		    const arelent *rel ATTRIBUTE_UNUSED)
{
  const struct elf_sh_plt_info *plt_info;
  bfd_boolean is_dynamic = (plt->owner->flags & DYNAMIC) != 0;
  
  plt_info = get_plt_info (plt->owner, is_dynamic);
  return plt->vma + get_plt_offset (plt_info, i);
}

/* Decide whether to attempt to turn absptr or lsda encodings in
   shared libraries into pcrel within the given input section.  */

static bool
sh_elf_use_relative_eh_frame (bfd *input_bfd ATTRIBUTE_UNUSED,
			      struct bfd_link_info *info,
			      asection *eh_frame_section ATTRIBUTE_UNUSED)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  return !htab->fdpic_p;
}

/* Adjust the contents of an eh_frame_hdr section before they're output.  */

static bfd_byte
sh_elf_encode_eh_address (bfd *abfd,
			  struct bfd_link_info *info,
			  asection *osec, bfd_vma offset,
			  asection *loc_sec, bfd_vma loc_offset,
			  bfd_vma *encoded)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  struct elf_link_hash_entry *h;

  if (!htab->fdpic_p)
    return _bfd_elf_encode_eh_address (abfd, info, osec, offset, loc_sec,
				       loc_offset, encoded);

  h = htab->root.hgot;
  BFD_ASSERT (h && h->root.type == bfd_link_hash_defined);

  if (!h)
    return _bfd_elf_encode_eh_address (abfd, info, osec, offset,
				       loc_sec, loc_offset, encoded);

  if (sh_elf_osec_to_segment (abfd, osec)
      == sh_elf_osec_to_segment (abfd, loc_sec->output_section))
    return _bfd_elf_encode_eh_address (abfd, info, osec, offset,
				       loc_sec, loc_offset, encoded);

  BFD_ASSERT (sh_elf_osec_to_segment (abfd, osec)
	      == (sh_elf_osec_to_segment
		  (abfd, h->root.u.def.section->output_section)));

  *encoded = osec->vma + offset
    - (h->root.u.def.value
       + h->root.u.def.section->output_section->vma
       + h->root.u.def.section->output_offset);

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
