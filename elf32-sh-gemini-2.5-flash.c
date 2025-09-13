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
vxworks_object_p (bfd *abfd
#if defined SH_TARGET_ALREADY_DEFINED
                  ATTRIBUTE_UNUSED
#endif
                 )
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
  if (abfd == NULL)
    {
      return false;
    }

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
  if (abfd == NULL)
    return sh_elf_howto_table;

  if (vxworks_object_p (abfd))
    return sh_vxworks_howto_table;
  return sh_elf_howto_table;
}

static bfd_reloc_status_type
sh_elf_reloc_loop (int r_type ATTRIBUTE_UNUSED, bfd *input_bfd,
		   asection *input_section, bfd_byte *contents,
		   bfd_vma addr, asection *symbol_section,
		   bfd_vma start, bfd_vma end)
{
  static bfd_vma last_addr;
  static asection *last_symbol_section;

  bfd_byte *current_symbol_section_contents;
  bfd_byte *temp_contents_buffer = NULL;

  if (addr > bfd_get_section_limit (input_bfd, input_section))
    return bfd_reloc_outofrange;

  if (!last_addr)
    {
      last_addr = addr;
      last_symbol_section = symbol_section;
      return bfd_reloc_ok;
    }

  if (last_addr != addr)
    abort ();
  last_addr = 0;

  if (!symbol_section || last_symbol_section != symbol_section || end < start)
    return bfd_reloc_outofrange;

  if (symbol_section == input_section)
    {
      current_symbol_section_contents = contents;
    }
  else
    {
      if (elf_section_data (symbol_section)->this_hdr.contents != NULL)
        {
	  current_symbol_section_contents = elf_section_data (symbol_section)->this_hdr.contents;
        }
      else
        {
	  if (!bfd_malloc_and_get_section (input_bfd, symbol_section, &temp_contents_buffer))
	    {
	      return bfd_reloc_outofrange;
	    }
	  current_symbol_section_contents = temp_contents_buffer;
        }
    }

#define IS_PPI(PTR) ((bfd_get_16 (input_bfd, (PTR)) & 0xfc00) == 0xf800)

  bfd_byte *start_ptr = current_symbol_section_contents + start;
  bfd_byte *ptr = current_symbol_section_contents + end;
  bfd_byte *last_ptr;
  int diff, cum_diff;

  for (cum_diff = -6; cum_diff < 0 && ptr > start_ptr;)
    {
      last_ptr = ptr;
      ptr -= 4;

      while (ptr >= start_ptr && IS_PPI (ptr))
	ptr -= 2;

      ptr += 2;
      diff = (int)((last_ptr - ptr) >> 1);
      cum_diff += diff + (diff & 1);
    }

  if (cum_diff >= 0)
    {
      start -= 4;
      end = (bfd_vma)(ptr + (bfd_vma)cum_diff * 2) - (bfd_vma)current_symbol_section_contents;
    }
  else
    {
      bfd_vma temp_start = start - 4;

      while (temp_start && IS_PPI (current_symbol_section_contents + temp_start))
	temp_start -= 2;

      temp_start = start - 2 - ((start - temp_start) & 2);
      start = temp_start - cum_diff - 2;
      end = temp_start;
    }

  if (temp_contents_buffer != NULL)
    free (temp_contents_buffer);
#undef IS_PPI

  int insn = bfd_get_16 (input_bfd, current_symbol_section_contents + addr);

  bfd_signed_vma x_val = (insn & 0x200 ? end : start) - addr;

  if (input_section != symbol_section)
    {
      bfd_vma symbol_output_vma = symbol_section->output_section->vma + symbol_section->output_offset;
      bfd_vma input_output_vma = input_section->output_section->vma + input_section->output_offset;
      x_val += (symbol_output_vma - input_output_vma);
    }

  x_val >>= 1;

  if (x_val < -128 || x_val > 127)
    return bfd_reloc_overflow;

  bfd_vma modified_insn = (insn & ~0xff) | (x_val & 0xff);
  bfd_put_16 (input_bfd, modified_insn, current_symbol_section_contents + addr);

  return bfd_reloc_ok;
}

/* This function is used for normal relocs.  This used to be like the COFF
   function, and is almost certainly incorrect for other ELF targets.  */

static bfd_reloc_status_type
sh_elf_reloc (bfd *abfd, arelent *reloc_entry, asymbol *symbol_in,
	      void *data, asection *input_section, bfd *output_bfd,
	      char **error_message ATTRIBUTE_UNUSED)
{
  bfd_vma insn;
  bfd_vma sym_value;
  enum elf_sh_reloc_type r_type;
  bfd_vma addr = reloc_entry->address;
  bfd_size_type octets = addr * OCTETS_PER_BYTE (abfd, input_section);
  bfd_byte *hit_data = (bfd_byte *) data + octets;

  r_type = (enum elf_sh_reloc_type) reloc_entry->howto->type;

  if (output_bfd != NULL)
    {
      reloc_entry->address += input_section->output_offset;
      return bfd_reloc_ok;
    }

  if (r_type == R_SH_IND12W && (symbol_in->flags & BSF_LOCAL) != 0)
    return bfd_reloc_ok;

  if (symbol_in != NULL && bfd_is_und_section (symbol_in->section))
    return bfd_reloc_undefined;

  if (octets + bfd_get_reloc_size (reloc_entry->howto)
      > bfd_get_section_limit_octets (abfd, input_section))
    return bfd_reloc_outofrange;

  if (bfd_is_com_section (symbol_in->section))
    sym_value = 0;
  else
    sym_value = (symbol_in->value +
		 symbol_in->section->output_section->vma +
		 symbol_in->section->output_offset);

  switch (r_type)
    {
    case R_SH_DIR32:
      insn = bfd_get_32 (abfd, hit_data);
      insn += sym_value + reloc_entry->addend;
      bfd_put_32 (abfd, insn, hit_data);
      break;
    case R_SH_IND12W:
      insn = bfd_get_16 (abfd, hit_data);
      sym_value += reloc_entry->addend;
      sym_value -= (input_section->output_section->vma
		    + input_section->output_offset
		    + addr
		    + 4);
      sym_value += (((insn & 0xfff) ^ 0x800) - 0x800) << 1;
      insn = (insn & 0xf000) | ((sym_value >> 1) & 0xfff);
      bfd_put_16 (abfd, insn, hit_data);
      if (sym_value + 0x1000 >= 0x2000 || (sym_value & 1) != 0)
	return bfd_reloc_overflow;
      break;
    default:
      return bfd_reloc_bad_type;
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
    {
      if (reloc_entry != NULL && input_section != NULL)
        {
          reloc_entry->address += input_section->output_offset;
        }
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

static reloc_howto_type *
sh_elf_reloc_type_lookup (bfd *abfd, bfd_reloc_code_real_type code)
{
  size_t i;
  const size_t num_relocs = sizeof (sh_reloc_map) / sizeof (sh_reloc_map[0]);

  for (i = 0; i < num_relocs; ++i)
    {
      if (sh_reloc_map[i].bfd_reloc_val == code)
	{
	  return get_howto_table (abfd) + (size_t) sh_reloc_map[i].elf_reloc_val;
	}
    }

  return NULL;
}

static reloc_howto_type *
find_reloc_howto_in_table(const reloc_howto_type *table, unsigned int table_size, const char *r_name)
{
  for (unsigned int i = 0; i < table_size; i++)
    {
      if (table[i].name != NULL && strcasecmp(table[i].name, r_name) == 0)
        {
          return (reloc_howto_type *)&table[i];
        }
    }
  return NULL;
}

static reloc_howto_type *
sh_elf_reloc_name_lookup (bfd *abfd, const char *r_name)
{
  if (r_name == NULL)
    {
      return NULL;
    }

  if (vxworks_object_p (abfd))
    {
      return find_reloc_howto_in_table(
          sh_vxworks_howto_table,
          sizeof(sh_vxworks_howto_table) / sizeof(sh_vxworks_howto_table[0]),
          r_name
      );
    }
  else
    {
      return find_reloc_howto_in_table(
          sh_elf_howto_table,
          sizeof(sh_elf_howto_table) / sizeof(sh_elf_howto_table[0]),
          r_name
      );
    }
}

/* Given an ELF reloc, fill in the howto field of a relent.  */

static bool
is_sh_invalid_reloc_type(unsigned int r)
{
  return r >= R_SH_FIRST_INVALID_RELOC_6
         || (r >= R_SH_FIRST_INVALID_RELOC   && r <= R_SH_LAST_INVALID_RELOC)
         || (r >= R_SH_FIRST_INVALID_RELOC_2 && r <= R_SH_LAST_INVALID_RELOC_2)
         || (r >= R_SH_FIRST_INVALID_RELOC_3 && r <= R_SH_LAST_INVALID_RELOC_3)
         || (r >= R_SH_FIRST_INVALID_RELOC_4 && r <= R_SH_LAST_INVALID_RELOC_4)
         || (r >= R_SH_FIRST_INVALID_RELOC_5 && r <= R_SH_LAST_INVALID_RELOC_5);
}

static bool
sh_elf_info_to_howto (bfd *abfd, arelent *cache_ptr, Elf_Internal_Rela *dst)
{
  unsigned int r;

  r = ELF32_R_TYPE (dst->r_info);

  if (is_sh_invalid_reloc_type(r))
    {
      _bfd_error_handler (_("%pB: unsupported relocation type %#x"), abfd, r);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

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

static bool
sh_elf_relax_section (bfd *abfd, asection *sec,
		      struct bfd_link_info *link_info, bool *again)
{
  Elf_Internal_Shdr *symtab_header = &elf_symtab_hdr(abfd);
  Elf_Internal_Rela *section_relocs = NULL;
  bfd_byte *section_contents = NULL;
  Elf_Internal_Sym *symbol_buffer = NULL;

  *again = false;

  if (bfd_link_relocatable(link_info)
      || !(sec->flags & SEC_HAS_CONTENTS)
      || !(sec->flags & SEC_RELOC)
      || sec->reloc_count == 0)
    return true;

  section_relocs = (_bfd_elf_link_read_relocs
                    (abfd, sec, NULL, (Elf_Internal_Rela *) NULL,
                     link_info->keep_memory));
  if (section_relocs == NULL)
    goto error_cleanup;

  bool have_code_relocs = false;
  Elf_Internal_Rela *relocs_end = section_relocs + sec->reloc_count;

  for (Elf_Internal_Rela *current_reloc = section_relocs; current_reloc < relocs_end; current_reloc++)
    {
      if (ELF32_R_TYPE(current_reloc->r_info) == (int)R_SH_CODE)
        have_code_relocs = true;

      if (ELF32_R_TYPE(current_reloc->r_info) != (int)R_SH_USES)
        continue;

      bfd_vma load_addr, pointer_addr, symbol_value;
      unsigned short instruction;
      Elf_Internal_Rela *function_reloc, *scan_reloc, *count_reloc;
      bfd_signed_vma function_offset;

      if (section_contents == NULL)
        {
          if (elf_section_data(sec)->this_hdr.contents != NULL)
            section_contents = elf_section_data(sec)->this_hdr.contents;
          else
            {
              if (!bfd_malloc_and_get_section(abfd, sec, &section_contents))
                goto error_cleanup;
            }
        }

      load_addr = current_reloc->r_offset + 4 + current_reloc->r_addend;
      if (load_addr >= sec->size)
        {
          _bfd_error_handler(_("%pB: %#" PRIx64 ": warning: bad R_SH_USES offset"),
                             abfd, (uint64_t)current_reloc->r_offset);
          continue;
        }
      instruction = bfd_get_16(abfd, section_contents + load_addr);

      if ((instruction & 0xf000) != 0xd000)
        {
          _bfd_error_handler(_("%pB: %#" PRIx64 ": warning: R_SH_USES points to unrecognized insn 0x%x"),
                             abfd, (uint64_t)current_reloc->r_offset, instruction);
          continue;
        }

      pointer_addr = instruction & 0xff;
      pointer_addr *= 4;
      pointer_addr += (load_addr + 4) &~ (bfd_vma) 3;
      if (pointer_addr >= sec->size)
        {
          _bfd_error_handler(_("%pB: %#" PRIx64 ": warning: bad R_SH_USES load offset"),
                             abfd, (uint64_t)current_reloc->r_offset);
          continue;
        }

      for (function_reloc = section_relocs; function_reloc < relocs_end; function_reloc++)
        if (function_reloc->r_offset == pointer_addr
            && ELF32_R_TYPE(function_reloc->r_info) == (int)R_SH_DIR32)
          break;
      if (function_reloc >= relocs_end)
        {
          _bfd_error_handler(_("%pB: %#" PRIx64 ": warning: could not find expected reloc"),
                             abfd, (uint64_t)pointer_addr);
          continue;
        }

      if (symbol_buffer == NULL && symtab_header->sh_info != 0)
        {
          symbol_buffer = (Elf_Internal_Sym *)symtab_header->contents;
          if (symbol_buffer == NULL)
            symbol_buffer = bfd_elf_get_elf_syms(abfd, symtab_header,
                                                    symtab_header->sh_info, 0,
                                                    NULL, NULL, NULL);
          if (symbol_buffer == NULL)
            goto error_cleanup;
        }

      if (ELF32_R_SYM(function_reloc->r_info) < symtab_header->sh_info)
        {
          Elf_Internal_Sym *isym = symbol_buffer + ELF32_R_SYM(function_reloc->r_info);
          if (isym->st_shndx != (unsigned int)_bfd_elf_section_from_bfd_section(abfd, sec))
            {
              _bfd_error_handler(_("%pB: %#" PRIx64 ": warning: symbol in unexpected section"),
                                 abfd, (uint64_t)pointer_addr);
              continue;
            }

          symbol_value = (isym->st_value
                          + sec->output_section->vma
                          + sec->output_offset);
        }
      else
        {
          unsigned long indx = ELF32_R_SYM(function_reloc->r_info) - symtab_header->sh_info;
          struct elf_link_hash_entry *h = elf_sym_hashes(abfd)[indx];
          BFD_ASSERT(h != NULL);
          if (h->root.type != bfd_link_hash_defined
              && h->root.type != bfd_link_hash_defweak)
            {
              continue;
            }

          symbol_value = (h->root.u.def.value
                          + h->root.u.def.section->output_section->vma
                          + h->root.u.def.section->output_offset);
        }

      if (get_howto_table(abfd)[R_SH_DIR32].partial_inplace)
        symbol_value += bfd_get_32(abfd, section_contents + pointer_addr);
      else
        symbol_value += function_reloc->r_addend;

      function_offset = (symbol_value
                         - (current_reloc->r_offset
                            + sec->output_section->vma
                            + sec->output_offset
                            + 4));
      if (function_offset < -0x1000 || function_offset >= 0x1000 - 8)
        {
          continue;
        }

      elf_section_data(sec)->relocs = section_relocs;
      elf_section_data(sec)->this_hdr.contents = section_contents;
      symtab_header->contents = (unsigned char *)symbol_buffer;

      current_reloc->r_info = ELF32_R_INFO(ELF32_R_SYM(function_reloc->r_info), R_SH_IND12W);

      if (bfd_get_16(abfd, section_contents + current_reloc->r_offset) & 0x0020)
        bfd_put_16(abfd, (bfd_vma) 0xa000, section_contents + current_reloc->r_offset);
      else
        bfd_put_16(abfd, (bfd_vma) 0xb000, section_contents + current_reloc->r_offset);

      current_reloc->r_addend = -4;
      current_reloc->r_addend += bfd_get_32(abfd, section_contents + pointer_addr);

      for (scan_reloc = section_relocs; scan_reloc < relocs_end; scan_reloc++)
        if (ELF32_R_TYPE(scan_reloc->r_info) == (int)R_SH_USES
            && load_addr == scan_reloc->r_offset + 4 + scan_reloc->r_addend)
          break;
      if (scan_reloc < relocs_end)
        {
          continue;
        }

      for (count_reloc = section_relocs; count_reloc < relocs_end; count_reloc++)
        if (count_reloc->r_offset == pointer_addr
            && ELF32_R_TYPE(count_reloc->r_info) == (int)R_SH_COUNT)
          break;

      if (!sh_elf_relax_delete_bytes(abfd, sec, load_addr, 2))
        goto error_cleanup;

      *again = true;

      if (count_reloc >= relocs_end)
        {
          _bfd_error_handler(_("%pB: %#" PRIx64 ": warning: could not find expected COUNT reloc"),
                             abfd, (uint64_t)pointer_addr);
          continue;
        }

      if (count_reloc->r_addend == 0)
        {
          _bfd_error_handler(_("%pB: %#" PRIx64 ": warning: bad count"),
                             abfd, (uint64_t)pointer_addr);
          continue;
        }

      --count_reloc->r_addend;

      if (count_reloc->r_addend == 0)
        {
          if (!sh_elf_relax_delete_bytes(abfd, sec, function_reloc->r_offset, 4))
            goto error_cleanup;
        }
    }

  if ((elf_elfheader(abfd)->e_flags & EF_SH_MACH_MASK) != EF_SH4
      && have_code_relocs)
    {
      bool swapped_alignment;

      if (section_contents == NULL)
        {
          if (elf_section_data(sec)->this_hdr.contents != NULL)
            section_contents = elf_section_data(sec)->this_hdr.contents;
          else
            {
              if (!bfd_malloc_and_get_section(abfd, sec, &section_contents))
                goto error_cleanup;
            }
        }

      if (!sh_elf_align_loads(abfd, sec, section_relocs, section_contents,
                              &swapped_alignment))
        goto error_cleanup;

      if (swapped_alignment)
        {
          elf_section_data(sec)->relocs = section_relocs;
          elf_section_data(sec)->this_hdr.contents = section_contents;
          symtab_header->contents = (unsigned char *)symbol_buffer;
        }
    }

cleanup:
  if (symbol_buffer != NULL)
    {
      if (symtab_header->contents != (unsigned char *)symbol_buffer)
        {
          if (!link_info->keep_memory)
            free(symbol_buffer);
          else
            symtab_header->contents = (unsigned char *)symbol_buffer;
        }
    }

  if (section_contents != NULL)
    {
      if (elf_section_data(sec)->this_hdr.contents != section_contents)
        {
          if (!link_info->keep_memory)
            free(section_contents);
          else
            elf_section_data(sec)->this_hdr.contents = section_contents;
        }
    }

  if (section_relocs != NULL && elf_section_data(sec)->relocs != section_relocs)
    free(section_relocs);

  return true;

error_cleanup:
  if (symbol_buffer != NULL && symtab_header->contents != (unsigned char *)symbol_buffer)
      free(symbol_buffer);
  if (section_contents != NULL && elf_section_data(sec)->this_hdr.contents != section_contents)
      free(section_contents);
  if (section_relocs != NULL && elf_section_data(sec)->relocs != section_relocs)
      free(section_relocs);

  return false;
}

/* Delete some bytes from a section while relaxing.  FIXME: There is a
   lot of duplication between this function and sh_relax_delete_bytes
   in coff-sh.c.  */

static bool
sh_elf_relax_delete_bytes (bfd *abfd, asection *sec, bfd_vma addr,
			   int count)
{
  Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr (abfd);
  Elf_Internal_Sym *isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;
  unsigned int sec_shndx = _bfd_elf_section_from_bfd_section (abfd, sec);
  bfd_byte *contents = elf_section_data (sec)->this_hdr.contents;

  static const bfd_vma NOP_OPCODE_VAL = 0x0009;

  Elf_Internal_Rela *irelalign = NULL;
  bfd_vma toaddr = sec->size;

  Elf_Internal_Rela *irel_start = elf_section_data (sec)->relocs;
  Elf_Internal_Rela *irel_end = irel_start + sec->reloc_count;

  for (Elf_Internal_Rela *irel = irel_start; irel < irel_end; irel++)
    {
      if (((enum elf_sh_reloc_type) ELF32_R_TYPE (irel->r_info)) == R_SH_ALIGN
	  && irel->r_offset > addr
	  && count < (1 << irel->r_addend))
	{
	  irelalign = irel;
	  toaddr = irel->r_offset;
	  break;
	}
    }

  size_t bytes_to_shift = 0;
  if (toaddr > addr + count) {
      bytes_to_shift = (size_t) (toaddr - (addr + count));
  }
  memmove(contents + addr, contents + addr + count, bytes_to_shift);

  if (irelalign == NULL)
    sec->size -= count;
  else
    {
      BFD_ASSERT ((count & 1) == 0);
      for (int i = 0; i < count; i += 2)
	bfd_put_16 (abfd, NOP_OPCODE_VAL, contents + toaddr - count + i);
    }

  for (Elf_Internal_Rela *irel = irel_start; irel < irel_end; irel++)
    {
      bfd_vma nraddr = irel->r_offset;
      enum elf_sh_reloc_type reloc_type = (enum elf_sh_reloc_type) ELF32_R_TYPE (irel->r_info);

      if ((irel->r_offset > addr && irel->r_offset < toaddr)
	  || (reloc_type == R_SH_ALIGN && irel->r_offset == toaddr))
	nraddr -= count;

      if (irel->r_offset >= addr
	  && irel->r_offset < addr + count
	  && reloc_type != R_SH_ALIGN
	  && reloc_type != R_SH_CODE
	  && reloc_type != R_SH_DATA
	  && reloc_type != R_SH_LABEL)
	{
	  irel->r_info = ELF32_R_INFO (ELF32_R_SYM (irel->r_info), R_SH_NONE);
	}

      bfd_vma start = addr, stop = addr;
      int insn = 0;
      bfd_signed_vma voff = 0;

      switch (reloc_type)
	{
	case R_SH_DIR8WPN:
	case R_SH_IND12W:
	case R_SH_DIR8WPZ:
	case R_SH_DIR8WPL:
	  start = irel->r_offset;
	  insn = bfd_get_16 (abfd, contents + nraddr);
	  break;
    default:
        break;
	}

      switch (reloc_type)
	{
	case R_SH_DIR32:
	  if (ELF32_R_SYM (irel->r_info) < symtab_hdr->sh_info)
	    {
	      Elf_Internal_Sym *isym_target = isymbuf + ELF32_R_SYM (irel->r_info);
	      if (isym_target->st_shndx == sec_shndx
		  && (isym_target->st_value <= addr
		      || isym_target->st_value >= toaddr))
		{
		  bfd_vma val;
		  if (get_howto_table (abfd)[R_SH_DIR32].partial_inplace)
		    {
		      val = bfd_get_32 (abfd, contents + nraddr);
		      val += isym_target->st_value;
		      if (val > addr && val < toaddr)
			bfd_put_32 (abfd, val - count, contents + nraddr);
		    }
		  else
		    {
		      val = isym_target->st_value + irel->r_addend;
		      if (val > addr && val < toaddr)
			irel->r_addend -= count;
		    }
		}
	    }
	  start = stop = addr;
	  break;

	case R_SH_DIR8WPN:
	  {
	    int off = insn & 0xff;
	    if (off & 0x80) off -= 0x100;
	    stop = (bfd_vma) ((bfd_signed_vma) start + 4 + (bfd_signed_vma) off * 2);
	  }
	  break;

	case R_SH_IND12W:
	  {
	    int off = insn & 0xfff;
	    if (off == 0)
	      {
		start = stop = addr;
	      }
	    else
	      {
		if (off & 0x800) off -= 0x1000;
		stop = (bfd_vma) ((bfd_signed_vma) start + 4 + (bfd_signed_vma) off * 2);

		if (stop > addr && stop < toaddr)
		  irel->r_addend -= count;
	      }
	  }
	  break;

	case R_SH_DIR8WPZ:
	  {
	    int off = insn & 0xff;
	    stop = start + 4 + (bfd_vma) off * 2;
	  }
	  break;

	case R_SH_DIR8WPL:
	  {
	    int off = insn & 0xff;
	    stop = (start & ~(bfd_vma) 3) + 4 + (bfd_vma) off * 4;
	  }
	  break;

	case R_SH_SWITCH8:
	case R_SH_SWITCH16:
	case R_SH_SWITCH32:
	  start = (bfd_vma) ((bfd_signed_vma) irel->r_offset - (long) irel->r_addend);

	  if (reloc_type == R_SH_SWITCH16)
	    voff = bfd_get_signed_16 (abfd, contents + nraddr);
	  else if (reloc_type == R_SH_SWITCH8)
	    voff = bfd_get_8 (abfd, contents + nraddr);
	  else /* R_SH_SWITCH32 */
	    voff = bfd_get_signed_32 (abfd, contents + nraddr);

	  stop = (bfd_vma) ((bfd_signed_vma) start + voff);

	  if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr))
	    irel->r_addend += count;
	  else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))
	    irel->r_addend -= count;
	  break;

	case R_SH_USES:
	  start = irel->r_offset;
	  stop = (bfd_vma) ((bfd_signed_vma) start + (long) irel->r_addend + 4);
	  break;

    default:
        break;
	}

      int adjust = 0;
      if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr))
	adjust = count;
      else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))
	adjust = - count;

      if (adjust != 0)
	{
	  bool overflow = false;
	  int original_insn = insn;
	  bfd_signed_vma original_voff = voff;

	  switch (reloc_type)
	    {
	    case R_SH_DIR8WPN:
	    case R_SH_DIR8WPZ:
	      insn += adjust / 2;
	      if (((original_insn ^ insn) & 0xFF00) != 0)
		overflow = true;
	      bfd_put_16 (abfd, (bfd_vma) insn, contents + nraddr);
	      break;

	    case R_SH_IND12W:
	      insn += adjust / 2;
	      if (((original_insn ^ insn) & 0xF000) != 0)
		overflow = true;
	      bfd_put_16 (abfd, (bfd_vma) insn, contents + nraddr);
	      break;

	    case R_SH_DIR8WPL:
	      if (count >= 4)
	          insn += adjust / 4;
	      else
	      {
	          if ((irel->r_offset & 3) == 0)
	              ++insn;
	      }
	      if (((original_insn ^ insn) & 0xFF00) != 0)
		overflow = true;
	      bfd_put_16 (abfd, (bfd_vma) insn, contents + nraddr);
	      break;

	    case R_SH_SWITCH8:
	      voff += adjust;
	      if (voff < 0 || voff >= 0xff)
		overflow = true;
	      bfd_put_8 (abfd, voff, contents + nraddr);
	      break;

	    case R_SH_SWITCH16:
	      voff += adjust;
	      if (voff < -0x8000 || voff >= 0x8000)
		overflow = true;
	      bfd_put_signed_16 (abfd, (bfd_vma) voff, contents + nraddr);
	      break;

	    case R_SH_SWITCH32:
	      voff += adjust;
	      bfd_put_signed_32 (abfd, (bfd_vma) voff, contents + nraddr);
	      break;

	    case R_SH_USES:
	      irel->r_addend += adjust;
	      break;

	    default:
	      _bfd_error_handler
		(_("%pB: %#" PRIx64 ": fatal: unhandled reloc type %u for relaxation adjustment"),
		 abfd, (uint64_t) irel->r_offset, reloc_type);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }

	  if (overflow)
	    {
	      _bfd_error_handler
		(_("%pB: %#" PRIx64 ": fatal: reloc overflow while relaxing"),
		 abfd, (uint64_t) irel->r_offset);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	}

      irel->r_offset = nraddr;
    }

  bfd_byte *current_ocontents = NULL;
  bool ocontents_is_temporary = false;

#define GET_OTHER_SECTION_CONTENTS(target_abfd, target_o, p_ocontents_var, p_is_temporary_allocated_var) \
  do { \
    if (elf_section_data(target_o)->this_hdr.contents != NULL) \
      *(p_ocontents_var) = elf_section_data(target_o)->this_hdr.contents; \
    else \
    { \
      if (!bfd_malloc_and_get_section (target_abfd, target_o, (p_ocontents_var))) \
	{ \
	  _bfd_error_handler (_("%pB: Failed to read contents for section %s"), \
			      target_abfd, target_o->name); \
	  return false; \
	} \
      elf_section_data(target_o)->this_hdr.contents = *(p_ocontents_var); \
      *(p_is_temporary_allocated_var) = true; \
    } \
  } while (0)


  for (asection *o = abfd->sections; o != NULL; o = o->next)
    {
      if (o == sec
	  || (o->flags & SEC_HAS_CONTENTS) == 0
	  || (o->flags & SEC_RELOC) == 0
	  || o->reloc_count == 0)
	continue;

      Elf_Internal_Rela *internal_relocs = (_bfd_elf_link_read_relocs
			 (abfd, o, NULL, (Elf_Internal_Rela *) NULL, true));
      if (internal_relocs == NULL)
	{
	  return false;
	}

      Elf_Internal_Rela *irelscan_end = internal_relocs + o->reloc_count;
      for (Elf_Internal_Rela *irelscan = internal_relocs; irelscan < irelscan_end; irelscan++)
	{
	  enum elf_sh_reloc_type irelscan_reloc_type = (enum elf_sh_reloc_type) ELF32_R_TYPE (irelscan->r_info);

	  if (irelscan_reloc_type == R_SH_SWITCH32)
	    {
	      if (current_ocontents == NULL || ocontents_is_temporary) {
              current_ocontents = NULL;
              ocontents_is_temporary = false;
              GET_OTHER_SECTION_CONTENTS(abfd, o, &current_ocontents, &ocontents_is_temporary);
	      }
          if (current_ocontents == NULL) {
              return false;
          }

	      bfd_vma start_o, stop_o;
	      bfd_signed_vma voff_o;

	      start_o = (bfd_vma) ((bfd_signed_vma) irelscan->r_offset - (long) irelscan->r_addend);

	      if (start_o > addr && start_o < toaddr)
		irelscan->r_addend += count;

	      voff_o = bfd_get_signed_32 (abfd, current_ocontents + irelscan->r_offset);
	      stop_o = (bfd_vma) ((bfd_signed_vma) start_o + voff_o);

	      int adjust_o = 0;
	      if (start_o > addr && start_o < toaddr && (stop_o <= addr || stop_o >= toaddr))
		adjust_o = count;
	      else if (stop_o > addr && stop_o < toaddr && (start_o <= addr || start_o >= toaddr))
		adjust_o = - count;

	      if (adjust_o != 0)
		bfd_put_signed_32 (abfd, (bfd_vma) voff_o + adjust_o,
				   current_ocontents + irelscan->r_offset);
	    }

	  if (irelscan_reloc_type != R_SH_DIR32)
	    continue;

	  if (ELF32_R_SYM (irelscan->r_info) >= symtab_hdr->sh_info)
	    continue;

	  Elf_Internal_Sym *isym_target = isymbuf + ELF32_R_SYM (irelscan->r_info);
	  if (isym_target->st_shndx == sec_shndx
	      && (isym_target->st_value <= addr
		  || isym_target->st_value >= toaddr))
	    {
	      if (current_ocontents == NULL || ocontents_is_temporary) {
              current_ocontents = NULL;
              ocontents_is_temporary = false;
              GET_OTHER_SECTION_CONTENTS(abfd, o, &current_ocontents, &ocontents_is_temporary);
	      }
          if (current_ocontents == NULL) {
              return false;
          }

	      bfd_vma val;
	      val = bfd_get_32 (abfd, current_ocontents + irelscan->r_offset);
	      val += isym_target->st_value;
	      if (val > addr && val < toaddr)
		bfd_put_32 (abfd, val - count,
			    current_ocontents + irelscan->r_offset);
	    }
	}
    }
#undef GET_OTHER_SECTION_CONTENTS

  Elf_Internal_Sym *isym_end_local = isymbuf + symtab_hdr->sh_info;
  for (Elf_Internal_Sym *isym = isymbuf; isym < isym_end_local; isym++)
    {
      if (isym->st_shndx == sec_shndx
	  && isym->st_value > addr
	  && isym->st_value < toaddr)
	isym->st_value -= count;
    }

  unsigned int symcount_global = (symtab_hdr->sh_size / sizeof (Elf32_External_Sym)
			      - symtab_hdr->sh_info);
  struct elf_link_hash_entry **sym_hashes = elf_sym_hashes (abfd);
  struct elf_link_hash_entry **end_hashes = sym_hashes + symcount_global;
  for (struct elf_link_hash_entry **sym_hash_ptr = sym_hashes; sym_hash_ptr < end_hashes; sym_hash_ptr++)
    {
      struct elf_link_hash_entry *sym_hash = *sym_hash_ptr;
      if ((sym_hash->root.type == bfd_link_hash_defined
	   || sym_hash->root.type == bfd_link_hash_defweak)
	  && sym_hash->root.u.def.section == sec
	  && sym_hash->root.u.def.value > addr
	  && sym_hash->root.u.def.value < toaddr)
	{
	  sym_hash->root.u.def.value -= count;
	}
    }

  if (irelalign != NULL)
    {
      bfd_vma alignto = BFD_ALIGN (toaddr, 1 << irelalign->r_addend);
      bfd_vma alignaddr = BFD_ALIGN (irelalign->r_offset,
			     1 << irelalign->r_addend);
      if (alignto != alignaddr)
	{
	  return sh_elf_relax_delete_bytes (abfd, sec, alignaddr,
					    (int) (alignto - alignaddr));
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
  Elf_Internal_Rela *irel_iterator = NULL;
  Elf_Internal_Rela *irelend = NULL;
  bfd_vma *labels = NULL;
  bfd_vma *label_current = NULL;
  bfd_vma *label_end = NULL;
  bfd_size_type amt = 0;
  bool success = false;

  *pswapped = false;

  if (sec->reloc_count == 0)
    {
      return true;
    }

  irelend = internal_relocs + sec->reloc_count;

  amt = sec->reloc_count;
  amt *= sizeof (bfd_vma);
  labels = (bfd_vma *) bfd_malloc (amt);
  if (labels == NULL)
    {
      return false;
    }
  label_end = labels;
  for (irel_iterator = internal_relocs; irel_iterator < irelend; irel_iterator++)
    {
      if (ELF32_R_TYPE (irel_iterator->r_info) == (int) R_SH_LABEL)
	{
	  *label_end = irel_iterator->r_offset;
	  ++label_end;
	}
    }

  label_current = labels;

  Elf_Internal_Rela *current_reloc = internal_relocs;
  while (current_reloc < irelend)
    {
      if (ELF32_R_TYPE (current_reloc->r_info) != (int) R_SH_CODE)
	{
	  current_reloc++;
	  continue;
	}

      bfd_vma start_address = current_reloc->r_offset;
      Elf_Internal_Rela *next_span_element = current_reloc + 1;

      while (next_span_element < irelend
	     && ELF32_R_TYPE (next_span_element->r_info) != (int) R_SH_DATA)
	{
	  next_span_element++;
	}

      bfd_vma stop_address;
      if (next_span_element < irelend)
	{
	  stop_address = next_span_element->r_offset;
	}
      else
	{
	  stop_address = sec->size;
	}

      if (! _bfd_sh_align_load_span (abfd, sec, contents, sh_elf_swap_insns,
				     internal_relocs, &label_current,
				     label_end, start_address, stop_address, pswapped))
	{
	  goto cleanup;
	}

      current_reloc = next_span_element;
    }

  success = true;

cleanup:
  if (labels != NULL)
    {
      free (labels);
    }

  return success;
}

/* Swap two SH instructions.  This is like sh_swap_insns in coff-sh.c.  */

static bool
adjust_and_check_insn (bfd *abfd, bfd_byte *loc, int adjustment, unsigned short mask)
{
  unsigned short insn = bfd_get_16 (abfd, loc);
  unsigned short original_insn = insn;
  insn += adjustment;

  if ((original_insn & mask) != (insn & mask))
    return true;

  bfd_put_16 (abfd, insn, loc);
  return false;
}

static bool
sh_elf_swap_insns (bfd *abfd, asection *sec, void *relocs,
		   bfd_byte *contents, bfd_vma addr)
{
  Elf_Internal_Rela *internal_relocs = (Elf_Internal_Rela *) relocs;
  Elf_Internal_Rela *irel;
  Elf_Internal_Rela *irelend = internal_relocs + sec->reloc_count;

  unsigned short insn1 = bfd_get_16 (abfd, contents + addr);
  unsigned short insn2 = bfd_get_16 (abfd, contents + addr + 2);
  bfd_put_16 (abfd, insn2, contents + addr);
  bfd_put_16 (abfd, insn1, contents + addr + 2);

  for (irel = internal_relocs; irel < irelend; irel++)
    {
      enum elf_sh_reloc_type type = (enum elf_sh_reloc_type) ELF32_R_TYPE (irel->r_info);

      if (type == R_SH_ALIGN || type == R_SH_CODE || type == R_SH_DATA || type == R_SH_LABEL)
	    continue;

      if (type == R_SH_USES)
	    {
	      bfd_vma offset_plus_addend = irel->r_offset + 4 + irel->r_addend;
	      if (offset_plus_addend == addr)
		    irel->r_addend += 2;
	      else if (offset_plus_addend == addr + 2)
		    irel->r_addend -= 2;
	    }

      int offset_adjustment = 0;
      if (irel->r_offset == addr)
	    {
	      irel->r_offset += 2;
	      offset_adjustment = -2;
	    }
      else if (irel->r_offset == addr + 2)
	    {
	      irel->r_offset -= 2;
	      offset_adjustment = 2;
	    }

      if (offset_adjustment != 0)
	    {
	      bfd_byte *location = contents + irel->r_offset;
	      bool overflow = false;
	      int instruction_adjustment = offset_adjustment / 2;

	      switch (type)
		    {
		    default:
		      break;

		    case R_SH_DIR8WPN:
		    case R_SH_DIR8WPZ:
		      overflow = adjust_and_check_insn (abfd, location, instruction_adjustment, 0xff00);
		      break;

		    case R_SH_IND12W:
		      overflow = adjust_and_check_insn (abfd, location, instruction_adjustment, 0xf000);
		      break;

		    case R_SH_DIR8WPL:
		      if ((addr & 3) != 0)
			    {
			      overflow = adjust_and_check_insn (abfd, location, instruction_adjustment, 0xff00);
			    }
		      break;
		    }

	      if (overflow)
		    {
		      _bfd_error_handler
			(_("%pB: %#" PRIx64 ": fatal: reloc overflow while relaxing"),
			 abfd, (uint64_t) irel->r_offset);
		      bfd_set_error (bfd_error_bad_value);
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

static const struct elf_sh_plt_info *
get_plt_info (bfd *abfd, bool pic_p)
{
  const int is_little_endian = !bfd_big_endian (abfd);

  if (fdpic_object_p (abfd))
    {
      if (sh_get_arch_from_bfd_mach (bfd_get_mach (abfd)) & arch_sh2a_base)
	return &fdpic_sh2a_plts[is_little_endian];
      else
	return &fdpic_sh_plts[is_little_endian];
    }
  if (vxworks_object_p (abfd))
    return &vxworks_sh_plts[pic_p][is_little_endian];
  
  return &elf_sh_plts[pic_p][is_little_endian];
}

/* Install a 32-bit PLT field starting at ADDR, which occurs in OUTPUT_BFD.
   VALUE is the field's value and CODE_P is true if VALUE refers to code,
   not data.  */

inline static void
install_plt_field (bfd *output_bfd,
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

static bfd_vma
get_plt_index (const struct elf_sh_plt_info *info, bfd_vma offset)
{
  if (info == NULL || info->symbol_entry_size == 0)
    return 0;

  bfd_vma base_index = 0;
  const struct elf_sh_plt_info *current_plt_info = info;

  offset -= current_plt_info->plt0_entry_size;

  if (current_plt_info->short_plt != NULL)
    {
      if (current_plt_info->short_plt->symbol_entry_size == 0)
        return 0;

      bfd_vma total_short_plt_size = (bfd_vma)MAX_SHORT_PLT * current_plt_info->short_plt->symbol_entry_size;

      if (offset > total_short_plt_size)
        {
          base_index = MAX_SHORT_PLT;
          offset -= total_short_plt_size;
        }
      else
        {
          current_plt_info = current_plt_info->short_plt;
        }
    }

  return base_index + offset / current_plt_info->symbol_entry_size;
}

/* Do the inverse operation.  */

static bfd_vma
get_plt_offset (const struct elf_sh_plt_info *info, bfd_vma plt_index)
{
  bfd_vma offset = 0;
  const struct elf_sh_plt_info *current_info = info;

  if (info->short_plt != NULL)
    {
      if (plt_index > MAX_SHORT_PLT)
        {
          offset = MAX_SHORT_PLT * info->short_plt->symbol_entry_size;
          plt_index -= MAX_SHORT_PLT;
        }
      else
        {
          current_info = info->short_plt;
        }
    }

  return (offset
          + current_info->plt0_entry_size
          + (plt_index * current_info->symbol_entry_size));
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

static bool
sh_elf_mkobject (bfd *abfd)
{
  if (abfd == NULL)
    {
      return false;
    }
  return bfd_elf_allocate_object (abfd, sizeof (struct sh_elf_obj_tdata));
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
    return (struct bfd_hash_entry *) ret;

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
  const size_t amt = sizeof (struct elf_sh_link_hash_table);

  ret = bfd_zmalloc (amt);
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
  unsigned int section_type = elf_section_data (p)->this_hdr.sh_type;

  bool is_fdpic_binary = htab->fdpic_p;

  bool is_section_type_that_requires_dynsym_in_fdpic =
    (section_type == SHT_PROGBITS ||
     section_type == SHT_NOBITS ||
     section_type == SHT_NULL);

  return !is_fdpic_binary || !is_section_type_that_requires_dynsym_in_fdpic;
}

/* Create .got, .gotplt, and .rela.got sections in DYNOBJ, and set up
   shortcuts to them in our hash table.  */

static bool
create_and_align_bfd_section(bfd *dynobj, bfd_section **section_out,
                             const char *name, flagword flags, unsigned int alignment)
{
  *section_out = bfd_make_section_anyway_with_flags(dynobj, name, flags);
  if (*section_out == NULL)
    return false;
  return bfd_set_section_alignment(*section_out, alignment);
}

static bool
create_got_section (bfd *dynobj, struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab;

  if (! _bfd_elf_create_got_section (dynobj, info))
    return false;

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  const flagword common_flags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS
                                 | SEC_IN_MEMORY | SEC_LINKER_CREATED);
  const flagword readonly_flags = (common_flags | SEC_READONLY);
  const unsigned int alignment = 2;

  if (!create_and_align_bfd_section(dynobj, &htab->sfuncdesc, ".got.funcdesc",
                                    common_flags, alignment))
    return false;

  if (!create_and_align_bfd_section(dynobj, &htab->srelfuncdesc, ".rela.got.funcdesc",
                                    readonly_flags, alignment))
    return false;

  if (!create_and_align_bfd_section(dynobj, &htab->srofixup, ".rofixup",
                                    readonly_flags, alignment))
    return false;

  return true;
}

/* Create dynamic sections when linking against a dynamic object.  */

static bool
bfd_create_aligned_section(bfd *abfd, const char *name, flagword flags, int alignment, asection **out_section)
{
  asection *s = bfd_make_section_anyway_with_flags(abfd, name, flags);
  if (s == NULL)
    return false;
  if (!bfd_set_section_alignment(s, alignment))
    return false;

  *out_section = s;
  return true;
}


static bool
sh_elf_create_dynamic_sections (bfd *abfd, struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab;
  flagword base_flags, plt_flags;
  const struct elf_backend_data *bed = get_elf_backend_data (abfd);
  int ptr_alignment;

  switch (bed->s->arch_size)
    {
    case 32:
      ptr_alignment = 2;
      break;

    case 64:
      ptr_alignment = 3;
      break;

    default:
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  if (htab->root.dynamic_sections_created)
    return true;

  base_flags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS | SEC_IN_MEMORY
	        | SEC_LINKER_CREATED);

  plt_flags = base_flags | SEC_CODE;
  if (bed->plt_not_loaded)
    plt_flags &= ~ (SEC_LOAD | SEC_HAS_CONTENTS);
  if (bed->plt_readonly)
    plt_flags |= SEC_READONLY;

  if (!bfd_create_aligned_section(abfd, ".plt", plt_flags, bed->plt_alignment, &htab->root.splt))
    return false;

  if (bed->want_plt_sym)
    {
      struct elf_link_hash_entry *h_plt_sym;
      struct bfd_link_hash_entry *bh_plt_sym = NULL;

      if (!_bfd_generic_link_add_one_symbol
	     (info, abfd, "_PROCEDURE_LINKAGE_TABLE_", BSF_GLOBAL, htab->root.splt,
	      (bfd_vma) 0, NULL, false,
	      get_elf_backend_data (abfd)->collect, &bh_plt_sym))
	return false;

      h_plt_sym = (struct elf_link_hash_entry *) bh_plt_sym;
      h_plt_sym->def_regular = 1;
      h_plt_sym->type = STT_OBJECT;
      htab->root.hplt = h_plt_sym;

      if (bfd_link_pic (info)
	  && !bfd_elf_link_record_dynamic_symbol (info, h_plt_sym))
	return false;
    }

  const char *relplt_section_name = bed->default_use_rela_p ? ".rela.plt" : ".rel.plt";
  if (!bfd_create_aligned_section(abfd, relplt_section_name, base_flags | SEC_READONLY, ptr_alignment, &htab->root.srelplt))
    return false;

  if (htab->root.sgot == NULL && !create_got_section (abfd, info))
    return false;

  if (bed->want_dynbss)
    {
      asection *dynbss_section = bfd_make_section_anyway_with_flags (abfd, ".dynbss",
					      SEC_ALLOC | SEC_LINKER_CREATED);
      htab->root.sdynbss = dynbss_section;
      if (dynbss_section == NULL)
	return false;

      if (!bfd_link_pic (info))
	{
	  const char *relbss_section_name = bed->default_use_rela_p ? ".rela.bss" : ".rel.bss";
	  if (!bfd_create_aligned_section(abfd, relbss_section_name, base_flags | SEC_READONLY, ptr_alignment, &htab->root.srelbss))
	    return false;
	}
    }

  if (htab->root.target_os == is_vxworks)
    {
      if (!elf_vxworks_create_dynamic_sections (abfd, info, &htab->srelplt2))
	return false;
    }

  return true;
}

/* Adjust a symbol defined by a dynamic object and referenced by a
   regular object.  The current definition is in some section of the
   dynamic object, but we're not including those sections.  We have to
   change the definition to something the rest of the link can
   understand.  */

static bool
sh_elf_adjust_dynamic_symbol (struct bfd_link_info *info,
			      struct elf_link_hash_entry *h)
{
  struct elf_sh_link_hash_table *htab;
  asection *s;

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  BFD_ASSERT (htab->root.dynobj != NULL
	      && (h->needs_plt
		  || h->is_weakalias
		  || (h->def_dynamic
		      && h->ref_regular
		      && !h->def_regular)));

  if (h->type == STT_FUNC || h->needs_plt)
    {
      if (h->plt.refcount <= 0
	  || SYMBOL_CALLS_LOCAL (info, h)
	  || (ELF_ST_VISIBILITY (h->other) != STV_DEFAULT
	      && h->root.type == bfd_link_hash_undefweak))
	{
	  h->plt.offset = (bfd_vma) -1;
	  h->needs_plt = 0;
	}
      return true;
    }
  else
    {
      h->plt.offset = (bfd_vma) -1;
    }

  if (h->is_weakalias)
    {
      struct elf_link_hash_entry *def = weakdef (h);
      BFD_ASSERT (def->root.type == bfd_link_hash_defined);
      h->root.u.def.section = def->root.u.def.section;
      h->root.u.def.value = def->root.u.def.value;
      if (info->nocopyreloc)
	h->non_got_ref = def->non_got_ref;
      return true;
    }

  if (bfd_link_pic (info) || !h->non_got_ref)
    {
      return true;
    }

  s = htab->root.sdynbss;
  BFD_ASSERT (s != NULL);

  if ((h->root.u.def.section->flags & SEC_ALLOC) != 0 && h->size != 0)
    {
      asection *srel;

      srel = htab->root.srelbss;
      BFD_ASSERT (srel != NULL);
      srel->size += sizeof (Elf32_External_Rela);
      h->needs_copy = 1;
    }

  return _bfd_elf_adjust_dynamic_copy (info, h, s);
}

/* Allocate space in .plt, .got and associated reloc sections for
   dynamic relocs.  */

static bool record_dynamic_symbol_if_needed(struct bfd_link_info *info, struct elf_link_hash_entry *h) {
  if (h->dynindx == -1 && !h->forced_local) {
    return bfd_elf_link_record_dynamic_symbol(info, h);
  }
  return true;
}

static bool handle_plt_allocation(struct bfd_link_info *info,
                                   struct elf_link_hash_entry *h,
                                   struct elf_sh_link_hash_table *htab,
                                   struct elf_sh_link_hash_entry *eh) {
  h->plt.offset = (bfd_vma) -1;
  h->needs_plt = 0;

  if (!htab->root.dynamic_sections_created || h->plt.refcount == 0) {
    return true;
  }

  if (ELF_ST_VISIBILITY(h->other) != STV_DEFAULT && h->root.type == bfd_link_hash_undefweak) {
    return true;
  }

  if (!record_dynamic_symbol_if_needed(info, h)) {
    return false;
  }

  if (bfd_link_pic(info) || WILL_CALL_FINISH_DYNAMIC_SYMBOL(1, 0, h)) {
    asection *s = htab->root.splt;
    const struct elf_sh_plt_info *plt_info = htab->plt_info;

    if (s->size == 0) {
      s->size += plt_info->plt0_entry_size;
    }

    h->plt.offset = s->size;

    if (!htab->fdpic_p && !bfd_link_pic(info) && !h->def_regular) {
      h->root.u.def.section = s;
      h->root.u.def.value = h->plt.offset;
    }

    if (plt_info->short_plt != NULL && get_plt_index(plt_info->short_plt, s->size) < MAX_SHORT_PLT) {
      plt_info = plt_info->short_plt;
    }
    s->size += plt_info->symbol_entry_size;

    htab->root.sgotplt->size += htab->fdpic_p ? 8 : 4;
    htab->root.srelplt->size += sizeof(Elf32_External_Rela);

    if (htab->root.target_os == is_vxworks && !bfd_link_pic(info)) {
      if (h->plt.offset == htab->plt_info->plt0_entry_size) {
        htab->srelplt2->size += sizeof(Elf32_External_Rela);
      }
      htab->srelplt2->size += sizeof(Elf32_External_Rela) * 2;
    }
    h->needs_plt = 1;
  }
  return true;
}

static bool handle_got_allocation(struct bfd_link_info *info,
                                  struct elf_link_hash_entry *h,
                                  struct elf_sh_link_hash_table *htab,
                                  struct elf_sh_link_hash_entry *eh) {
  h->got.offset = (bfd_vma) -1;

  if (h->got.refcount == 0) {
    return true;
  }

  if (!record_dynamic_symbol_if_needed(info, h)) {
    return false;
  }

  asection *s = htab->root.sgot;
  enum got_type got_type = sh_elf_hash_entry(h)->got_type;

  h->got.offset = s->size;
  s->size += 4;
  if (got_type == GOT_TLS_GD) {
    s->size += 4;
  }

  bool dyn_sections_created = htab->root.dynamic_sections_created;
  bool is_pic = bfd_link_pic(info);
  bool is_undef_weak = (h->root.type == bfd_link_hash_undefweak);
  bool is_default_visibility = (ELF_ST_VISIBILITY(h->other) == STV_DEFAULT);

  if (!dyn_sections_created) {
    if (htab->fdpic_p && !is_pic && !is_undef_weak && (got_type == GOT_NORMAL || got_type == GOT_FUNCDESC)) {
      htab->srofixup->size += 4;
    }
  } else if (got_type == GOT_TLS_IE && !h->def_dynamic && !is_pic) {
    
  } else if ((got_type == GOT_TLS_GD && h->dynindx == -1) || got_type == GOT_TLS_IE) {
    htab->root.srelgot->size += sizeof(Elf32_External_Rela);
  } else if (got_type == GOT_TLS_GD) {
    htab->root.srelgot->size += 2 * sizeof(Elf32_External_Rela);
  } else if (got_type == GOT_FUNCDESC) {
    if (!is_pic && SYMBOL_FUNCDESC_LOCAL(info, h)) {
      htab->srofixup->size += 4;
    } else {
      htab->root.srelgot->size += sizeof(Elf32_External_Rela);
    }
  } else if ((is_default_visibility || !is_undef_weak) && (is_pic || WILL_CALL_FINISH_DYNAMIC_SYMBOL(dyn_sections_created, 0, h))) {
    htab->root.srelgot->size += sizeof(Elf32_External_Rela);
  } else if (htab->fdpic_p && !is_pic && got_type == GOT_NORMAL && (is_default_visibility || !is_undef_weak)) {
    htab->srofixup->size += 4;
  }
  return true;
}

static bool handle_abs_funcdesc_relocs(struct bfd_link_info *info,
                                        struct elf_link_hash_entry *h,
                                        struct elf_sh_link_hash_table *htab,
                                        struct elf_sh_link_hash_entry *eh) {
  if (eh->abs_funcdesc_refcount > 0) {
    bool is_undef_weak = (h->root.type == bfd_link_hash_undefweak);
    bool dyn_sections_created = htab->root.dynamic_sections_created;
    bool calls_local_symbol = SYMBOL_CALLS_LOCAL(info, h);

    if (!is_undef_weak || (dyn_sections_created && !calls_local_symbol)) {
      if (!bfd_link_pic(info) && SYMBOL_FUNCDESC_LOCAL(info, h)) {
        htab->srofixup->size += eh->abs_funcdesc_refcount * 4;
      } else {
        htab->root.srelgot->size += eh->abs_funcdesc_refcount * sizeof(Elf32_External_Rela);
      }
    }
  }
  return true;
}

static bool handle_funcdesc_allocation(struct bfd_link_info *info,
                                        struct elf_link_hash_entry *h,
                                        struct elf_sh_link_hash_table *htab,
                                        struct elf_sh_link_hash_entry *eh) {
  bool needs_funcdesc = (eh->funcdesc.refcount > 0 || (h->got.offset != MINUS_ONE && eh->got_type == GOT_FUNCDESC));
  bool is_undef_weak = (h->root.type == bfd_link_hash_undefweak);

  if (needs_funcdesc && !is_undef_weak && SYMBOL_FUNCDESC_LOCAL(info, h)) {
    eh->funcdesc.offset = htab->sfuncdesc->size;
    htab->sfuncdesc->size += 8;

    if (!bfd_link_pic(info) && SYMBOL_CALLS_LOCAL(info, h)) {
      htab->srofixup->size += 8;
    } else {
      htab->srelfuncdesc->size += sizeof(Elf32_External_Rela);
    }
  }
  return true;
}

static bool process_pic_dyn_relocs(struct bfd_link_info *info,
                                   struct elf_link_hash_entry *h,
                                   struct elf_sh_link_hash_table *htab,
                                   struct elf_sh_link_hash_entry *eh) {
  struct elf_dyn_relocs **pp;
  struct elf_dyn_relocs *p;

  if (SYMBOL_CALLS_LOCAL(info, h)) {
    pp = &h->dyn_relocs;
    while ((p = *pp) != NULL) {
      p->count -= p->pc_count;
      p->pc_count = 0;
      if (p->count == 0) {
        *pp = p->next;
      } else {
        pp = &p->next;
      }
    }
  }

  if (htab->root.target_os == is_vxworks) {
    pp = &h->dyn_relocs;
    while ((p = *pp) != NULL) {
      if (strcmp(p->sec->output_section->name, ".tls_vars") == 0) {
        *pp = p->next;
      } else {
        pp = &p->next;
      }
    }
  }

  if (h->dyn_relocs != NULL && h->root.type == bfd_link_hash_undefweak) {
    if (ELF_ST_VISIBILITY(h->other) != STV_DEFAULT || UNDEFWEAK_NO_DYNAMIC_RELOC(info, h)) {
      h->dyn_relocs = NULL;
    } else {
      if (!record_dynamic_symbol_if_needed(info, h)) {
        return false;
      }
    }
  }
  return true;
}

static bool process_non_pic_dyn_relocs(struct bfd_link_info *info,
                                       struct elf_link_hash_entry *h,
                                       struct elf_sh_link_hash_table *htab,
                                       struct elf_sh_link_hash_entry *eh) {
  bool keep_dyn_relocs = false;

  if (!h->non_got_ref &&
      ((h->def_dynamic && !h->def_regular) ||
       (htab->root.dynamic_sections_created &&
        (h->root.type == bfd_link_hash_undefweak || h->root.type == bfd_link_hash_undefined)))) {

    if (!record_dynamic_symbol_if_needed(info, h)) {
      return false;
    }

    if (h->dynindx != -1) {
      keep_dyn_relocs = true;
    }
  }

  if (!keep_dyn_relocs) {
    h->dyn_relocs = NULL;
  }
  return true;
}

static bool allocate_final_dyn_relocs_space(struct bfd_link_info *info,
                                            struct elf_link_hash_entry *h,
                                            struct elf_sh_link_hash_table *htab) {
  bool is_pic = bfd_link_pic(info);

  for (struct elf_dyn_relocs *p = h->dyn_relocs; p != NULL; p = p->next) {
    asection *sreloc = elf_section_data(p->sec)->sreloc;
    sreloc->size += p->count * sizeof(Elf32_External_Rela);

    if (htab->fdpic_p && !is_pic) {
      htab->srofixup->size -= 4 * (p->count - p->pc_count);
    }
  }
  return true;
}


static bool
allocate_dynrelocs (struct elf_link_hash_entry *h, void *inf)
{
  struct bfd_link_info *info = (struct bfd_link_info *) inf;
  struct elf_sh_link_hash_table *htab;
  struct elf_sh_link_hash_entry *eh;

  if (h->root.type == bfd_link_hash_indirect)
    return true;

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  eh = (struct elf_sh_link_hash_entry *) h;

  if ((h->got.refcount > 0 || h->forced_local) && eh->gotplt_refcount > 0) {
    h->got.refcount += eh->gotplt_refcount;
    if (h->plt.refcount >= eh->gotplt_refcount) {
      h->plt.refcount -= eh->gotplt_refcount;
    } else {
      h->plt.refcount = 0;
    }
  }

  if (!handle_plt_allocation(info, h, htab, eh)) {
    return false;
  }

  if (!handle_got_allocation(info, h, htab, eh)) {
    return false;
  }

  if (!handle_abs_funcdesc_relocs(info, h, htab, eh)) {
    return false;
  }

  if (!handle_funcdesc_allocation(info, h, htab, eh)) {
    return false;
  }

  if (h->dyn_relocs == NULL) {
    return true;
  }

  if (bfd_link_pic(info)) {
    if (!process_pic_dyn_relocs(info, h, htab, eh)) {
      return false;
    }
  } else {
    if (!process_non_pic_dyn_relocs(info, h, htab, eh)) {
      return false;
    }
  }

  if (!allocate_final_dyn_relocs_space(info, h, htab)) {
    return false;
  }

  return true;
}

/* This function is called after all the input files have been read,
   and the input sections have been assigned to output sections.
   It's a convenient place to determine the PLT style.  */

static bool
sh_elf_early_size_sections (bfd *output_bfd, struct bfd_link_info *info)
{
  struct sh_elf_hash_table *hash_table = sh_elf_hash_table (info);

  hash_table->plt_info = get_plt_info (output_bfd, bfd_link_pic (info));

  return !hash_table->fdpic_p
         || bfd_link_relocatable (info)
         || bfd_elf_stack_segment_size (output_bfd, info, "__stacksize", DEFAULT_STACK_SIZE);
}

/* Set the sizes of the dynamic sections.  */

#define SH_ELF_GOT_ENTRY_SIZE 4
#define SH_ELF_FUNCDESC_ENTRY_SIZE 8
#define SH_ELF_GOTPLT_RESERVED_SIZE 12
#define SH_ELF_FDPIC_ROFIXUP_POINTER_SIZE 4
#define SH_ELF_TLS_LDM_GOT_ENTRY_SIZE 8

static bool
process_elf_dyn_relocs (struct elf_sh_link_hash_table *htab,
                        struct bfd_link_info *info,
                        asection *s)
{
  for (struct elf_dyn_relocs *p = elf_section_data (s)->local_dynrel;
       p != NULL;
       p = p->next)
    {
      if (!bfd_is_abs_section (p->sec) && bfd_is_abs_section (p->sec->output_section))
        {
          continue;
        }

      if (htab->root.target_os == is_vxworks && strcmp (p->sec->output_section->name, ".tls_vars") == 0)
        {
          continue;
        }

      if (p->count != 0)
        {
          asection *srel = elf_section_data (p->sec)->sreloc;
          srel->size += p->count * sizeof (Elf32_External_Rela);
          if ((p->sec->output_section->flags & SEC_READONLY) != 0)
            {
              info->flags |= DF_TEXTREL;
              info->callbacks->minfo (_("%pB: dynamic relocation in read-only section `%pA'\n"),
                                      p->sec->owner, p->sec);
            }

          if (htab->fdpic_p && !bfd_link_pic (info))
            {
              htab->srofixup->size -= (bfd_size_type)SH_ELF_GOT_ENTRY_SIZE * (p->count - p->pc_count);
            }
        }
    }
  return true;
}

static bool
process_local_got_entries (struct elf_sh_link_hash_table *htab,
                           struct bfd_link_info *info,
                           bfd *ibfd,
                           bfd_size_type locsymcount)
{
  bfd_signed_vma *local_got_refcounts = elf_local_got_refcounts (ibfd);
  if (local_got_refcounts == NULL || locsymcount == 0)
    return true;

  bfd_signed_vma *end_local_got_refcounts = local_got_refcounts + locsymcount;
  char *local_got_types = sh_elf_local_got_type (ibfd);
  union gotref *local_funcdesc_array = sh_elf_local_funcdesc (ibfd);

  asection *sgot = htab->root.sgot;
  asection *srelgot = htab->root.srelgot;

  for (bfd_signed_vma *current_got_refcount_ptr = local_got_refcounts;
       current_got_refcount_ptr < end_local_got_refcounts;
       ++current_got_refcount_ptr, ++local_got_types)
    {
      if (*current_got_refcount_ptr > 0)
        {
          *current_got_refcount_ptr = sgot->size;
          sgot->size += SH_ELF_GOT_ENTRY_SIZE;
          if (*local_got_types == GOT_TLS_GD)
            sgot->size += SH_ELF_GOT_ENTRY_SIZE;
          if (bfd_link_pic (info))
            srelgot->size += sizeof (Elf32_External_Rela);
          else
            htab->srofixup->size += SH_ELF_GOT_ENTRY_SIZE;

          if (*local_got_types == GOT_FUNCDESC)
            {
              if (local_funcdesc_array == NULL)
                {
                  bfd_size_type alloc_size = locsymcount * sizeof (union gotref);
                  local_funcdesc_array = (union gotref *) bfd_zalloc (ibfd, alloc_size);
                  if (local_funcdesc_array == NULL)
                    return false;
                  sh_elf_local_funcdesc (ibfd) = local_funcdesc_array;
                }
              union gotref *current_funcdesc_entry = local_funcdesc_array + (current_got_refcount_ptr - local_got_refcounts);
              current_funcdesc_entry->refcount++;
            }
        }
      else
        {
          *current_got_refcount_ptr = MINUS_ONE;
        }
    }
  return true;
}

static bool
process_local_funcdesc_entries (struct elf_sh_link_hash_table *htab,
                                struct bfd_link_info *info,
                                bfd *ibfd ATTRIBUTE_UNUSED,
                                bfd_size_type locsymcount)
{
  union gotref *local_funcdesc_array = sh_elf_local_funcdesc (ibfd);
  if (local_funcdesc_array == NULL || locsymcount == 0)
    return true;

  union gotref *end_local_funcdesc_array = local_funcdesc_array + locsymcount;

  for (union gotref *current_funcdesc_entry = local_funcdesc_array;
       current_funcdesc_entry < end_local_funcdesc_array;
       ++current_funcdesc_entry)
    {
      if (current_funcdesc_entry->refcount > 0)
        {
          current_funcdesc_entry->offset = htab->sfuncdesc->size;
          htab->sfuncdesc->size += SH_ELF_FUNCDESC_ENTRY_SIZE;
          if (!bfd_link_pic (info))
            htab->srofixup->size += SH_ELF_FUNCDESC_ENTRY_SIZE;
          else
            htab->srelfuncdesc->size += sizeof (Elf32_External_Rela);
        }
      else
        {
          current_funcdesc_entry->offset = MINUS_ONE;
        }
    }
  return true;
}

static bool
should_allocate_dynamic_section(struct elf_sh_link_hash_table *htab, asection *s, bool *relocs_needed)
{
    if ((s->flags & SEC_LINKER_CREATED) == 0)
        return false;

    if (s == htab->root.splt
        || s == htab->root.sgot
        || s == htab->root.sgotplt
        || s == htab->sfuncdesc
        || s == htab->srofixup
        || s == htab->root.sdynbss)
    {
        // These sections are handled further below based on their calculated size.
    }
    else if (startswith(bfd_section_name(s), ".rela"))
    {
        if (s->size != 0 && s != htab->root.srelplt && s != htab->srelplt2)
            *relocs_needed = true;

        s->reloc_count = 0;
    }
    else
    {
        return false;
    }

    if (s->size == 0)
    {
        s->flags |= SEC_EXCLUDE;
        return false;
    }

    return (s->flags & SEC_HAS_CONTENTS) != 0;
}

static bool
sh_elf_late_size_sections (bfd *output_bfd ATTRIBUTE_UNUSED,
                           struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  bfd *dynobj = htab->root.dynobj;
  if (dynobj == NULL)
    return true;

  if (htab->root.dynamic_sections_created)
    {
      if (bfd_link_executable (info) && !info->nointerp)
	{
	  asection *s_interp = bfd_get_linker_section (dynobj, ".interp");
	  BFD_ASSERT (s_interp != NULL);
	  s_interp->size = sizeof ELF_DYNAMIC_INTERPRETER;
	  s_interp->contents = (unsigned char *) ELF_DYNAMIC_INTERPRETER;
	  s_interp->alloced = 1;
	}
    }

  for (bfd *ibfd = info->input_bfds; ibfd != NULL; ibfd = ibfd->link.next)
    {
      if (! is_sh_elf (ibfd))
	    continue;

      for (asection *s = ibfd->sections; s != NULL; s = s->next)
	    {
	      if (!process_elf_dyn_relocs (htab, info, s))
            return false;
	    }

      Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr (ibfd);
      bfd_size_type locsymcount = symtab_hdr->sh_info;

      if (!process_local_got_entries (htab, info, ibfd, locsymcount))
        return false;

      if (!process_local_funcdesc_entries (htab, info, ibfd, locsymcount))
        return false;
    }

  if (htab->tls_ldm_got.refcount > 0)
    {
      htab->tls_ldm_got.offset = htab->root.sgot->size;
      htab->root.sgot->size += SH_ELF_TLS_LDM_GOT_ENTRY_SIZE;
      htab->root.srelgot->size += sizeof (Elf32_External_Rela);
    }
  else
    htab->tls_ldm_got.offset = MINUS_ONE;

  if (htab->fdpic_p)
    {
      BFD_ASSERT (htab->root.sgotplt && htab->root.sgotplt->size == SH_ELF_GOTPLT_RESERVED_SIZE);
      htab->root.sgotplt->size = 0;
    }

  elf_link_hash_traverse (&htab->root, allocate_dynrelocs, info);

  if (htab->fdpic_p)
    {
      htab->root.hgot->root.u.def.value = htab->root.sgotplt->size;
      htab->root.sgotplt->size += SH_ELF_GOTPLT_RESERVED_SIZE;
    }

  if (htab->fdpic_p && htab->srofixup != NULL)
    htab->srofixup->size += SH_ELF_FDPIC_ROFIXUP_POINTER_SIZE;

  bool relocs_needed = false;
  for (asection *s = dynobj->sections; s != NULL; s = s->next)
    {
      if (!should_allocate_dynamic_section(htab, s, &relocs_needed))
        continue;

      s->contents = (bfd_byte *) bfd_zalloc (dynobj, s->size);
      if (s->contents == NULL)
        return false;
      s->alloced = 1;
    }

  return _bfd_elf_maybe_vxworks_add_dynamic_tags (output_bfd, info,
                                                  relocs_needed);
}

/* Add a dynamic relocation to the SRELOC section.  */

inline static bfd_vma
sh_elf_add_dyn_reloc (bfd *output_bfd, asection *sreloc, bfd_vma offset,
		      int reloc_type, long dynindx, bfd_vma addend)
{
  Elf_Internal_Rela outrel;
  bfd_vma reloc_offset;
  bfd_vma unit_size = (bfd_vma) sizeof (Elf32_External_Rela);
  bfd_vma count = sreloc->reloc_count;

  outrel.r_offset = offset;
  outrel.r_info = ELF32_R_INFO (dynindx, reloc_type);
  outrel.r_addend = addend;

  BFD_ASSERT(unit_size != 0);

  BFD_ASSERT(count <= BFD_VMA_MAX / unit_size);

  reloc_offset = count * unit_size;

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
  bfd_vma current_reloc_index = srofixup->reloc_count;
  bfd_vma calculated_offset;

  if (current_reloc_index > ((bfd_vma)-1 / 4))
    {
      BFD_ASSERT (0 && "bfd: Integer overflow in fixup_offset calculation");
      return;
    }

  calculated_offset = current_reloc_index * 4;
  srofixup->reloc_count++;

  BFD_ASSERT (calculated_offset < srofixup->size);
  BFD_ASSERT (srofixup->size >= 4);
  BFD_ASSERT (srofixup->contents != NULL);

  bfd_put_32 (output_bfd, offset, srofixup->contents + calculated_offset);
}

/* Return the offset of the generated .got section from the
   _GLOBAL_OFFSET_TABLE_ symbol.  */

static bfd_signed_vma
sh_elf_got_offset (struct elf_sh_link_hash_table *htab)
{
  if (htab == NULL)
    {
      return 0;
    }

  if (htab->root.sgot == NULL)
    {
      return 0;
    }
  bfd_signed_vma sgot_output_offset = htab->root.sgot->output_offset;

  if (htab->root.sgotplt == NULL)
    {
      return 0;
    }
  bfd_signed_vma sgotplt_output_offset = htab->root.sgotplt->output_offset;

  if (htab->root.hgot == NULL)
    {
      return 0;
    }
  bfd_signed_vma hgot_def_value = htab->root.hgot->root.u.def.value;

  return (sgot_output_offset - sgotplt_output_offset - hgot_def_value);
}

/* Find the segment number in which OSEC, and output section, is
   located.  */

static int
sh_elf_osec_to_segment (bfd *output_bfd, asection *osec)
{
  Elf_Internal_Phdr *p = NULL;

  if (output_bfd->xvec->flavour == bfd_target_elf_flavour
      && output_bfd->direction != read_direction)
    p = _bfd_elf_find_segment_containing_section (output_bfd, osec);

  return (p != NULL) ? (int)(p - elf_tdata (output_bfd)->phdr) : -1;
}

static bool
sh_elf_osec_readonly_p (bfd *output_bfd, asection *osec)
{
  const unsigned int ELF_INVALID_SEGMENT = (unsigned int) -1;

  if (output_bfd == NULL) {
    return false;
  }

  struct bfd_elf_obj_data *elf_data = elf_tdata (output_bfd);
  if (elf_data == NULL || elf_data->phdr == NULL) {
    return false;
  }

  unsigned seg = sh_elf_osec_to_segment (output_bfd, osec);

  if (seg == ELF_INVALID_SEGMENT || seg >= elf_data->ehdr.e_phnum) {
    return false;
  }

  return ! (elf_data->phdr[seg].p_flags & PF_W);
}

/* Generate the initial contents of a local function descriptor, along
   with any relocations or fixups required.  */
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
  bfd_vma addr;
  bfd_vma seg;
  asection *resolved_section;
  bfd_vma resolved_value;
  bool is_local_symbol;

  htab = sh_elf_hash_table (info);

  is_local_symbol = (h == NULL || SYMBOL_CALLS_LOCAL (info, h));

  resolved_section = section;
  resolved_value = value;
  if (h != NULL && SYMBOL_CALLS_LOCAL (info, h))
    {
      resolved_section = h->root.u.def.section;
      resolved_value = h->root.u.def.value;
    }

  if (is_local_symbol)
    {
      dynindx = elf_section_data (resolved_section->output_section)->dynindx;
      addr = resolved_value + resolved_section->output_offset;
      seg = sh_elf_osec_to_segment (output_bfd, resolved_section->output_section);
    }
  else
    {
      BFD_ASSERT (h->dynindx != -1);
      dynindx = h->dynindx;
      addr = 0;
      seg = 0;
    }

  bfd_vma funcdesc_base_output_addr = htab->sfuncdesc->output_section->vma
                                     + htab->sfuncdesc->output_offset;
  bfd_vma funcdesc_value_location = offset + funcdesc_base_output_addr;
  bfd_vma funcdesc_seg_location = offset + 4 + funcdesc_base_output_addr;

  if (!bfd_link_pic (info) && is_local_symbol)
    {
      if (h == NULL || h->root.type != bfd_link_hash_undefweak)
	{
	  sh_elf_add_rofixup (output_bfd, htab->srofixup, funcdesc_value_location);
	  sh_elf_add_rofixup (output_bfd, htab->srofixup, funcdesc_seg_location);
	}

      addr += resolved_section->output_section->vma;
      seg = htab->root.hgot->root.u.def.value
	+ htab->root.hgot->root.u.def.section->output_section->vma
	+ htab->root.hgot->root.u.def.section->output_offset;
    }
  else
    {
      sh_elf_add_dyn_reloc (output_bfd, htab->srelfuncdesc,
			    funcdesc_value_location, R_SH_FUNCDESC_VALUE, dynindx, 0);
    }

  bfd_put_32 (output_bfd, addr, htab->sfuncdesc->contents + offset);
  bfd_put_32 (output_bfd, seg, htab->sfuncdesc->contents + offset + 4);

  return true;
}

/* Install a 20-bit movi20 field starting at ADDR, which occurs in OUTPUT_BFD.
   VALUE is the field's value.  Return bfd_reloc_ok if successful or an error
   otherwise.  */

static bfd_reloc_status_type
install_movi20_field (bfd *output_bfd, unsigned long relocation,
		      bfd *input_bfd, asection *input_section,
		      bfd_byte *contents, bfd_vma offset)
{
  bfd_reloc_status_type status;

  const bfd_vma required_bytes = 4;
  const bfd_vma section_data_size = bfd_get_section_limit(input_bfd, input_section);

  if (section_data_size < required_bytes) {
    return bfd_reloc_outofrange;
  }
  if (offset > section_data_size - required_bytes) {
    return bfd_reloc_outofrange;
  }

  status = bfd_check_overflow (complain_overflow_signed, 20, 0,
			       bfd_arch_bits_per_address (input_bfd), relocation);
  if (status != bfd_reloc_ok) {
    return status;
  }

  bfd_byte *target_addr = contents + offset;

  unsigned int relocation_high_4_bits_shifted = (unsigned int)((relocation & 0xF0000UL) >> 12);
  unsigned int relocation_low_16_bits = (unsigned int)(relocation & 0xFFFFUL);

  unsigned int current_word_at_addr = bfd_get_16(output_bfd, target_addr);

  unsigned int new_word_at_addr = current_word_at_addr | relocation_high_4_bits_shifted;

  bfd_put_16(output_bfd, new_word_at_addr, target_addr);
  bfd_put_16(output_bfd, relocation_low_16_bits, target_addr + 2);

  return bfd_reloc_ok;
}

/* Relocate an SH ELF section.  */

static bool
validate_reloc_type_range (int r_type, bfd *abfd, asection *sec, bfd_vma offset)
{
  if (r_type < 0
      || r_type >= (int) R_SH_max
      || (r_type >= (int) R_SH_FIRST_INVALID_RELOC
	  && r_type <= (int) R_SH_LAST_INVALID_RELOC)
      || (r_type >= (int) R_SH_FIRST_INVALID_RELOC_2
	  && r_type <= (int) R_SH_LAST_INVALID_RELOC_2)
      || (r_type >= (int) R_SH_FIRST_INVALID_RELOC_3
	  && r_type <= (int) R_SH_LAST_INVALID_RELOC_3)
      || (r_type >= (int) R_SH_FIRST_INVALID_RELOC_4
	  && r_type <= (int) R_SH_LAST_INVALID_RELOC_4)
      || (r_type >= (int) R_SH_FIRST_INVALID_RELOC_5
	  && r_type <= (int) R_SH_LAST_INVALID_RELOC_5)
      || (r_type >= (int) R_SH_FIRST_INVALID_RELOC_6
	  && r_type <= (int) R_SH_LAST_INVALID_RELOC_6))
    {
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
resolve_relocation_symbol_info (bfd *output_bfd, struct bfd_link_info *info,
                                bfd *input_bfd, asection *input_section,
                                Elf_Internal_Rela *rel, unsigned long r_symndx,
                                Elf_Internal_Sym *local_syms,
                                asection **local_sections, Elf_Internal_Shdr *symtab_hdr,
                                struct elf_link_hash_entry **sym_hashes,
                                reloc_howto_type *howto, bfd_byte *contents,
                                struct elf_link_hash_entry **ph, Elf_Internal_Sym **psym,
                                asection **psec, bfd_vma *prelocation,
                                const char **psymname, bool *presolved_to_zero,
                                bfd_vma *paddend)
{
  *ph = NULL;
  *psym = NULL;
  *psec = NULL;
  *presolved_to_zero = false;
  *prelocation = 0;

  if (r_symndx < symtab_hdr->sh_info)
    {
      *psym = local_syms + r_symndx;
      *psec = local_sections[r_symndx];

      *psymname = bfd_elf_string_from_elf_section
	(input_bfd, symtab_hdr->sh_link, (*psym)->st_name);
      if (*psymname == NULL || **psymname == '\0')
	*psymname = bfd_section_name (*psec);

      *prelocation = ((*psec)->output_section->vma
		      + (*psec)->output_offset
		      + (*psym)->st_value);

      if (*psec != NULL && discarded_section (*psec))
	{
	  RELOC_AGAINST_DISCARDED_SECTION (info, input_bfd, input_section,
					   rel, 1, rel + 1, R_SH_NONE,
					   howto, 0, contents);
	}
      else if (bfd_link_relocatable (info))
	{
	  if (ELF_ST_TYPE ((*psym)->st_info) == STT_SECTION)
	    {
	      if (!howto->partial_inplace)
		{
		  rel->r_addend += (*psec)->output_offset;
		  return true;
		}
	      _bfd_relocate_contents (howto, input_bfd,
				      (*psec)->output_offset + (*psym)->st_value,
				      contents + rel->r_offset);
	    }
	  return true;
	}
      else if (!howto->partial_inplace)
	{
	  *prelocation = _bfd_elf_rela_local_sym (output_bfd, *psym, psec, rel);
	  *paddend = rel->r_addend;
	}
      else if (((*psec)->flags & SEC_MERGE)
	       && ELF_ST_TYPE ((*psym)->st_info) == STT_SECTION)
	{
	  asection *msec;

	  if (howto->rightshift || howto->src_mask != 0xffffffff)
	    {
	      _bfd_error_handler
		(_("%pB(%pA+%#" PRIx64 "): "
		   "%s relocation against SEC_MERGE section"),
		 input_bfd, input_section,
		 (uint64_t) rel->r_offset, howto->name);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }

	  *paddend = bfd_get_32 (input_bfd, contents + rel->r_offset);
	  msec = *psec;
	  *paddend = (_bfd_elf_rel_local_sym (output_bfd, *psym, &msec, *paddend)
		      - *prelocation);
	  *paddend += msec->output_section->vma + msec->output_offset;
	  bfd_put_32 (input_bfd, *paddend, contents + rel->r_offset);
	  *paddend = 0;
	}
    }
  else
    {
      *ph = sym_hashes[r_symndx - symtab_hdr->sh_info];
      *psymname = (*ph)->root.root.string;
      while ((*ph)->root.type == bfd_link_hash_indirect
	     || (*ph)->root.type == bfd_link_hash_warning)
	*ph = (struct elf_link_hash_entry *) (*ph)->root.u.i.link;
      if ((*ph)->root.type == bfd_link_hash_defined
	  || (*ph)->root.type == bfd_link_hash_defweak)
	{
	  *psec = (*ph)->root.u.def.section;
	  if (! (r_type == R_SH_GOTPC
		 || r_type == R_SH_GOTPC_LOW16
		 || r_type == R_SH_GOTPC_MEDLOW16
		 || r_type == R_SH_GOTPC_MEDHI16
		 || r_type == R_SH_GOTPC_HI16
		 || ((r_type == R_SH_PLT32
		      || r_type == R_SH_PLT_LOW16
		      || r_type == R_SH_PLT_MEDLOW16
		      || r_type == R_SH_PLT_MEDHI16
		      || r_type == R_SH_PLT_HI16)
		     && (*ph)->plt.offset != (bfd_vma) -1)
		 || ((r_type == R_SH_GOT32
		      || r_type == R_SH_GOT20
		      || r_type == R_SH_GOTFUNCDESC
		      || r_type == R_SH_GOTFUNCDESC20
		      || r_type == R_SH_GOTOFFFUNCDESC
		      || r_type == R_SH_GOTOFFFUNCDESC20
		      || r_type == R_SH_FUNCDESC
		      || r_type == R_SH_GOT_LOW16
		      || r_type == R_SH_GOT_MEDLOW16
		      || r_type == R_SH_GOT_MEDHI16
		      || r_type == R_SH_GOT_HI16)
		     && WILL_CALL_FINISH_DYNAMIC_SYMBOL (info->callbacks->htab->root.dynamic_sections_created,
							 bfd_link_pic (info),
							 *ph)
		     && (! bfd_link_pic (info)
			 || (! info->symbolic && (*ph)->dynindx != -1)
			 || !(*ph)->def_regular))
		 || (bfd_link_pic (info)
		     && ((! info->symbolic && (*ph)->dynindx != -1)
			 || !(*ph)->def_regular)
		     && ((r_type == R_SH_DIR32
			  && !(*ph)->forced_local)
			 || (r_type == R_SH_REL32
			     && !SYMBOL_CALLS_LOCAL (info, *ph)))
		     && (((*psec)->flags & SEC_ALLOC) != 0
			 || (((*psec)->flags & SEC_DEBUGGING) != 0
			     && (*ph)->def_dynamic)))
		 || ((*psec)->output_section == NULL
		     && (((*psec)->flags & SEC_DEBUGGING) != 0
			 && (*ph)->def_dynamic))
		 || ((*psec)->output_section == NULL
		     && (sh_elf_hash_entry (*ph)->got_type == GOT_TLS_IE
			 || sh_elf_hash_entry (*ph)->got_type == GOT_TLS_GD))))
	    ;
	  else if ((*psec)->output_section != NULL)
	    *prelocation = ((*ph)->root.u.def.value
			    + (*psec)->output_section->vma
			    + (*psec)->output_offset);
	  else if (!bfd_link_relocatable (info)
		   && (_bfd_elf_section_offset (output_bfd, info,
						input_section,
						rel->r_offset)
		       != (bfd_vma) -1))
	    {
	      _bfd_error_handler
		(_("%pB(%pA+%#" PRIx64 "): "
		   "unresolvable %s relocation against symbol `%s'"),
		 input_bfd,
		 input_section,
		 (uint64_t) rel->r_offset,
		 howto->name,
		 (*ph)->root.root.string);
	      return false;
	    }
	}
      else if ((*ph)->root.type == bfd_link_hash_undefweak)
	*presolved_to_zero = UNDEFWEAK_NO_DYNAMIC_RELOC (info, *ph);
      else if (info->unresolved_syms_in_objects == RM_IGNORE
	       && ELF_ST_VISIBILITY ((*ph)->other) == STV_DEFAULT)
	;
      else if (!bfd_link_relocatable (info))
        info->callbacks->undefined_symbol
	      (info, (*ph)->root.root.string, input_bfd, input_section,
	       rel->r_offset,
	       (info->unresolved_syms_in_objects == RM_DIAGNOSE
		&& !info->warn_unresolved_syms)
	       || ELF_ST_VISIBILITY ((*ph)->other));
    }
  return true;
}

static bfd_reloc_status_type
handle_dir8wp_reloc (bfd *output_bfd, bfd *input_bfd, asection *input_section,
                     bfd_byte *contents, Elf_Internal_Rela *rel,
                     reloc_howto_type *howto, bfd_vma relocation, bfd_vma addend,
                     int r_type)
{
  if (input_section->output_section->vma + input_section->output_offset
      != relocation)
    {
      int disp = (relocation
		  - input_section->output_section->vma
		  - input_section->output_offset
		  - rel->r_offset);
      int mask = 0;
      switch (r_type)
	{
	case R_SH_DIR8WPN:
	case R_SH_DIR8WPZ: mask = 1; break;
	case R_SH_DIR8WPL: mask = 3; break;
	default: break; // Should not happen based on caller
	}
      if (disp & mask)
	{
	  _bfd_error_handler
	    (_("%pB: %#" PRIx64 ": fatal: "
	       "unaligned branch target for relax-support relocation"),
	     input_section->owner,
	     (uint64_t) rel->r_offset);
	  bfd_set_error (bfd_error_bad_value);
	  return bfd_reloc_outofrange; // Indicate fatal error
	}
      relocation -= 4;
      return _bfd_final_link_relocate (howto, input_bfd, input_section,
				       contents, rel->r_offset,
				       relocation, addend);
    }
  return bfd_reloc_ok;
}

static bool
handle_unaligned_reloc_check (bfd *abfd, asection *sec, bfd_vma offset,
                              reloc_howto_type *howto, bfd_vma relocation, int align_mask)
{
  if (relocation & align_mask)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": fatal: "
	   "unaligned %s relocation %#" PRIx64),
	 sec->owner, (uint64_t) offset,
	 howto->name, (uint64_t) relocation);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
handle_psha_pshl_reloc_check (bfd *abfd, asection *sec, bfd_vma offset,
                              int r_type, bfd_vma relocation)
{
  int min_range, max_range;
  const char *msg;
  if (r_type == R_SH_PSHA)
    {
      min_range = -32;
      max_range = 32;
      msg = _("%pB: %#" PRIx64 ": fatal: R_SH_PSHA relocation %" PRId64
	      " not in range -32..32");
    }
  else
    { /* R_SH_PSHL */
      min_range = -16;
      max_range = 16;
      msg = _("%pB: %#" PRIx64 ": fatal: R_SH_PSHL relocation %" PRId64
	      " not in range -32..32"); /* Original text bug, was 32 */
    }

  if ((signed int)relocation < min_range || (signed int)relocation > max_range)
    {
      _bfd_error_handler (msg, sec->owner, (uint64_t) offset, (int64_t) relocation);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  return true;
}

static bool
handle_dir32_rel32_reloc (bfd *output_bfd, struct bfd_link_info *info,
                          bfd *input_bfd, asection *input_section,
                          bfd_byte *contents, Elf_Internal_Rela *rel,
                          reloc_howto_type *howto,
                          struct elf_sh_link_hash_table *htab,
                          struct elf_link_hash_entry *h, asection *sec,
                          bool is_vxworks_tls, bool fdpic_p,
                          bfd_vma *prelocation, bfd_vma *paddend,
                          asection **psreloc, unsigned *pcheck_segment0,
                          unsigned *pcheck_segment1, bool resolved_to_zero)
{
  int r_type = ELF32_R_TYPE (rel->r_info);

  if (bfd_link_pic (info)
      && (h == NULL
	  || (ELF_ST_VISIBILITY (h->other) == STV_DEFAULT
	      && !resolved_to_zero)
	  || h->root.type != bfd_link_hash_undefweak)
      && ELF32_R_SYM (rel->r_info) != STN_UNDEF
      && (input_section->flags & SEC_ALLOC) != 0
      && !is_vxworks_tls
      && (r_type == R_SH_DIR32
	  || !SYMBOL_CALLS_LOCAL (info, h)))
    {
      Elf_Internal_Rela outrel;
      bfd_byte *loc;
      bool skip_reloc, relocate_contents = false;

      if (*psreloc == NULL)
	{
	  *psreloc = _bfd_elf_get_dynamic_reloc_section
	    (input_bfd, input_section, /*rela?*/ true);
	  if (*psreloc == NULL)
	    return false;
	}

      skip_reloc = false;
      outrel.r_offset = _bfd_elf_section_offset (output_bfd, info, input_section,
						 rel->r_offset);
      if (outrel.r_offset == (bfd_vma) -1)
	skip_reloc = true;
      else if (outrel.r_offset == (bfd_vma) -2)
	skip_reloc = true, relocate_contents = true;
      outrel.r_offset += (input_section->output_section->vma
			  + input_section->output_offset);

      if (skip_reloc)
	memset (&outrel, 0, sizeof outrel);
      else if (r_type == R_SH_REL32)
	{
	  BFD_ASSERT (h != NULL && h->dynindx != -1);
	  outrel.r_info = ELF32_R_INFO (h->dynindx, R_SH_REL32);
	  outrel.r_addend = (howto->partial_inplace
			     ? bfd_get_32 (input_bfd, contents + rel->r_offset)
			     : *paddend);
	}
      else if (fdpic_p
	       && (h == NULL
		   || ((info->symbolic || h->dynindx == -1)
		       && h->def_regular)))
	{
	  int dynindx;
	  BFD_ASSERT (sec != NULL);
	  BFD_ASSERT (sec->output_section != NULL);
	  dynindx = elf_section_data (sec->output_section)->dynindx;
	  outrel.r_info = ELF32_R_INFO (dynindx, R_SH_DIR32);
	  outrel.r_addend = *prelocation;
	  outrel.r_addend += (howto->partial_inplace
			      ? bfd_get_32 (input_bfd, contents + rel->r_offset)
			      : *paddend);
	  outrel.r_addend -= sec->output_section->vma;
	}
      else
	{
	  if (h == NULL
	      || ((info->symbolic || h->dynindx == -1)
		  && h->def_regular))
	    {
	      relocate_contents = howto->partial_inplace;
	      outrel.r_info = ELF32_R_INFO (0, R_SH_RELATIVE);
	    }
	  else
	    {
	      BFD_ASSERT (h->dynindx != -1);
	      outrel.r_info = ELF32_R_INFO (h->dynindx, R_SH_DIR32);
	    }
	  outrel.r_addend = *prelocation;
	  outrel.r_addend += (howto->partial_inplace
			      ? bfd_get_32 (input_bfd, contents + rel->r_offset)
			      : *paddend);
	}

      loc = (*psreloc)->contents;
      loc += (*psreloc)->reloc_count++ * sizeof (Elf32_External_Rela);
      bfd_elf32_swap_reloca_out (output_bfd, &outrel, loc);

      *pcheck_segment0 = (unsigned) -1;
      *pcheck_segment1 = (unsigned) -1;

      if (!relocate_contents)
	return true; // continue in main loop
    }
  else if (fdpic_p && !bfd_link_pic (info)
	   && r_type == R_SH_DIR32
	   && (input_section->flags & SEC_ALLOC) != 0)
    {
      bfd_vma offset;

      BFD_ASSERT (htab);

      if (sh_elf_osec_readonly_p (output_bfd,
				  input_section->output_section))
	{
	  _bfd_error_handler
	    (_("%pB(%pA+%#" PRIx64 "): "
	       "cannot emit fixup to `%s' in read-only section"),
	     input_bfd,
	     input_section,
	     (uint64_t) rel->r_offset,
	     *psymname);
	  return false;
	}

      offset = _bfd_elf_section_offset (output_bfd, info,
					input_section, rel->r_offset);
      if (offset != (bfd_vma)-1)
	sh_elf_add_rofixup (output_bfd, htab->srofixup,
			    input_section->output_section->vma
			    + input_section->output_offset
			    + rel->r_offset);

      *pcheck_segment0 = (unsigned) -1;
      *pcheck_segment1 = (unsigned) -1;
    }
  else if (r_type == R_SH_REL32
	   && h && h->root.type == bfd_link_hash_undefweak)
    {
      *pcheck_segment0 = (unsigned) -1;
      *pcheck_segment1 = (unsigned) -1;
    }
  return false; // means continue to final_link_relocate
}

static bool
handle_gotplt32_and_got_reloc (bfd *output_bfd, struct bfd_link_info *info,
                               bfd *input_bfd, asection *input_section,
                               bfd_byte *contents, Elf_Internal_Rela *rel,
                               reloc_howto_type *howto,
                               struct elf_sh_link_hash_table *htab,
                               struct elf_link_hash_entry *h, Elf_Internal_Sym *sym,
                               asection *sec, bfd_vma *local_got_offsets,
                               bfd_vma *prelocation, bfd_vma *paddend,
                               int r_type, bool resolved_to_zero,
                               unsigned *pcheck_segment0, unsigned *pcheck_segment1,
                               asection **psrelgot)
{
  bfd_vma off;
  bool dyn;
  enum got_type got_type_val;

  *pcheck_segment0 = (unsigned) -1;
  *pcheck_segment1 = (unsigned) -1;

  if (r_type == R_SH_GOTPLT32)
    {
      if (h == NULL
	  || h->forced_local
	  || !bfd_link_pic (info)
	  || info->symbolic
	  || h->dynindx == -1
	  || h->plt.offset == (bfd_vma) -1
	  || h->got.offset != (bfd_vma) -1)
	r_type = R_SH_GOT32; // Force to GOT32 logic
    }

  if (r_type == R_SH_GOTPLT32)
    {
      BFD_ASSERT (htab && htab->root.sgotplt != NULL);
      *prelocation = (htab->root.sgotplt->output_offset
		      + (get_plt_index (htab->plt_info, h->plt.offset)
			 + 3) * 4);
#ifdef GOT_BIAS
      *prelocation -= GOT_BIAS;
#endif
      return false; // continue to final_link_relocate
    }

  /* R_SH_GOT32 or R_SH_GOT20 or forced GOTPLT32 */
  BFD_ASSERT (htab && htab->root.sgot != NULL);

  if (h != NULL)
    {
      off = h->got.offset;
      BFD_ASSERT (off != (bfd_vma) -1);

      dyn = htab->root.dynamic_sections_created;
      if (!WILL_CALL_FINISH_DYNAMIC_SYMBOL (dyn, bfd_link_pic (info), h)
	  || (bfd_link_pic (info) && SYMBOL_REFERENCES_LOCAL (info, h))
	  || ((ELF_ST_VISIBILITY (h->other) || resolved_to_zero)
	      && h->root.type == bfd_link_hash_undefweak))
	{
	  if ((off & 1) != 0)
	    off &= ~1;
	  else
	    {
	      bfd_put_32 (output_bfd, *prelocation, htab->root.sgot->contents + off);
	      h->got.offset |= 1;

	      if (htab->fdpic_p && !bfd_link_pic (info)
		  && sh_elf_hash_entry (h)->got_type == GOT_NORMAL
		  && (ELF_ST_VISIBILITY (h->other) == STV_DEFAULT
		      || h->root.type != bfd_link_hash_undefweak))
		sh_elf_add_rofixup (output_bfd, htab->srofixup,
				    htab->root.sgot->output_section->vma
				    + htab->root.sgot->output_offset
				    + off);
	    }
	}
      *prelocation = sh_elf_got_offset (htab) + off;
    }
  else
    {
      BFD_ASSERT (local_got_offsets != NULL
		  && local_got_offsets[ELF32_R_SYM (rel->r_info)] != (bfd_vma) -1);

      off = local_got_offsets[ELF32_R_SYM (rel->r_info)];

      if ((off & 1) != 0)
	off &= ~1;
      else
	{
	  bfd_put_32 (output_bfd, *prelocation, htab->root.sgot->contents + off);

	  if (bfd_link_pic (info))
	    {
	      Elf_Internal_Rela outrel;
	      bfd_byte *loc;

	      outrel.r_offset = (htab->root.sgot->output_section->vma
				 + htab->root.sgot->output_offset
				 + off);
	      if (htab->fdpic_p)
		{
		  int dynindx = elf_section_data (sec->output_section)->dynindx;
		  outrel.r_info = ELF32_R_INFO (dynindx, R_SH_DIR32);
		  outrel.r_addend = *prelocation;
		  outrel.r_addend -= sec->output_section->vma;
		}
	      else
		{
		  outrel.r_info = ELF32_R_INFO (0, R_SH_RELATIVE);
		  outrel.r_addend = *prelocation;
		}
	      loc = (*psrelgot)->contents;
	      loc += (*psrelgot)->reloc_count++ * sizeof (Elf32_External_Rela);
	      bfd_elf32_swap_reloca_out (output_bfd, &outrel, loc);
	    }
	  else if (htab->fdpic_p
		   && (sh_elf_local_got_type (input_bfd) [ELF32_R_SYM (rel->r_info)]
		       == GOT_NORMAL))
	    sh_elf_add_rofixup (output_bfd, htab->srofixup,
				htab->root.sgot->output_section->vma
				+ htab->root.sgot->output_offset
				+ off);

	  local_got_offsets[ELF32_R_SYM (rel->r_info)] |= 1;
	}
      *prelocation = sh_elf_got_offset (htab) + off;
    }

#ifdef GOT_BIAS
  *prelocation -= GOT_BIAS;
#endif

  if (r_type == R_SH_GOT20)
    {
      if (install_movi20_field (output_bfd, *prelocation + *paddend,
				input_bfd, input_section, contents,
				rel->r_offset) == bfd_reloc_ok)
	return true; // handled, skip final relocate
      return false; // error
    }
  return false; // continue to final_link_relocate
}

static bool
handle_gotoff_reloc (bfd *output_bfd, struct bfd_link_info *info,
                     bfd *input_bfd, asection *input_section,
                     bfd_byte *contents, Elf_Internal_Rela *rel,
                     reloc_howto_type *howto,
                     struct elf_sh_link_hash_table *htab,
                     bfd_vma *prelocation, bfd_vma *paddend,
                     int r_type, unsigned *pcheck_segment0)
{
  BFD_ASSERT (htab && htab->root.sgotplt != NULL);
  *pcheck_segment0 = htab->got_segment;
  *prelocation -= (htab->root.sgotplt->output_section->vma + htab->root.sgotplt->output_offset
		   + htab->root.hgot->root.u.def.value);
#ifdef GOT_BIAS
  *prelocation -= GOT_BIAS;
#endif
  *paddend = rel->r_addend;

  if (r_type == R_SH_GOTOFF20)
    {
      if (install_movi20_field (output_bfd, *prelocation + *paddend,
				input_bfd, input_section, contents,
				rel->r_offset) == bfd_reloc_ok)
	return true; // handled, skip final relocate
      return false; // error
    }
  return false; // continue to final_link_relocate
}

static bool
handle_plt32_reloc (bfd *output_bfd, struct bfd_link_info *info,
                    bfd *input_bfd, asection *input_section,
                    Elf_Internal_Rela *rel, reloc_howto_type *howto,
                    struct elf_sh_link_hash_table *htab,
                    struct elf_link_hash_entry *h,
                    bfd_vma *prelocation, bfd_vma *paddend,
                    bool resolved_to_zero,
                    unsigned *pcheck_segment0, unsigned *pcheck_segment1,
                    unsigned plt_segment)
{
  if (h == NULL || h->forced_local || h->plt.offset == (bfd_vma) -1)
    {
      // Resolve against local symbol directly or no PLT entry
      return false; // continue to final_link_relocate
    }

  if (h->root.type == bfd_link_hash_undefweak)
    {
      *pcheck_segment0 = (unsigned) -1;
      *pcheck_segment1 = (unsigned) -1;
    }

  BFD_ASSERT (htab && htab->root.splt != NULL);
  *pcheck_segment1 = plt_segment;
  *prelocation = (htab->root.splt->output_section->vma
		  + htab->root.splt->output_offset
		  + h->plt.offset);

  *paddend = rel->r_addend;
  return false; // continue to final_link_relocate
}

static bool
handle_funcdesc_reloc (bfd *output_bfd, struct bfd_link_info *info,
                       bfd *input_bfd, asection *input_section,
                       bfd_byte *contents, Elf_Internal_Rela *rel,
                       reloc_howto_type *howto,
                       struct elf_sh_link_hash_table *htab,
                       struct elf_link_hash_entry *h, Elf_Internal_Sym *sym,
                       asection *sec, bfd_vma *local_got_offsets,
                       bfd_vma *prelocation, bfd_vma *paddend,
                       const char *symname, int r_type,
                       unsigned *pcheck_segment0, unsigned *pcheck_segment1,
                       asection **psrelgot)
{
  int dynindx = -1;
  asection *reloc_section;
  bfd_vma reloc_offset;
  int reloc_type = R_SH_FUNCDESC;
  unsigned long r_symndx = ELF32_R_SYM(rel->r_info);

  BFD_ASSERT (htab);

  *pcheck_segment0 = (unsigned) -1;
  *pcheck_segment1 = (unsigned) -1;
  *prelocation = 0;
  *paddend = 0;

  if (r_type == R_SH_FUNCDESC)
    {
      reloc_section = input_section;
      reloc_offset = rel->r_offset;
    }
  else
    {
      reloc_section = htab->root.sgot;
      if (h != NULL)
	reloc_offset = h->got.offset;
      else
	{
	  BFD_ASSERT (local_got_offsets != NULL);
	  reloc_offset = local_got_offsets[r_symndx];
	}
      BFD_ASSERT (reloc_offset != MINUS_ONE);

      if (reloc_offset & 1)
	{
	  reloc_offset &= ~1;
	  goto funcdesc_done_got;
	}
    }

  if (h && h->root.type == bfd_link_hash_undefweak
      && (SYMBOL_CALLS_LOCAL (info, h)
	  || !htab->root.dynamic_sections_created))
    goto funcdesc_leave_zero;
  else if (SYMBOL_CALLS_LOCAL (info, h)
	   && ! SYMBOL_FUNCDESC_LOCAL (info, h))
    {
      dynindx = elf_section_data (h->root.u.def.section->output_section)->dynindx;
      *prelocation += h->root.u.def.section->output_offset
	+ h->root.u.def.value;
    }
  else if (! SYMBOL_FUNCDESC_LOCAL (info, h))
    {
      BFD_ASSERT (h->dynindx != -1);
      dynindx = h->dynindx;
    }
  else
    {
      bfd_vma offset;

      reloc_type = R_SH_DIR32;
      dynindx = elf_section_data (htab->sfuncdesc->output_section)->dynindx;

      if (h)
	{
	  offset = sh_elf_hash_entry (h)->funcdesc.offset;
	  BFD_ASSERT (offset != MINUS_ONE);
	  if ((offset & 1) == 0)
	    {
	      if (!sh_elf_initialize_funcdesc (output_bfd, info, h,
					       offset, NULL, 0))
		return false;
	      sh_elf_hash_entry (h)->funcdesc.offset |= 1;
	    }
	}
      else
	{
	  union gotref *local_funcdesc;

	  local_funcdesc = sh_elf_local_funcdesc (input_bfd);
	  offset = local_funcdesc[r_symndx].offset;
	  BFD_ASSERT (offset != MINUS_ONE);
	  if ((offset & 1) == 0)
	    {
	      if (!sh_elf_initialize_funcdesc (output_bfd, info, NULL,
					       offset, sec,
					       sym->st_value))
		return false;
	      local_funcdesc[r_symndx].offset |= 1;
	    }
	}
      *prelocation = htab->sfuncdesc->output_offset + (offset & ~1);
    }

  if (!bfd_link_pic (info) && SYMBOL_FUNCDESC_LOCAL (info, h))
    {
      bfd_vma offset;

      if (sh_elf_osec_readonly_p (output_bfd,
				  reloc_section->output_section))
	{
	  _bfd_error_handler
	    (_("%pB(%pA+%#" PRIx64 "): "
	       "cannot emit fixup to `%s' in read-only section"),
	     input_bfd,
	     input_section,
	     (uint64_t) rel->r_offset,
	     symname);
	  return false;
	}

      offset = _bfd_elf_section_offset (output_bfd, info,
					reloc_section, reloc_offset);

      if (offset != (bfd_vma)-1)
	sh_elf_add_rofixup (output_bfd, htab->srofixup,
			    offset
			    + reloc_section->output_section->vma
			    + reloc_section->output_offset);
    }
  else if ((reloc_section->output_section->flags
	    & (SEC_ALLOC | SEC_LOAD)) == (SEC_ALLOC | SEC_LOAD))
    {
      bfd_vma offset;

      if (sh_elf_osec_readonly_p (output_bfd,
				  reloc_section->output_section))
	{
	  info->callbacks->warning
	    (info,
	     _("cannot emit dynamic relocations in read-only section"),
	     symname, input_bfd, reloc_section, reloc_offset);
	  return false;
	}

      offset = _bfd_elf_section_offset (output_bfd, info,
					reloc_section, reloc_offset);

      if (offset != (bfd_vma)-1)
	sh_elf_add_dyn_reloc (output_bfd, *psrelgot,
			      offset
			      + reloc_section->output_section->vma
			      + reloc_section->output_offset,
			      reloc_type, dynindx, *prelocation);

      if (r_type == R_SH_FUNCDESC)
	return true; // handled, skip final relocate
      else
	{
	  *prelocation = 0;
	  goto funcdesc_leave_zero;
	}
    }

  if (SYMBOL_FUNCDESC_LOCAL (info, h))
    *prelocation += htab->sfuncdesc->output_section->vma;

 funcdesc_leave_zero:
  if (r_type != R_SH_FUNCDESC)
    {
      bfd_put_32 (output_bfd, *prelocation,
		  reloc_section->contents + reloc_offset);
      if (h != NULL)
	h->got.offset |= 1;
      else
	local_got_offsets[r_symndx] |= 1;

    funcdesc_done_got:
      *prelocation = sh_elf_got_offset (htab) + reloc_offset;
#ifdef GOT_BIAS
      *prelocation -= GOT_BIAS;
#endif
    }

  if (r_type == R_SH_GOTFUNCDESC20)
    {
      if (install_movi20_field (output_bfd, *prelocation + *paddend,
				input_bfd, input_section, contents,
				rel->r_offset) == bfd_reloc_ok)
	return true; // handled, skip final relocate
      return false; // error
    }
  return false; // continue to final_link_relocate
}

static bool
handle_gotoff_funcdesc_reloc (bfd *output_bfd, struct bfd_link_info *info,
                              bfd *input_bfd, asection *input_section,
                              bfd_byte *contents, Elf_Internal_Rela *rel,
                              reloc_howto_type *howto,
                              struct elf_sh_link_hash_table *htab,
                              struct elf_link_hash_entry *h, Elf_Internal_Sym *sym,
                              asection *sec, bfd_vma *local_got_offsets,
                              bfd_vma *prelocation, bfd_vma *paddend,
                              const char *symname, int r_type,
                              unsigned *pcheck_segment0, unsigned *pcheck_segment1)
{
  unsigned long r_symndx = ELF32_R_SYM(rel->r_info);

  BFD_ASSERT (htab);
  *pcheck_segment0 = (unsigned) -1;
  *pcheck_segment1 = (unsigned) -1;
  *prelocation = 0;
  *paddend = rel->r_addend;

  if (h && (h->root.type == bfd_link_hash_undefweak
	    || !SYMBOL_FUNCDESC_LOCAL (info, h)))
    {
      _bfd_error_handler
	(_("%pB(%pA+%#" PRIx64 "): "
	   "%s relocation against external symbol \"%s\""),
	 input_bfd, input_section, (uint64_t) rel->r_offset,
	 howto->name, h->root.root.string);
      return false;
    }
  else
    {
      bfd_vma offset;
      if (h)
	{
	  offset = sh_elf_hash_entry (h)->funcdesc.offset;
	  BFD_ASSERT (offset != MINUS_ONE);
	  if ((offset & 1) == 0)
	    {
	      if (!sh_elf_initialize_funcdesc (output_bfd, info, h,
					       offset, NULL, 0))
		return false;
	      sh_elf_hash_entry (h)->funcdesc.offset |= 1;
	    }
	}
      else
	{
	  union gotref *local_funcdesc;

	  local_funcdesc = sh_elf_local_funcdesc (input_bfd);
	  offset = local_funcdesc[r_symndx].offset;
	  BFD_ASSERT (offset != MINUS_ONE);
	  if ((offset & 1) == 0)
	    {
	      if (!sh_elf_initialize_funcdesc (output_bfd, info, NULL,
					       offset, sec,
					       sym->st_value))
		return false;
	      local_funcdesc[r_symndx].offset |= 1;
	    }
	}
      *prelocation = htab->sfuncdesc->output_offset + (offset & ~1);
    }

  *prelocation -= (htab->root.hgot->root.u.def.value
		   + htab->root.sgotplt->output_offset);
#ifdef GOT_BIAS
  *prelocation -= GOT_BIAS;
#endif

  if (r_type == R_SH_GOTOFFFUNCDESC20)
    {
      if (install_movi20_field (output_bfd, *prelocation + *paddend,
				input_bfd, input_section, contents,
				rel->r_offset) == bfd_reloc_ok)
	return true; // handled, skip final relocate
      return false; // error
    }
  return false; // continue to final_link_relocate
}

static bfd_reloc_status_type
handle_loop_reloc (bfd *input_bfd, asection *input_section,
                   bfd_byte *contents, Elf_Internal_Rela *rel,
                   int r_type, bfd_vma relocation, bfd_vma addend,
                   asection *sec)
{
  static bfd_vma loop_start_val; // Renamed to avoid collision/clarify scope

  if (r_type == R_SH_LOOP_START)
    {
      loop_start_val = (relocation + addend
			- (sec->output_section->vma + sec->output_offset));
      return sh_elf_reloc_loop (r_type, input_bfd, input_section, contents,
				rel->r_offset, sec, loop_start_val, 0); // end is not used for START
    }
  else /* R_SH_LOOP_END */
    {
      bfd_vma loop_end_val = (relocation + addend
			      - (sec->output_section->vma + sec->output_offset));
      return sh_elf_reloc_loop (r_type, input_bfd, input_section, contents,
				rel->r_offset, sec, loop_start_val, loop_end_val);
    }
}

static bool
handle_tls_gd_to_le_transition (bfd *output_bfd, bfd *input_bfd,
                                asection *input_section, bfd_byte *contents,
                                Elf_Internal_Rela *rel, bfd_vma *prelocation)
{
  bfd_vma offset = rel->r_offset;
  unsigned short insn;

  if (offset < 16)
    {
      _bfd_error_handler
	(_("%pB(%pA): offset in relocation for GD->LE translation is too small: %#" PRIx64),
	 input_bfd, input_section, (uint64_t) offset);
      return false;
    }

  offset -= 16;
  insn = bfd_get_16 (input_bfd, contents + offset + 0);
  if ((insn & 0xff00) == 0xc700)
    {
      BFD_ASSERT (offset >= 2);
      offset -= 2;
      insn = bfd_get_16 (input_bfd, contents + offset + 0);
    }

  if ((insn & 0xff00) != 0xd400)
    _bfd_error_handler
      (_("%pB(%pA+%#" PRIx64 "): unexpected instruction %#04X (expected 0xd4??)"),
       input_bfd, input_section, (uint64_t) offset, (int) insn);

  insn = bfd_get_16 (input_bfd, contents + offset + 2);
  if ((insn & 0xff00) != 0xc700)
    _bfd_error_handler
      (_("%pB(%pA+%#" PRIx64 "): unexpected instruction %#04X (expected 0xc7??)"),
       input_bfd, input_section, (uint64_t) offset, (int) insn);

  insn = bfd_get_16 (input_bfd, contents + offset + 4);
  if ((insn & 0xff00) != 0xd100)
    _bfd_error_handler
      (_("%pB(%pA+%#" PRIx64 "): unexpected instruction %#04X (expected 0xd1??)"),
       input_bfd, input_section, (uint64_t) offset, (int) insn);

  insn = bfd_get_16 (input_bfd, contents + offset + 6);
  if (insn != 0x310c)
    _bfd_error_handler
      (_("%pB(%pA+%#" PRIx64 "): unexpected instruction %#04X (expected 0x310c)"),
       input_bfd, input_section, (uint64_t) offset, (int) insn);

  insn = bfd_get_16 (input_bfd, contents + offset + 8);
  if (insn != 0x410b)
    _bfd_error_handler
      (_("%pB(%pA+%#" PRIx64 "): unexpected instruction %#04X (expected 0x410b)"),
       input_bfd, input_section, (uint64_t) offset, (int) insn);

  insn = bfd_get_16 (input_bfd, contents + offset + 10);
  if (insn != 0x34cc)
    _bfd_error_handler
      (_("%pB(%pA+%#" PRIx64 "): unexpected instruction %#04X (expected 0x34cc)"),
       input_bfd, input_section, (uint64_t) offset, (int) insn);

  bfd_put_16 (output_bfd, 0x0012, contents + offset + 2);
  bfd_put_16 (output_bfd, 0x304c, contents + offset + 4);
  bfd_put_16 (output_bfd, 0x0009, contents + offset + 6);
  bfd_put_16 (output_bfd, 0x0009, contents + offset + 8);
  bfd_put_16 (output_bfd, 0x0009, contents + offset + 10);

  return true;
}

static bool
handle_tls_ie_to_le_transition (bfd *output_bfd, bfd *input_bfd,
                                asection *input_section, bfd_byte *contents,
                                Elf_Internal_Rela *rel, bfd_vma *prelocation)
{
  bfd_vma offset = rel->r_offset;
  unsigned short insn;
  int target;

  if (offset < 16)
    {
      _bfd_error_handler
	(_("%pB(%pA): offset in relocation for IE->LE translation is too small: %#" PRIx64),
	 input_bfd, input_section, (uint64_t) offset);
      return false;
    }

  offset -= 10;
  insn = bfd_get_16 (input_bfd, contents + offset + 0);
  if ((insn & 0xf0ff) == 0x0012)
    {
      BFD_ASSERT (offset >= 2);
      offset -= 2;
      insn = bfd_get_16 (input_bfd, contents + offset + 0);
    }

  if ((insn & 0xff00) != 0xd000)
    _bfd_error_handler
      (_("%pB(%pA+%#" PRIx64 "): unexpected instruction %#04X (expected 0xd0??: mov.l)"),
       input_bfd, input_section, (uint64_t) offset, (int) insn);

  target = insn & 0x00ff;

  insn = bfd_get_16 (input_bfd, contents + offset + 2);
  if ((insn & 0xf0ff) != 0x0012)
    _bfd_error_handler
      (_("%pB(%pA+%#" PRIx64 "): unexpected instruction %#04X (expected 0x0?12: stc)"),
       input_bfd, input_section, (uint64_t) (offset + 2), (int) insn);

  insn = bfd_get_16 (input_bfd, contents + offset + 4);
  if ((insn & 0xf0ff) != 0x00ce)
    _bfd_error_handler
      (_("%pB(%pA+%#" PRIx64 "): unexpected instruction %#04X (expected 0x0?ce: mov.l)"),
       input_bfd, input_section, (uint64_t) (offset + 4), (int) insn);

  insn = 0xd000 | (insn & 0x0f00) | target;
  bfd_put_16 (output_bfd, insn, contents + offset + 0);
  bfd_put_16 (output_bfd, 0x0009, contents + offset + 4);

  return true;
}

static bool
handle_tls_gd_to_ie_transition (bfd *output_bfd, bfd *input_bfd,
                                asection *input_section, bfd_byte *contents,
                                Elf_Internal_Rela *rel, bfd_vma *prelocation,
                                struct elf_sh_link_hash_table *htab, bfd_vma off)
{
  bfd_vma offset = rel->r_offset;
  unsigned short insn;

  if (offset < 16)
    {
      _bfd_error_handler
	(_("%pB(%pA): offset in relocation for GD->IE translation is too small: %#" PRIx64),
	 input_bfd, input_section, (uint64_t) offset);
      return false;
    }

  offset -= 16;
  insn = bfd_get_16 (input_bfd, contents + offset + 0);
  if ((insn & 0xff00) == 0xc700)
    {
      BFD_ASSERT (offset >= 2);
      offset -= 2;
      insn = bfd_get_16 (input_bfd, contents + offset + 0);
    }
  BFD_ASSERT ((insn & 0xff00) == 0xd400);
  bfd_put_16 (output_bfd, insn & 0xf0ff, contents + offset);

  insn = bfd_get_16 (input_bfd, contents + offset + 2);
  BFD_ASSERT ((insn & 0xff00) == 0xc700);
  insn = bfd_get_16 (input_bfd, contents + offset + 4);
  BFD_ASSERT ((insn & 0xff00) == 0xd100);
  insn = bfd_get_16 (input_bfd, contents + offset + 6);
  BFD_ASSERT (insn == 0x310c);
  insn = bfd_get_16 (input_bfd, contents + offset + 8);
  BFD_ASSERT (insn == 0x410b);
  insn = bfd_get_16 (input_bfd, contents + offset + 10);
  BFD_ASSERT (insn == 0x34cc);

  bfd_put_16 (output_bfd, 0x0412, contents + offset + 2);
  bfd_put_16 (output_bfd, 0x00ce, contents + offset + 4);
  bfd_put_16 (output_bfd, 0x304c, contents + offset + 6);
  bfd_put_16 (output_bfd, 0x0009, contents + offset + 8);
  bfd_put_16 (output_bfd, 0x0009, contents + offset + 10);

  bfd_put_32 (output_bfd, sh_elf_got_offset (htab) + off,
	      contents + rel->r_offset);
  return true;
}

static bool
handle_tls_reloc (bfd *output_bfd, struct bfd_link_info *info,
                  bfd *input_bfd, asection *input_section,
                  bfd_byte *contents, Elf_Internal_Rela *rel,
                  struct elf_sh_link_hash_table *htab,
                  struct elf_link_hash_entry *h, Elf_Internal_Sym *sym,
                  bfd_vma *local_got_offsets, bfd_vma *prelocation,
                  bfd_vma *paddend, int r_type,
                  unsigned *pcheck_segment0, unsigned *pcheck_segment1,
                  asection **psreloc, asection **psrelgot)
{
  int original_r_type = ELF32_R_TYPE (rel->r_info);
  unsigned long r_symndx = ELF32_R_SYM (rel->r_info);
  bfd_vma off;
  enum got_type got_type_val = GOT_UNKNOWN;
  int new_r_type = r_type;

  *pcheck_segment0 = (unsigned) -1;
  *pcheck_segment1 = (unsigned) -1;

  if (htab->root.sgot == NULL || htab->root.sgotplt == NULL)
    abort (); // Critical, should not happen

  // R_SH_TLS_GD_32, R_SH_TLS_IE_32
  if (r_type == R_SH_TLS_GD_32 || r_type == R_SH_TLS_IE_32)
    {
      new_r_type = sh_elf_optimized_tls_reloc (info, r_type, h == NULL);
      if (h == NULL && local_got_offsets)
	got_type_val = sh_elf_local_got_type (input_bfd) [r_symndx];
      else if (h != NULL)
	{
	  got_type_val = sh_elf_hash_entry (h)->got_type;
	  if (! bfd_link_pic (info)
	      && (h->dynindx == -1 || h->def_regular))
	    new_r_type = R_SH_TLS_LE_32;
	}

      if (new_r_type == R_SH_TLS_GD_32 && got_type_val == GOT_TLS_IE)
	new_r_type = R_SH_TLS_IE_32;

      if (new_r_type == R_SH_TLS_LE_32)
	{
	  bool res;
	  if (original_r_type == R_SH_TLS_GD_32)
	    res = handle_tls_gd_to_le_transition (output_bfd, input_bfd, input_section, contents, rel, prelocation);
	  else
	    res = handle_tls_ie_to_le_transition (output_bfd, input_bfd, input_section, contents, rel, prelocation);
	  if (!res) return false;

	  bfd_put_32 (output_bfd, tpoff (info, *prelocation),
		      contents + rel->r_offset);
	  return true; // handled, skip final relocate
	}

      if (h != NULL)
	off = h->got.offset;
      else
	{
	  BFD_ASSERT (local_got_offsets != NULL);
	  off = local_got_offsets[r_symndx];
	}

      if (new_r_type == R_SH_TLS_IE_32 && ! htab->root.dynamic_sections_created)
	{
	  off &= ~1;
	  bfd_put_32 (output_bfd, tpoff (info, *prelocation),
		      htab->root.sgot->contents + off);
	  bfd_put_32 (output_bfd, sh_elf_got_offset (htab) + off,
		      contents + rel->r_offset);
	  return true; // handled, skip final relocate
	}

      if ((off & 1) != 0)
	off &= ~1;
      else
	{
	  Elf_Internal_Rela outrel;
	  bfd_byte *loc;
	  int dr_type, indx;

	  outrel.r_offset = (htab->root.sgot->output_section->vma
			     + htab->root.sgot->output_offset + off);

	  indx = (h == NULL || h->dynindx == -1) ? 0 : h->dynindx;

	  dr_type = (new_r_type == R_SH_TLS_GD_32 ? R_SH_TLS_DTPMOD32 :
		     R_SH_TLS_TPOFF32);
	  if (dr_type == R_SH_TLS_TPOFF32 && indx == 0)
	    outrel.r_addend = *prelocation - dtpoff_base (info);
	  else
	    outrel.r_addend = 0;
	  outrel.r_info = ELF32_R_INFO (indx, dr_type);
	  loc = (*psrelgot)->contents;
	  loc += (*psrelgot)->reloc_count++ * sizeof (Elf32_External_Rela);
	  bfd_elf32_swap_reloca_out (output_bfd, &outrel, loc);

	  if (new_r_type == R_SH_TLS_GD_32)
	    {
	      if (indx == 0)
		{
		  bfd_put_32 (output_bfd,
			      *prelocation - dtpoff_base (info),
			      htab->root.sgot->contents + off + 4);
		}
	      else
		{
		  outrel.r_info = ELF32_R_INFO (indx, R_SH_TLS_DTPOFF32);
		  outrel.r_offset += 4;
		  outrel.r_addend = 0;
		  (*psrelgot)->reloc_count++;
		  loc += sizeof (Elf32_External_Rela);
		  bfd_elf32_swap_reloca_out (output_bfd, &outrel, loc);
		}
	    }

	  if (h != NULL)
	    h->got.offset |= 1;
	  else
	    local_got_offsets[r_symndx] |= 1;
	}

      if (off >= (bfd_vma) -2)
	abort ();

      if (new_r_type == original_r_type)
	*prelocation = sh_elf_got_offset (htab) + off;
      else
	{
	  if (!handle_tls_gd_to_ie_transition (output_bfd, input_bfd, input_section, contents, rel, prelocation, htab, off))
	    return false;
	  return true; // handled, skip final relocate
	}
    }
  // R_SH_TLS_LD_32
  else if (r_type == R_SH_TLS_LD_32)
    {
      if (! bfd_link_pic (info))
	{
	  bfd_vma offset = rel->r_offset;
	  unsigned short insn;

	  if (offset < 16)
	    {
	      _bfd_error_handler
		(_("%pB(%pA): offset in relocation for LD->LE translation is too small: %#" PRIx64),
		 input_bfd, input_section, (uint64_t) offset);
	      return false;
	    }

	  offset -= 16;
	  insn = bfd_get_16 (input_bfd, contents + offset + 0);
	  if ((insn & 0xff00) == 0xc700)
	    {
	      BFD_ASSERT (offset >= 2);
	      offset -= 2;
	      insn = bfd_get_16 (input_bfd, contents + offset + 0);
	    }
	  BFD_ASSERT ((insn & 0xff00) == 0xd400);
	  insn = bfd_get_16 (input_bfd, contents + offset + 2);
	  BFD_ASSERT ((insn & 0xff00) == 0xc700);
	  insn = bfd_get_16 (input_bfd, contents + offset + 4);
	  BFD_ASSERT ((insn & 0xff00) == 0xd100);
	  insn = bfd_get_16 (input_bfd, contents + offset + 6);
	  BFD_ASSERT (insn == 0x310c);
	  insn = bfd_get_16 (input_bfd, contents + offset + 8);
	  BFD_ASSERT (insn == 0x410b);
	  insn = bfd_get_16 (input_bfd, contents + offset + 10);
	  BFD_ASSERT (insn == 0x34cc);

	  bfd_put_16 (output_bfd, 0x0012, contents + offset + 0);
	  bfd_put_16 (output_bfd, 0x0009, contents + offset + 2);
	  bfd_put_16 (output_bfd, 0x0009, contents + offset + 4);
	  bfd_put_16 (output_bfd, 0x0009, contents + offset + 6);
	  bfd_put_16 (output_bfd, 0x0009, contents + offset + 8);
	  bfd_put_16 (output_bfd, 0x0009, contents + offset + 10);
	  return true; // handled, skip final relocate
	}

      off = htab->tls_ldm_got.offset;
      if (off & 1)
	off &= ~1;
      else
	{
	  Elf_Internal_Rela outrel;
	  bfd_byte *loc;

	  outrel.r_offset = (htab->root.sgot->output_section->vma
			     + htab->root.sgot->output_offset + off);
	  outrel.r_addend = 0;
	  outrel.r_info = ELF32_R_INFO (0, R_SH_TLS_DTPMOD32);
	  loc = (*psrelgot)->contents;
	  loc += (*psrelgot)->reloc_count++ * sizeof (Elf32_External_Rela);
	  bfd_elf32_swap_reloca_out (output_bfd, &outrel, loc);
	  htab->tls_ldm_got.offset |= 1;
	}
      *prelocation = sh_elf_got_offset (htab) + off;
    }
  // R_SH_TLS_LDO_32
  else if (r_type == R_SH_TLS_LDO_32)
    {
      if (! bfd_link_pic (info))
	*prelocation = tpoff (info, *prelocation);
      else
	*prelocation -= dtpoff_base (info);
    }
  // R_SH_TLS_LE_32
  else if (r_type == R_SH_TLS_LE_32)
    {
      int indx;
      Elf_Internal_Rela outrel;
      bfd_byte *loc;

      if (!bfd_link_dll (info))
	{
	  *prelocation = tpoff (info, *prelocation);
	  return false; // continue to final_link_relocate
	}

      if (*psreloc == NULL)
	{
	  *psreloc = _bfd_elf_get_dynamic_reloc_section
	    (input_bfd, input_section, /*rela?*/ true);
	  if (*psreloc == NULL)
	    return false;
	}

      indx = (h == NULL || h->dynindx == -1) ? 0 : h->dynindx;

      outrel.r_offset = (input_section->output_section->vma
			 + input_section->output_offset
			 + rel->r_offset);
      outrel.r_info = ELF32_R_INFO (indx, R_SH_TLS_TPOFF32);
      if (indx == 0)
	outrel.r_addend = *prelocation - dtpoff_base (info);
      else
	outrel.r_addend = 0;

      loc = (*psreloc)->contents;
      loc += (*psreloc)->reloc_count++ * sizeof (Elf32_External_Rela);
      bfd_elf32_swap_reloca_out (output_bfd, &outrel, loc);
      return true; // handled, skip final relocate
    }
  *paddend = rel->r_addend;
  return false; // continue to final_link_relocate
}

static void
report_fdpic_segment_issue (struct bfd_link_info *info, bfd *abfd,
                            asection *sec, bfd_vma offset,
                            const char *symname, struct elf_link_hash_entry *h,
                            bool is_error)
{
  if (!h || h->root.type != bfd_link_hash_undefined)
    {
      if (is_error)
	info->callbacks->einfo
	  (_("%X%H: relocation to \"%s\" references a different segment\n"),
	   abfd, sec, offset, symname);
      else
	info->callbacks->einfo
	  (_("%H: warning: relocation to \"%s\" references a different segment\n"),
	   abfd, sec, offset, symname);
    }
}

static void
report_reloc_overflow (struct bfd_link_info *info,
                       struct elf_link_hash_entry *h, Elf_Internal_Sym *sym,
                       asection *sec, Elf_Internal_Shdr *symtab_hdr,
                       reloc_howto_type *howto, bfd_reloc_status_type r,
                       bfd *abfd, asection *input_section, bfd_vma offset)
{
  if (r != bfd_reloc_overflow)
    abort ();

  const char *name;
  if (h != NULL)
    name = NULL;
  else
    {
      name = (bfd_elf_string_from_elf_section
	      (abfd, symtab_hdr->sh_link, sym->st_name));
      if (name == NULL)
	return;
      if (*name == '\0')
	name = bfd_section_name (sec);
    }
  (*info->callbacks->reloc_overflow)
    (info, (h ? &h->root : NULL), name, howto->name,
     (bfd_vma) 0, abfd, input_section, offset);
}

static int
sh_elf_relocate_section (bfd *output_bfd, struct bfd_link_info *info,
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
  unsigned isec_segment, got_segment, plt_segment;
  bool fdpic_p = false;

  if (!is_sh_elf (input_bfd))
    {
      bfd_set_error (bfd_error_wrong_format);
      return false;
    }

  htab = sh_elf_hash_table (info);
  if (htab != NULL)
    {
      sgot = htab->root.sgot;
      sgotplt = htab->root.sgotplt;
      srelgot = htab->root.srelgot;
      splt = htab->root.splt;
      fdpic_p = htab->fdpic_p;
    }
  symtab_hdr = &elf_symtab_hdr (input_bfd);
  sym_hashes = elf_sym_hashes (input_bfd);
  local_got_offsets = elf_local_got_offsets (input_bfd);

  isec_segment = sh_elf_osec_to_segment (output_bfd, input_section->output_section);
  got_segment = (fdpic_p && sgot) ? sh_elf_osec_to_segment (output_bfd, sgot->output_section) : (unsigned) -1;
  plt_segment = (fdpic_p && splt) ? sh_elf_osec_to_segment (output_bfd, splt->output_section) : (unsigned) -1;

  is_vxworks_tls = (htab && htab->root.target_os == is_vxworks && bfd_link_pic (info)
		    && !strcmp (input_section->output_section->name, ".tls_vars"));

  rel = relocs;
  relend = relocs + input_section->reloc_count;
  for (; rel < relend; rel++)
    {
      int r_type = ELF32_R_TYPE (rel->r_info);
      unsigned long r_symndx = ELF32_R_SYM (rel->r_info);
      reloc_howto_type *howto;
      bfd_vma relocation = (bfd_vma) 0;
      bfd_vma addend = (bfd_vma) 0;
      struct elf_link_hash_entry *h = NULL;
      Elf_Internal_Sym *sym = NULL;
      asection *sec = NULL;
      const char *symname = NULL;
      bool resolved_to_zero = false;
      unsigned check_segment[2] = {(unsigned) -1, (unsigned) -1};
      bfd_reloc_status_type current_reloc_status = bfd_reloc_ok;
      bool handled_by_specific_case = false;

      if (r_type >= (int) R_SH_GNU_VTINHERIT && r_type <= (int) R_SH_LABEL)
	continue;
      if (r_type == (int) R_SH_NONE)
	continue;

      if (!validate_reloc_type_range(r_type, output_bfd, input_section, rel->r_offset))
        return false;

      howto = get_howto_table (output_bfd) + r_type;

      if (! howto->partial_inplace)
	addend = rel->r_addend;

      if (!resolve_relocation_symbol_info(output_bfd, info, input_bfd, input_section, rel, r_symndx,
                                          local_syms, local_sections, symtab_hdr, sym_hashes,
                                          howto, contents, &h, &sym, &sec, &relocation,
                                          &symname, &resolved_to_zero, &addend))
        return false;

      if (bfd_link_relocatable (info))
        continue;

      if (sec != NULL)
	check_segment[1] = sh_elf_osec_to_segment (output_bfd, sec->output_section);
      check_segment[0] = isec_segment;

      switch (r_type)
	{
	case R_SH_IND12W:
	case R_SH_DIR16:
	case R_SH_DIR8:
	case R_SH_DIR8U:
	case R_SH_DIR8S:
	case R_SH_DIR4U:
	  current_reloc_status = _bfd_final_link_relocate (howto, input_bfd, input_section,
							    contents, rel->r_offset,
							    relocation, addend);
	  handled_by_specific_case = true;
	  break;

	case R_SH_DIR8WPN:
	case R_SH_DIR8WPZ:
	case R_SH_DIR8WPL:
	  current_reloc_status = handle_dir8wp_reloc(output_bfd, input_bfd, input_section, contents,
						       rel, howto, relocation, addend, r_type);
	  if (current_reloc_status == bfd_reloc_outofrange) return false;
	  handled_by_specific_case = true;
	  break;

	case R_SH_DIR8UL:
	case R_SH_DIR4UL:
	  if (!handle_unaligned_reloc_check(input_bfd, input_section, rel->r_offset, howto, relocation, 3))
	    return false;
	  break;

	case R_SH_DIR8UW:
	case R_SH_DIR8SW:
	case R_SH_DIR4UW:
	  if (!handle_unaligned_reloc_check(input_bfd, input_section, rel->r_offset, howto, relocation, 1))
	    return false;
	  break;

	case R_SH_PSHA:
	case R_SH_PSHL:
	  if (!handle_psha_pshl_reloc_check(input_bfd, input_section, rel->r_offset, r_type, relocation))
	    return false;
	  break;

	case R_SH_DIR32:
	case R_SH_REL32:
	  if (handle_dir32_rel32_reloc(output_bfd, info, input_bfd, input_section,
                                       contents, rel, howto, htab, h, sec,
                                       is_vxworks_tls, fdpic_p, &relocation, &addend,
                                       &sreloc, &check_segment[0], &check_segment[1],
                                       resolved_to_zero))
	    {
	      handled_by_specific_case = true; // Continue to next reloc, or already did final link for dyn reloc.
	    }
	  break;

	case R_SH_GOTPLT32:
	case R_SH_GOT32:
	case R_SH_GOT20:
	  if (!handle_gotplt32_and_got_reloc(output_bfd, info, input_bfd, input_section,
                                            contents, rel, howto, htab, h, sym, sec,
                                            local_got_offsets, &relocation, &addend,
                                            r_type, resolved_to_zero,
                                            &check_segment[0], &check_segment[1], &srelgot))
	    {
	      // Falls through to final_link_relocate if not handled internally
	    }
	  else
	    {
	      handled_by_specific_case = true; // Handled internally
	    }
	  break;

	case R_SH_GOTOFF:
	case R_SH_GOTOFF20:
	  if (!handle_gotoff_reloc(output_bfd, info, input_bfd, input_section,
                                   contents, rel, howto, htab,
                                   &relocation, &addend, r_type, &check_segment[0]))
	    {
	      // Falls through to final_link_relocate if not handled internally
	    }
	  else
	    {
	      handled_by_specific_case = true; // Handled internally
	    }
	  break;

	case R_SH_GOTPC:
	  BFD_ASSERT (sgotplt != NULL);
	  relocation = sgotplt->output_section->vma + sgotplt->output_offset;
#ifdef GOT_BIAS
	  relocation += GOT_BIAS;
#endif
	  addend = rel->r_addend;
	  break;

	case R_SH_PLT32:
	  if (!handle_plt32_reloc(output_bfd, info, input_bfd, input_section,
                                  rel, howto, htab, h, &relocation, &addend,
                                  resolved_to_zero, &check_segment[0], &check_segment[1], plt_segment))
	    {
	      // Falls through to final_link_relocate
	    }
	  else
	    {
	      handled_by_specific_case = true; // Not strictly, it just passed, but for control flow.
	    }
	  break;

	case R_SH_GOTFUNCDESC:
	case R_SH_GOTFUNCDESC20:
	case R_SH_FUNCDESC:
	  if (!handle_funcdesc_reloc(output_bfd, info, input_bfd, input_section,
                                     contents, rel, howto, htab, h, sym, sec,
                                     local_got_offsets, &relocation, &addend,
                                     symname, r_type,
                                     &check_segment[0], &check_segment[1], &srelgot))
	    return false;
	  handled_by_specific_case = true;
	  break;

	case R_SH_GOTOFFFUNCDESC:
	case R_SH_GOTOFFFUNCDESC20:
	  if (!handle_gotoff_funcdesc_reloc(output_bfd, info, input_bfd, input_section,
                                            contents, rel, howto, htab, h, sym, sec,
                                            local_got_offsets, &relocation, &addend,
                                            symname, r_type,
                                            &check_segment[0], &check_segment[1]))
	    return false;
	  handled_by_specific_case = true;
	  break;

	case R_SH_LOOP_START:
	case R_SH_LOOP_END:
	  current_reloc_status = handle_loop_reloc(input_bfd, input_section, contents,
						     rel, r_type, relocation, addend, sec);
	  handled_by_specific_case = true;
	  break;

	case R_SH_TLS_GD_32:
	case R_SH_TLS_IE_32:
	case R_SH_TLS_LD_32:
	case R_SH_TLS_LDO_32:
	case R_SH_TLS_LE_32:
	  if (!handle_tls_reloc(output_bfd, info, input_bfd, input_section,
                                contents, rel, htab, h, sym, local_got_offsets,
                                &relocation, &addend, r_type,
                                &check_segment[0], &check_segment[1], &sreloc, &srelgot))
	    return false;
	  handled_by_specific_case = true;
	  break;

	default:
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}

      if (!handled_by_specific_case)
	{
	  current_reloc_status = _bfd_final_link_relocate (howto, input_bfd, input_section,
							    contents, rel->r_offset,
							    relocation, addend);
	}

      if (fdpic_p && check_segment[0] != (unsigned) -1
	  && check_segment[0] != check_segment[1])
	{
	  report_fdpic_segment_issue(info, input_bfd, input_section, rel->r_offset, symname, h, bfd_link_pic(info));
	  if (bfd_link_pic (info)) return false;
	  elf_elfheader (output_bfd)->e_flags |= EF_SH_PIC;
	}

      if (current_reloc_status != bfd_reloc_ok)
	{
	  report_reloc_overflow(info, h, sym, sec, symtab_hdr, howto,
                                  current_reloc_status, input_bfd, input_section, rel->r_offset);
	  return false;
	}
    }

  return true;
}

/* This is a version of bfd_generic_get_relocated_section_contents
   which uses sh_elf_relocate_section.  */

static bfd_byte *
sh_elf_get_relocated_section_contents (bfd *output_bfd,
				       struct bfd_link_info *link_info,
				       struct bfd_link_order *link_order,
				       bfd_byte *data,
				       bool relocatable,
				       asymbol **symbols)
{
  Elf_Internal_Shdr *symtab_hdr;
  asection *input_section = link_order->u.indirect.section;
  bfd *input_bfd = input_section->owner;

  bfd_byte *return_data = NULL;
  bool data_was_allocated = false;

  Elf_Internal_Rela *internal_relocs = NULL;
  bool internal_relocs_allocated = false;

  Elf_Internal_Sym *isymbuf = NULL;
  bool isymbuf_allocated = false;

  asection **sections = NULL;
  bool sections_allocated = false;

  if (relocatable
      || elf_section_data (input_section)->this_hdr.contents == NULL)
    return bfd_generic_get_relocated_section_contents (output_bfd, link_info,
						       link_order, data,
						       relocatable,
						       symbols);

  symtab_hdr = &elf_symtab_hdr (input_bfd);

  if (data == NULL)
    {
      data = bfd_malloc (input_section->size);
      if (data == NULL)
        goto fail;
      data_was_allocated = true;
    }
  return_data = data;

  memcpy (return_data, elf_section_data (input_section)->this_hdr.contents,
	  (size_t) input_section->size);

  if ((input_section->flags & SEC_RELOC) != 0
      && input_section->reloc_count > 0)
    {
      asection **secpp;
      Elf_Internal_Sym *isym, *isymend;
      bfd_size_type amt;

      internal_relocs = _bfd_elf_link_read_relocs (input_bfd, input_section, NULL,
						   (Elf_Internal_Rela *) NULL, false);
      if (internal_relocs == NULL)
	goto fail;
      internal_relocs_allocated = true;

      if (symtab_hdr->sh_info != 0)
	{
	  isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;
	  if (isymbuf == NULL)
	    {
	      isymbuf = bfd_elf_get_elf_syms (input_bfd, symtab_hdr,
						symtab_hdr->sh_info, 0,
						NULL, NULL, NULL);
	      if (isymbuf == NULL)
		goto fail;
	      isymbuf_allocated = true;
	    }
	}

      amt = symtab_hdr->sh_info;
      amt *= sizeof (asection *);
      if (amt != 0)
        {
          sections = (asection **) bfd_malloc (amt);
          if (sections == NULL)
            goto fail;
          sections_allocated = true;
        }

      isymend = isymbuf + symtab_hdr->sh_info;
      for (isym = isymbuf, secpp = sections; isym < isymend; ++isym, ++secpp)
	{
	  asection *isec;

	  if (isym->st_shndx == SHN_UNDEF)
	    isec = bfd_und_section_ptr;
	  else if (isym->st_shndx == SHN_ABS)
	    isec = bfd_abs_section_ptr;
	  else if (isym->st_shndx == SHN_COMMON)
	    isec = bfd_com_section_ptr;
	  else
	    isec = bfd_section_from_elf_index (input_bfd, isym->st_shndx);

	  *secpp = isec;
	}

      if (! sh_elf_relocate_section (output_bfd, link_info, input_bfd,
				     input_section, return_data, internal_relocs,
				     isymbuf, sections))
	goto fail;
    }

  if (sections_allocated)
    free (sections);
  if (isymbuf_allocated)
    free (isymbuf);
  if (internal_relocs_allocated)
    free (internal_relocs);

  return return_data;

 fail:
  if (sections_allocated)
    free (sections);
  if (isymbuf_allocated)
    free (isymbuf);
  if (internal_relocs_allocated)
    free (internal_relocs);
  if (data_was_allocated)
    free (return_data);
  return NULL;
}

/* Return the base VMA address which should be subtracted from real addresses
   when resolving @dtpoff relocation.
   This is PT_TLS segment p_vaddr.  */

static bfd_vma
dtpoff_base (struct bfd_link_info *info)
{
  struct elf_hash_table *hash_table = elf_hash_table (info);
  if (hash_table->tls_sec == NULL)
    return 0;
  return hash_table->tls_sec->vma;
}

/* Return the relocation value for R_SH_TLS_TPOFF32..  */

static bfd_vma
tpoff (struct bfd_link_info *info, bfd_vma address)
{
  struct elf_hash_table *const hash_table = elf_hash_table (info);
  struct elf_section_data *const tls_sec = hash_table->tls_sec;

  if (tls_sec == NULL)
    {
      return 0;
    }

  const bfd_vma tcb_head_raw_size = (bfd_vma) 8;
  const bfd_vma tcb_head_aligned_size = align_power (tcb_head_raw_size, tls_sec->alignment_power);

  return (address - tls_sec->vma + tcb_head_aligned_size);
}

static asection *
sh_elf_gc_mark_hook (asection *sec,
		     struct bfd_link_info *info,
		     Elf_Internal_Rela *rel,
		     struct elf_link_hash_entry *h,
		     Elf_Internal_Sym *sym)
{
  if (h != NULL && rel != NULL)
    {
      unsigned int r_type = ELF32_R_TYPE (rel->r_info);
      if (r_type == R_SH_GNU_VTINHERIT || r_type == R_SH_GNU_VTENTRY)
        {
          return NULL;
        }
    }

  return _bfd_elf_gc_mark_hook (sec, info, rel, h, sym);
}

/* Copy the extra info we tack onto an elf_link_hash_entry.  */

static void
sh_elf_copy_indirect_symbol (struct bfd_link_info *info,
			     struct elf_link_hash_entry *dir,
			     struct elf_link_hash_entry *ind)
{
  struct elf_sh_link_hash_entry *edir = (struct elf_sh_link_hash_entry *) dir;
  struct elf_sh_link_hash_entry *eind = (struct elf_sh_link_hash_entry *) ind;

  edir->gotplt_refcount = eind->gotplt_refcount;
  eind->gotplt_refcount = 0;
  edir->funcdesc.refcount += eind->funcdesc.refcount;
  eind->funcdesc.refcount = 0;
  edir->abs_funcdesc_refcount += eind->abs_funcdesc_refcount;
  eind->abs_funcdesc_refcount = 0;

  if (ind->root.type == bfd_link_hash_indirect
      && dir->got.refcount <= 0)
    {
      edir->got_type = eind->got_type;
      eind->got_type = GOT_UNKNOWN;
    }

  if (ind->root.type != bfd_link_hash_indirect
      && dir->dynamic_adjusted)
    {
      if (dir->versioned != versioned_hidden)
        {
	  dir->ref_dynamic |= ind->ref_dynamic;
        }
      dir->ref_regular |= ind->ref_regular;
      dir->ref_regular_nonweak |= ind->ref_regular_nonweak;
      dir->needs_plt |= ind->needs_plt;
    }
  else
    {
      _bfd_elf_link_hash_copy_indirect (info, dir, ind);
    }
}

static int
sh_elf_optimized_tls_reloc (struct bfd_link_info *info, int r_type,
			    int is_local)
{
  if (bfd_link_pic (info))
    return r_type;

  switch (r_type)
    {
    case R_SH_TLS_GD_32:
    case R_SH_TLS_IE_32:
      return is_local ? R_SH_TLS_LE_32 : R_SH_TLS_IE_32;

    case R_SH_TLS_LD_32:
      return R_SH_TLS_LE_32;

    default:
      return r_type;
    }
}

/* Look through the relocs for a section during the first phase.
   Since we don't do .gots or .plts, we just need to consider the
   virtual table relocs for gc.  */

static bool
sh_elf_ensure_local_got_data (bfd *abfd, Elf_Internal_Shdr *symtab_hdr)
{
  if (elf_local_got_refcounts (abfd) == NULL)
    {
      bfd_size_type size;
      void *mem;

      size = symtab_hdr->sh_info;
      size *= sizeof (bfd_signed_vma);
      size += symtab_hdr->sh_info; /* For sh_elf_local_got_type. */

      mem = bfd_zalloc (abfd, size);
      if (mem == NULL)
        return false;

      elf_local_got_refcounts (abfd) = (bfd_signed_vma *) mem;
      sh_elf_local_got_type (abfd) = (char *) ((bfd_signed_vma *) mem + symtab_hdr->sh_info);
    }
  return true;
}

static bool
sh_elf_ensure_local_funcdesc_data (bfd *abfd, Elf_Internal_Shdr *symtab_hdr)
{
  if (sh_elf_local_funcdesc (abfd) == NULL)
    {
      bfd_size_type size;

      size = symtab_hdr->sh_info * sizeof (union gotref);
      union gotref *local_funcdesc = (union gotref *) bfd_zalloc (abfd, size);
      if (local_funcdesc == NULL)
        return false;
      sh_elf_local_funcdesc (abfd) = local_funcdesc;
    }
  return true;
}

static struct elf_link_hash_entry *
sh_elf_get_resolved_hash_entry (struct elf_link_hash_entry **sym_hashes,
                                Elf_Internal_Shdr *symtab_hdr,
                                unsigned long r_symndx)
{
  if (r_symndx < symtab_hdr->sh_info)
    return NULL;

  struct elf_link_hash_entry *h = sym_hashes[r_symndx - symtab_hdr->sh_info];
  while (h != NULL && (h->root.type == bfd_link_hash_indirect || h->root.type == bfd_link_hash_warning))
    h = (struct elf_link_hash_entry *) h->root.u.i.link;
  return h;
}

static bool
sh_elf_ensure_got_section (bfd *abfd, struct bfd_link_info *info,
                           struct elf_sh_link_hash_table *htab)
{
  if (htab->root.sgot == NULL)
    {
      if (htab->root.dynobj == NULL)
        htab->root.dynobj = abfd;
      if (!create_got_section (htab->root.dynobj, info))
        return false;
    }
  return true;
}

static bool
sh_elf_handle_got_relocation (bfd *abfd, struct bfd_link_info *info,
                              struct elf_sh_link_hash_table *htab,
                              struct elf_link_hash_entry *h,
                              unsigned long r_symndx, unsigned int r_type,
                              Elf_Internal_Shdr *symtab_hdr)
{
  enum got_type current_got_type;
  enum got_type old_got_type = GOT_UNKNOWN;

  switch (r_type)
    {
    case R_SH_TLS_GD_32:
      current_got_type = GOT_TLS_GD;
      break;
    case R_SH_TLS_IE_32:
      current_got_type = GOT_TLS_IE;
      if (bfd_link_pic (info))
        info->flags |= DF_STATIC_TLS;
      break;
    case R_SH_GOTFUNCDESC:
    case R_SH_GOTFUNCDESC20:
      current_got_type = GOT_FUNCDESC;
      break;
    default: /* R_SH_GOT32, R_SH_GOT20, and generic for GOTPLT32 fallthrough */
      current_got_type = GOT_NORMAL;
      break;
    }

  if (h != NULL)
    {
      h->got.refcount += 1;
      old_got_type = sh_elf_hash_entry (h)->got_type;
    }
  else
    {
      if (!sh_elf_ensure_local_got_data (abfd, symtab_hdr))
        return false;
      elf_local_got_refcounts (abfd) [r_symndx] += 1;
      old_got_type = sh_elf_local_got_type (abfd) [r_symndx];
    }

  if (old_got_type != current_got_type && old_got_type != GOT_UNKNOWN)
    {
      if (old_got_type == GOT_TLS_IE && current_got_type == GOT_TLS_GD)
        current_got_type = GOT_TLS_IE;
      else
        {
          const char *sym_name = (h != NULL) ? h->root.root.string : "local symbol";
          const char *msg = NULL;

          if ((old_got_type == GOT_FUNCDESC || current_got_type == GOT_FUNCDESC)
              && (old_got_type == GOT_NORMAL || current_got_type == GOT_NORMAL))
            msg = _("%pB: `%s' accessed both as normal and FDPIC symbol");
          else if (old_got_type == GOT_FUNCDESC || current_got_type == GOT_FUNCDESC)
            msg = _("%pB: `%s' accessed both as FDPIC and thread local symbol");
          else
            msg = _("%pB: `%s' accessed both as normal and thread local symbol");

          _bfd_error_handler (msg, abfd, sym_name);
          return false;
        }
    }

  if (old_got_type != current_got_type)
    {
      if (h != NULL)
        sh_elf_hash_entry (h)->got_type = current_got_type;
      else
        sh_elf_local_got_type (abfd) [r_symndx] = current_got_type;
    }

  return true;
}

static bool
sh_elf_handle_funcdesc_relocation (bfd *abfd, struct bfd_link_info *info,
                                   struct elf_sh_link_hash_table *htab,
                                   struct elf_link_hash_entry *h,
                                   unsigned long r_symndx, unsigned int r_type,
                                   bfd_vma r_addend,
                                   Elf_Internal_Shdr *symtab_hdr)
{
  static const int SH_WORD_SIZE = 4; /* Standard word size for SH architecture. */

  if (r_addend)
    {
      _bfd_error_handler (_("%pB: Function descriptor relocation with non-zero addend"), abfd);
      return false;
    }

  if (h == NULL)
    {
      if (!sh_elf_ensure_local_funcdesc_data (abfd, symtab_hdr))
        return false;
      sh_elf_local_funcdesc (abfd) [r_symndx].refcount += 1;

      if (r_type == R_SH_FUNCDESC)
        {
          if (!bfd_link_pic (info))
            htab->srofixup->size += SH_WORD_SIZE;
          else
            htab->root.srelgot->size += sizeof (Elf32_External_Rela);
        }
    }
  else
    {
      sh_elf_hash_entry (h)->funcdesc.refcount++;
      if (r_type == R_SH_FUNCDESC)
        sh_elf_hash_entry (h)->abs_funcdesc_refcount++;

      enum got_type old_got_type = sh_elf_hash_entry (h)->got_type;
      if (old_got_type != GOT_FUNCDESC && old_got_type != GOT_UNKNOWN)
        {
          const char *msg = NULL;
          if (old_got_type == GOT_NORMAL)
            msg = _("%pB: `%s' accessed both as normal and FDPIC symbol");
          else
            msg = _("%pB: `%s' accessed both as FDPIC and thread local symbol");
          _bfd_error_handler (msg, abfd, h->root.root.string);
          return false;
        }
    }
  return true;
}

static bool
sh_elf_update_dyn_relocs (bfd *abfd, struct elf_sh_link_hash_table *htab,
                          asection *sec, struct elf_link_hash_entry *h,
                          unsigned long r_symndx, unsigned int r_type)
{
  struct elf_dyn_relocs **head;

  if (h != NULL)
    head = &h->dyn_relocs;
  else
    {
      Elf_Internal_Sym *isym = bfd_sym_from_r_symndx (&htab->root.sym_cache, abfd, r_symndx);
      if (isym == NULL)
        return false;

      asection *target_sec = bfd_section_from_elf_index (abfd, isym->st_shndx);
      /* If section cannot be found (e.g., against an absolute symbol with SHN_ABS),
         fall back to the current section. */
      if (target_sec == NULL)
        target_sec = sec;

      head = (struct elf_dyn_relocs **) &elf_section_data (target_sec)->local_dynrel;
    }

  struct elf_dyn_relocs *p = *head;
  if (p == NULL || p->sec != sec)
    {
      p = bfd_alloc (htab->root.dynobj, sizeof (*p));
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
sh_elf_handle_dir_rel_relocation (bfd *abfd, struct bfd_link_info *info,
                                  struct elf_sh_link_hash_table *htab,
                                  asection *sec,
                                  struct elf_link_hash_entry *h,
                                  unsigned long r_symndx, unsigned int r_type,
                                  asection **sreloc_ptr)
{
  static const int SH_WORD_SIZE = 4; /* Standard word size for SH architecture. */

  if (h != NULL && !bfd_link_pic (info))
    {
      h->non_got_ref = 1;
      h->plt.refcount += 1;
    }

  bool needs_dynamic_reloc = false;
  if ((sec->flags & SEC_ALLOC) != 0)
    {
      if (bfd_link_pic (info))
        {
          if (r_type != R_SH_REL32 || (h != NULL && (!info->symbolic || h->root.type == bfd_link_hash_defweak || !h->def_regular)))
            needs_dynamic_reloc = true;
        }
      else
        {
          if (h != NULL && (h->root.type == bfd_link_hash_defweak || !h->def_regular))
            needs_dynamic_reloc = true;
        }
    }

  if (needs_dynamic_reloc)
    {
      if (htab->root.dynobj == NULL)
        htab->root.dynobj = abfd;

      if (*sreloc_ptr == NULL)
        {
          /* The '2' argument historically denotes the rela_type.
             Since the last argument 'rela' is true, it implies Elf32_External_Rela. */
          *sreloc_ptr = _bfd_elf_make_dynamic_reloc_section (sec, htab->root.dynobj, 2, abfd, /*rela?*/ true);

          if (*sreloc_ptr == NULL)
            return false;
        }

      if (!sh_elf_update_dyn_relocs (abfd, htab, sec, h, r_symndx, r_type))
        return false;
    }

  /* Allocate the fixup regardless of whether we need a relocation. */
  if (htab->fdpic_p && !bfd_link_pic (info) && r_type == R_SH_DIR32 && (sec->flags & SEC_ALLOC) != 0)
    htab->srofixup->size += SH_WORD_SIZE;

  return true;
}


static bool
sh_elf_check_relocs (bfd *abfd, struct bfd_link_info *info, asection *sec,
                     const Elf_Internal_Rela *relocs)
{
  if (bfd_link_relocatable (info))
    return true;

  BFD_ASSERT (is_sh_elf (abfd));

  Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr (abfd);
  struct elf_link_hash_entry **sym_hashes = elf_sym_hashes (abfd);

  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  asection *sreloc = NULL;

  const Elf_Internal_Rela *rel_end = relocs + sec->reloc_count;
  for (const Elf_Internal_Rela *rel = relocs; rel < rel_end; rel++)
    {
      unsigned long r_symndx = ELF32_R_SYM (rel->r_info);
      unsigned int r_type = ELF32_R_TYPE (rel->r_info);

      struct elf_link_hash_entry *h =
        sh_elf_get_resolved_hash_entry (sym_hashes, symtab_hdr, r_symndx);

      r_type = sh_elf_optimized_tls_reloc (info, r_type, h == NULL);

      if (! bfd_link_pic (info)
	  && r_type == R_SH_TLS_IE_32
	  && h != NULL
	  && h->root.type != bfd_link_hash_undefined
	  && h->root.type != bfd_link_hash_undefweak
	  && (h->dynindx == -1
	      || h->def_regular))
	r_type = R_SH_TLS_LE_32;

      if (htab->fdpic_p)
        {
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
                      if (!bfd_elf_link_record_dynamic_symbol (info, h))
                        return false;
                      break;
                    }
                }
              break;
            }
        }

      /* Some relocs require a global offset table. */
      bool requires_got_section = false;
      switch (r_type)
        {
        case R_SH_DIR32:
          if (!htab->fdpic_p) break; /* Only if FDPIC. */
          /* Fall through. */
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
          requires_got_section = true;
          break;
        default:
          break;
        }

      if (requires_got_section && !sh_elf_ensure_got_section (abfd, info, htab))
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
        case R_SH_TLS_GD_32:
        case R_SH_GOT32:
        case R_SH_GOT20:
        case R_SH_GOTFUNCDESC:
        case R_SH_GOTFUNCDESC20:
          if (!sh_elf_handle_got_relocation (abfd, info, htab, h, r_symndx, r_type, symtab_hdr))
            return false;
          break;

        case R_SH_TLS_LD_32:
          htab->tls_ldm_got.refcount += 1;
          break;

        case R_SH_FUNCDESC:
        case R_SH_GOTOFFFUNCDESC:
        case R_SH_GOTOFFFUNCDESC20:
          if (!sh_elf_handle_funcdesc_relocation (abfd, info, htab, h, r_symndx, r_type, rel->r_addend, symtab_hdr))
            return false;
          break;

        case R_SH_GOTPLT32:
          if (h == NULL
              || h->forced_local
              || ! bfd_link_pic (info)
              || info->symbolic
              || h->dynindx == -1)
            {
              /* This path corresponds to the original 'goto force_got'
                 and implies treating it as a generic GOT_NORMAL relocation. */
              if (!sh_elf_handle_got_relocation (abfd, info, htab, h, r_symndx, R_SH_GOT32, symtab_hdr))
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
          if (h != NULL && !h->forced_local)
            {
              h->needs_plt = 1;
              h->plt.refcount += 1;
            }
          break;

        case R_SH_DIR32:
        case R_SH_REL32:
          if (!sh_elf_handle_dir_rel_relocation (abfd, info, htab, sec, h, r_symndx, r_type, &sreloc))
            return false;
          break;

        case R_SH_TLS_LE_32:
          if (bfd_link_dll (info))
            {
              _bfd_error_handler (_("%pB: TLS local exec code cannot be linked into shared objects"), abfd);
              return false;
            }
          break;

        case R_SH_TLS_LDO_32:
          /* Nothing to do. */
          break;

        default:
          break;
        }
    }

  return true;
}

#ifndef sh_elf_set_mach_from_flags
static unsigned int sh_ef_bfd_table[] = { EF_SH_BFD_TABLE };

static bool
sh_elf_set_mach_from_flags (bfd *abfd)
{
  const Elf_Internal_Ehdr *ehdr;
  flagword flags;

  if (abfd == NULL)
    return false;

  ehdr = elf_elfheader (abfd);
  if (ehdr == NULL)
    return false;

  flags = ehdr->e_flags & EF_SH_MACH_MASK;

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
  int found_index = -1;

  for (int i = ARRAY_SIZE(sh_ef_bfd_table) - 1; i > 0; i--)
    {
      if (sh_ef_bfd_table[i] == mach)
        {
          found_index = i;
          break;
        }
    }

  if (found_index == -1)
    {
      BFD_FAIL();
    }

  return found_index;
}
#endif /* not sh_elf_set_mach_from_flags */

#ifndef sh_elf_copy_private_data
/* Copy backend specific data from one object module to another */

static bool
sh_elf_copy_private_data (bfd * ibfd, bfd * obfd)
{
  const bool ibfd_is_sh_elf_type = is_sh_elf(ibfd);
  const bool obfd_is_sh_elf_type = is_sh_elf(obfd);

  if (!ibfd_is_sh_elf_type || !obfd_is_sh_elf_type)
    return true;

  if (! _bfd_elf_copy_private_bfd_data (ibfd, obfd))
    return false;

  return sh_elf_set_mach_from_flags (obfd);
}
#endif /* not sh_elf_copy_private_data */

#ifndef sh_elf_merge_private_data

/* This function returns the ELF architecture number that
   corresponds to the given arch_sh* flags.  */

int
sh_find_elf_flags (unsigned int arch_set)
{
  unsigned long bfd_mach = sh_get_bfd_mach_from_arch_set (arch_set);

  if (bfd_mach == 0)
    {
      return -1;
    }

  return sh_elf_get_flags_from_mach (bfd_mach);
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
  if (! _bfd_generic_verify_endian_match (ibfd, info))
    return false;

  bfd *obfd = info->output_bfd;
  const unsigned int old_arch = sh_get_arch_up_from_bfd_mach (bfd_get_mach (obfd));
  const unsigned int new_arch = sh_get_arch_up_from_bfd_mach (bfd_get_mach (ibfd));
  const unsigned int merged_arch = SH_MERGE_ARCH_SET (old_arch, new_arch);

  if (!SH_VALID_CO_ARCH_SET (merged_arch))
    {
      const char *new_arch_instr_type = SH_ARCH_SET_HAS_DSP(new_arch) ? "dsp" : "floating point";
      const char *old_arch_instr_type = SH_ARCH_SET_HAS_DSP(old_arch) ? "dsp" : "floating point";

      _bfd_error_handler
	/* xgettext:c-format */
	(_("%pB: uses %s instructions while previous modules "
	   "use %s instructions"),
	 ibfd,
	 new_arch_instr_type,
	 old_arch_instr_type);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  else if (!SH_VALID_ARCH_SET (merged_arch))
    {
      _bfd_error_handler
	/* xgettext:c-format */
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

static bool
sh_elf_merge_private_data (bfd *ibfd, struct bfd_link_info *info)
{
  bfd *obfd = info->output_bfd;
  Elf_Internal_Ehdr *obfd_ehdr = elf_elfheader (obfd);
  Elf_Internal_Ehdr *ibfd_ehdr = elf_elfheader (ibfd);

  if ((ibfd->flags & DYNAMIC) != 0)
    return true;

  if (!is_sh_elf (ibfd) || !is_sh_elf (obfd))
    return true;

  if (!elf_flags_init (obfd))
    {
      elf_flags_init (obfd) = true;
      obfd_ehdr->e_flags = ibfd_ehdr->e_flags;
      sh_elf_set_mach_from_flags (obfd);
      if (obfd_ehdr->e_flags & EF_SH_FDPIC)
	obfd_ehdr->e_flags &= ~EF_SH_PIC;
    }

  if (!sh_merge_bfd_arch (ibfd, info))
    {
      _bfd_error_handler (_("%pB: uses instructions which are incompatible "
			    "with instructions used in previous modules"),
			  ibfd);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  obfd_ehdr->e_flags &= ~EF_SH_MACH_MASK;
  obfd_ehdr->e_flags |= sh_elf_get_flags_from_mach (bfd_get_mach (obfd));

  if (fdpic_object_p (ibfd) != fdpic_object_p (obfd))
    {
      _bfd_error_handler (_("%pB: attempt to mix FDPIC and non-FDPIC objects"),
			  ibfd);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  return true;
}
#endif /* not sh_elf_merge_private_data */

/* Override the generic function because we need to store sh_elf_obj_tdata
   as the specific tdata.  We set also the machine architecture from flags
   here.  */

static bool
sh_elf_object_p (bfd *abfd)
{
  if (!sh_elf_set_mach_from_flags(abfd))
    return false;

  const Elf_Internal_Ehdr *ehdr = elf_elfheader(abfd);
  if (ehdr == NULL)
    return false;

  bool fdpic_flag_set = (ehdr->e_flags & EF_SH_FDPIC) != 0;
  bool is_fdpic_object = fdpic_object_p(abfd);

  return fdpic_flag_set == is_fdpic_object;
}

/* Finish up dynamic symbol handling.  We set the contents of various
   dynamic sections here.  */

static bfd_vma
calculate_plt_got_offset (struct elf_sh_link_hash_table *htab,
                          bfd_vma plt_index,
                          asection *sgotplt,
                          struct bfd_link_info *info)
{
  bfd_vma got_offset;

  if (htab->fdpic_p)
    got_offset = plt_index * 8 + 12 - sgotplt->size;
  else
    got_offset = (plt_index + 3) * 4;

#ifdef GOT_BIAS
  if (bfd_link_pic (info))
    got_offset -= GOT_BIAS;
#endif

  return got_offset;
}

static void
install_plt_entry_fields (bfd *output_bfd,
                          struct elf_sh_link_hash_table *htab,
                          struct bfd_link_info *info,
                          const struct elf_sh_plt_info *plt_info,
                          asection *splt,
                          asection *sgotplt,
                          bfd_vma h_plt_offset,
                          bfd_vma got_offset_for_fields,
                          bfd_vma plt_index)
{
  memcpy (splt->contents + h_plt_offset,
          plt_info->symbol_entry,
          plt_info->symbol_entry_size);

  if (bfd_link_pic (info) || htab->fdpic_p)
    {
      if (plt_info->symbol_fields.got20)
        {
          bfd_reloc_status_type r;
          r = install_movi20_field (output_bfd, got_offset_for_fields,
                                    splt->owner, splt, splt->contents,
                                    h_plt_offset + plt_info->symbol_fields.got_entry);
          BFD_ASSERT (r == bfd_reloc_ok);
        }
      else
        install_plt_field (output_bfd, false, got_offset_for_fields,
                           (splt->contents + h_plt_offset + plt_info->symbol_fields.got_entry));
    }
  else
    {
      BFD_ASSERT (!plt_info->symbol_fields.got20);

      install_plt_field (output_bfd, false,
                         (sgotplt->output_section->vma + sgotplt->output_offset + got_offset_for_fields),
                         (splt->contents + h_plt_offset + plt_info->symbol_fields.got_entry));

      if (htab->root.target_os == is_vxworks)
        {
          unsigned int reachable_plts;
          unsigned int plts_per_4k;
          int distance;

          reachable_plts = ((4096 - plt_info->plt0_entry_size - (plt_info->symbol_fields.plt + 4))
                            / plt_info->symbol_entry_size) + 1;
          plts_per_4k = (4096 / plt_info->symbol_entry_size);

          if (plt_index < reachable_plts)
            distance = -(h_plt_offset + plt_info->symbol_fields.plt);
          else
            distance = -(((plt_index - reachable_plts) % plts_per_4k + 1)
                         * plt_info->symbol_entry_size);

          bfd_put_16 (output_bfd,
                      0xa000 | (0x0fff & ((distance - 4) / 2)),
                      (splt->contents + h_plt_offset + plt_info->symbol_fields.plt));
        }
      else
        install_plt_field (output_bfd, true,
                           splt->output_section->vma + splt->output_offset,
                           (splt->contents + h_plt_offset + plt_info->symbol_fields.plt));
    }

  if (plt_info->symbol_fields.reloc_offset != MINUS_ONE)
    install_plt_field (output_bfd, false,
                       plt_index * sizeof (Elf32_External_Rela),
                       (splt->contents + h_plt_offset + plt_info->symbol_fields.reloc_offset));
}

static void
fill_got_plt_contents (bfd *output_bfd,
                       struct elf_sh_link_hash_table *htab,
                       asection *splt,
                       asection *sgotplt,
                       bfd_vma h_plt_offset,
                       bfd_vma got_offset_for_contents,
                       const struct elf_sh_plt_info *plt_info)
{
  bfd_put_32 (output_bfd,
              (splt->output_section->vma
               + splt->output_offset
               + h_plt_offset
               + plt_info->symbol_resolve_offset),
              sgotplt->contents + got_offset_for_contents);
  if (htab->fdpic_p)
    bfd_put_32 (output_bfd,
                sh_elf_osec_to_segment (output_bfd, splt->output_section),
                sgotplt->contents + got_offset_for_contents + 4);
}

static void
create_rela_plt_relocation (bfd *output_bfd,
                            struct elf_sh_link_hash_table *htab,
                            struct elf_link_hash_entry *h,
                            asection *srelplt,
                            asection *sgotplt,
                            bfd_vma plt_index,
                            bfd_vma got_offset_for_reloc)
{
  Elf_Internal_Rela rel;
  bfd_byte *loc = srelplt->contents + plt_index * sizeof (Elf32_External_Rela);

  rel.r_offset = (sgotplt->output_section->vma + sgotplt->output_offset + got_offset_for_reloc);
  rel.r_info = ELF32_R_INFO (h->dynindx, htab->fdpic_p ? R_SH_FUNCDESC_VALUE : R_SH_JMP_SLOT);
  rel.r_addend = 0;
#ifdef GOT_BIAS
  rel.r_addend = GOT_BIAS;
#endif
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
}

static void
create_vxworks_srelplt2_relocations (bfd *output_bfd,
                                     struct elf_sh_link_hash_table *htab,
                                     struct bfd_link_info *info,
                                     asection *splt,
                                     asection *sgotplt,
                                     bfd_vma plt_index,
                                     bfd_vma h_plt_offset,
                                     bfd_vma got_offset_for_relocs,
                                     const struct elf_sh_plt_info *plt_info)
{
  if (htab->root.target_os != is_vxworks || bfd_link_pic (info))
    return;

  Elf_Internal_Rela rel;
  bfd_byte *loc = htab->srelplt2->contents + (plt_index * 2 + 1) * sizeof (Elf32_External_Rela);

  rel.r_offset = (splt->output_section->vma + splt->output_offset + h_plt_offset + plt_info->symbol_fields.got_entry);
  rel.r_info = ELF32_R_INFO (htab->root.hgot->indx, R_SH_DIR32);
  rel.r_addend = got_offset_for_relocs;
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
  loc += sizeof (Elf32_External_Rela);

  rel.r_offset = (sgotplt->output_section->vma + sgotplt->output_offset + got_offset_for_relocs);
  rel.r_info = ELF32_R_INFO (htab->root.hplt->indx, R_SH_DIR32);
  rel.r_addend = 0;
  bfd_elf32_swap_reloc_out (output_bfd, &rel, loc);
}

static void
handle_plt_entry (bfd *output_bfd, struct bfd_link_info *info,
                  struct elf_link_hash_entry *h,
                  struct elf_sh_link_hash_table *htab)
{
  asection *splt = htab->root.splt;
  asection *sgotplt = htab->root.sgotplt;
  asection *srelplt = htab->root.srelplt;

  BFD_ASSERT (h->dynindx != -1);
  BFD_ASSERT (splt != NULL && sgotplt != NULL && srelplt != NULL);

  bfd_vma plt_index = get_plt_index (htab->plt_info, h->plt.offset);

  const struct elf_sh_plt_info *plt_info = htab->plt_info;
  if (plt_info->short_plt != NULL && plt_index <= MAX_SHORT_PLT)
    plt_info = plt_info->short_plt;

  bfd_vma got_offset_for_plt_fields = calculate_plt_got_offset (htab, plt_index, sgotplt, info);

  install_plt_entry_fields (output_bfd, htab, info, plt_info, splt, sgotplt,
                            h->plt.offset, got_offset_for_plt_fields, plt_index);

  bfd_vma got_offset_for_got_rela_entries = got_offset_for_plt_fields;
#ifdef GOT_BIAS
  if (bfd_link_pic (info))
    got_offset_for_got_rela_entries += GOT_BIAS;
#endif
  if (htab->fdpic_p)
    got_offset_for_got_rela_entries = plt_index * 8;

  fill_got_plt_contents (output_bfd, htab, splt, sgotplt,
                         h->plt.offset, got_offset_for_got_rela_entries, plt_info);

  create_rela_plt_relocation (output_bfd, htab, h, srelplt, sgotplt,
                              plt_index, got_offset_for_got_rela_entries);

  create_vxworks_srelplt2_relocations (output_bfd, htab, info, splt, sgotplt,
                                        plt_index, h->plt.offset, got_offset_for_got_rela_entries, plt_info);
}

static void
handle_got_entry (bfd *output_bfd, struct bfd_link_info *info,
                  struct elf_link_hash_entry *h,
                  struct elf_sh_link_hash_table *htab)
{
  asection *sgot = htab->root.sgot;
  asection *srelgot = htab->root.srelgot;

  BFD_ASSERT (sgot != NULL && srelgot != NULL);

  Elf_Internal_Rela rel;
  rel.r_offset = (sgot->output_section->vma + sgot->output_offset + (h->got.offset &~ (bfd_vma) 1));

  if (bfd_link_pic (info)
      && (h->root.type == bfd_link_hash_defined || h->root.type == bfd_link_hash_defweak)
      && SYMBOL_REFERENCES_LOCAL (info, h))
    {
      if (htab->fdpic_p)
        {
          asection *sec = h->root.u.def.section;
          int dynindx = elf_section_data (sec->output_section)->dynindx;
          rel.r_info = ELF32_R_INFO (dynindx, R_SH_DIR32);
          rel.r_addend = (h->root.u.def.value + h->root.u.def.section->output_offset);
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

  bfd_byte *loc = srelgot->contents;
  loc += srelgot->reloc_count++ * sizeof (Elf32_External_Rela);
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
}

static void
handle_copy_relocation (bfd *output_bfd,
                        struct elf_link_hash_entry *h,
                        struct elf_sh_link_hash_table *htab)
{
  BFD_ASSERT (h->dynindx != -1
              && (h->root.type == bfd_link_hash_defined
                  || h->root.type == bfd_link_hash_defweak));

  asection *s = bfd_get_linker_section (htab->root.dynobj, ".rela.bss");
  BFD_ASSERT (s != NULL);

  Elf_Internal_Rela rel;
  rel.r_offset = (h->root.u.def.value
                  + h->root.u.def.section->output_section->vma
                  + h->root.u.def.section->output_offset);
  rel.r_info = ELF32_R_INFO (h->dynindx, R_SH_COPY);
  rel.r_addend = 0;

  bfd_byte *loc = s->contents + s->reloc_count++ * sizeof (Elf32_External_Rela);
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
}

static bool
sh_elf_finish_dynamic_symbol (bfd *output_bfd, struct bfd_link_info *info,
                              struct elf_link_hash_entry *h,
                              Elf_Internal_Sym *sym)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);

  if (h->plt.offset != (bfd_vma) -1)
    {
      handle_plt_entry (output_bfd, info, h, htab);

      if (!h->def_regular)
        sym->st_shndx = SHN_UNDEF;
    }

  if (h->got.offset != (bfd_vma) -1
      && sh_elf_hash_entry (h)->got_type != GOT_TLS_GD
      && sh_elf_hash_entry (h)->got_type != GOT_TLS_IE
      && sh_elf_hash_entry (h)->got_type != GOT_FUNCDESC)
    {
      handle_got_entry (output_bfd, info, h, htab);
    }

  if (h->needs_copy)
    {
      handle_copy_relocation (output_bfd, h, htab);
    }

  if (h == htab->root.hdynamic
      || (htab->root.target_os != is_vxworks && h == htab->root.hgot))
    sym->st_shndx = SHN_ABS;

  return true;
}

/* Finish up the dynamic sections.  */

static bool
update_dynamic_entry_value(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                           Elf_Internal_Dyn *dyn_internal, Elf32_External_Dyn *dyn_external)
{
  asection *s;

  switch (dyn_internal->d_tag)
    {
    case DT_PLTGOT:
      BFD_ASSERT (htab->root.hgot != NULL);
      s = htab->root.hgot->root.u.def.section;
      BFD_ASSERT (s != NULL && s->output_section != NULL);
      dyn_internal->d_un.d_ptr = htab->root.hgot->root.u.def.value
                               + s->output_section->vma + s->output_offset;
      break;

    case DT_JMPREL:
      s = htab->root.srelplt;
      BFD_ASSERT (s != NULL && s->output_section != NULL);
      dyn_internal->d_un.d_ptr = s->output_section->vma + s->output_offset;
      break;

    case DT_PLTRELSZ:
      s = htab->root.srelplt;
      BFD_ASSERT (s != NULL);
      dyn_internal->d_un.d_val = s->size;
      break;

    default:
      if (htab->root.target_os == is_vxworks
          && elf_vxworks_finish_dynamic_entry (output_bfd, dyn_internal))
        return true;

      return false;
    }
  bfd_elf32_swap_dyn_out (output_bfd, dyn_internal, dyn_external);
  return true;
}

static bool
handle_vxworks_plt_rela(bfd *output_bfd, struct elf_sh_link_hash_table *htab, asection *splt)
{
  if (!htab->srelplt2 || !htab->root.hgot || !htab->root.hplt)
    return false;

  if (!htab->srelplt2->contents || htab->srelplt2->size == 0)
    return false;

  Elf_Internal_Rela rel;
  bfd_byte *current_loc = htab->srelplt2->contents;

  if (!splt || !splt->output_section || !htab->plt_info
      || htab->plt_info->plt0_got_fields[2] == MINUS_ONE)
    return false;

  rel.r_offset = (splt->output_section->vma
                  + splt->output_offset
                  + htab->plt_info->plt0_got_fields[2]);
  rel.r_info = ELF32_R_INFO (htab->root.hgot->indx, R_SH_DIR32);
  rel.r_addend = 8;
  bfd_elf32_swap_reloca_out (output_bfd, &rel, current_loc);
  current_loc += sizeof (Elf32_External_Rela);

  while (current_loc < htab->srelplt2->contents + htab->srelplt2->size)
    {
      bfd_elf32_swap_reloc_in (output_bfd, current_loc, &rel);
      rel.r_info = ELF32_R_INFO (htab->root.hgot->indx, R_SH_DIR32);
      bfd_elf32_swap_reloc_out (output_bfd, &rel, current_loc);
      current_loc += sizeof (Elf32_External_Rela);

      bfd_elf32_swap_reloc_in (output_bfd, current_loc, &rel);
      rel.r_info = ELF32_R_INFO (htab->root.hplt->indx, R_SH_DIR32);
      bfd_elf32_swap_reloc_out (output_bfd, &rel, current_loc);
      current_loc += sizeof (Elf32_External_Rela);
    }
  return true;
}

static bool
fill_plt_first_entry(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                     asection *sgotplt, asection *splt)
{
  if (!splt || splt->size == 0 || !htab->plt_info || !htab->plt_info->plt0_entry)
    return false;

  if (!splt->contents)
    return false;

  memcpy (splt->contents,
          htab->plt_info->plt0_entry,
          htab->plt_info->plt0_entry_size);

  if (!sgotplt || !sgotplt->output_section)
    return false;

  bfd_vma sgotplt_base_vma = sgotplt->output_section->vma + sgotplt->output_offset;

  for (unsigned int i = 0; i < ARRAY_SIZE (htab->plt_info->plt0_got_fields); ++i)
    {
      if (htab->plt_info->plt0_got_fields[i] != MINUS_ONE)
        {
          install_plt_field (output_bfd, false,
                             sgotplt_base_vma + (i * 4),
                             splt->contents + htab->plt_info->plt0_got_fields[i]);
        }
    }

  if (htab->root.target_os == is_vxworks)
    {
      if (!handle_vxworks_plt_rela(output_bfd, htab, splt))
        return false;
    }

  if (splt->output_section)
    elf_section_data (splt->output_section)->this_hdr.sh_entsize = 4;
  return true;
}

static bool
fill_got_first_entries(bfd *output_bfd, asection *sgotplt, asection *sdyn, bool is_fdpic)
{
  if (!sgotplt || sgotplt->size == 0 || is_fdpic)
    return false;

  if (!sgotplt->contents)
    return false;

  bfd_vma dynamic_section_vma = 0;
  if (sdyn && sdyn->output_section)
    dynamic_section_vma = sdyn->output_section->vma + sdyn->output_offset;

  bfd_put_32 (output_bfd, dynamic_section_vma, sgotplt->contents);
  bfd_put_32 (output_bfd, (bfd_vma) 0, sgotplt->contents + 4);
  bfd_put_32 (output_bfd, (bfd_vma) 0, sgotplt->contents + 8);
  return true;
}

static bool
sh_elf_finish_dynamic_sections (bfd *output_bfd, struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  asection *sgotplt = htab->root.sgotplt;
  asection *sdyn = bfd_get_linker_section (htab->root.dynobj, ".dynamic");

  if (htab->root.dynamic_sections_created)
    {
      BFD_ASSERT (sgotplt != NULL && sdyn != NULL);
      if (!sgotplt || !sdyn)
        return false;

      if (!sdyn->contents || sdyn->size == 0)
        return false;

      Elf32_External_Dyn *dyncon_ptr = (Elf32_External_Dyn *) sdyn->contents;
      Elf32_External_Dyn *dyncon_end = (Elf32_External_Dyn *) (sdyn->contents + sdyn->size);

      for (; dyncon_ptr < dyncon_end; ++dyncon_ptr)
        {
          Elf_Internal_Dyn dyn_internal;
          bfd_elf32_swap_dyn_in (htab->root.dynobj, dyncon_ptr, &dyn_internal);
          (void) update_dynamic_entry_value(output_bfd, htab, &dyn_internal, dyncon_ptr);
        }

      asection *splt = htab->root.splt;
      if (!fill_plt_first_entry(output_bfd, htab, sgotplt, splt))
        return false;
    }

  (void) fill_got_first_entries(output_bfd, sgotplt, sdyn, htab->fdpic_p);

  if (sgotplt && sgotplt->size > 0 && sgotplt->output_section)
    elf_section_data (sgotplt->output_section)->this_hdr.sh_entsize = 4;

  if (htab->fdpic_p && htab->srofixup != NULL)
    {
      struct elf_link_hash_entry *hgot = htab->root.hgot;
      if (!hgot || !hgot->root.u.def.section || !hgot->root.u.def.section->output_section)
        return false;

      bfd_vma got_value = hgot->root.u.def.value
                        + hgot->root.u.def.section->output_section->vma
                        + hgot->root.u.def.section->output_offset;

      sh_elf_add_rofixup (output_bfd, htab->srofixup, got_value);

      BFD_ASSERT (htab->srofixup->reloc_count * 4 == htab->srofixup->size);
    }

  if (htab->srelfuncdesc)
    BFD_ASSERT (htab->srelfuncdesc->reloc_count * sizeof (Elf32_External_Rela)
                == htab->srelfuncdesc->size);

  if (htab->root.srelgot)
    BFD_ASSERT (htab->root.srelgot->reloc_count * sizeof (Elf32_External_Rela)
                == htab->root.srelgot->size);

  return true;
}

static enum elf_reloc_type_class
sh_elf_reloc_type_class (const struct bfd_link_info *info ATTRIBUTE_UNUSED,
			 const asection *rel_sec ATTRIBUTE_UNUSED,
			 const Elf_Internal_Rela *rela)
{
  switch (ELF32_R_TYPE (rela->r_info))
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
  enum
  {
    NOTE_PRSTATUS_SH_DESCSZ = 168,
    NOTE_PRSTATUS_SH_CURSIG_OFFSET = 12,
    NOTE_PRSTATUS_SH_PID_OFFSET = 24,
    NOTE_PRSTATUS_SH_REG_OFFSET = 72,
    NOTE_PRSTATUS_SH_REG_SIZE = 92
  };

  unsigned int reg_offset;
  unsigned int reg_size;
  elf_data_type *data = elf_tdata (abfd);

  if (!data || !data->core)
    {
      return false;
    }

  switch (note->descsz)
    {
      default:
	return false;

      case NOTE_PRSTATUS_SH_DESCSZ:
	data->core->signal = bfd_get_16 (abfd, note->descdata + NOTE_PRSTATUS_SH_CURSIG_OFFSET);
	data->core->lwpid = bfd_get_32 (abfd, note->descdata + NOTE_PRSTATUS_SH_PID_OFFSET);

	reg_offset = NOTE_PRSTATUS_SH_REG_OFFSET;
	reg_size = NOTE_PRSTATUS_SH_REG_SIZE;

	break;
    }

  return _bfd_elfcore_make_pseudosection (abfd, ".reg",
					  reg_size, note->descpos + reg_offset);
}

static bool
elf32_shlin_grok_psinfo (bfd *abfd, Elf_Internal_Note *note)
{
  /* Constants for Linux/SH elf_prpsinfo structure offsets and lengths.
     These would typically be defined as preprocessor macros or global
     constants in a header file or the compilation unit. */
#define ELF_PRPSINFO_DESCSZ_SH 124
#define ELF_PRPSINFO_PROGRAM_OFFSET 28
#define ELF_PRPSINFO_PROGRAM_LENGTH 16
#define ELF_PRPSINFO_COMMAND_OFFSET 44
#define ELF_PRPSINFO_COMMAND_LENGTH 80

  switch (note->descsz)
    {
      default:
	return false;

      case ELF_PRPSINFO_DESCSZ_SH:
	{
	  char *program_str = _bfd_elfcore_strndup (abfd,
						   note->descdata + ELF_PRPSINFO_PROGRAM_OFFSET,
						   ELF_PRPSINFO_PROGRAM_LENGTH);
	  if (program_str == NULL)
	    return false; /* Memory allocation or string copy failed */

	  elf_tdata (abfd)->core->program = program_str;

	  char *command_str = _bfd_elfcore_strndup (abfd,
						   note->descdata + ELF_PRPSINFO_COMMAND_OFFSET,
						   ELF_PRPSINFO_COMMAND_LENGTH);
	  if (command_str == NULL)
	    {
	      /* _bfd_elfcore_strndup failures imply memory issues.
	         The BFD library's core processing is expected to clean up
	         previously allocated strings upon bfd_core_close, so
	         explicitly freeing program_str here is not needed to
	         maintain external functionality. */
	      return false;
	    }
	  elf_tdata (abfd)->core->command = command_str;
	}
	break; /* Exit switch after handling the case */
    }

  /* Note that for some reason, a spurious space is tacked
     onto the end of the args in some (at least one anyway)
     implementations, so strip it off if it exists.
     At this point, elf_tdata(abfd)->core->command is guaranteed
     to be non-NULL if the function has not returned false earlier. */
  {
    char *command_to_trim = elf_tdata (abfd)->core->command;
    size_t n = strlen (command_to_trim);

    if (n > 0 && command_to_trim[n - 1] == ' ')
      command_to_trim[n - 1] = '\0';
  }

  return true;

#undef ELF_PRPSINFO_DESCSZ_SH
#undef ELF_PRPSINFO_PROGRAM_OFFSET
#undef ELF_PRPSINFO_PROGRAM_LENGTH
#undef ELF_PRPSINFO_COMMAND_OFFSET
#undef ELF_PRPSINFO_COMMAND_LENGTH
}
#endif /* not SH_TARGET_ALREADY_DEFINED */


/* Return address for Ith PLT stub in section PLT, for relocation REL
   or (bfd_vma) -1 if it should not be included.  */

static bfd_vma
sh_elf_plt_sym_val (bfd_vma i, const asection *plt,
		    const arelent *rel ATTRIBUTE_UNUSED)
{
  const struct elf_sh_plt_info *plt_info;

  if (plt == NULL || plt->owner == NULL)
    {
      return 0;
    }

  plt_info = get_plt_info (plt->owner, (plt->owner->flags & DYNAMIC) != 0);

  if (plt_info == NULL)
    {
      return 0;
    }

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

  if (!htab || !htab->fdpic_p)
    {
      return _bfd_elf_encode_eh_address (abfd, info, osec, offset, loc_sec,
                                         loc_offset, encoded);
    }

  struct elf_link_hash_entry *hgot_entry = htab->root.hgot;

  if (!hgot_entry || hgot_entry->root.type != bfd_link_hash_defined)
    {
      return _bfd_elf_encode_eh_address (abfd, info, osec, offset, loc_sec,
                                         loc_offset, encoded);
    }

  bfd_vma osec_segment_id = sh_elf_osec_to_segment (abfd, osec);
  bfd_vma loc_sec_output_segment_id = sh_elf_osec_to_segment (abfd, loc_sec->output_section);

  if (osec_segment_id == loc_sec_output_segment_id)
    {
      return _bfd_elf_encode_eh_address (abfd, info, osec, offset, loc_sec,
                                         loc_offset, encoded);
    }

  asection *hgot_def_section = hgot_entry->root.u.def.section;

  if (!hgot_def_section || !hgot_def_section->output_section)
    {
      return _bfd_elf_encode_eh_address (abfd, info, osec, offset, loc_sec,
                                         loc_offset, encoded);
    }

  bfd_vma hgot_section_output_segment_id = sh_elf_osec_to_segment (abfd, hgot_def_section->output_section);

  if (osec_segment_id != hgot_section_output_segment_id)
    {
      return _bfd_elf_encode_eh_address (abfd, info, osec, offset, loc_sec,
                                         loc_offset, encoded);
    }

  bfd_vma hgot_resolved_address = hgot_entry->root.u.def.value
                                + hgot_def_section->output_section->vma
                                + hgot_def_section->output_offset;

  *encoded = osec->vma + offset - hgot_resolved_address;

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
