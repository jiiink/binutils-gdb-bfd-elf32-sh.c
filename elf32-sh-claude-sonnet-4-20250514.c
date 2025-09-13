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
vxworks_object_p (bfd *abfd)
{
#if !defined SH_TARGET_ALREADY_DEFINED
  extern const bfd_target sh_elf32_vxworks_le_vec;
  extern const bfd_target sh_elf32_vxworks_vec;

  if (!abfd || !abfd->xvec) {
    return false;
  }

  return (abfd->xvec == &sh_elf32_vxworks_le_vec ||
          abfd->xvec == &sh_elf32_vxworks_vec);
#else
  return false;
#endif
}

/* Return true if OUTPUT_BFD is an FDPIC object.  */

static bool
fdpic_object_p (bfd *abfd)
{
#if !defined SH_TARGET_ALREADY_DEFINED
  extern const bfd_target sh_elf32_fdpic_le_vec;
  extern const bfd_target sh_elf32_fdpic_be_vec;

  if (!abfd || !abfd->xvec) {
    return false;
  }

  return (abfd->xvec == &sh_elf32_fdpic_le_vec ||
          abfd->xvec == &sh_elf32_fdpic_be_vec);
#else
  return false;
#endif
}

/* Return the howto table for ABFD.  */

static reloc_howto_type *
get_howto_table (bfd *abfd)
{
  if (abfd == NULL)
    return NULL;
    
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
  bfd_byte *start_ptr, *ptr, *last_ptr;
  int diff, cum_diff;
  bfd_signed_vma x;
  int insn;
  bfd_byte *symbol_contents = NULL;
  bfd_boolean free_symbol_contents = FALSE;

  if (addr > bfd_get_section_limit (input_bfd, input_section))
    return bfd_reloc_outofrange;

  if (!last_addr)
    {
      last_addr = addr;
      last_symbol_section = symbol_section;
      return bfd_reloc_ok;
    }
  
  if (last_addr != addr)
    return bfd_reloc_dangerous;
  
  last_addr = 0;

  if (!symbol_section || last_symbol_section != symbol_section || end < start)
    return bfd_reloc_outofrange;

  if (symbol_section != input_section)
    {
      if (elf_section_data (symbol_section)->this_hdr.contents != NULL)
	symbol_contents = elf_section_data (symbol_section)->this_hdr.contents;
      else
	{
	  if (!bfd_malloc_and_get_section (input_bfd, symbol_section, &symbol_contents))
	    {
	      free (symbol_contents);
	      return bfd_reloc_outofrange;
	    }
	  free_symbol_contents = TRUE;
	}
    }
  else
    {
      symbol_contents = contents;
    }

  start_ptr = symbol_contents + start;
  for (cum_diff = -6, ptr = symbol_contents + end; cum_diff < 0 && ptr > start_ptr;)
    {
      for (last_ptr = ptr, ptr -= 4; ptr >= start_ptr && ((bfd_get_16 (input_bfd, ptr) & 0xfc00) == 0xf800);)
	ptr -= 2;
      ptr += 2;
      diff = (last_ptr - ptr) >> 1;
      cum_diff += diff & 1;
      cum_diff += diff;
    }

  if (cum_diff >= 0)
    {
      start -= 4;
      end = (ptr + cum_diff * 2) - symbol_contents;
    }
  else
    {
      bfd_vma start0 = start - 4;

      while (start0 && ((bfd_get_16 (input_bfd, symbol_contents + start0) & 0xfc00) == 0xf800))
	start0 -= 2;
      start0 = start - 2 - ((start - start0) & 2);
      start = start0 - cum_diff - 2;
      end = start0;
    }

  if (free_symbol_contents)
    free (symbol_contents);

  insn = bfd_get_16 (input_bfd, contents + addr);

  x = (insn & 0x200 ? end : start) - addr;
  if (input_section != symbol_section)
    x += ((symbol_section->output_section->vma + symbol_section->output_offset)
	  - (input_section->output_section->vma + input_section->output_offset));
  x >>= 1;
  
  if (x < -128 || x > 127)
    return bfd_reloc_overflow;

  x = (insn & ~0xff) | (x & 0xff);
  bfd_put_16 (input_bfd, (bfd_vma) x, contents + addr);

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
  bfd_vma addr;
  bfd_size_type octets;
  bfd_byte *hit_data;

  if (!abfd || !reloc_entry || !symbol_in || !data || !input_section)
    return bfd_reloc_notsupported;

  addr = reloc_entry->address;
  octets = addr * OCTETS_PER_BYTE (abfd, input_section);
  hit_data = (bfd_byte *) data + octets;
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

  if (octets + bfd_get_reloc_size (reloc_entry->howto) > bfd_get_section_limit_octets (abfd, input_section))
    return bfd_reloc_outofrange;

  if (bfd_is_com_section (symbol_in->section))
    {
      sym_value = 0;
    }
  else
    {
      sym_value = symbol_in->value +
                  symbol_in->section->output_section->vma +
                  symbol_in->section->output_offset;
    }

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
      sym_value -= (input_section->output_section->vma +
                    input_section->output_offset +
                    addr + 4);
      sym_value += (((insn & 0xfff) ^ 0x800) - 0x800) << 1;
      insn = (insn & 0xf000) | ((sym_value >> 1) & 0xfff);
      bfd_put_16 (abfd, insn, hit_data);
      if (sym_value + 0x1000 >= 0x2000 || (sym_value & 1) != 0)
        return bfd_reloc_overflow;
      break;

    default:
      return bfd_reloc_notsupported;
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
  if (reloc_entry == NULL || input_section == NULL)
    return bfd_reloc_dangerous;
  
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
  size_t i;
  size_t map_size;
  reloc_howto_type *howto_table;

  if (abfd == NULL)
    return NULL;

  howto_table = get_howto_table (abfd);
  if (howto_table == NULL)
    return NULL;

  map_size = sizeof (sh_reloc_map) / sizeof (sh_reloc_map[0]);

  for (i = 0; i < map_size; i++)
    {
      if (sh_reloc_map[i].bfd_reloc_val == code)
        return howto_table + sh_reloc_map[i].elf_reloc_val;
    }

  return NULL;
}

static reloc_howto_type *
sh_elf_reloc_name_lookup (bfd *abfd, const char *r_name)
{
  unsigned int i;
  const reloc_howto_type *howto_table;
  unsigned int table_size;

  if (r_name == NULL)
    return NULL;

  if (vxworks_object_p (abfd))
    {
      howto_table = sh_vxworks_howto_table;
      table_size = sizeof (sh_vxworks_howto_table) / sizeof (sh_vxworks_howto_table[0]);
    }
  else
    {
      howto_table = sh_elf_howto_table;
      table_size = sizeof (sh_elf_howto_table) / sizeof (sh_elf_howto_table[0]);
    }

  for (i = 0; i < table_size; i++)
    {
      if (howto_table[i].name != NULL
          && strcasecmp (howto_table[i].name, r_name) == 0)
        return (reloc_howto_type *) &howto_table[i];
    }

  return NULL;
}

/* Given an ELF reloc, fill in the howto field of a relent.  */

static bool
sh_elf_info_to_howto (bfd *abfd, arelent *cache_ptr, Elf_Internal_Rela *dst)
{
  unsigned int r;

  if (!abfd || !cache_ptr || !dst)
    {
      bfd_set_error (bfd_error_invalid_operation);
      return false;
    }

  r = ELF32_R_TYPE (dst->r_info);

  if (sh_is_invalid_relocation_type(r))
    {
      _bfd_error_handler (_("%pB: unsupported relocation type %#x"),
                          abfd, r);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  cache_ptr->howto = get_howto_table (abfd) + r;
  return true;
}

static bool
sh_is_invalid_relocation_type(unsigned int r)
{
  return (r >= R_SH_FIRST_INVALID_RELOC_6 ||
          (r >= R_SH_FIRST_INVALID_RELOC && r <= R_SH_LAST_INVALID_RELOC) ||
          (r >= R_SH_FIRST_INVALID_RELOC_2 && r <= R_SH_LAST_INVALID_RELOC_2) ||
          (r >= R_SH_FIRST_INVALID_RELOC_3 && r <= R_SH_LAST_INVALID_RELOC_3) ||
          (r >= R_SH_FIRST_INVALID_RELOC_4 && r <= R_SH_LAST_INVALID_RELOC_4) ||
          (r >= R_SH_FIRST_INVALID_RELOC_5 && r <= R_SH_LAST_INVALID_RELOC_5));
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
  Elf_Internal_Shdr *symtab_hdr;
  Elf_Internal_Rela *internal_relocs = NULL;
  bool have_code;
  Elf_Internal_Rela *irel, *irelend;
  bfd_byte *contents = NULL;
  Elf_Internal_Sym *isymbuf = NULL;
  bool result = false;

  *again = false;

  if (bfd_link_relocatable (link_info)
      || (sec->flags & SEC_HAS_CONTENTS) == 0
      || (sec->flags & SEC_RELOC) == 0
      || sec->reloc_count == 0)
    return true;

  symtab_hdr = &elf_symtab_hdr (abfd);

  internal_relocs = _bfd_elf_link_read_relocs (abfd, sec, NULL, NULL, link_info->keep_memory);
  if (internal_relocs == NULL)
    goto cleanup;

  have_code = false;

  irelend = internal_relocs + sec->reloc_count;
  for (irel = internal_relocs; irel < irelend; irel++)
    {
      if (ELF32_R_TYPE (irel->r_info) == (int) R_SH_CODE)
	have_code = true;

      if (ELF32_R_TYPE (irel->r_info) != (int) R_SH_USES)
	continue;

      if (!process_sh_uses_reloc(abfd, sec, irel, internal_relocs, irelend,
				 &contents, &isymbuf, symtab_hdr, link_info, again))
	continue;
    }

  if ((elf_elfheader (abfd)->e_flags & EF_SH_MACH_MASK) != EF_SH4 && have_code)
    {
      if (!align_sh_loads(abfd, sec, internal_relocs, &contents, &isymbuf, symtab_hdr))
	goto cleanup;
    }

  result = true;

cleanup:
  cleanup_resources(abfd, sec, symtab_hdr, link_info, isymbuf, contents, internal_relocs);
  return result;
}

static bool
process_sh_uses_reloc(bfd *abfd, asection *sec, Elf_Internal_Rela *irel,
		      Elf_Internal_Rela *internal_relocs, Elf_Internal_Rela *irelend,
		      bfd_byte **contents_ptr, Elf_Internal_Sym **isymbuf_ptr,
		      Elf_Internal_Shdr *symtab_hdr, struct bfd_link_info *link_info,
		      bool *again)
{
  bfd_vma laddr, paddr, symval;
  unsigned short insn;
  Elf_Internal_Rela *irelfn, *irelscan, *irelcount;
  bfd_signed_vma foff;
  
  if (!get_section_contents(abfd, sec, contents_ptr))
    return false;

  laddr = irel->r_offset + 4 + irel->r_addend;
  if (laddr >= sec->size)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": warning: bad R_SH_USES offset"),
	 abfd, (uint64_t) irel->r_offset);
      return false;
    }

  insn = bfd_get_16 (abfd, *contents_ptr + laddr);

  if ((insn & 0xf000) != 0xd000)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": warning: R_SH_USES points to unrecognized insn 0x%x"),
	 abfd, (uint64_t) irel->r_offset, insn);
      return false;
    }

  paddr = (insn & 0xff) * 4 + ((laddr + 4) & ~(bfd_vma) 3);
  if (paddr >= sec->size)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": warning: bad R_SH_USES load offset"),
	 abfd, (uint64_t) irel->r_offset);
      return false;
    }

  irelfn = find_dir32_reloc(internal_relocs, irelend, paddr);
  if (irelfn == NULL)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": warning: could not find expected reloc"),
	 abfd, (uint64_t) paddr);
      return false;
    }

  if (!get_symbol_buffer(abfd, symtab_hdr, isymbuf_ptr))
    return false;

  if (!get_symbol_value(abfd, sec, irelfn, *isymbuf_ptr, symtab_hdr, *contents_ptr, paddr, &symval))
    return false;

  foff = symval - (irel->r_offset + sec->output_section->vma + sec->output_offset + 4);
  
  if (foff < -0x1000 || foff >= 0x1000 - 8)
    return false;

  if (!can_shorten_function_call(internal_relocs, irelend, laddr, irel))
    return false;

  if (!perform_function_call_shortening(abfd, sec, irel, irelfn, *contents_ptr, paddr))
    return false;

  if (!delete_register_load(abfd, sec, laddr, again))
    return false;

  irelcount = find_count_reloc(internal_relocs, irelend, paddr);
  if (irelcount == NULL)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": warning: could not find expected COUNT reloc"),
	 abfd, (uint64_t) paddr);
      return false;
    }

  return handle_count_reloc(abfd, sec, irelcount, irelfn);
}

static bool
get_section_contents(bfd *abfd, asection *sec, bfd_byte **contents_ptr)
{
  if (*contents_ptr != NULL)
    return true;

  if (elf_section_data (sec)->this_hdr.contents != NULL)
    {
      *contents_ptr = elf_section_data (sec)->this_hdr.contents;
      return true;
    }

  return bfd_malloc_and_get_section (abfd, sec, contents_ptr);
}

static Elf_Internal_Rela *
find_dir32_reloc(Elf_Internal_Rela *internal_relocs, Elf_Internal_Rela *irelend, bfd_vma paddr)
{
  Elf_Internal_Rela *irelfn;
  
  for (irelfn = internal_relocs; irelfn < irelend; irelfn++)
    {
      if (irelfn->r_offset == paddr && ELF32_R_TYPE (irelfn->r_info) == (int) R_SH_DIR32)
	return irelfn;
    }
  return NULL;
}

static bool
get_symbol_buffer(bfd *abfd, Elf_Internal_Shdr *symtab_hdr, Elf_Internal_Sym **isymbuf_ptr)
{
  if (*isymbuf_ptr != NULL || symtab_hdr->sh_info == 0)
    return true;

  *isymbuf_ptr = (Elf_Internal_Sym *) symtab_hdr->contents;
  if (*isymbuf_ptr == NULL)
    {
      *isymbuf_ptr = bfd_elf_get_elf_syms (abfd, symtab_hdr, symtab_hdr->sh_info, 0, NULL, NULL, NULL);
    }
  return *isymbuf_ptr != NULL;
}

static bool
get_symbol_value(bfd *abfd, asection *sec, Elf_Internal_Rela *irelfn,
		 Elf_Internal_Sym *isymbuf, Elf_Internal_Shdr *symtab_hdr,
		 bfd_byte *contents, bfd_vma paddr, bfd_vma *symval)
{
  if (ELF32_R_SYM (irelfn->r_info) < symtab_hdr->sh_info)
    {
      Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM (irelfn->r_info);
      
      if (isym->st_shndx != (unsigned int) _bfd_elf_section_from_bfd_section (abfd, sec))
	{
	  _bfd_error_handler
	    (_("%pB: %#" PRIx64 ": warning: symbol in unexpected section"),
	     abfd, (uint64_t) paddr);
	  return false;
	}

      *symval = isym->st_value + sec->output_section->vma + sec->output_offset;
    }
  else
    {
      unsigned long indx = ELF32_R_SYM (irelfn->r_info) - symtab_hdr->sh_info;
      struct elf_link_hash_entry *h = elf_sym_hashes (abfd)[indx];
      
      if (h == NULL || (h->root.type != bfd_link_hash_defined && h->root.type != bfd_link_hash_defweak))
	return false;

      *symval = (h->root.u.def.value
		 + h->root.u.def.section->output_section->vma
		 + h->root.u.def.section->output_offset);
    }

  if (get_howto_table (abfd)[R_SH_DIR32].partial_inplace)
    *symval += bfd_get_32 (abfd, contents + paddr);
  else
    *symval += irelfn->r_addend;

  return true;
}

static bool
can_shorten_function_call(Elf_Internal_Rela *internal_relocs, Elf_Internal_Rela *irelend,
			  bfd_vma laddr, Elf_Internal_Rela *irel)
{
  Elf_Internal_Rela *irelscan;
  
  for (irelscan = internal_relocs; irelscan < irelend; irelscan++)
    {
      if (ELF32_R_TYPE (irelscan->r_info) == (int) R_SH_USES
	  && laddr == irelscan->r_offset + 4 + irelscan->r_addend)
	return false;
    }
  return true;
}

static bool
perform_function_call_shortening(bfd *abfd, asection *sec, Elf_Internal_Rela *irel,
				 Elf_Internal_Rela *irelfn, bfd_byte *contents, bfd_vma paddr)
{
  elf_section_data (sec)->this_hdr.contents = contents;

  irel->r_info = ELF32_R_INFO (ELF32_R_SYM (irelfn->r_info), R_SH_IND12W);

  if (bfd_get_16 (abfd, contents + irel->r_offset) & 0x0020)
    bfd_put_16 (abfd, (bfd_vma) 0xa000, contents + irel->r_offset);
  else
    bfd_put_16 (abfd, (bfd_vma) 0xb000, contents + irel->r_offset);

  irel->r_addend = -4 + bfd_get_32 (abfd, contents + paddr);

  return true;
}

static bool
delete_register_load(bfd *abfd, asection *sec, bfd_vma laddr, bool *again)
{
  if (!sh_elf_relax_delete_bytes (abfd, sec, laddr, 2))
    return false;
  
  *again = true;
  return true;
}

static Elf_Internal_Rela *
find_count_reloc(Elf_Internal_Rela *internal_relocs, Elf_Internal_Rela *irelend, bfd_vma paddr)
{
  Elf_Internal_Rela *irelcount;
  
  for (irelcount = internal_relocs; irelcount < irelend; irelcount++)
    {
      if (irelcount->r_offset == paddr && ELF32_R_TYPE (irelcount->r_info) == (int) R_SH_COUNT)
	return irelcount;
    }
  return NULL;
}

static bool
handle_count_reloc(bfd *abfd, asection *sec, Elf_Internal_Rela *irelcount, Elf_Internal_Rela *irelfn)
{
  if (irelcount->r_addend == 0)
    {
      _bfd_error_handler (_("%pB: %#" PRIx64 ": warning: bad count"),
			  abfd, (uint64_t) irelcount->r_offset);
      return false;
    }

  --irelcount->r_addend;

  if (irelcount->r_addend == 0)
    {
      return sh_elf_relax_delete_bytes (abfd, sec, irelfn->r_offset, 4);
    }

  return true;
}

static bool
align_sh_loads(bfd *abfd, asection *sec, Elf_Internal_Rela *internal_relocs,
	       bfd_byte **contents_ptr, Elf_Internal_Sym **isymbuf_ptr,
	       Elf_Internal_Shdr *symtab_hdr)
{
  bool swapped;

  if (!get_section_contents(abfd, sec, contents_ptr))
    return false;

  if (!sh_elf_align_loads (abfd, sec, internal_relocs, *contents_ptr, &swapped))
    return false;

  if (swapped)
    {
      elf_section_data (sec)->relocs = internal_relocs;
      elf_section_data (sec)->this_hdr.contents = *contents_ptr;
      symtab_hdr->contents = (unsigned char *) *isymbuf_ptr;
    }

  return true;
}

static void
cleanup_resources(bfd *abfd, asection *sec, Elf_Internal_Shdr *symtab_hdr,
		  struct bfd_link_info *link_info, Elf_Internal_Sym *isymbuf,
		  bfd_byte *contents, Elf_Internal_Rela *internal_relocs)
{
  if (isymbuf != NULL && symtab_hdr->contents != (unsigned char *) isymbuf)
    {
      if (!link_info->keep_memory)
	free (isymbuf);
      else
	symtab_hdr->contents = (unsigned char *) isymbuf;
    }

  if (contents != NULL && elf_section_data (sec)->this_hdr.contents != contents)
    {
      if (!link_info->keep_memory)
	free (contents);
      else
	elf_section_data (sec)->this_hdr.contents = contents;
    }

  if (internal_relocs != NULL && elf_section_data (sec)->relocs != internal_relocs)
    free (internal_relocs);
}

/* Delete some bytes from a section while relaxing.  FIXME: There is a
   lot of duplication between this function and sh_relax_delete_bytes
   in coff-sh.c.  */

static bool
sh_elf_relax_delete_bytes (bfd *abfd, asection *sec, bfd_vma addr,
                          int count)
{
  Elf_Internal_Shdr *symtab_hdr;
  unsigned int sec_shndx;
  bfd_byte *contents;
  Elf_Internal_Rela *irel, *irelend;
  Elf_Internal_Rela *irelalign;
  bfd_vma toaddr;
  Elf_Internal_Sym *isymbuf, *isym, *isymend;
  struct elf_link_hash_entry **sym_hashes;
  struct elf_link_hash_entry **end_hashes;
  unsigned int symcount;
  asection *o;

  if (count <= 0)
    return true;

  symtab_hdr = &elf_symtab_hdr (abfd);
  isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;

  sec_shndx = _bfd_elf_section_from_bfd_section (abfd, sec);

  contents = elf_section_data (sec)->this_hdr.contents;
  if (contents == NULL)
    return false;

  irelalign = NULL;
  toaddr = sec->size;

  irel = elf_section_data (sec)->relocs;
  if (irel != NULL)
    {
      irelend = irel + sec->reloc_count;
      for (; irel < irelend; irel++)
        {
          if (ELF32_R_TYPE (irel->r_info) == (int) R_SH_ALIGN
              && irel->r_offset > addr
              && count < (1 << irel->r_addend))
            {
              irelalign = irel;
              toaddr = irel->r_offset;
              break;
            }
        }
    }

  if (toaddr <= addr + count)
    return false;

  memmove (contents + addr, contents + addr + count,
           (size_t) (toaddr - addr - count));
  if (irelalign == NULL)
    sec->size -= count;
  else
    {
      int i;
      const bfd_vma nop_opcode = 0x0009;

      if ((count & 1) != 0)
        return false;
      for (i = 0; i < count; i += 2)
        bfd_put_16 (abfd, nop_opcode, contents + toaddr - count + i);
    }

  if (elf_section_data (sec)->relocs != NULL)
    {
      irel = elf_section_data (sec)->relocs;
      irelend = irel + sec->reloc_count;
      for (; irel < irelend; irel++)
        {
          bfd_vma nraddr;
          bfd_vma start = 0;
          int insn = 0;
          int off, adjust;
          bfd_signed_vma voff = 0;
          bool overflow = false;

          nraddr = irel->r_offset;
          if ((irel->r_offset > addr && irel->r_offset < toaddr)
              || (ELF32_R_TYPE (irel->r_info) == (int) R_SH_ALIGN
                  && irel->r_offset == toaddr))
            nraddr -= count;

          if (irel->r_offset >= addr
              && irel->r_offset < addr + count
              && ELF32_R_TYPE (irel->r_info) != (int) R_SH_ALIGN
              && ELF32_R_TYPE (irel->r_info) != (int) R_SH_CODE
              && ELF32_R_TYPE (irel->r_info) != (int) R_SH_DATA
              && ELF32_R_TYPE (irel->r_info) != (int) R_SH_LABEL)
            irel->r_info = ELF32_R_INFO (ELF32_R_SYM (irel->r_info), (int) R_SH_NONE);

          switch ((enum elf_sh_reloc_type) ELF32_R_TYPE (irel->r_info))
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

          bfd_vma stop = start;
          switch ((enum elf_sh_reloc_type) ELF32_R_TYPE (irel->r_info))
            {
            case R_SH_DIR32:
              if (!handle_dir32_reloc(abfd, sec, irel, nraddr, contents, isymbuf, 
                                    symtab_hdr, sec_shndx, addr, toaddr, count))
                return false;
              break;

            case R_SH_DIR8WPN:
              off = insn & 0xff;
              if (off & 0x80)
                off -= 0x100;
              stop = start + 4 + off * 2;
              break;

            case R_SH_IND12W:
              off = insn & 0xfff;
              if (off == 0)
                {
                  start = stop = addr;
                }
              else
                {
                  if (off & 0x800)
                    off -= 0x1000;
                  stop = start + 4 + off * 2;
                  if (stop > addr && stop < toaddr)
                    irel->r_addend -= count;
                }
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
              start = stop - (long) irel->r_addend;

              if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr))
                irel->r_addend += count;
              else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))
                irel->r_addend -= count;

              if (ELF32_R_TYPE (irel->r_info) == (int) R_SH_SWITCH16)
                voff = bfd_get_signed_16 (abfd, contents + nraddr);
              else if (ELF32_R_TYPE (irel->r_info) == (int) R_SH_SWITCH8)
                voff = bfd_get_8 (abfd, contents + nraddr);
              else
                voff = bfd_get_signed_32 (abfd, contents + nraddr);
              stop = start + voff;
              break;

            case R_SH_USES:
              start = irel->r_offset;
              stop = start + (long) irel->r_addend + 4;
              break;

            default:
              start = stop = addr;
              break;
            }

          adjust = calculate_adjustment(start, stop, addr, toaddr, count);

          if (adjust != 0)
            {
              if (!apply_reloc_adjustment(abfd, contents, irel, nraddr, adjust, 
                                        insn, voff, &overflow))
                return false;

              if (overflow)
                {
                  _bfd_error_handler (_("%pB: %#" PRIx64 ": fatal: reloc overflow while relaxing"),
                                    abfd, (uint64_t) irel->r_offset);
                  bfd_set_error (bfd_error_bad_value);
                  return false;
                }
            }

          irel->r_offset = nraddr;
        }
    }

  if (!adjust_other_sections(abfd, sec, addr, toaddr, count, isymbuf, 
                           symtab_hdr, sec_shndx))
    return false;

  adjust_local_symbols(isymbuf, symtab_hdr, sec_shndx, addr, toaddr, count);

  symcount = (symtab_hdr->sh_size / sizeof (Elf32_External_Sym) - symtab_hdr->sh_info);
  sym_hashes = elf_sym_hashes (abfd);
  end_hashes = sym_hashes + symcount;
  for (; sym_hashes < end_hashes; sym_hashes++)
    {
      struct elf_link_hash_entry *sym_hash = *sym_hashes;
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
      bfd_vma alignaddr = BFD_ALIGN (irelalign->r_offset, 1 << irelalign->r_addend);
      if (alignto != alignaddr)
        return sh_elf_relax_delete_bytes (abfd, sec, alignaddr, (int) (alignto - alignaddr));
    }

  return true;
}

static bool
handle_dir32_reloc(bfd *abfd, asection *sec, Elf_Internal_Rela *irel, 
                  bfd_vma nraddr, bfd_byte *contents, Elf_Internal_Sym *isymbuf,
                  Elf_Internal_Shdr *symtab_hdr, unsigned int sec_shndx,
                  bfd_vma addr, bfd_vma toaddr, int count)
{
  if (ELF32_R_SYM (irel->r_info) < symtab_hdr->sh_info)
    {
      Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM (irel->r_info);
      if (isym->st_shndx == sec_shndx
          && (isym->st_value <= addr || isym->st_value >= toaddr))
        {
          bfd_vma val;
          if (get_howto_table (abfd)[R_SH_DIR32].partial_inplace)
            {
              val = bfd_get_32 (abfd, contents + nraddr);
              val += isym->st_value;
              if (val > addr && val < toaddr)
                bfd_put_32 (abfd, val - count, contents + nraddr);
            }
          else
            {
              val = isym->st_value + irel->r_addend;
              if (val > addr && val < toaddr)
                irel->r_addend -= count;
            }
        }
    }
  return true;
}

static int
calculate_adjustment(bfd_vma start, bfd_vma stop, bfd_vma addr, bfd_vma toaddr, int count)
{
  if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr))
    return count;
  else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))
    return -count;
  else
    return 0;
}

static bool
apply_reloc_adjustment(bfd *abfd, bfd_byte *contents, Elf_Internal_Rela *irel,
                      bfd_vma nraddr, int adjust, int insn, bfd_signed_vma voff,
                      bool *overflow)
{
  int oinsn = insn;
  
  switch ((enum elf_sh_reloc_type) ELF32_R_TYPE (irel->r_info))
    {
    case R_SH_DIR8WPN:
    case R_SH_DIR8WPZ:
      insn += adjust / 2;
      if ((oinsn & 0xff00) != (insn & 0xff00))
        *overflow = true;
      bfd_put_16 (abfd, (bfd_vma) insn, contents + nraddr);
      break;

    case R_SH_IND12W:
      insn += adjust / 2;
      if ((oinsn & 0xf000) != (insn & 0xf000))
        *overflow = true;
      bfd_put_16 (abfd, (bfd_vma) insn, contents + nraddr);
      break;

    case R_SH_DIR8WPL:
      if ((adjust != 4 && adjust != -4) && adjust != 0)
        return false;
      if (adjust >= 4)
        insn += adjust / 4;
      else if (adjust > 0)
        {
          if ((irel->r_offset & 3) == 0)
            ++insn;
        }
      if ((oinsn & 0xff00) != (insn & 0xff00))
        *overflow = true;
      bfd_put_16 (abfd, (bfd_vma) insn, contents + nraddr);
      break;

    case R_SH_SWITCH8:
      voff += adjust;
      if (voff < 0 || voff >= 0xff)
        *overflow = true;
      bfd_put_8 (abfd, voff, contents + nraddr);
      break;

    case R_SH_SWITCH16:
      voff += adjust;
      if (voff < -0x8000 || voff >= 0x8000)
        *overflow = true;
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
      return false;
    }
  
  return true;
}

static bool
adjust_other_sections(bfd *abfd, asection *sec, bfd_vma addr, bfd_vma toaddr, 
                     int count, Elf_Internal_Sym *isymbuf,
                     Elf_Internal_Shdr *symtab_hdr, unsigned int sec_shndx)
{
  asection *o;
  
  for (o = abfd->sections; o != NULL; o = o->next)
    {
      if (o == sec || (o->flags & SEC_HAS_CONTENTS) == 0 ||
          (o->flags & SEC_RELOC) == 0 || o->reloc_count == 0)
        continue;

      Elf_Internal_Rela *internal_relocs = _bfd_elf_link_read_relocs(abfd, o, NULL, NULL, true);
      if (internal_relocs == NULL)
        return false;

      if (!process_section_relocs(abfd, o, sec, internal_relocs, addr, toaddr, 
                                count, isymbuf, symtab_hdr, sec_shndx))
        return false;
    }
  return true;
}

static bool
process_section_relocs(bfd *abfd, asection *o, asection *sec,
                      Elf_Internal_Rela *internal_relocs, bfd_vma addr, 
                      bfd_vma toaddr, int count, Elf_Internal_Sym *isymbuf,
                      Elf_Internal_Shdr *symtab_hdr, unsigned int sec_shndx)
{
  Elf_Internal_Rela *irelscan, *irelscanend;
  bfd_byte *ocontents = NULL;

  irelscanend = internal_relocs + o->reloc_count;
  for (irelscan = internal_relocs; irelscan < irelscanend; irelscan++)
    {
      if (ELF32_R_TYPE (irelscan->r_info) == (int) R_SH_SWITCH32)
        {
          if (!handle_switch32_reloc(abfd, o, irelscan, &ocontents, addr, toaddr, count))
            return false;
        }

      if (ELF32_R_TYPE (irelscan->r_info) == (int) R_SH_DIR32 &&
          ELF32_R_SYM (irelscan->r_info) < symtab_hdr->sh_info)
        {
          if (!handle_dir32_in_other_section(abfd, o, irelscan, &ocontents, 
                                           isymbuf, sec_shndx, addr, toaddr, count))
            return false;
        }
    }
  return true;
}

static bool
handle_switch32_reloc(bfd *abfd, asection *o, Elf_Internal_Rela *irelscan,
                     bfd_byte **ocontents, bfd_vma addr, bfd_vma toaddr, int count)
{
  bfd_vma start, stop;
  bfd_signed_vma voff;

  if (*ocontents == NULL)
    {
      if (elf_section_data (o)->this_hdr.contents != NULL)
        *ocontents = elf_section_data (o)->this_hdr.contents;
      else
        {
          if (!bfd_malloc_and_get_section (abfd, o, ocontents))
            {
              free (*ocontents);
              return false;
            }
          elf_section_data (o)->this_hdr.contents = *ocontents;
        }
    }

  stop = irelscan->r_offset;
  start = stop - (long) irelscan->r_addend;

  if (start > addr && start < toaddr)
    irelscan->r_addend += count;

  voff = bfd_get_signed_32 (abfd, *ocontents + irelscan->r_offset);
  stop = start + voff;

  if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr))
    bfd_put_signed_32 (abfd, voff + count, *ocontents + irelscan->r_offset);
  else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))
    bfd_put_signed_32 (abfd, voff - count, *ocontents + irelscan->r_offset);

  return true;
}

static bool
handle_dir32_in_other_section(bfd *abfd, asection *o, Elf_Internal_Rela *irelscan,
                              bfd_byte **ocontents, Elf_Internal_Sym *isymbuf,
                              unsigned int sec_shndx, bfd_vma addr, 
                              bfd_vma toaddr, int count)
{
  Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM (irelscan->r_info);
  if (isym->st_shndx != sec_shndx || 
      (isym->st_value > addr && isym->st_value < toaddr))
    return true;

  if (*ocontents == NULL)
    {
      if (elf_section_data (o)->this_hdr.contents != NULL)
        *ocontents = elf_section_data (o)->this_hdr.contents;
      else
        {
          if (!bfd_malloc_and_get_section (abfd, o, ocontents))
            {
              free (*ocontents);
              return false;
            }
          elf_section_data (o)->this_hdr.contents = *ocontents;
        }
    }

  bfd_vma val = bfd_get_32 (abfd, *ocontents + irelscan->r_offset);
  val += isym->st_value;
  if (val > addr && val < toaddr)
    bfd_put_32 (abfd, val - count, *ocontents + irelscan->r_offset);

  return true;
}

static void
adjust_local_symbols(Elf_Internal_Sym *isymbuf, Elf_Internal_Shdr *symtab_hdr,
                     unsigned int sec_shndx, bfd_vma addr, bfd_vma toaddr, int count)
{
  Elf_Internal_Sym *isym, *isymend;

  isymend = isymbuf + symtab_hdr->sh_info;
  for (isym = isymbuf; isym < isymend; isym++)
    {
      if (isym->st_shndx == sec_shndx && 
          isym->st_value > addr && isym->st_value < toaddr)
        isym->st_value -= count;
    }
}

/* Look for loads and stores which we can align to four byte
   boundaries.  This is like sh_align_loads in coff-sh.c.  */

static bool
sh_elf_align_loads (bfd *abfd ATTRIBUTE_UNUSED, asection *sec,
		    Elf_Internal_Rela *internal_relocs,
		    bfd_byte *contents ATTRIBUTE_UNUSED,
		    bool *pswapped)
{
  Elf_Internal_Rela *irel, *irelend;
  bfd_vma *labels = NULL;
  bfd_vma *label, *label_end;
  bfd_size_type amt;

  if (!pswapped)
    return false;

  *pswapped = false;

  if (!sec || !internal_relocs || sec->reloc_count == 0)
    return true;

  irelend = internal_relocs + sec->reloc_count;

  amt = sec->reloc_count * sizeof (bfd_vma);
  labels = (bfd_vma *) bfd_malloc (amt);
  if (!labels)
    return false;

  label_end = labels;
  for (irel = internal_relocs; irel < irelend; irel++)
    {
      if (ELF32_R_TYPE (irel->r_info) == (int) R_SH_LABEL)
	{
	  *label_end = irel->r_offset;
	  label_end++;
	}
    }

  label = labels;

  for (irel = internal_relocs; irel < irelend; irel++)
    {
      bfd_vma start, stop;

      if (ELF32_R_TYPE (irel->r_info) != (int) R_SH_CODE)
	continue;

      start = irel->r_offset;

      irel++;
      for (; irel < irelend; irel++)
	{
	  if (ELF32_R_TYPE (irel->r_info) == (int) R_SH_DATA)
	    break;
	}

      stop = (irel < irelend) ? irel->r_offset : sec->size;

      if (!_bfd_sh_align_load_span (abfd, sec, contents, sh_elf_swap_insns,
				    internal_relocs, &label,
				    label_end, start, stop, pswapped))
	{
	  free (labels);
	  return false;
	}
    }

  free (labels);
  return true;
}

/* Swap two SH instructions.  This is like sh_swap_insns in coff-sh.c.  */

static bool
sh_elf_swap_insns (bfd *abfd, asection *sec, void *relocs,
		   bfd_byte *contents, bfd_vma addr)
{
  Elf_Internal_Rela *internal_relocs = (Elf_Internal_Rela *) relocs;
  Elf_Internal_Rela *irel, *irelend;
  unsigned short i1, i2;

  if (!abfd || !sec || !contents || !internal_relocs)
    {
      bfd_set_error (bfd_error_invalid_operation);
      return false;
    }

  i1 = bfd_get_16 (abfd, contents + addr);
  i2 = bfd_get_16 (abfd, contents + addr + 2);
  bfd_put_16 (abfd, (bfd_vma) i2, contents + addr);
  bfd_put_16 (abfd, (bfd_vma) i1, contents + addr + 2);

  irelend = internal_relocs + sec->reloc_count;
  for (irel = internal_relocs; irel < irelend; irel++)
    {
      enum elf_sh_reloc_type type = (enum elf_sh_reloc_type) ELF32_R_TYPE (irel->r_info);
      
      if (type == R_SH_ALIGN || type == R_SH_CODE || 
          type == R_SH_DATA || type == R_SH_LABEL)
	continue;

      if (type == R_SH_USES)
	{
	  bfd_vma off = irel->r_offset + 4 + irel->r_addend;
	  if (off == addr)
	    irel->r_addend += 2;
	  else if (off == addr + 2)
	    irel->r_addend -= 2;
	}

      int add = 0;
      if (irel->r_offset == addr)
	{
	  irel->r_offset += 2;
	  add = -2;
	}
      else if (irel->r_offset == addr + 2)
	{
	  irel->r_offset -= 2;
	  add = 2;
	}

      if (add != 0)
	{
	  bfd_byte *loc = contents + irel->r_offset;
	  unsigned short insn, oinsn;
	  bool overflow = false;

	  switch (type)
	    {
	    case R_SH_DIR8WPN:
	    case R_SH_DIR8WPZ:
	      insn = bfd_get_16 (abfd, loc);
	      oinsn = insn;
	      insn += add / 2;
	      if ((oinsn & 0xff00) != (insn & 0xff00))
		overflow = true;
	      bfd_put_16 (abfd, (bfd_vma) insn, loc);
	      break;

	    case R_SH_IND12W:
	      insn = bfd_get_16 (abfd, loc);
	      oinsn = insn;
	      insn += add / 2;
	      if ((oinsn & 0xf000) != (insn & 0xf000))
		overflow = true;
	      bfd_put_16 (abfd, (bfd_vma) insn, loc);
	      break;

	    case R_SH_DIR8WPL:
	      if ((addr & 3) != 0)
		{
		  insn = bfd_get_16 (abfd, loc);
		  oinsn = insn;
		  insn += add / 2;
		  if ((oinsn & 0xff00) != (insn & 0xff00))
		    overflow = true;
		  bfd_put_16 (abfd, (bfd_vma) insn, loc);
		}
	      break;

	    default:
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
  bool is_big_endian;
  int endian_index;

  if (abfd == NULL)
    return NULL;

  is_big_endian = bfd_big_endian (abfd);
  endian_index = is_big_endian ? 0 : 1;

  if (fdpic_object_p (abfd))
    {
      unsigned int arch = sh_get_arch_from_bfd_mach (bfd_get_mach (abfd));
      if (arch & arch_sh2a_base)
        return &fdpic_sh2a_plts[endian_index];
      else
        return &fdpic_sh_plts[endian_index];
    }
  
  if (vxworks_object_p (abfd))
    return &vxworks_sh_plts[pic_p][endian_index];
  
  return &elf_sh_plts[pic_p][endian_index];
}

/* Install a 32-bit PLT field starting at ADDR, which occurs in OUTPUT_BFD.
   VALUE is the field's value and CODE_P is true if VALUE refers to code,
   not data.  */

static void
install_plt_field (bfd *output_bfd, unsigned long value, bfd_byte *addr)
{
  if (output_bfd == NULL || addr == NULL) {
    return;
  }
  
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
  bfd_vma plt_index = 0;

  if (info == NULL || info->symbol_entry_size == 0)
    return 0;

  if (offset < info->plt0_entry_size)
    return 0;

  offset -= info->plt0_entry_size;
  
  if (info->short_plt != NULL && info->short_plt->symbol_entry_size > 0)
    {
      bfd_vma short_plt_size = MAX_SHORT_PLT * info->short_plt->symbol_entry_size;
      if (offset > short_plt_size)
	{
	  plt_index = MAX_SHORT_PLT;
	  offset -= short_plt_size;
	}
      else
	{
	  info = info->short_plt;
	}
    }
  
  return plt_index + offset / info->symbol_entry_size;
}

/* Do the inverse operation.  */

static bfd_vma
get_plt_offset (const struct elf_sh_plt_info *info, bfd_vma plt_index)
{
  bfd_vma offset = 0;
  const struct elf_sh_plt_info *current_info = info;

  if (info == NULL)
    return 0;

  if (info->short_plt != NULL)
    {
      if (plt_index > MAX_SHORT_PLT)
	{
	  offset = MAX_SHORT_PLT * info->short_plt->symbol_entry_size;
	  plt_index -= MAX_SHORT_PLT;
	}
      else
	current_info = info->short_plt;
    }
  return (offset + current_info->plt0_entry_size
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
    return false;
    
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
  struct elf_sh_link_hash_entry *ret = (struct elf_sh_link_hash_entry *) entry;

  if (ret == NULL) {
    ret = (struct elf_sh_link_hash_entry *) bfd_hash_allocate (table,
                                                               sizeof (struct elf_sh_link_hash_entry));
  }
  if (ret == NULL)
    return NULL;

  ret = (struct elf_sh_link_hash_entry *) _bfd_elf_link_hash_newfunc ((struct bfd_hash_entry *) ret,
                                                                      table, string);
  if (ret != NULL) {
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
  struct elf_sh_link_hash_table *htab;
  Elf_Internal_Shdr *section_header;
  
  if (!info || !p)
    return true;
    
  htab = sh_elf_hash_table (info);
  if (!htab)
    return true;

  if (!htab->fdpic_p)
    return true;

  section_header = &elf_section_data (p)->this_hdr;
  
  switch (section_header->sh_type)
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
create_section_with_flags_and_alignment(bfd *dynobj, const char *name, 
                                       flagword flags, asection **section)
{
  *section = bfd_make_section_anyway_with_flags(dynobj, name, flags);
  if (*section == NULL || !bfd_set_section_alignment(*section, 2))
    return false;
  return true;
}

static bool
create_got_section(bfd *dynobj, struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab;
  const flagword funcdesc_flags = SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS 
                                 | SEC_IN_MEMORY | SEC_LINKER_CREATED;
  const flagword rela_flags = funcdesc_flags | SEC_READONLY;

  if (!_bfd_elf_create_got_section(dynobj, info))
    return false;

  htab = sh_elf_hash_table(info);
  if (htab == NULL)
    return false;

  if (!create_section_with_flags_and_alignment(dynobj, ".got.funcdesc", 
                                             funcdesc_flags, &htab->sfuncdesc))
    return false;

  if (!create_section_with_flags_and_alignment(dynobj, ".rela.got.funcdesc", 
                                             rela_flags, &htab->srelfuncdesc))
    return false;

  if (!create_section_with_flags_and_alignment(dynobj, ".rofixup", 
                                             rela_flags, &htab->srofixup))
    return false;

  return true;
}

/* Create dynamic sections when linking against a dynamic object.  */

static bool
sh_elf_create_dynamic_sections (bfd *abfd, struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab;
  flagword flags, pltflags;
  asection *s;
  const struct elf_backend_data *bed = get_elf_backend_data (abfd);
  int ptralign = 0;

  switch (bed->s->arch_size)
    {
    case 32:
      ptralign = 2;
      break;
    case 64:
      ptralign = 3;
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

  flags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS | SEC_IN_MEMORY
           | SEC_LINKER_CREATED);

  pltflags = flags | SEC_CODE;
  if (bed->plt_not_loaded)
    pltflags &= ~(SEC_LOAD | SEC_HAS_CONTENTS);
  if (bed->plt_readonly)
    pltflags |= SEC_READONLY;

  s = bfd_make_section_anyway_with_flags (abfd, ".plt", pltflags);
  htab->root.splt = s;
  if (s == NULL || !bfd_set_section_alignment (s, bed->plt_alignment))
    return false;

  if (bed->want_plt_sym)
    {
      struct elf_link_hash_entry *h;
      struct bfd_link_hash_entry *bh = NULL;

      if (!(_bfd_generic_link_add_one_symbol
            (info, abfd, "_PROCEDURE_LINKAGE_TABLE_", BSF_GLOBAL, s,
             (bfd_vma) 0, (const char *) NULL, false,
             get_elf_backend_data (abfd)->collect, &bh)))
        return false;

      h = (struct elf_link_hash_entry *) bh;
      h->def_regular = 1;
      h->type = STT_OBJECT;
      htab->root.hplt = h;

      if (bfd_link_pic (info) && !bfd_elf_link_record_dynamic_symbol (info, h))
        return false;
    }

  s = bfd_make_section_anyway_with_flags (abfd,
                                          bed->default_use_rela_p
                                          ? ".rela.plt" : ".rel.plt",
                                          flags | SEC_READONLY);
  htab->root.srelplt = s;
  if (s == NULL || !bfd_set_section_alignment (s, ptralign))
    return false;

  if (htab->root.sgot == NULL && !create_got_section (abfd, info))
    return false;

  if (bed->want_dynbss)
    {
      s = bfd_make_section_anyway_with_flags (abfd, ".dynbss",
                                              SEC_ALLOC | SEC_LINKER_CREATED);
      htab->root.sdynbss = s;
      if (s == NULL)
        return false;

      if (!bfd_link_pic (info))
        {
          s = bfd_make_section_anyway_with_flags (abfd,
                                                  (bed->default_use_rela_p
                                                   ? ".rela.bss" : ".rel.bss"),
                                                  flags | SEC_READONLY);
          htab->root.srelbss = s;
          if (s == NULL || !bfd_set_section_alignment (s, ptralign))
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

    if (h->type == STT_FUNC || h->needs_plt) {
        if (h->plt.refcount <= 0
            || SYMBOL_CALLS_LOCAL(info, h)
            || (ELF_ST_VISIBILITY(h->other) != STV_DEFAULT
                && h->root.type == bfd_link_hash_undefweak)) {
            h->plt.offset = (bfd_vma) -1;
            h->needs_plt = 0;
        }
        return true;
    }

    h->plt.offset = (bfd_vma) -1;

    if (h->is_weakalias) {
        struct elf_link_hash_entry *def = weakdef(h);
        BFD_ASSERT(def->root.type == bfd_link_hash_defined);
        h->root.u.def.section = def->root.u.def.section;
        h->root.u.def.value = def->root.u.def.value;
        if (info->nocopyreloc)
            h->non_got_ref = def->non_got_ref;
        return true;
    }

    if (bfd_link_pic(info))
        return true;

    if (!h->non_got_ref)
        return true;

    s = htab->root.sdynbss;
    BFD_ASSERT(s != NULL);

    if ((h->root.u.def.section->flags & SEC_ALLOC) != 0 && h->size != 0) {
        asection *srel;

        srel = htab->root.srelbss;
        BFD_ASSERT(srel != NULL);
        srel->size += sizeof(Elf32_External_Rela);
        h->needs_copy = 1;
    }

    return _bfd_elf_adjust_dynamic_copy(info, h, s);
}

/* Allocate space in .plt, .got and associated reloc sections for
   dynamic relocs.  */

static bool
allocate_dynrelocs (struct elf_link_hash_entry *h, void *inf)
{
  struct bfd_link_info *info;
  struct elf_sh_link_hash_table *htab;
  struct elf_sh_link_hash_entry *eh;
  struct elf_dyn_relocs *p;

  if (h->root.type == bfd_link_hash_indirect)
    return true;

  info = (struct bfd_link_info *) inf;
  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  eh = (struct elf_sh_link_hash_entry *) h;

  if ((h->got.refcount > 0 || h->forced_local) && eh->gotplt_refcount > 0)
    {
      h->got.refcount += eh->gotplt_refcount;
      if (h->plt.refcount >= eh->gotplt_refcount)
        h->plt.refcount -= eh->gotplt_refcount;
    }

  if (!allocate_plt_entry(h, info, htab))
    return false;

  if (!allocate_got_entry(h, info, htab, eh))
    return false;

  if (!allocate_funcdesc_entry(h, info, htab, eh))
    return false;

  if (!process_dynamic_relocations(h, info, htab))
    return false;

  return true;
}

static bool
allocate_plt_entry(struct elf_link_hash_entry *h, struct bfd_link_info *info, 
                   struct elf_sh_link_hash_table *htab)
{
  if (htab->root.dynamic_sections_created &&
      h->plt.refcount > 0 &&
      (ELF_ST_VISIBILITY (h->other) == STV_DEFAULT ||
       h->root.type != bfd_link_hash_undefweak))
    {
      if (h->dynindx == -1 && !h->forced_local)
        {
          if (!bfd_elf_link_record_dynamic_symbol (info, h))
            return false;
        }

      if (bfd_link_pic (info) || WILL_CALL_FINISH_DYNAMIC_SYMBOL (1, 0, h))
        {
          asection *s = htab->root.splt;
          const struct elf_sh_plt_info *plt_info;

          if (s->size == 0)
            s->size += htab->plt_info->plt0_entry_size;

          h->plt.offset = s->size;

          if (!htab->fdpic_p && !bfd_link_pic (info) && !h->def_regular)
            {
              h->root.u.def.section = s;
              h->root.u.def.value = h->plt.offset;
            }

          plt_info = htab->plt_info;
          if (plt_info->short_plt != NULL &&
              get_plt_index (plt_info->short_plt, s->size) < MAX_SHORT_PLT)
            plt_info = plt_info->short_plt;
          s->size += plt_info->symbol_entry_size;

          if (!htab->fdpic_p)
            htab->root.sgotplt->size += 4;
          else
            htab->root.sgotplt->size += 8;

          htab->root.srelplt->size += sizeof (Elf32_External_Rela);

          if (htab->root.target_os == is_vxworks && !bfd_link_pic (info))
            {
              if (h->plt.offset == htab->plt_info->plt0_entry_size)
                htab->srelplt2->size += sizeof (Elf32_External_Rela);
              htab->srelplt2->size += sizeof (Elf32_External_Rela) * 2;
            }
        }
      else
        {
          h->plt.offset = (bfd_vma) -1;
          h->needs_plt = 0;
        }
    }
  else
    {
      h->plt.offset = (bfd_vma) -1;
      h->needs_plt = 0;
    }
  return true;
}

static bool
allocate_got_entry(struct elf_link_hash_entry *h, struct bfd_link_info *info,
                   struct elf_sh_link_hash_table *htab, struct elf_sh_link_hash_entry *eh)
{
  if (h->got.refcount > 0)
    {
      asection *s;
      bool dyn;
      enum got_type got_type = eh->got_type;

      if (h->dynindx == -1 && !h->forced_local)
        {
          if (!bfd_elf_link_record_dynamic_symbol (info, h))
            return false;
        }

      s = htab->root.sgot;
      h->got.offset = s->size;
      s->size += 4;
      if (got_type == GOT_TLS_GD)
        s->size += 4;
      
      dyn = htab->root.dynamic_sections_created;
      
      if (!dyn)
        {
          if (htab->fdpic_p && !bfd_link_pic (info) &&
              h->root.type != bfd_link_hash_undefweak &&
              (got_type == GOT_NORMAL || got_type == GOT_FUNCDESC))
            htab->srofixup->size += 4;
        }
      else if (got_type == GOT_TLS_IE && !h->def_dynamic && !bfd_link_pic (info))
        {
          /* No dynamic relocations required */
        }
      else
        {
          update_got_relocations(h, info, htab, got_type, dyn);
        }
    }
  else
    h->got.offset = (bfd_vma) -1;
  
  return true;
}

static void
update_got_relocations(struct elf_link_hash_entry *h, struct bfd_link_info *info,
                       struct elf_sh_link_hash_table *htab, enum got_type got_type, bool dyn)
{
  if ((got_type == GOT_TLS_GD && h->dynindx == -1) || got_type == GOT_TLS_IE)
    htab->root.srelgot->size += sizeof (Elf32_External_Rela);
  else if (got_type == GOT_TLS_GD)
    htab->root.srelgot->size += 2 * sizeof (Elf32_External_Rela);
  else if (got_type == GOT_FUNCDESC)
    {
      if (!bfd_link_pic (info) && SYMBOL_FUNCDESC_LOCAL (info, h))
        htab->srofixup->size += 4;
      else
        htab->root.srelgot->size += sizeof (Elf32_External_Rela);
    }
  else if ((ELF_ST_VISIBILITY (h->other) == STV_DEFAULT ||
            h->root.type != bfd_link_hash_undefweak) &&
           (bfd_link_pic (info) || WILL_CALL_FINISH_DYNAMIC_SYMBOL (dyn, 0, h)))
    htab->root.srelgot->size += sizeof (Elf32_External_Rela);
  else if (htab->fdpic_p && !bfd_link_pic (info) && got_type == GOT_NORMAL &&
           (ELF_ST_VISIBILITY (h->other) == STV_DEFAULT ||
            h->root.type != bfd_link_hash_undefweak))
    htab->srofixup->size += 4;
}

static bool
allocate_funcdesc_entry(struct elf_link_hash_entry *h, struct bfd_link_info *info,
                        struct elf_sh_link_hash_table *htab, struct elf_sh_link_hash_entry *eh)
{
  if (eh->abs_funcdesc_refcount > 0 &&
      (h->root.type != bfd_link_hash_undefweak ||
       (htab->root.dynamic_sections_created && !SYMBOL_CALLS_LOCAL (info, h))))
    {
      if (!bfd_link_pic (info) && SYMBOL_FUNCDESC_LOCAL (info, h))
        htab->srofixup->size += eh->abs_funcdesc_refcount * 4;
      else
        htab->root.srelgot->size += eh->abs_funcdesc_refcount * sizeof (Elf32_External_Rela);
    }

  if ((eh->funcdesc.refcount > 0 || 
       (h->got.offset != (bfd_vma) -1 && eh->got_type == GOT_FUNCDESC)) &&
      h->root.type != bfd_link_hash_undefweak &&
      SYMBOL_FUNCDESC_LOCAL (info, h))
    {
      eh->funcdesc.offset = htab->sfuncdesc->size;
      htab->sfuncdesc->size += 8;

      if (!bfd_link_pic (info) && SYMBOL_CALLS_LOCAL (info, h))
        htab->srofixup->size += 8;
      else
        htab->srelfuncdesc->size += sizeof (Elf32_External_Rela);
    }

  return true;
}

static bool
process_dynamic_relocations(struct elf_link_hash_entry *h, struct bfd_link_info *info,
                           struct elf_sh_link_hash_table *htab)
{
  struct elf_dyn_relocs *p;

  if (h->dyn_relocs == NULL)
    return true;

  if (bfd_link_pic (info))
    {
      if (!process_shared_relocations(h, info, htab))
        return false;
    }
  else
    {
      if (!process_nonshared_relocations(h, info, htab))
        return false;
    }

  for (p = h->dyn_relocs; p != NULL; p = p->next)
    {
      asection *sreloc = elf_section_data (p->sec)->sreloc;
      sreloc->size += p->count * sizeof (Elf32_External_Rela);

      if (htab->fdpic_p && !bfd_link_pic (info))
        htab->srofixup->size -= 4 * (p->count - p->pc_count);
    }

  return true;
}

static bool
process_shared_relocations(struct elf_link_hash_entry *h, struct bfd_link_info *info,
                          struct elf_sh_link_hash_table *htab)
{
  struct elf_dyn_relocs *p, **pp;

  if (SYMBOL_CALLS_LOCAL (info, h))
    {
      for (pp = &h->dyn_relocs; (p = *pp) != NULL; )
        {
          p->count -= p->pc_count;
          p->pc_count = 0;
          if (p->count == 0)
            *pp = p->next;
          else
            pp = &p->next;
        }
    }

  if (htab->root.target_os == is_vxworks)
    {
      for (pp = &h->dyn_relocs; (p = *pp) != NULL; )
        {
          if (strcmp (p->sec->output_section->name, ".tls_vars") == 0)
            *pp = p->next;
          else
            pp = &p->next;
        }
    }

  if (h->dyn_relocs != NULL && h->root.type == bfd_link_hash_undefweak)
    {
      if (ELF_ST_VISIBILITY (h->other) != STV_DEFAULT ||
          UNDEFWEAK_NO_DYNAMIC_RELOC (info, h))
        h->dyn_relocs = NULL;
      else if (h->dynindx == -1 && !h->forced_local)
        {
          if (!bfd_elf_link_record_dynamic_symbol (info, h))
            return false;
        }
    }

  return true;
}

static bool
process_nonshared_relocations(struct elf_link_hash_entry *h, struct bfd_link_info *info,
                             struct elf_sh_link_hash_table *htab)
{
  if (!h->non_got_ref &&
      ((h->def_dynamic && !h->def_regular) ||
       (htab->root.dynamic_sections_created &&
        (h->root.type == bfd_link_hash_undefweak ||
         h->root.type == bfd_link_hash_undefined))))
    {
      if (h->dynindx == -1 && !h->forced_local)
        {
          if (!bfd_elf_link_record_dynamic_symbol (info, h))
            return false;
        }

      if (h->dynindx != -1)
        return true;
    }

  h->dyn_relocs = NULL;
  return true;
}

/* This function is called after all the input files have been read,
   and the input sections have been assigned to output sections.
   It's a convenient place to determine the PLT style.  */

static bool
sh_elf_early_size_sections (bfd *output_bfd, struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab;
  
  if (!output_bfd || !info)
    return false;
    
  htab = sh_elf_hash_table (info);
  if (!htab)
    return false;
    
  htab->plt_info = get_plt_info (output_bfd, bfd_link_pic (info));
  
  if (htab->fdpic_p && !bfd_link_relocatable (info))
    {
      if (!bfd_elf_stack_segment_size (output_bfd, info,
                                       "__stacksize", DEFAULT_STACK_SIZE))
        return false;
    }
    
  return true;
}

/* Set the sizes of the dynamic sections.  */

static bool
sh_elf_late_size_sections (bfd *output_bfd ATTRIBUTE_UNUSED,
			   struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab;
  bfd *dynobj;
  asection *s;
  bool relocs;
  bfd *ibfd;

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  dynobj = htab->root.dynobj;
  if (dynobj == NULL)
    return true;

  if (htab->root.dynamic_sections_created)
    {
      if (bfd_link_executable (info) && !info->nointerp)
	{
	  s = bfd_get_linker_section (dynobj, ".interp");
	  if (s == NULL)
	    return false;
	  s->size = sizeof ELF_DYNAMIC_INTERPRETER;
	  s->contents = (unsigned char *) ELF_DYNAMIC_INTERPRETER;
	  s->alloced = 1;
	}
    }

  for (ibfd = info->input_bfds; ibfd != NULL; ibfd = ibfd->link.next)
    {
      if (! is_sh_elf (ibfd))
	continue;

      if (!process_ibfd_sections(ibfd, htab, info))
	return false;

      if (!process_local_got_entries(ibfd, htab, info))
	return false;

      if (!process_local_funcdesc_entries(ibfd, htab))
	return false;
    }

  if (htab->tls_ldm_got.refcount > 0)
    {
      htab->tls_ldm_got.offset = htab->root.sgot->size;
      htab->root.sgot->size += 8;
      htab->root.srelgot->size += sizeof (Elf32_External_Rela);
    }
  else
    htab->tls_ldm_got.offset = -1;

  if (htab->fdpic_p)
    {
      if (htab->root.sgotplt == NULL || htab->root.sgotplt->size != 12)
	return false;
      htab->root.sgotplt->size = 0;
    }

  elf_link_hash_traverse (&htab->root, allocate_dynrelocs, info);

  if (htab->fdpic_p && htab->root.hgot != NULL)
    {
      htab->root.hgot->root.u.def.value = htab->root.sgotplt->size;
      htab->root.sgotplt->size += 12;
    }

  if (htab->fdpic_p && htab->srofixup != NULL)
    htab->srofixup->size += 4;

  relocs = false;
  for (s = dynobj->sections; s != NULL; s = s->next)
    {
      if ((s->flags & SEC_LINKER_CREATED) == 0)
	continue;

      if (is_special_section(s, htab))
	{
	  continue;
	}
      else if (startswith (bfd_section_name (s), ".rela"))
	{
	  if (s->size != 0 && s != htab->root.srelplt && s != htab->srelplt2)
	    relocs = true;
	  s->reloc_count = 0;
	}
      else
	{
	  continue;
	}

      if (s->size == 0)
	{
	  s->flags |= SEC_EXCLUDE;
	  continue;
	}

      if ((s->flags & SEC_HAS_CONTENTS) == 0)
	continue;

      s->contents = (bfd_byte *) bfd_zalloc (dynobj, s->size);
      if (s->contents == NULL)
	return false;
      s->alloced = 1;
    }

  return _bfd_elf_maybe_vxworks_add_dynamic_tags (output_bfd, info, relocs);
}

static bool
process_ibfd_sections(bfd *ibfd, struct elf_sh_link_hash_table *htab, struct bfd_link_info *info)
{
  asection *s;
  
  for (s = ibfd->sections; s != NULL; s = s->next)
    {
      struct elf_dyn_relocs *p;

      for (p = ((struct elf_dyn_relocs *) elf_section_data (s)->local_dynrel);
	   p != NULL; p = p->next)
	{
	  if (!should_process_reloc(p, htab))
	    continue;

	  if (p->count != 0)
	    {
	      asection *srel = elf_section_data (p->sec)->sreloc;
	      if (srel == NULL)
		return false;
	      
	      srel->size += p->count * sizeof (Elf32_External_Rela);
	      
	      if ((p->sec->output_section->flags & SEC_READONLY) != 0)
		{
		  info->flags |= DF_TEXTREL;
		  if (info->callbacks && info->callbacks->minfo)
		    info->callbacks->minfo (_("%pB: dynamic relocation in read-only section `%pA'\n"),
					    p->sec->owner, p->sec);
		}

	      if (htab->fdpic_p && !bfd_link_pic (info))
		htab->srofixup->size -= 4 * (p->count - p->pc_count);
	    }
	}
    }
  return true;
}

static bool
should_process_reloc(struct elf_dyn_relocs *p, struct elf_sh_link_hash_table *htab)
{
  if (! bfd_is_abs_section (p->sec) && bfd_is_abs_section (p->sec->output_section))
    return false;
    
  if (htab->root.target_os == is_vxworks && 
      p->sec->output_section != NULL &&
      strcmp (p->sec->output_section->name, ".tls_vars") == 0)
    return false;
    
  return true;
}

static bool
process_local_got_entries(bfd *ibfd, struct elf_sh_link_hash_table *htab, struct bfd_link_info *info)
{
  bfd_signed_vma *local_got;
  bfd_signed_vma *end_local_got;
  union gotref *local_funcdesc;
  char *local_got_type;
  bfd_size_type locsymcount;
  Elf_Internal_Shdr *symtab_hdr;
  asection *s;
  asection *srel;

  symtab_hdr = &elf_symtab_hdr (ibfd);
  locsymcount = symtab_hdr->sh_info;
  s = htab->root.sgot;
  srel = htab->root.srelgot;

  local_got = elf_local_got_refcounts (ibfd);
  if (local_got == NULL)
    return true;

  end_local_got = local_got + locsymcount;
  local_got_type = sh_elf_local_got_type (ibfd);
  local_funcdesc = sh_elf_local_funcdesc (ibfd);
  
  for (; local_got < end_local_got; ++local_got)
    {
      if (*local_got > 0)
	{
	  *local_got = s->size;
	  s->size += 4;
	  if (*local_got_type == GOT_TLS_GD)
	    s->size += 4;
	  if (bfd_link_pic (info))
	    srel->size += sizeof (Elf32_External_Rela);
	  else
	    htab->srofixup->size += 4;

	  if (*local_got_type == GOT_FUNCDESC)
	    {
	      if (local_funcdesc == NULL)
		{
		  bfd_size_type size = locsymcount * sizeof (union gotref);
		  local_funcdesc = (union gotref *) bfd_zalloc (ibfd, size);
		  if (local_funcdesc == NULL)
		    return false;
		  sh_elf_local_funcdesc (ibfd) = local_funcdesc;
		  local_funcdesc += (local_got - elf_local_got_refcounts (ibfd));
		}
	      local_funcdesc->refcount++;
	      ++local_funcdesc;
	    }
	}
      else
	*local_got = (bfd_vma) -1;
      ++local_got_type;
    }
  return true;
}

static bool
process_local_funcdesc_entries(bfd *ibfd, struct elf_sh_link_hash_table *htab)
{
  union gotref *local_funcdesc;
  union gotref *end_local_funcdesc;
  bfd_size_type locsymcount;
  Elf_Internal_Shdr *symtab_hdr;

  symtab_hdr = &elf_symtab_hdr (ibfd);
  locsymcount = symtab_hdr->sh_info;
  
  local_funcdesc = sh_elf_local_funcdesc (ibfd);
  if (local_funcdesc == NULL)
    return true;

  end_local_funcdesc = local_funcdesc + locsymcount;

  for (; local_funcdesc < end_local_funcdesc; ++local_funcdesc)
    {
      if (local_funcdesc->refcount > 0)
	{
	  local_funcdesc->offset = htab->sfuncdesc->size;
	  htab->sfuncdesc->size += 8;
	  if (!bfd_link_pic (info))
	    htab->srofixup->size += 8;
	  else
	    htab->srelfuncdesc->size += sizeof (Elf32_External_Rela);
	}
      else
	local_funcdesc->offset = MINUS_ONE;
    }
  return true;
}

static bool
is_special_section(asection *s, struct elf_sh_link_hash_table *htab)
{
  return (s == htab->root.splt ||
	  s == htab->root.sgot ||
	  s == htab->root.sgotplt ||
	  s == htab->sfuncdesc ||
	  s == htab->srofixup ||
	  s == htab->root.sdynbss);
}

/* Add a dynamic relocation to the SRELOC section.  */

static bfd_vma
sh_elf_add_dyn_reloc (bfd *output_bfd, asection *sreloc, bfd_vma offset,
		      int reloc_type, long dynindx, bfd_vma addend)
{
  Elf_Internal_Rela outrel;
  bfd_vma reloc_offset;

  if (!output_bfd || !sreloc || !sreloc->contents) {
    return 0;
  }

  outrel.r_offset = offset;
  outrel.r_info = ELF32_R_INFO (dynindx, reloc_type);
  outrel.r_addend = addend;

  reloc_offset = sreloc->reloc_count * sizeof (Elf32_External_Rela);
  
  if (reloc_offset >= sreloc->size) {
    return 0;
  }

  bfd_elf32_swap_reloca_out (output_bfd, &outrel,
			     sreloc->contents + reloc_offset);
  sreloc->reloc_count++;

  return reloc_offset;
}

/* Add an FDPIC read-only fixup.  */

static void
sh_elf_add_rofixup (bfd *output_bfd, asection *srofixup, bfd_vma offset)
{
  bfd_vma fixup_offset;

  if (output_bfd == NULL || srofixup == NULL || srofixup->contents == NULL) {
    return;
  }

  fixup_offset = srofixup->reloc_count * 4;
  
  if (fixup_offset >= srofixup->size) {
    return;
  }
  
  bfd_put_32 (output_bfd, offset, srofixup->contents + fixup_offset);
  srofixup->reloc_count++;
}

/* Return the offset of the generated .got section from the
   _GLOBAL_OFFSET_TABLE_ symbol.  */

static bfd_signed_vma
sh_elf_got_offset (struct elf_sh_link_hash_table *htab)
{
  if (!htab || !htab->root.sgot || !htab->root.sgotplt || !htab->root.hgot)
    return 0;
    
  return (htab->root.sgot->output_offset - htab->root.sgotplt->output_offset
          - htab->root.hgot->root.u.def.value);
}

/* Find the segment number in which OSEC, and output section, is
   located.  */

static unsigned
sh_elf_osec_to_segment (bfd *output_bfd, asection *osec)
{
  Elf_Internal_Phdr *p = NULL;
  
  if (output_bfd == NULL || osec == NULL)
    return (unsigned) -1;

  if (output_bfd->xvec != NULL &&
      output_bfd->xvec->flavour == bfd_target_elf_flavour &&
      output_bfd->direction != read_direction)
    {
      p = _bfd_elf_find_segment_containing_section (output_bfd, osec);
    }

  if (p == NULL)
    return (unsigned) -1;

  if (elf_tdata (output_bfd) == NULL || elf_tdata (output_bfd)->phdr == NULL)
    return (unsigned) -1;

  return (unsigned) (p - elf_tdata (output_bfd)->phdr);
}

static bool
sh_elf_osec_readonly_p (bfd *output_bfd, asection *osec)
{
  unsigned seg;
  
  if (!output_bfd || !osec) {
    return false;
  }
  
  seg = sh_elf_osec_to_segment (output_bfd, osec);
  
  if (seg == (unsigned) -1) {
    return false;
  }
  
  if (!elf_tdata (output_bfd) || !elf_tdata (output_bfd)->phdr) {
    return false;
  }
  
  return !(elf_tdata (output_bfd)->phdr[seg].p_flags & PF_W);
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
  bfd_vma addr, seg;
  bool is_local_symbol;

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  is_local_symbol = (h == NULL || SYMBOL_CALLS_LOCAL (info, h));

  if (h != NULL && is_local_symbol)
    {
      section = h->root.u.def.section;
      value = h->root.u.def.value;
    }

  if (is_local_symbol)
    {
      if (section == NULL || section->output_section == NULL)
        return false;
      
      dynindx = elf_section_data (section->output_section)->dynindx;
      addr = value + section->output_offset;
      seg = sh_elf_osec_to_segment (output_bfd, section->output_section);
    }
  else
    {
      if (h->dynindx == -1)
        return false;
      
      dynindx = h->dynindx;
      addr = seg = 0;
    }

  if (!bfd_link_pic (info) && is_local_symbol)
    {
      if (h == NULL || h->root.type != bfd_link_hash_undefweak)
	{
	  bfd_vma base_addr = htab->sfuncdesc->output_section->vma
	                      + htab->sfuncdesc->output_offset;
	  
	  sh_elf_add_rofixup (output_bfd, htab->srofixup, offset + base_addr);
	  sh_elf_add_rofixup (output_bfd, htab->srofixup, offset + 4 + base_addr);
	}

      addr += section->output_section->vma;
      
      if (htab->root.hgot != NULL)
        {
          seg = htab->root.hgot->root.u.def.value
	        + htab->root.hgot->root.u.def.section->output_section->vma
	        + htab->root.hgot->root.u.def.section->output_offset;
        }
    }
  else
    {
      bfd_vma reloc_offset = offset + htab->sfuncdesc->output_section->vma
                             + htab->sfuncdesc->output_offset;
      sh_elf_add_dyn_reloc (output_bfd, htab->srelfuncdesc, reloc_offset,
                            R_SH_FUNCDESC_VALUE, dynindx, 0);
    }

  if (htab->sfuncdesc->contents == NULL)
    return false;
    
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
  bfd_byte *addr;
  bfd_reloc_status_type r;
  unsigned long cur_val;
  unsigned long high_bits;
  unsigned long low_bits;

  if (!output_bfd || !input_bfd || !input_section || !contents)
    return bfd_reloc_dangerous;

  if (offset > bfd_get_section_limit (input_bfd, input_section))
    return bfd_reloc_outofrange;

  if (offset + 4 > bfd_get_section_limit (input_bfd, input_section))
    return bfd_reloc_outofrange;

  r = bfd_check_overflow (complain_overflow_signed, 20, 0,
			  bfd_arch_bits_per_address (input_bfd), relocation);
  if (r != bfd_reloc_ok)
    return r;

  addr = contents + offset;
  cur_val = bfd_get_16 (output_bfd, addr);
  high_bits = (relocation & 0xf0000) >> 12;
  low_bits = relocation & 0xffff;

  bfd_put_16 (output_bfd, cur_val | high_bits, addr);
  bfd_put_16 (output_bfd, low_bits, addr + 2);

  return bfd_reloc_ok;
}

/* Relocate an SH ELF section.  */

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
  unsigned isec_segment, got_segment, plt_segment, check_segment[2];
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

  isec_segment = sh_elf_osec_to_segment (output_bfd,
					 input_section->output_section);
  if (fdpic_p && sgot)
    got_segment = sh_elf_osec_to_segment (output_bfd,
					  sgot->output_section);
  else
    got_segment = -1;
  if (fdpic_p && splt)
    plt_segment = sh_elf_osec_to_segment (output_bfd,
					  splt->output_section);
  else
    plt_segment = -1;

  is_vxworks_tls = (htab && htab->root.target_os == is_vxworks && bfd_link_pic (info)
		    && !strcmp (input_section->output_section->name,
				".tls_vars"));

  rel = relocs;
  relend = relocs + input_section->reloc_count;
  for (; rel < relend; rel++)
    {
      int r_type;
      reloc_howto_type *howto;
      unsigned long r_symndx;
      Elf_Internal_Sym *sym;
      asection *sec;
      struct elf_link_hash_entry *h;
      bfd_vma relocation;
      bfd_vma addend = (bfd_vma) 0;
      bfd_reloc_status_type r;
      bfd_vma off;
      enum got_type got_type;
      const char *symname = NULL;
      bool resolved_to_zero;

      r_symndx = ELF32_R_SYM (rel->r_info);
      r_type = ELF32_R_TYPE (rel->r_info);

      if (r_type >= (int) R_SH_GNU_VTINHERIT
	  && r_type <= (int) R_SH_LABEL)
	continue;
      if (r_type == (int) R_SH_NONE)
	continue;

      if (r_type < 0
	  || r_type >= R_SH_max
	  || (r_type >= (int) R_SH_FIRST_INVALID_RELOC
	      && r_type <= (int) R_SH_LAST_INVALID_RELOC)
	  || (r_type >= (int) R_SH_FIRST_INVALID_RELOC_2
	      && r_type <= (int) R_SH_LAST_INVALID_RELOC_2)
	  || (   r_type >= (int) R_SH_FIRST_INVALID_RELOC_3
	      && r_type <= (int) R_SH_LAST_INVALID_RELOC_3)
	  || (   r_type >= (int) R_SH_FIRST_INVALID_RELOC_4
	      && r_type <= (int) R_SH_LAST_INVALID_RELOC_4)
	  || (   r_type >= (int) R_SH_FIRST_INVALID_RELOC_5
	      && r_type <= (int) R_SH_LAST_INVALID_RELOC_5)
	  || (   r_type >= (int) R_SH_FIRST_INVALID_RELOC_6
	      && r_type <= (int) R_SH_LAST_INVALID_RELOC_6))
	{
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}

      howto = get_howto_table (output_bfd) + r_type;

      if (! howto->partial_inplace)
	addend = rel->r_addend;

      resolved_to_zero = false;
      h = NULL;
      sym = NULL;
      sec = NULL;
      check_segment[0] = -1;
      check_segment[1] = -1;
      
      if (r_symndx < symtab_hdr->sh_info)
	{
	  sym = local_syms + r_symndx;
	  sec = local_sections[r_symndx];

	  symname = bfd_elf_string_from_elf_section
	    (input_bfd, symtab_hdr->sh_link, sym->st_name);
	  if (symname == NULL || *symname == '\0')
	    symname = bfd_section_name (sec);

	  relocation = (sec->output_section->vma
			+ sec->output_offset
			+ sym->st_value);

	  if (sec != NULL && discarded_section (sec))
	    ;
	  else if (bfd_link_relocatable (info))
	    {
	      if (ELF_ST_TYPE (sym->st_info) == STT_SECTION)
		{
		  if (! howto->partial_inplace)
		    {
		      rel->r_addend += sec->output_offset;
		      continue;
		    }

		  r = _bfd_relocate_contents (howto, input_bfd,
					      sec->output_offset
					      + sym->st_value,
					      contents + rel->r_offset);
		  goto relocation_done;
		}
	      continue;
	    }
	  else if (! howto->partial_inplace)
	    {
	      relocation = _bfd_elf_rela_local_sym (output_bfd, sym, &sec, rel);
	      addend = rel->r_addend;
	    }
	  else if ((sec->flags & SEC_MERGE)
		   && ELF_ST_TYPE (sym->st_info) == STT_SECTION)
	    {
	      asection *msec;

	      if (howto->rightshift || howto->src_mask != 0xffffffff)
		{
		  _bfd_error_handler
		    (_("%pB(%pA+%#" PRIx64 "): "
		       "%s relocation against SEC_MERGE section"),
		     input_bfd, input_section,
		     (uint64_t) rel->r_offset, howto->name);
		  return false;
		}

	      addend = bfd_get_32 (input_bfd, contents + rel->r_offset);
	      msec = sec;
	      addend =
		_bfd_elf_rel_local_sym (output_bfd, sym, &msec, addend)
		- relocation;
	      addend += msec->output_section->vma + msec->output_offset;
	      bfd_put_32 (input_bfd, addend, contents + rel->r_offset);
	      addend = 0;
	    }
	}
      else
	{
	  relocation = 0;
	  h = sym_hashes[r_symndx - symtab_hdr->sh_info];
	  symname = h->root.root.string;
	  while (h->root.type == bfd_link_hash_indirect
		 || h->root.type == bfd_link_hash_warning)
	    h = (struct elf_link_hash_entry *) h->root.u.i.link;
	  if (h->root.type == bfd_link_hash_defined
	      || h->root.type == bfd_link_hash_defweak)
	    {
	      bool dyn;

	      dyn = htab ? htab->root.dynamic_sections_created : false;
	      sec = h->root.u.def.section;
	      
	      if (r_type == R_SH_GOTPC
		  || r_type == R_SH_GOTPC_LOW16
		  || r_type == R_SH_GOTPC_MEDLOW16
		  || r_type == R_SH_GOTPC_MEDHI16
		  || r_type == R_SH_GOTPC_HI16
		  || ((r_type == R_SH_PLT32
		       || r_type == R_SH_PLT_LOW16
		       || r_type == R_SH_PLT_MEDLOW16
		       || r_type == R_SH_PLT_MEDHI16
		       || r_type == R_SH_PLT_HI16)
		      && h->plt.offset != (bfd_vma) -1)
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
		      && WILL_CALL_FINISH_DYNAMIC_SYMBOL (dyn,
							  bfd_link_pic (info),
							  h)
		      && (! bfd_link_pic (info)
			  || (! info->symbolic && h->dynindx != -1)
			  || !h->def_regular))
		  || (bfd_link_pic (info)
		      && ((! info->symbolic && h->dynindx != -1)
			  || !h->def_regular)
		      && ((r_type == R_SH_DIR32
			   && !h->forced_local)
			  || (r_type == R_SH_REL32
			      && !SYMBOL_CALLS_LOCAL (info, h)))
		      && ((input_section->flags & SEC_ALLOC) != 0
			  || ((input_section->flags & SEC_DEBUGGING) != 0
			      && h->def_dynamic)))
		  || (sec->output_section == NULL
		      && ((input_section->flags & SEC_DEBUGGING) != 0
			  && h->def_dynamic))
		  || (sec->output_section == NULL
		      && (sh_elf_hash_entry (h)->got_type == GOT_TLS_IE
			  || sh_elf_hash_entry (h)->got_type == GOT_TLS_GD)))
		;
	      else if (sec->output_section != NULL)
		relocation = (h->root.u.def.value
			      + sec->output_section->vma
			      + sec->output_offset);
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
		     h->root.root.string);
		  return false;
		}
	    }
	  else if (h->root.type == bfd_link_hash_undefweak)
	    resolved_to_zero = UNDEFWEAK_NO_DYNAMIC_RELOC (info, h);
	  else if (info->unresolved_syms_in_objects == RM_IGNORE
		   && ELF_ST_VISIBILITY (h->other) == STV_DEFAULT)
	    ;
	  else if (!bfd_link_relocatable (info))
            info->callbacks->undefined_symbol
	      (info, h->root.root.string, input_bfd, input_section,
	       rel->r_offset,
	       (info->unresolved_syms_in_objects == RM_DIAGNOSE
		&& !info->warn_unresolved_syms)
	       || ELF_ST_VISIBILITY (h->other));
        }

      if (sec != NULL && discarded_section (sec))
	RELOC_AGAINST_DISCARDED_SECTION (info, input_bfd, input_section,
					 rel, 1, relend, R_SH_NONE,
					 howto, 0, contents);

      if (bfd_link_relocatable (info))
	continue;

      check_segment[0] = isec_segment;
      if (sec != NULL)
	check_segment[1] = sh_elf_osec_to_segment (output_bfd,
						   sec->output_section);
      else
	check_segment[1] = -1;

      switch ((int) r_type)
	{
	final_link_relocate:
	  r = _bfd_final_link_relocate (howto, input_bfd, input_section,
					contents, rel->r_offset,
					relocation, addend);
	  break;

	case R_SH_IND12W:
	  goto final_link_relocate;

	case R_SH_DIR8WPN:
	case R_SH_DIR8WPZ:
	case R_SH_DIR8WPL:
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
		default: mask = 0; break;
		}
	      if (disp & mask)
		{
		  _bfd_error_handler
		    (_("%pB: %#" PRIx64 ": fatal: "
		       "unaligned branch target for relax-support relocation"),
		     input_section->owner,
		     (uint64_t) rel->r_offset);
		  bfd_set_error (bfd_error_bad_value);
		  return false;
		}
	      relocation -= 4;
	      goto final_link_relocate;
	    }
	  r = bfd_reloc_ok;
	  break;

	default:
	  bfd_set_error (bfd_error_bad_value);
	  return false;

	case R_SH_DIR16:
	case R_SH_DIR8:
	case R_SH_DIR8U:
	case R_SH_DIR8S:
	case R_SH_DIR4U:
	  goto final_link_relocate;

	case R_SH_DIR8UL:
	case R_SH_DIR4UL:
	  if (relocation & 3)
	    {
	      _bfd_error_handler
		(_("%pB: %#" PRIx64 ": fatal: "
		   "unaligned %s relocation %#" PRIx64),
		 input_section->owner, (uint64_t) rel->r_offset,
		 howto->name, (uint64_t) relocation);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  goto final_link_relocate;

	case R_SH_DIR8UW:
	case R_SH_DIR8SW:
	case R_SH_DIR4UW:
	  if (relocation & 1)
	    {
	      _bfd_error_handler
		(_("%pB: %#" PRIx64 ": fatal: "
		   "unaligned %s relocation %#" PRIx64 ""),
		 input_section->owner,
		 (uint64_t) rel->r_offset, howto->name,
		 (uint64_t) relocation);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  goto final_link_relocate;

	case R_SH_PSHA:
	  if ((signed int)relocation < -32
	      || (signed int)relocation > 32)
	    {
	      _bfd_error_handler
		(_("%pB: %#" PRIx64 ": fatal: R_SH_PSHA relocation %" PRId64
		   " not in range -32..32"),
		 input_section->owner,
		 (uint64_t) rel->r_offset,
		 (int64_t) relocation);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  goto final_link_relocate;

	case R_SH_PSHL:
	  if ((signed int)relocation < -16
	      || (signed int)relocation > 16)
	    {
	      _bfd_error_handler
		(_("%pB: %#" PRIx64 ": fatal: R_SH_PSHL relocation %" PRId64
		   " not in range -32..32"),
		 input_section->owner,
		 (uint64_t) rel->r_offset,
		 (int64_t) relocation);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  goto final_link_relocate;

	case R_SH_DIR32:
	case R_SH_REL32:
	  if (bfd_link_pic (info)
	      && (h == NULL
		  || (ELF_ST_VISIBILITY (h->other) == STV_DEFAULT
		      && !resolved_to_zero)
		  || h->root.type != bfd_link_hash_undefweak)
	      && r_symndx != STN_UNDEF
	      && (input_section->flags & SEC_ALLOC) != 0
	      && !is_vxworks_tls
	      && (r_type == R_SH_DIR32
		  || !SYMBOL_CALLS_LOCAL (info, h)))
	    {
	      Elf_Internal_Rela outrel;
	      bfd_byte *loc;
	      bool skip, relocate;

	      if (sreloc == NULL)
		{
		  sreloc = _bfd_elf_get_dynamic_reloc_section
		    (input_bfd, input_section, true);
		  if (sreloc == NULL)
		    return false;
		}

	      skip = false;
	      relocate = false;

	      outrel.r_offset =
		_bfd_elf_section_offset (output_bfd, info, input_section,
					 rel->r_offset);
	      if (outrel.r_offset == (bfd_vma) -1)
		skip = true;
	      else if (outrel.r_offset == (bfd_vma) -2)
		skip = true, relocate = true;
	      outrel.r_offset += (input_section->output_section->vma
				  + input_section->output_offset);

	      if (skip)
		memset (&outrel, 0, sizeof outrel);
	      else if (r_type == R_SH_REL32)
		{
		  BFD_ASSERT (h != NULL && h->dynindx != -1);
		  outrel.r_info = ELF32_R_INFO (h->dynindx, R_SH_REL32);
		  outrel.r_addend
		    = (howto->partial_inplace
		       ? bfd_get_32 (input_bfd, contents + rel->r_offset)
		       : addend);
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
		  outrel.r_addend = relocation;
		  outrel.r_addend
		    += (howto->partial_inplace
			? bfd_get_32 (input_bfd, contents + rel->r_offset)
			: addend);
		  outrel.r_addend -= sec->output_section->vma;
		}
	      else
		{
		  if (h == NULL
		      || ((info->symbolic || h->dynindx == -1)
			  && h->def_regular))
		    {
		      relocate = howto->partial_inplace;
		      outrel.r_info = ELF32_R_INFO (0, R_SH_RELATIVE);
		    }
		  else
		    {
		      BFD_ASSERT (h->dynindx != -1);
		      outrel.r_info = ELF32_R_INFO (h->dynindx, R_SH_DIR32);
		    }
		  outrel.r_addend = relocation;
		  outrel.r_addend
		    += (howto->partial_inplace
			? bfd_get_32 (input_bfd, contents + rel->r_offset)
			: addend);
		}

	      loc = sreloc->contents;
	      loc += sreloc->reloc_count++ * sizeof (Elf32_External_Rela);
	      bfd_elf32_swap_reloca_out (output_bfd, &outrel, loc);

	      check_segment[0] = check_segment[1] = -1;

	      if (! relocate)
		continue;
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
		       symname);
		    return false;
		  }

	      offset = _bfd_elf_section_offset (output_bfd, info,
						input_section, rel->r_offset);
	      if (offset != (bfd_vma)-1)
		sh_elf_add_rofixup (output_bfd, htab->srofixup,
				    input_section->output_section->vma
				    + input_section->output_offset
				    + rel->r_offset);

	      check_segment[0] = check_segment[1] = -1;
	    }
	    else if (r_type == R_SH_REL32
		     && h
		     && h->root.type == bfd_link_hash_undefweak)
	      check_segment[0] = check_segment[1] = -1;
	  goto final_link_relocate;

	case R_SH_GOTPLT32:
	  if (h == NULL
	      || h->forced_local
	      || ! bfd_link_pic (info)
	      || info->symbolic
	      || h->dynindx == -1
	      || h->plt.offset == (bfd_vma) -1
	      || h->got.offset != (bfd_vma) -1)
	    goto force_got;

	  BFD_ASSERT (htab);
	  BFD_ASSERT (sgotplt != NULL);
	  relocation = (sgotplt->output_offset
			+ (get_plt_index (htab->plt_info, h->plt.offset)
			   + 3) * 4);

#ifdef GOT_BIAS
	  relocation -= GOT_BIAS;
#endif

	  goto final_link_relocate;

	force_got:
	case R_SH_GOT32:
	case R_SH_GOT20:
	  BFD_ASSERT (htab);
	  BFD_ASSERT (sgot != NULL);
	  check_segment[0] = check_segment[1] = -1;

	  if (h != NULL)
	    {
	      bool dyn;

	      off = h->got.offset;
	      BFD_ASSERT (off != (bfd_vma) -1);

	      dyn = htab->root.dynamic_sections_created;
	      if (! WILL_CALL_FINISH_DYNAMIC_SYMBOL (dyn,
						     bfd_link_pic (info),
						     h)
		  || (bfd_link_pic (info)
		      && SYMBOL_REFERENCES_LOCAL (info, h))
		  || ((ELF_ST_VISIBILITY (h->other)
		       || resolved_to_zero)
		      && h->root.type == bfd_link_hash_undefweak))
		{
		  if ((off & 1) != 0)
		    off &= ~1;
		  else
		    {
		      bfd_put_32 (output_bfd, relocation,
				  sgot->contents + off);
		      h->got.offset |= 1;

		      if (fdpic_p && !bfd_link_pic (info)
			  && sh_elf_hash_entry (h)->got_type == GOT_NORMAL
			  && (ELF_ST_VISIBILITY (h->other) == STV_DEFAULT
			      || h->root.type != bfd_link_hash_undefweak))
			sh_elf_add_rofixup (output_bfd, htab->srofixup,
					    sgot->output_section->vma
					    + sgot->output_offset
					    + off);
		    }
		}

	      relocation = sh_elf_got_offset (htab) + off;
	    }
	  else
	    {
	      BFD_ASSERT (local_got_offsets != NULL
			  && local_got_offsets[r_symndx] != (bfd_vma) -1);

	      off = local_got_offsets[r_symndx];

	      if ((off & 1) != 0)
		off &= ~1;
	      else
		{
		  bfd_put_32 (output_bfd, relocation, sgot->contents + off);

		  if (bfd_link_pic (info))
		    {
		      Elf_Internal_Rela outrel;
		      bfd_byte *loc;

		      outrel.r_offset = (sgot->output_section->vma
					 + sgot->output_offset
					 + off);
		      if (fdpic_p)
			{
			  int dynindx
			    = elf_section_data (sec->output_section)->dynindx;
			  outrel.r_info = ELF32_R_INFO (dynindx, R_SH_DIR32);
			  outrel.r_addend = relocation;
			  outrel.r_addend -= sec->output_section->vma;
			}
		      else
			{
			  outrel.r_info = ELF32_R_INFO (0, R_SH_RELATIVE);
			  outrel.r_addend = relocation;
			}
		      loc = srelgot->contents;
		      loc += srelgot->reloc_count++ * sizeof (Elf32_External_Rela);
		      bfd_elf32_swap_reloca_out (output_bfd, &outrel, loc);
		    }
		  else if (fdpic_p
			   && (sh_elf_local_got_type (input_bfd) [r_symndx]
			       == GOT_NORMAL))
		    sh_elf_add_rofixup (output_bfd, htab->srofixup,
					sgot->output_section->vma
					+ sgot->output_offset
					+ off);

		  local_got_offsets[r_symndx] |= 1;
		}

	      relocation = sh_elf_got_offset (htab) + off;
	    }

#ifdef GOT_BIAS
	  relocation -= GOT_BIAS;
#endif

	  if (r_type == R_SH_GOT20)
	    {
	      r = install_movi20_field (output_bfd, relocation + addend,
					input_bfd, input_section, contents,
					rel->r_offset);
	      break;
	    }
	  else
	    goto final_link_relocate;

	case R_SH_GOTOFF:
	case R_SH_GOTOFF20:
	  BFD_ASSERT (htab);

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
  asection **sections = NULL;
  Elf_Internal_Rela *internal_relocs = NULL;
  Elf_Internal_Sym *isymbuf = NULL;
  bfd_byte *orig_data = data;

  if (relocatable || elf_section_data (input_section)->this_hdr.contents == NULL)
    return bfd_generic_get_relocated_section_contents (output_bfd, link_info,
						       link_order, data,
						       relocatable,
						       symbols);

  symtab_hdr = &elf_symtab_hdr (input_bfd);

  if (data == NULL)
    {
      data = bfd_malloc (input_section->size);
      if (data == NULL)
	return NULL;
    }
  memcpy (data, elf_section_data (input_section)->this_hdr.contents,
	  (size_t) input_section->size);

  if ((input_section->flags & SEC_RELOC) == 0 || input_section->reloc_count == 0)
    return data;

  internal_relocs = _bfd_elf_link_read_relocs (input_bfd, input_section, NULL,
					       (Elf_Internal_Rela *) NULL, false);
  if (internal_relocs == NULL)
    goto error_return;

  if (symtab_hdr->sh_info != 0)
    {
      isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;
      if (isymbuf == NULL)
	{
	  isymbuf = bfd_elf_get_elf_syms (input_bfd, symtab_hdr,
					  symtab_hdr->sh_info, 0,
					  NULL, NULL, NULL);
	  if (isymbuf == NULL)
	    goto error_return;
	}
    }

  bfd_size_type amt = symtab_hdr->sh_info * sizeof (asection *);
  if (amt > 0)
    {
      sections = (asection **) bfd_malloc (amt);
      if (sections == NULL)
	goto error_return;

      Elf_Internal_Sym *isymend = isymbuf + symtab_hdr->sh_info;
      asection **secpp = sections;
      for (Elf_Internal_Sym *isym = isymbuf; isym < isymend; ++isym, ++secpp)
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
    }

  if (!sh_elf_relocate_section (output_bfd, link_info, input_bfd,
				input_section, data, internal_relocs,
				isymbuf, sections))
    goto error_return;

  free (sections);
  if (isymbuf && symtab_hdr->contents != (unsigned char *) isymbuf)
    free (isymbuf);
  if (internal_relocs && elf_section_data (input_section)->relocs != internal_relocs)
    free (internal_relocs);

  return data;

 error_return:
  free (sections);
  if (isymbuf && symtab_hdr->contents != (unsigned char *) isymbuf)
    free (isymbuf);
  if (internal_relocs && elf_section_data (input_section)->relocs != internal_relocs)
    free (internal_relocs);
  if (orig_data == NULL)
    free (data);
  return NULL;
}

/* Return the base VMA address which should be subtracted from real addresses
   when resolving @dtpoff relocation.
   This is PT_TLS segment p_vaddr.  */

static bfd_vma
dtpoff_base (struct bfd_link_info *info)
{
  struct elf_link_hash_table *hash_table;
  
  if (info == NULL)
    return 0;
    
  hash_table = elf_hash_table (info);
  if (hash_table == NULL || hash_table->tls_sec == NULL)
    return 0;
    
  return hash_table->tls_sec->vma;
}

/* Return the relocation value for R_SH_TLS_TPOFF32..  */

static bfd_vma
tpoff (struct bfd_link_info *info, bfd_vma address)
{
  struct elf_link_hash_table *hash_table;
  asection *tls_sec;
  
  if (info == NULL)
    return 0;
    
  hash_table = elf_hash_table (info);
  if (hash_table == NULL)
    return 0;
    
  tls_sec = hash_table->tls_sec;
  if (tls_sec == NULL)
    return 0;
  
  return (address - tls_sec->vma + align_power ((bfd_vma) 8, tls_sec->alignment_power));
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
sh_elf_copy_indirect_symbol (struct bfd_link_info *info,
                             struct elf_link_hash_entry *dir,
                             struct elf_link_hash_entry *ind)
{
  struct elf_sh_link_hash_entry *edir, *eind;

  if (!dir || !ind) {
    return;
  }

  edir = (struct elf_sh_link_hash_entry *) dir;
  eind = (struct elf_sh_link_hash_entry *) ind;

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
    _bfd_elf_link_hash_copy_indirect (info, dir, ind);
  }
}

static int
sh_elf_optimized_tls_reloc (struct bfd_link_info *info, int r_type,
			    int is_local)
{
  if (info == NULL || bfd_link_pic (info))
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
sh_elf_check_relocs (bfd *abfd, struct bfd_link_info *info, asection *sec,
		     const Elf_Internal_Rela *relocs)
{
  Elf_Internal_Shdr *symtab_hdr;
  struct elf_link_hash_entry **sym_hashes;
  struct elf_sh_link_hash_table *htab;
  const Elf_Internal_Rela *rel;
  const Elf_Internal_Rela *rel_end;
  asection *sreloc;
  unsigned int r_type;
  enum got_type got_type, old_got_type;

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
      struct elf_link_hash_entry *h;
      unsigned long r_symndx;

      r_symndx = ELF32_R_SYM (rel->r_info);
      r_type = ELF32_R_TYPE (rel->r_info);

      if (r_symndx < symtab_hdr->sh_info)
	h = NULL;
      else
	{
	  h = sym_hashes[r_symndx - symtab_hdr->sh_info];
	  while (h->root.type == bfd_link_hash_indirect
		 || h->root.type == bfd_link_hash_warning)
	    h = (struct elf_link_hash_entry *) h->root.u.i.link;
	}

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
	  if (r_type == R_SH_GOTOFFFUNCDESC ||
	      r_type == R_SH_GOTOFFFUNCDESC20 ||
	      r_type == R_SH_FUNCDESC ||
	      r_type == R_SH_GOTFUNCDESC ||
	      r_type == R_SH_GOTFUNCDESC20)
	    {
	      if (h != NULL)
		{
		  if (h->dynindx == -1)
		    {
		      int visibility = ELF_ST_VISIBILITY (h->other);
		      if (visibility != STV_INTERNAL && visibility != STV_HIDDEN)
			bfd_elf_link_record_dynamic_symbol (info, h);
		    }
		}
	    }
	}

      if (htab->root.sgot == NULL)
	{
	  bool needs_got = false;
	  
	  switch (r_type)
	    {
	    case R_SH_DIR32:
	      needs_got = htab->fdpic_p;
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
	      needs_got = true;
	      break;
	    default:
	      needs_got = false;
	      break;
	    }
	    
	  if (needs_got)
	    {
	      if (htab->root.dynobj == NULL)
		htab->root.dynobj = abfd;
	      if (!create_got_section (htab->root.dynobj, info))
		return false;
	    }
	}

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
	  /* FALLTHROUGH */
	force_got:
	case R_SH_TLS_GD_32:
	case R_SH_GOT32:
	case R_SH_GOT20:
	case R_SH_GOTFUNCDESC:
	case R_SH_GOTFUNCDESC20:
	  switch (r_type)
	    {
	    default:
	      got_type = GOT_NORMAL;
	      break;
	    case R_SH_TLS_GD_32:
	      got_type = GOT_TLS_GD;
	      break;
	    case R_SH_TLS_IE_32:
	      got_type = GOT_TLS_IE;
	      break;
	    case R_SH_GOTFUNCDESC:
	    case R_SH_GOTFUNCDESC20:
	      got_type = GOT_FUNCDESC;
	      break;
	    }

	  if (h != NULL)
	    {
	      h->got.refcount += 1;
	      old_got_type = sh_elf_hash_entry (h)->got_type;
	    }
	  else
	    {
	      bfd_signed_vma *local_got_refcounts;

	      local_got_refcounts = elf_local_got_refcounts (abfd);
	      if (local_got_refcounts == NULL)
		{
		  bfd_size_type size;

		  size = symtab_hdr->sh_info;
		  size *= sizeof (bfd_signed_vma);
		  size += symtab_hdr->sh_info;
		  local_got_refcounts = ((bfd_signed_vma *)
					 bfd_zalloc (abfd, size));
		  if (local_got_refcounts == NULL)
		    return false;
		  elf_local_got_refcounts (abfd) = local_got_refcounts;
		  sh_elf_local_got_type (abfd)
		    = (char *) (local_got_refcounts + symtab_hdr->sh_info);
		}
	      local_got_refcounts[r_symndx] += 1;
	      old_got_type = sh_elf_local_got_type (abfd) [r_symndx];
	    }

	  if (old_got_type != got_type && old_got_type != GOT_UNKNOWN
	      && (old_got_type != GOT_TLS_GD || got_type != GOT_TLS_IE))
	    {
	      if (old_got_type == GOT_TLS_IE && got_type == GOT_TLS_GD)
		got_type = GOT_TLS_IE;
	      else
		{
		  const char *error_msg = NULL;
		  
		  if ((old_got_type == GOT_FUNCDESC || got_type == GOT_FUNCDESC)
		      && (old_got_type == GOT_NORMAL || got_type == GOT_NORMAL))
		    error_msg = _("%pB: `%s' accessed both as normal and FDPIC symbol");
		  else if (old_got_type == GOT_FUNCDESC || got_type == GOT_FUNCDESC)
		    error_msg = _("%pB: `%s' accessed both as FDPIC and thread local symbol");
		  else
		    error_msg = _("%pB: `%s' accessed both as normal and thread local symbol");

		  _bfd_error_handler (error_msg, abfd, h->root.root.string);
		  return false;
		}
	    }

	  if (old_got_type != got_type)
	    {
	      if (h != NULL)
		sh_elf_hash_entry (h)->got_type = got_type;
	      else
		sh_elf_local_got_type (abfd) [r_symndx] = got_type;
	    }

	  break;

	case R_SH_TLS_LD_32:
	  sh_elf_hash_table(info)->tls_ldm_got.refcount += 1;
	  break;

	case R_SH_FUNCDESC:
	case R_SH_GOTOFFFUNCDESC:
	case R_SH_GOTOFFFUNCDESC20:
	  if (rel->r_addend)
	    {
	      _bfd_error_handler
		(_("%pB: Function descriptor relocation with non-zero addend"),
		 abfd);
	      return false;
	    }

	  if (h == NULL)
	    {
	      union gotref *local_funcdesc;

	      local_funcdesc = sh_elf_local_funcdesc (abfd);
	      if (local_funcdesc == NULL)
		{
		  bfd_size_type size;

		  size = symtab_hdr->sh_info * sizeof (union gotref);
		  local_funcdesc = (union gotref *) bfd_zalloc (abfd, size);
		  if (local_funcdesc == NULL)
		    return false;
		  sh_elf_local_funcdesc (abfd) = local_funcdesc;
		}
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
	      sh_elf_hash_entry (h)->funcdesc.refcount++;
	      if (r_type == R_SH_FUNCDESC)
		sh_elf_hash_entry (h)->abs_funcdesc_refcount++;

	      old_got_type = sh_elf_hash_entry (h)->got_type;
	      if (old_got_type != GOT_FUNCDESC && old_got_type != GOT_UNKNOWN)
		{
		  const char *error_msg = (old_got_type == GOT_NORMAL) ?
		    _("%pB: `%s' accessed both as normal and FDPIC symbol") :
		    _("%pB: `%s' accessed both as FDPIC and thread local symbol");
		  
		  _bfd_error_handler (error_msg, abfd, h->root.root.string);
		}
	    }
	  break;

	case R_SH_GOTPLT32:
	  if (h == NULL
	      || h->forced_local
	      || ! bfd_link_pic (info)
	      || info->symbolic
	      || h->dynindx == -1)
	    goto force_got;

	  h->needs_plt = 1;
	  h->plt.refcount += 1;
	  ((struct elf_sh_link_hash_entry *) h)->gotplt_refcount += 1;

	  break;

	case R_SH_PLT32:
	  if (h == NULL)
	    continue;

	  if (h->forced_local)
	    break;

	  h->needs_plt = 1;
	  h->plt.refcount += 1;
	  break;

	case R_SH_DIR32:
	case R_SH_REL32:
	  if (h != NULL && ! bfd_link_pic (info))
	    {
	      h->non_got_ref = 1;
	      h->plt.refcount += 1;
	    }

	  if ((bfd_link_pic (info)
	       && (sec->flags & SEC_ALLOC) != 0
	       && (r_type != R_SH_REL32
		   || (h != NULL
		       && (! info->symbolic
			   || h->root.type == bfd_link_hash_defweak
			   || !h->def_regular))))
	      || (! bfd_link_pic (info)
		  && (sec->flags & SEC_ALLOC) != 0
		  && h != NULL
		  && (h->root.type == bfd_link_hash_defweak
		      || !h->def_regular)))
	    {
	      struct elf_dyn_relocs *p;
	      struct elf_dyn_relocs **head;

	      if (htab->root.dynobj == NULL)
		htab->root.dynobj = abfd;

	      if (sreloc == NULL)
		{
		  sreloc = _bfd_elf_make_dynamic_reloc_section
		    (sec, htab->root.dynobj, 2, abfd, /*rela?*/ true);

		  if (sreloc == NULL)
		    return false;
		}

	      if (h != NULL)
		head = &h->dyn_relocs;
	      else
		{
		  asection *s;
		  void *vpp;
		  Elf_Internal_Sym *isym;

		  isym = bfd_sym_from_r_symndx (&htab->root.sym_cache,
						abfd, r_symndx);
		  if (isym == NULL)
		    return false;

		  s = bfd_section_from_elf_index (abfd, isym->st_shndx);
		  if (s == NULL)
		    s = sec;

		  vpp = &elf_section_data (s)->local_dynrel;
		  head = (struct elf_dyn_relocs **) vpp;
		}

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
	    }

	  if (htab->fdpic_p && !bfd_link_pic (info)
	      && r_type == R_SH_DIR32
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
    }

  return true;
}

#ifndef sh_elf_set_mach_from_flags
static unsigned int sh_ef_bfd_table[] = { EF_SH_BFD_TABLE };

static bool
sh_elf_set_mach_from_flags (bfd *abfd)
{
  if (abfd == NULL)
    return false;

  flagword flags = elf_elfheader (abfd)->e_flags & EF_SH_MACH_MASK;

  if (flags >= ARRAY_SIZE (sh_ef_bfd_table))
    return false;

  if (sh_ef_bfd_table[flags] == 0)
    return false;

  return bfd_default_set_arch_mach (abfd, bfd_arch_sh, sh_ef_bfd_table[flags]);
}


/* Reverse table lookup for sh_ef_bfd_table[].
   Given a bfd MACH value from archures.c
   return the equivalent ELF flags from the table.
   Return -1 if no match is found.  */

int
sh_elf_get_flags_from_mach (unsigned long mach)
{
  for (int i = ARRAY_SIZE (sh_ef_bfd_table) - 1; i >= 0; i--)
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
  if (ibfd == NULL || obfd == NULL)
    return false;

  if (!is_sh_elf (ibfd) || !is_sh_elf (obfd))
    return true;

  if (!_bfd_elf_copy_private_bfd_data (ibfd, obfd))
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
  bfd *obfd;
  unsigned int old_arch, new_arch, merged_arch;
  const char *new_instr_type, *old_instr_type;

  if (!ibfd || !info || !info->output_bfd)
    return false;

  if (!_bfd_generic_verify_endian_match (ibfd, info))
    return false;

  obfd = info->output_bfd;
  old_arch = sh_get_arch_up_from_bfd_mach (bfd_get_mach (obfd));
  new_arch = sh_get_arch_up_from_bfd_mach (bfd_get_mach (ibfd));
  merged_arch = SH_MERGE_ARCH_SET (old_arch, new_arch);

  if (!SH_VALID_CO_ARCH_SET (merged_arch))
    {
      new_instr_type = SH_ARCH_SET_HAS_DSP (new_arch) ? "dsp" : "floating point";
      old_instr_type = SH_ARCH_SET_HAS_DSP (new_arch) ? "floating point" : "dsp";
      
      _bfd_error_handler
        (_("%pB: uses %s instructions while previous modules use %s instructions"),
         ibfd, new_instr_type, old_instr_type);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  if (!SH_VALID_ARCH_SET (merged_arch))
    {
      _bfd_error_handler
        (_("internal error: merge of architecture '%s' with architecture '%s' produced unknown architecture"),
         bfd_printable_name (obfd), bfd_printable_name (ibfd));
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
  bfd *obfd;
  
  if (!ibfd || !info)
    return false;
    
  obfd = info->output_bfd;
  if (!obfd)
    return false;

  if ((ibfd->flags & DYNAMIC) != 0)
    return true;

  if (!is_sh_elf (ibfd) || !is_sh_elf (obfd))
    return true;

  if (!elf_flags_init (obfd))
    {
      elf_flags_init (obfd) = true;
      elf_elfheader (obfd)->e_flags = elf_elfheader (ibfd)->e_flags;
      sh_elf_set_mach_from_flags (obfd);
      if (elf_elfheader (obfd)->e_flags & EF_SH_FDPIC)
        elf_elfheader (obfd)->e_flags &= ~EF_SH_PIC;
    }

  if (!sh_merge_bfd_arch (ibfd, info))
    {
      _bfd_error_handler (_("%pB: uses instructions which are incompatible "
                            "with instructions used in previous modules"),
                          ibfd);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  elf_elfheader (obfd)->e_flags &= ~EF_SH_MACH_MASK;
  elf_elfheader (obfd)->e_flags |=
    sh_elf_get_flags_from_mach (bfd_get_mach (obfd));

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
  if (abfd == NULL)
    return false;

  if (!sh_elf_set_mach_from_flags (abfd))
    return false;

  Elf_Internal_Ehdr *ehdr = elf_elfheader (abfd);
  if (ehdr == NULL)
    return false;

  bool has_fdpic_flag = (ehdr->e_flags & EF_SH_FDPIC) != 0;
  bool is_fdpic_object = fdpic_object_p (abfd);

  return has_fdpic_flag == is_fdpic_object;
}

/* Finish up dynamic symbol handling.  We set the contents of various
   dynamic sections here.  */

static bool
sh_elf_finish_dynamic_symbol (bfd *output_bfd, struct bfd_link_info *info,
                              struct elf_link_hash_entry *h,
                              Elf_Internal_Sym *sym)
{
  struct elf_sh_link_hash_table *htab;

  htab = sh_elf_hash_table (info);
  if (!htab)
    return false;

  if (h->plt.offset != (bfd_vma) -1)
    {
      if (!process_plt_entry(output_bfd, info, h, htab))
        return false;
    }

  if (h->got.offset != (bfd_vma) -1
      && sh_elf_hash_entry (h)->got_type != GOT_TLS_GD
      && sh_elf_hash_entry (h)->got_type != GOT_TLS_IE
      && sh_elf_hash_entry (h)->got_type != GOT_FUNCDESC)
    {
      if (!process_got_entry(output_bfd, info, h, htab))
        return false;
    }

  if (h->needs_copy)
    {
      if (!process_copy_reloc(output_bfd, h, htab))
        return false;
    }

  if (h == htab->root.hdynamic
      || (htab->root.target_os != is_vxworks && h == htab->root.hgot))
    sym->st_shndx = SHN_ABS;

  return true;
}

static bool
process_plt_entry(bfd *output_bfd, struct bfd_link_info *info,
                  struct elf_link_hash_entry *h,
                  struct elf_sh_link_hash_table *htab)
{
  asection *splt, *sgotplt, *srelplt;
  bfd_vma plt_index, got_offset;
  const struct elf_sh_plt_info *plt_info;

  if (h->dynindx == -1)
    return false;

  splt = htab->root.splt;
  sgotplt = htab->root.sgotplt;
  srelplt = htab->root.srelplt;
  
  if (!splt || !sgotplt || !srelplt)
    return false;

  plt_index = get_plt_index (htab->plt_info, h->plt.offset);
  plt_info = select_plt_info(htab->plt_info, plt_index);
  got_offset = calculate_got_offset(htab, plt_index, sgotplt->size, bfd_link_pic(info));

  if (!fill_plt_entry(output_bfd, info, h, htab, splt, sgotplt, 
                      plt_info, got_offset))
    return false;

  if (!fill_got_entry(output_bfd, h, sgotplt, splt, got_offset, 
                      htab, plt_info))
    return false;

  if (!create_plt_reloc(output_bfd, h, srelplt, sgotplt, plt_index, 
                        got_offset, htab))
    return false;

  if (htab->root.target_os == is_vxworks && !bfd_link_pic (info))
    {
      if (!create_vxworks_unloaded_relocs(output_bfd, h, htab, splt, 
                                          sgotplt, plt_index, got_offset, 
                                          plt_info))
        return false;
    }

  if (!h->def_regular)
    {
      Elf_Internal_Sym *sym = get_symbol_for_hash(h);
      if (sym)
        sym->st_shndx = SHN_UNDEF;
    }

  return true;
}

static const struct elf_sh_plt_info *
select_plt_info(const struct elf_sh_plt_info *base_info, bfd_vma plt_index)
{
  if (base_info->short_plt && plt_index <= MAX_SHORT_PLT)
    return base_info->short_plt;
  return base_info;
}

static bfd_vma
calculate_got_offset(struct elf_sh_link_hash_table *htab, bfd_vma plt_index,
                     bfd_vma sgotplt_size, bool is_pic)
{
  bfd_vma got_offset;
  
  if (htab->fdpic_p)
    got_offset = plt_index * 8 + 12 - sgotplt_size;
  else
    got_offset = (plt_index + 3) * 4;

#ifdef GOT_BIAS
  if (is_pic)
    got_offset -= GOT_BIAS;
#endif

  return got_offset;
}

static bool
fill_plt_entry(bfd *output_bfd, struct bfd_link_info *info,
               struct elf_link_hash_entry *h,
               struct elf_sh_link_hash_table *htab,
               asection *splt, asection *sgotplt,
               const struct elf_sh_plt_info *plt_info,
               bfd_vma got_offset)
{
  if (plt_info->symbol_entry_size > splt->size - h->plt.offset)
    return false;

  memcpy (splt->contents + h->plt.offset,
          plt_info->symbol_entry,
          plt_info->symbol_entry_size);

  if (bfd_link_pic (info) || htab->fdpic_p)
    {
      return install_got_field_pic(output_bfd, splt, h, plt_info, got_offset);
    }
  else
    {
      return install_got_field_non_pic(output_bfd, htab, splt, sgotplt, 
                                       h, plt_info, got_offset);
    }
}

static bool
install_got_field_pic(bfd *output_bfd, asection *splt,
                      struct elf_link_hash_entry *h,
                      const struct elf_sh_plt_info *plt_info,
                      bfd_vma got_offset)
{
  if (plt_info->symbol_fields.got20)
    {
      bfd_reloc_status_type r;
      r = install_movi20_field (output_bfd, got_offset,
                                splt->owner, splt, splt->contents,
                                h->plt.offset + plt_info->symbol_fields.got_entry);
      return (r == bfd_reloc_ok);
    }
  else
    {
      install_plt_field (output_bfd, false, got_offset,
                         splt->contents + h->plt.offset + 
                         plt_info->symbol_fields.got_entry);
      return true;
    }
}

static bool
install_got_field_non_pic(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                          asection *splt, asection *sgotplt,
                          struct elf_link_hash_entry *h,
                          const struct elf_sh_plt_info *plt_info,
                          bfd_vma got_offset)
{
  if (plt_info->symbol_fields.got20)
    return false;

  bfd_vma target_addr = sgotplt->output_section->vma + 
                        sgotplt->output_offset + got_offset;
  
  install_plt_field (output_bfd, false, target_addr,
                     splt->contents + h->plt.offset + 
                     plt_info->symbol_fields.got_entry);

  if (htab->root.target_os == is_vxworks)
    {
      return install_vxworks_branch(output_bfd, splt, h, plt_info);
    }
  else
    {
      bfd_vma plt_addr = splt->output_section->vma + splt->output_offset;
      install_plt_field (output_bfd, true, plt_addr,
                         splt->contents + h->plt.offset + 
                         plt_info->symbol_fields.plt);
      return true;
    }
}

static bool
install_vxworks_branch(bfd *output_bfd, asection *splt,
                       struct elf_link_hash_entry *h,
                       const struct elf_sh_plt_info *plt_info)
{
  unsigned int reachable_plts, plts_per_4k;
  int distance;
  bfd_vma plt_index = get_plt_index(plt_info, h->plt.offset);

  reachable_plts = ((4096 - plt_info->plt0_entry_size - 
                    (plt_info->symbol_fields.plt + 4)) / 
                    plt_info->symbol_entry_size) + 1;
  plts_per_4k = (4096 / plt_info->symbol_entry_size);
  
  if (plt_index < reachable_plts)
    distance = -(h->plt.offset + plt_info->symbol_fields.plt);
  else
    distance = -(((plt_index - reachable_plts) % plts_per_4k + 1) * 
                 plt_info->symbol_entry_size);

  unsigned short branch_instr = 0xa000 | (0x0fff & ((distance - 4) / 2));
  bfd_put_16 (output_bfd, branch_instr,
              splt->contents + h->plt.offset + plt_info->symbol_fields.plt);
  return true;
}

static bool
fill_got_entry(bfd *output_bfd, struct elf_link_hash_entry *h,
               asection *sgotplt, asection *splt, bfd_vma got_offset,
               struct elf_sh_link_hash_table *htab,
               const struct elf_sh_plt_info *plt_info)
{
  bfd_vma resolve_addr = splt->output_section->vma + splt->output_offset + 
                         h->plt.offset + plt_info->symbol_resolve_offset;
  
  if (got_offset + 4 > sgotplt->size)
    return false;

  bfd_put_32 (output_bfd, resolve_addr, sgotplt->contents + got_offset);
  
  if (htab->fdpic_p)
    {
      if (got_offset + 8 > sgotplt->size)
        return false;
      bfd_put_32 (output_bfd,
                  sh_elf_osec_to_segment (output_bfd, splt->output_section),
                  sgotplt->contents + got_offset + 4);
    }

  return true;
}

static bool
create_plt_reloc(bfd *output_bfd, struct elf_link_hash_entry *h,
                 asection *srelplt, asection *sgotplt, bfd_vma plt_index,
                 bfd_vma got_offset, struct elf_sh_link_hash_table *htab)
{
  Elf_Internal_Rela rel;
  bfd_byte *loc;

  got_offset = adjust_got_offset_for_reloc(got_offset, htab, plt_index);

  rel.r_offset = sgotplt->output_section->vma + sgotplt->output_offset + got_offset;
  
  if (htab->fdpic_p)
    rel.r_info = ELF32_R_INFO (h->dynindx, R_SH_FUNCDESC_VALUE);
  else
    rel.r_info = ELF32_R_INFO (h->dynindx, R_SH_JMP_SLOT);
    
  rel.r_addend = 0;
#ifdef GOT_BIAS
  rel.r_addend = GOT_BIAS;
#endif

  if (plt_index * sizeof(Elf32_External_Rela) >= srelplt->size)
    return false;

  loc = srelplt->contents + plt_index * sizeof (Elf32_External_Rela);
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
  return true;
}

static bfd_vma
adjust_got_offset_for_reloc(bfd_vma got_offset, struct elf_sh_link_hash_table *htab,
                           bfd_vma plt_index)
{
#ifdef GOT_BIAS
  if (bfd_link_pic (info))
    got_offset += GOT_BIAS;
#endif
  if (htab->fdpic_p)
    got_offset = plt_index * 8;
    
  return got_offset;
}

static bool
create_vxworks_unloaded_relocs(bfd *output_bfd, struct elf_link_hash_entry *h,
                               struct elf_sh_link_hash_table *htab,
                               asection *splt, asection *sgotplt,
                               bfd_vma plt_index, bfd_vma got_offset,
                               const struct elf_sh_plt_info *plt_info)
{
  Elf_Internal_Rela rel;
  bfd_byte *loc;

  if (!htab->srelplt2)
    return false;

  size_t reloc_offset = (plt_index * 2 + 1) * sizeof(Elf32_External_Rela);
  if (reloc_offset + 2 * sizeof(Elf32_External_Rela) > htab->srelplt2->size)
    return false;

  loc = htab->srelplt2->contents + reloc_offset;

  rel.r_offset = splt->output_section->vma + splt->output_offset + 
                 h->plt.offset + plt_info->symbol_fields.got_entry;
  rel.r_info = ELF32_R_INFO (htab->root.hgot->indx, R_SH_DIR32);
  rel.r_addend = got_offset;
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
  loc += sizeof (Elf32_External_Rela);

  rel.r_offset = sgotplt->output_section->vma + sgotplt->output_offset + got_offset;
  rel.r_info = ELF32_R_INFO (htab->root.hplt->indx, R_SH_DIR32);
  rel.r_addend = 0;
  bfd_elf32_swap_reloc_out (output_bfd, &rel, loc);
  
  return true;
}

static bool
process_got_entry(bfd *output_bfd, struct bfd_link_info *info,
                  struct elf_link_hash_entry *h,
                  struct elf_sh_link_hash_table *htab)
{
  asection *sgot, *srelgot;
  Elf_Internal_Rela rel;
  bfd_byte *loc;

  sgot = htab->root.sgot;
  srelgot = htab->root.srelgot;
  
  if (!sgot || !srelgot)
    return false;

  rel.r_offset = sgot->output_section->vma + sgot->output_offset + 
                 (h->got.offset &~ (bfd_vma) 1);

  if (should_emit_relative_reloc(info, h))
    {
      if (!create_relative_reloc(output_bfd, &rel, h, htab))
        return false;
    }
  else
    {
      if (h->got.offset >= sgot->size)
        return false;
      bfd_put_32 (output_bfd, (bfd_vma) 0, sgot->contents + h->got.offset);
      rel.r_info = ELF32_R_INFO (h->dynindx, R_SH_GLOB_DAT);
      rel.r_addend = 0;
    }

  if (srelgot->reloc_count * sizeof(Elf32_External_Rela) >= srelgot->size)
    return false;

  loc = srelgot->contents + srelgot->reloc_count * sizeof (Elf32_External_Rela);
  srelgot->reloc_count++;
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
  return true;
}

static bool
should_emit_relative_reloc(struct bfd_link_info *info, 
                          struct elf_link_hash_entry *h)
{
  return bfd_link_pic (info)
         && (h->root.type == bfd_link_hash_defined
             || h->root.type == bfd_link_hash_defweak)
         && SYMBOL_REFERENCES_LOCAL (info, h);
}

static bool
create_relative_reloc(bfd *output_bfd, Elf_Internal_Rela *rel,
                      struct elf_link_hash_entry *h,
                      struct elf_sh_link_hash_table *htab)
{
  if (htab->fdpic_p)
    {
      asection *sec = h->root.u.def.section;
      int dynindx = elf_section_data (sec->output_section)->dynindx;
      
      rel->r_info = ELF32_R_INFO (dynindx, R_SH_DIR32);
      rel->r_addend = h->root.u.def.value + h->root.u.def.section->output_offset;
    }
  else
    {
      rel->r_info = ELF32_R_INFO (0, R_SH_RELATIVE);
      rel->r_addend = h->root.u.def.value + 
                      h->root.u.def.section->output_section->vma + 
                      h->root.u.def.section->output_offset;
    }
  return true;
}

static bool
process_copy_reloc(bfd *output_bfd, struct elf_link_hash_entry *h,
                   struct elf_sh_link_hash_table *htab)
{
  asection *s;
  Elf_Internal_Rela rel;
  bfd_byte *loc;

  if (h->dynindx == -1)
    return false;
    
  if (h->root.type != bfd_link_hash_defined && 
      h->root.type != bfd_link_hash_defweak)
    return false;

  s = bfd_get_linker_section (htab->root.dynobj, ".rela.bss");
  if (!s)
    return false;

  if (s->reloc_count * sizeof(Elf32_External_Rela) >= s->size)
    return false;

  rel.r_offset = h->root.u.def.value + h->root.u.def.section->output_section->vma + 
                 h->root.u.def.section->output_offset;
  rel.r_info = ELF32_R_INFO (h->dynindx, R_SH_COPY);
  rel.r_addend = 0;
  
  loc = s->contents + s->reloc_count * sizeof (Elf32_External_Rela);
  s->reloc_count++;
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
  return true;
}

/* Finish up the dynamic sections.  */

static bool
sh_elf_finish_dynamic_sections (bfd *output_bfd, struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab;
  asection *sgotplt;
  asection *sdyn;

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  sgotplt = htab->root.sgotplt;
  sdyn = bfd_get_linker_section (htab->root.dynobj, ".dynamic");

  if (htab->root.dynamic_sections_created)
    {
      if (!process_dynamic_section(output_bfd, htab, sgotplt, sdyn))
        return false;
      
      if (!setup_plt_section(output_bfd, htab, sgotplt))
        return false;
    }

  if (!setup_got_section(output_bfd, htab, sgotplt, sdyn))
    return false;

  if (!finalize_fdpic_sections(output_bfd, htab))
    return false;

  validate_relocation_sections(htab);

  return true;
}

static bool
process_dynamic_section(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                       asection *sgotplt, asection *sdyn)
{
  Elf32_External_Dyn *dyncon, *dynconend;

  if (sgotplt == NULL || sdyn == NULL)
    return false;

  dyncon = (Elf32_External_Dyn *) sdyn->contents;
  dynconend = (Elf32_External_Dyn *) (sdyn->contents + sdyn->size);
  
  for (; dyncon < dynconend; dyncon++)
    {
      Elf_Internal_Dyn dyn;
      bfd_elf32_swap_dyn_in (htab->root.dynobj, dyncon, &dyn);

      if (!process_dynamic_entry(output_bfd, htab, &dyn, dyncon))
        return false;
    }
  return true;
}

static bool
process_dynamic_entry(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                     Elf_Internal_Dyn *dyn, Elf32_External_Dyn *dyncon)
{
  asection *s;

  switch (dyn->d_tag)
    {
    case DT_PLTGOT:
      if (htab->root.hgot == NULL)
        return false;
      s = htab->root.hgot->root.u.def.section;
      dyn->d_un.d_ptr = htab->root.hgot->root.u.def.value
        + s->output_section->vma + s->output_offset;
      bfd_elf32_swap_dyn_out (output_bfd, dyn, dyncon);
      break;

    case DT_JMPREL:
      s = htab->root.srelplt;
      if (s == NULL)
        return false;
      dyn->d_un.d_ptr = s->output_section->vma + s->output_offset;
      bfd_elf32_swap_dyn_out (output_bfd, dyn, dyncon);
      break;

    case DT_PLTRELSZ:
      s = htab->root.srelplt;
      if (s == NULL)
        return false;
      dyn->d_un.d_val = s->size;
      bfd_elf32_swap_dyn_out (output_bfd, dyn, dyncon);
      break;

    default:
      if (htab->root.target_os == is_vxworks
          && elf_vxworks_finish_dynamic_entry (output_bfd, dyn))
        bfd_elf32_swap_dyn_out (output_bfd, dyn, dyncon);
      break;
    }
  return true;
}

static bool
setup_plt_section(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                 asection *sgotplt)
{
  asection *splt = htab->root.splt;
  
  if (splt == NULL || splt->size == 0 || htab->plt_info->plt0_entry == NULL)
    return true;

  memcpy (splt->contents, htab->plt_info->plt0_entry,
          htab->plt_info->plt0_entry_size);

  if (!install_plt_fields(output_bfd, htab, sgotplt, splt))
    return false;

  if (htab->root.target_os == is_vxworks)
    {
      if (!setup_vxworks_plt_relocations(output_bfd, htab, splt))
        return false;
    }

  elf_section_data (splt->output_section)->this_hdr.sh_entsize = 4;
  return true;
}

static bool
install_plt_fields(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                   asection *sgotplt, asection *splt)
{
  unsigned int i;
  
  for (i = 0; i < ARRAY_SIZE (htab->plt_info->plt0_got_fields); i++)
    {
      if (htab->plt_info->plt0_got_fields[i] != MINUS_ONE)
        {
          install_plt_field (output_bfd, false,
                           (sgotplt->output_section->vma
                            + sgotplt->output_offset
                            + (i * 4)),
                           (splt->contents
                            + htab->plt_info->plt0_got_fields[i]));
        }
    }
  return true;
}

static bool
setup_vxworks_plt_relocations(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                              asection *splt)
{
  Elf_Internal_Rela rel;
  bfd_byte *loc;

  if (htab->srelplt2 == NULL)
    return false;

  loc = htab->srelplt2->contents;
  rel.r_offset = (splt->output_section->vma
                  + splt->output_offset
                  + htab->plt_info->plt0_got_fields[2]);
  rel.r_info = ELF32_R_INFO (htab->root.hgot->indx, R_SH_DIR32);
  rel.r_addend = 8;
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
  loc += sizeof (Elf32_External_Rela);

  while (loc < htab->srelplt2->contents + htab->srelplt2->size)
    {
      bfd_elf32_swap_reloc_in (output_bfd, loc, &rel);
      rel.r_info = ELF32_R_INFO (htab->root.hgot->indx, R_SH_DIR32);
      bfd_elf32_swap_reloc_out (output_bfd, &rel, loc);
      loc += sizeof (Elf32_External_Rela);

      bfd_elf32_swap_reloc_in (output_bfd, loc, &rel);
      rel.r_info = ELF32_R_INFO (htab->root.hplt->indx, R_SH_DIR32);
      bfd_elf32_swap_reloc_out (output_bfd, &rel, loc);
      loc += sizeof (Elf32_External_Rela);
    }
  return true;
}

static bool
setup_got_section(bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                 asection *sgotplt, asection *sdyn)
{
  if (sgotplt == NULL || sgotplt->size == 0 || htab->fdpic_p)
    {
      if (sgotplt && sgotplt->size > 0)
        elf_section_data (sgotplt->output_section)->this_hdr.sh_entsize = 4;
      return true;
    }

  if (sdyn == NULL)
    bfd_put_32 (output_bfd, (bfd_vma) 0, sgotplt->contents);
  else
    bfd_put_32 (output_bfd,
                sdyn->output_section->vma + sdyn->output_offset,
                sgotplt->contents);
  
  bfd_put_32 (output_bfd, (bfd_vma) 0, sgotplt->contents + 4);
  bfd_put_32 (output_bfd, (bfd_vma) 0, sgotplt->contents + 8);

  elf_section_data (sgotplt->output_section)->this_hdr.sh_entsize = 4;
  return true;
}

static bool
finalize_fdpic_sections(bfd *output_bfd, struct elf_sh_link_hash_table *htab)
{
  if (!htab->fdpic_p || htab->srofixup == NULL)
    return true;

  struct elf_link_hash_entry *hgot = htab->root.hgot;
  if (hgot == NULL)
    return false;

  bfd_vma got_value = hgot->root.u.def.value
    + hgot->root.u.def.section->output_section->vma
    + hgot->root.u.def.section->output_offset;

  sh_elf_add_rofixup (output_bfd, htab->srofixup, got_value);

  if (htab->srofixup->reloc_count * 4 != htab->srofixup->size)
    return false;

  return true;
}

static void
validate_relocation_sections(struct elf_sh_link_hash_table *htab)
{
  if (htab->srelfuncdesc)
    BFD_ASSERT (htab->srelfuncdesc->reloc_count * sizeof (Elf32_External_Rela)
                == htab->srelfuncdesc->size);

  if (htab->root.srelgot)
    BFD_ASSERT (htab->root.srelgot->reloc_count * sizeof (Elf32_External_Rela)
                == htab->root.srelgot->size);
}

static enum elf_reloc_type_class
sh_elf_reloc_type_class (const struct bfd_link_info *info ATTRIBUTE_UNUSED,
			 const asection *rel_sec ATTRIBUTE_UNUSED,
			 const Elf_Internal_Rela *rela)
{
  if (!rela) {
    return reloc_class_normal;
  }

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
  const int LINUX_SH_PRSTATUS_SIZE = 168;
  const int SIGNAL_OFFSET = 12;
  const int PID_OFFSET = 24;
  const int REG_OFFSET = 72;
  const int REG_SIZE = 92;

  if (!abfd || !note || !note->descdata)
    return false;

  if (note->descsz != LINUX_SH_PRSTATUS_SIZE)
    return false;

  if (!elf_tdata (abfd) || !elf_tdata (abfd)->core)
    return false;

  elf_tdata (abfd)->core->signal = bfd_get_16 (abfd, note->descdata + SIGNAL_OFFSET);
  elf_tdata (abfd)->core->lwpid = bfd_get_32 (abfd, note->descdata + PID_OFFSET);

  return _bfd_elfcore_make_pseudosection (abfd, ".reg", REG_SIZE, note->descpos + REG_OFFSET);
}

static bool
elf32_shlin_grok_psinfo (bfd *abfd, Elf_Internal_Note *note)
{
  if (note->descsz != 124) {
    return false;
  }

  if (!abfd || !note || !note->descdata) {
    return false;
  }

  if (!elf_tdata(abfd) || !elf_tdata(abfd)->core) {
    return false;
  }

  elf_tdata(abfd)->core->program = _bfd_elfcore_strndup(abfd, note->descdata + 28, 16);
  elf_tdata(abfd)->core->command = _bfd_elfcore_strndup(abfd, note->descdata + 44, 80);

  if (!elf_tdata(abfd)->core->program || !elf_tdata(abfd)->core->command) {
    return false;
  }

  char *command = elf_tdata(abfd)->core->command;
  int n = strlen(command);

  if (n > 0 && command[n - 1] == ' ') {
    command[n - 1] = '\0';
  }

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
  bfd_boolean is_dynamic;

  if (plt == NULL || plt->owner == NULL)
    return 0;

  is_dynamic = (plt->owner->flags & DYNAMIC) != 0;
  plt_info = get_plt_info (plt->owner, is_dynamic);
  
  if (plt_info == NULL)
    return 0;

  return plt->vma + get_plt_offset (plt_info, i);
}

/* Decide whether to attempt to turn absptr or lsda encodings in
   shared libraries into pcrel within the given input section.  */

static bool
sh_elf_use_relative_eh_frame (bfd *input_bfd ATTRIBUTE_UNUSED,
			      struct bfd_link_info *info,
			      asection *eh_frame_section ATTRIBUTE_UNUSED)
{
  struct elf_sh_link_hash_table *htab;

  if (info == NULL)
    return false;

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  if (htab->fdpic_p)
    return false;

  return true;
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

  if (!htab || !htab->fdpic_p)
    return _bfd_elf_encode_eh_address (abfd, info, osec, offset, loc_sec,
				       loc_offset, encoded);

  h = htab->root.hgot;
  if (!h || h->root.type != bfd_link_hash_defined)
    return _bfd_elf_encode_eh_address (abfd, info, osec, offset,
				       loc_sec, loc_offset, encoded);

  if (sh_elf_osec_to_segment (abfd, osec)
      == sh_elf_osec_to_segment (abfd, loc_sec->output_section))
    return _bfd_elf_encode_eh_address (abfd, info, osec, offset,
				       loc_sec, loc_offset, encoded);

  if (sh_elf_osec_to_segment (abfd, osec)
      != sh_elf_osec_to_segment (abfd, h->root.u.def.section->output_section))
    return _bfd_elf_encode_eh_address (abfd, info, osec, offset,
				       loc_sec, loc_offset, encoded);

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
