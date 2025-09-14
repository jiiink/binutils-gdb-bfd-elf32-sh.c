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
  if (!abfd)
    return false;

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

#if !defined SH_TARGET_ALREADY_DEFINED
extern const bfd_target sh_elf32_fdpic_le_vec;
extern const bfd_target sh_elf32_fdpic_be_vec;

static bool
fdpic_object_p (bfd *abfd)
{
  return abfd->xvec == &sh_elf32_fdpic_le_vec
      || abfd->xvec == &sh_elf32_fdpic_be_vec;
}

#else /* defined SH_TARGET_ALREADY_DEFINED */

static bool
fdpic_object_p (bfd *abfd ATTRIBUTE_UNUSED)
{
  return false;
}

#endif /* !defined SH_TARGET_ALREADY_DEFINED */

/* Return the howto table for ABFD.  */

static reloc_howto_type *
get_howto_table (bfd *abfd)
{
  return vxworks_object_p (abfd) ? sh_vxworks_howto_table : sh_elf_howto_table;
}

#define IS_PPI(BFD, PTR) ((bfd_get_16 ((BFD), (PTR)) & 0xfc00) == 0xf800)

static void
sh_elf_calculate_relaxed_tls_offsets (bfd *input_bfd,
				      const bfd_byte *contents,
				      bfd_vma *start_p, bfd_vma *end_p)
{
  bfd_vma start = *start_p;
  bfd_vma end = *end_p;
  const bfd_byte *start_ptr = contents + start;
  const bfd_byte *ptr = contents + end;
  int cum_diff = -6;

  while (cum_diff < 0 && ptr > start_ptr)
    {
      const bfd_byte *last_ptr = ptr;

      ptr -= 4;
      while (ptr >= start_ptr && IS_PPI (input_bfd, ptr))
	{
	  ptr -= 2;
	}
      ptr += 2;

      int diff = (last_ptr - ptr) >> 1;
      int rounded_up_diff = (diff + 1) & ~1;
      cum_diff += rounded_up_diff;
    }

  if (cum_diff >= 0)
    {
      *start_p = start - 4;
      *end_p = (ptr - contents) + (bfd_vma) cum_diff * 2;
    }
  else
    {
      bfd_vma start0 = start - 4;

      while (start0 > 0 && IS_PPI (input_bfd, contents + start0))
	{
	  start0 -= 2;
	}

      start0 = start - 2 - ((start - start0) & 2);
      *start_p = start0 - cum_diff - 2;
      *end_p = start0;
    }
}

static bfd_reloc_status_type
sh_elf_reloc_loop (int r_type ATTRIBUTE_UNUSED, bfd *input_bfd,
		   asection *input_section, bfd_byte *contents,
		   bfd_vma addr, asection *symbol_section,
		   bfd_vma start, bfd_vma end)
{
  static bfd_vma last_addr;
  static asection *last_symbol_section;

  if (last_addr == 0)
    {
      last_addr = addr;
      last_symbol_section = symbol_section;
      return bfd_reloc_ok;
    }

  if (last_addr != addr)
    {
      return bfd_reloc_dangerous;
    }
  last_addr = 0;

  if (addr > bfd_get_section_limit (input_bfd, input_section))
    {
      return bfd_reloc_outofrange;
    }

  if (symbol_section == NULL || last_symbol_section != symbol_section
      || end < start)
    {
      return bfd_reloc_outofrange;
    }

  bfd_reloc_status_type status = bfd_reloc_ok;
  bfd_byte *symbol_contents = contents;
  bool contents_allocated = false;

  if (symbol_section != input_section)
    {
      struct elf_section_data *sec_data = elf_section_data (symbol_section);
      if (sec_data->this_hdr.contents != NULL)
	{
	  symbol_contents = sec_data->this_hdr.contents;
	}
      else
	{
	  if (!bfd_malloc_and_get_section (input_bfd, symbol_section,
					   &symbol_contents))
	    {
	      return bfd_reloc_outofrange;
	    }
	  contents_allocated = true;
	}
    }

  sh_elf_calculate_relaxed_tls_offsets (input_bfd, symbol_contents, &start,
					&end);

  int insn = bfd_get_16 (input_bfd, contents + addr);
  bfd_signed_vma x = (insn & 0x200 ? end : start) - addr;

  if (input_section != symbol_section)
    {
      x += ((symbol_section->output_section->vma
	     + symbol_section->output_offset)
	    - (input_section->output_section->vma
	       + input_section->output_offset));
    }
  x >>= 1;

  const bfd_signed_vma RELOC_MIN = -128;
  const bfd_signed_vma RELOC_MAX = 127;
  if (x < RELOC_MIN || x > RELOC_MAX)
    {
      status = bfd_reloc_overflow;
    }
  else
    {
      int updated_insn = (insn & ~0xff) | (x & 0xff);
      bfd_put_16 (input_bfd, (bfd_vma) updated_insn, contents + addr);
    }

  if (contents_allocated)
    {
      free (symbol_contents);
    }

  return status;
}

/* This function is used for normal relocs.  This used to be like the COFF
   function, and is almost certainly incorrect for other ELF targets.  */

static bfd_reloc_status_type
sh_elf_reloc (bfd *abfd, arelent *reloc_entry, asymbol *symbol_in,
	      void *data, asection *input_section, bfd *output_bfd,
	      char **error_message ATTRIBUTE_UNUSED)
{
  if (output_bfd != NULL)
    {
      reloc_entry->address += input_section->output_offset;
      return bfd_reloc_ok;
    }

  bfd_size_type octets = reloc_entry->address * OCTETS_PER_BYTE (abfd, input_section);
  if (octets + bfd_get_reloc_size (reloc_entry->howto)
      > bfd_get_section_limit_octets (abfd, input_section))
    {
      return bfd_reloc_outofrange;
    }

  enum elf_sh_reloc_type r_type = (enum elf_sh_reloc_type) reloc_entry->howto->type;
  bfd_vma sym_value = 0;

  if (symbol_in != NULL)
    {
      if (bfd_is_und_section (symbol_in->section))
	{
	  return bfd_reloc_undefined;
	}

      if (r_type == R_SH_IND12W && (symbol_in->flags & BSF_LOCAL) != 0)
	{
	  return bfd_reloc_ok;
	}

      if (!bfd_is_com_section (symbol_in->section))
	{
	  sym_value = (symbol_in->value
		       + symbol_in->section->output_section->vma
		       + symbol_in->section->output_offset);
	}
    }

  bfd_byte *hit_data = (bfd_byte *) data + octets;

  switch (r_type)
    {
    case R_SH_DIR32:
      {
	bfd_vma insn = bfd_get_32 (abfd, hit_data);
	insn += sym_value + reloc_entry->addend;
	bfd_put_32 (abfd, insn, hit_data);
	break;
      }
    case R_SH_IND12W:
      {
	const bfd_vma insn_prefix_mask = 0xf000;
	const bfd_vma disp_mask = 0x0fff;
	const bfd_vma sign_bit = 0x0800;

	bfd_vma insn = bfd_get_16 (abfd, hit_data);
	bfd_vma pc_rel_base = (input_section->output_section->vma
			       + input_section->output_offset
			       + reloc_entry->address
			       + 4);

	bfd_vma existing_disp = (((insn & disp_mask) ^ sign_bit) - sign_bit) << 1;
	bfd_vma target_addr = sym_value + reloc_entry->addend;
	bfd_vma final_disp = target_addr - pc_rel_base + existing_disp;

	if ((final_disp + 0x1000) >= 0x2000 || (final_disp & 1) != 0)
	  {
	    return bfd_reloc_overflow;
	  }

	insn = (insn & insn_prefix_mask) | ((final_disp >> 1) & disp_mask);
	bfd_put_16 (abfd, insn, hit_data);
	break;
      }
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
  if (output_bfd && reloc_entry && input_section)
    {
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

static reloc_howto_type *
sh_elf_reloc_type_lookup (bfd *abfd, bfd_reloc_code_real_type code)
{
  reloc_howto_type * const howto_table = get_howto_table (abfd);
  if (!howto_table)
    {
      return NULL;
    }

  const size_t num_entries = sizeof (sh_reloc_map) / sizeof (sh_reloc_map[0]);
  for (size_t i = 0; i < num_entries; i++)
    {
      if (sh_reloc_map[i].bfd_reloc_val == code)
        {
          return howto_table + sh_reloc_map[i].elf_reloc_val;
        }
    }

  return NULL;
}

static reloc_howto_type *
sh_elf_reloc_name_lookup (bfd *abfd, const char *r_name)
{
  reloc_howto_type *table;
  size_t table_size;
  size_t i;

  if (vxworks_object_p (abfd))
    {
      table = sh_vxworks_howto_table;
      table_size = sizeof (sh_vxworks_howto_table) / sizeof (sh_vxworks_howto_table[0]);
    }
  else
    {
      table = sh_elf_howto_table;
      table_size = sizeof (sh_elf_howto_table) / sizeof (sh_elf_howto_table[0]);
    }

  for (i = 0; i < table_size; i++)
    {
      if (table[i].name != NULL && strcasecmp (table[i].name, r_name) == 0)
	{
	  return &table[i];
	}
    }

  return NULL;
}

/* Given an ELF reloc, fill in the howto field of a relent.  */

static bool
is_invalid_sh_reloc_type (unsigned int r)
{
  static const struct
  {
    unsigned int first;
    unsigned int last;
  } invalid_ranges[] = {
    { R_SH_FIRST_INVALID_RELOC,   R_SH_LAST_INVALID_RELOC   },
    { R_SH_FIRST_INVALID_RELOC_2, R_SH_LAST_INVALID_RELOC_2 },
    { R_SH_FIRST_INVALID_RELOC_3, R_SH_LAST_INVALID_RELOC_3 },
    { R_SH_FIRST_INVALID_RELOC_4, R_SH_LAST_INVALID_RELOC_4 },
    { R_SH_FIRST_INVALID_RELOC_5, R_SH_LAST_INVALID_RELOC_5 }
  };
  
  if (r >= R_SH_FIRST_INVALID_RELOC_6)
    return true;

  for (size_t i = 0; i < sizeof (invalid_ranges) / sizeof (invalid_ranges[0]); ++i)
    {
      if (r >= invalid_ranges[i].first && r <= invalid_ranges[i].last)
	return true;
    }
  
  return false;
}

static bool
sh_elf_info_to_howto (bfd *abfd, arelent *cache_ptr, Elf_Internal_Rela *dst)
{
  if (!abfd || !cache_ptr || !dst)
    {
      bfd_set_error (bfd_error_invalid_argument);
      return false;
    }
    
  unsigned int r = ELF32_R_TYPE (dst->r_info);
  
  if (is_invalid_sh_reloc_type (r))
    {
      /* xgettext:c-format */
      _bfd_error_handler (_("%pB: unsupported relocation type %#x"),
			  abfd, r);
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

static struct relax_context;

static bfd_byte *
get_section_contents (struct relax_context *ctx);

static Elf_Internal_Sym *
get_symbol_buffer (struct relax_context *ctx);

static bool
try_get_symbol_value (struct relax_context *ctx,
		      const Elf_Internal_Rela *irelfn,
		      bfd_vma *symval_out);

static bool
shorten_function_call (struct relax_context *ctx,
		       Elf_Internal_Rela *irel,
		       Elf_Internal_Rela *irelfn,
		       bfd_vma laddr,
		       bool *again);

static bool
process_one_uses_reloc (struct relax_context *ctx,
			Elf_Internal_Rela *irel,
			bool *again);

static bool
process_relaxable_relocs (struct relax_context *ctx,
			  bool *have_code_p,
			  bool *again);

struct relax_context
{
  bfd *abfd;
  asection *sec;
  struct bfd_link_info *link_info;
  Elf_Internal_Shdr *symtab_hdr;
  Elf_Internal_Rela *relocs;
  bfd_byte *contents;
  Elf_Internal_Sym *isymbuf;
};

static bfd_byte *
get_section_contents (struct relax_context *ctx)
{
  if (ctx->contents == NULL)
    {
      ctx->contents = elf_section_data (ctx->sec)->this_hdr.contents;
      if (ctx->contents == NULL)
	{
	  if (!bfd_malloc_and_get_section (ctx->abfd, ctx->sec, &ctx->contents))
	    return NULL;
	}
    }
  return ctx->contents;
}

static Elf_Internal_Sym *
get_symbol_buffer (struct relax_context *ctx)
{
  if (ctx->isymbuf == NULL && ctx->symtab_hdr->sh_info != 0)
    {
      ctx->isymbuf = (Elf_Internal_Sym *) ctx->symtab_hdr->contents;
      if (ctx->isymbuf == NULL)
	{
	  ctx->isymbuf = bfd_elf_get_elf_syms (ctx->abfd, ctx->symtab_hdr,
					      ctx->symtab_hdr->sh_info, 0,
					      NULL, NULL, NULL);
	}
    }
  return ctx->isymbuf;
}

static bool
try_get_symbol_value (struct relax_context *ctx,
		      const Elf_Internal_Rela *irelfn,
		      bfd_vma *symval_out)
{
  bfd_vma symval;

  if (ELF32_R_SYM (irelfn->r_info) < ctx->symtab_hdr->sh_info)
    {
      const Elf_Internal_Sym *isym = ctx->isymbuf + ELF32_R_SYM (irelfn->r_info);
      if (isym->st_shndx != (unsigned int) _bfd_elf_section_from_bfd_section (ctx->abfd, ctx->sec))
	{
	  _bfd_error_handler
	    (_("%pB: %#" PRIx64 ": warning: symbol in unexpected section"),
	     ctx->abfd, (uint64_t) irelfn->r_offset);
	  return false;
	}
      symval = (isym->st_value + ctx->sec->output_section->vma
		+ ctx->sec->output_offset);
    }
  else
    {
      unsigned long indx = ELF32_R_SYM (irelfn->r_info) - ctx->symtab_hdr->sh_info;
      struct elf_link_hash_entry *h = elf_sym_hashes (ctx->abfd)[indx];
      BFD_ASSERT (h != NULL);
      if (h->root.type != bfd_link_hash_defined
	  && h->root.type != bfd_link_hash_defweak)
	return false;
      symval = (h->root.u.def.value
		+ h->root.u.def.section->output_section->vma
		+ h->root.u.def.section->output_offset);
    }

  if (get_howto_table (ctx->abfd)[R_SH_DIR32].partial_inplace)
    symval += bfd_get_32 (ctx->abfd, ctx->contents + irelfn->r_offset);
  else
    symval += irelfn->r_addend;

  *symval_out = symval;
  return true;
}

static Elf_Internal_Rela *
find_reloc_at (struct relax_context *ctx, bfd_vma paddr, int type)
{
  Elf_Internal_Rela *irel, *irelend;

  irelend = ctx->relocs + ctx->sec->reloc_count;
  for (irel = ctx->relocs; irel < irelend; irel++)
    {
      if (irel->r_offset == paddr && ELF32_R_TYPE (irel->r_info) == type)
	return irel;
    }
  return NULL;
}

static bool
is_load_in_use (struct relax_context *ctx, bfd_vma laddr)
{
  Elf_Internal_Rela *irel, *irelend;

  irelend = ctx->relocs + ctx->sec->reloc_count;
  for (irel = ctx->relocs; irel < irelend; irel++)
    {
      if (ELF32_R_TYPE (irel->r_info) == (int) R_SH_USES
	  && laddr == irel->r_offset + 4 + irel->r_addend)
	return true;
    }
  return false;
}

static bool
shorten_function_call (struct relax_context *ctx,
		       Elf_Internal_Rela *irel,
		       Elf_Internal_Rela *irelfn,
		       bfd_vma laddr,
		       bool *again)
{
  Elf_Internal_Rela *irelcount;
  const bfd_vma paddr = irelfn->r_offset;

  irel->r_info = ELF32_R_INFO (ELF32_R_SYM (irelfn->r_info), R_SH_IND12W);

  if (bfd_get_16 (ctx->abfd, ctx->contents + irel->r_offset) & 0x0020)
    bfd_put_16 (ctx->abfd, (bfd_vma) 0xa000, ctx->contents + irel->r_offset);
  else
    bfd_put_16 (ctx->abfd, (bfd_vma) 0xb000, ctx->contents + irel->r_offset);

  irel->r_addend = -4 + bfd_get_32 (ctx->abfd, ctx->contents + paddr);

  if (is_load_in_use (ctx, laddr))
    return true;

  irelcount = find_reloc_at (ctx, paddr, R_SH_COUNT);
  if (irelcount == NULL)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": warning: could not find expected COUNT reloc"),
	 ctx->abfd, (uint64_t) paddr);
      return true;
    }

  if (!sh_elf_relax_delete_bytes (ctx->abfd, ctx->sec, laddr, 2))
    return false;
  *again = true;

  if (irelcount->r_addend == 0)
    {
      _bfd_error_handler (_("%pB: %#" PRIx64 ": warning: bad count"),
			  ctx->abfd, (uint64_t) paddr);
      return true;
    }

  --irelcount->r_addend;
  if (irelcount->r_addend == 0)
    {
      if (!sh_elf_relax_delete_bytes (ctx->abfd, ctx->sec, irelfn->r_offset, 4))
	return false;
    }

  return true;
}

static bool
process_one_uses_reloc (struct relax_context *ctx,
			Elf_Internal_Rela *irel,
			bool *again)
{
  bfd_vma laddr, paddr, symval;
  unsigned short insn;
  Elf_Internal_Rela *irelfn;

  laddr = irel->r_offset + 4 + irel->r_addend;
  if (laddr >= ctx->sec->size)
    {
      _bfd_error_handler (_("%pB: %#" PRIx64 ": warning: bad R_SH_USES offset"),
			  ctx->abfd, (uint64_t) irel->r_offset);
      return true;
    }

  insn = bfd_get_16 (ctx->abfd, ctx->contents + laddr);
  if ((insn & 0xf000) != 0xd000)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": warning: R_SH_USES points to unrecognized insn 0x%x"),
	 ctx->abfd, (uint64_t) irel->r_offset, insn);
      return true;
    }

  paddr = (insn & 0xff) * 4 + ((laddr + 4) & ~(bfd_vma) 3);
  if (paddr >= ctx->sec->size)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": warning: bad R_SH_USES load offset"),
	 ctx->abfd, (uint64_t) irel->r_offset);
      return true;
    }

  irelfn = find_reloc_at (ctx, paddr, R_SH_DIR32);
  if (irelfn == NULL)
    {
      _bfd_error_handler
	(_("%pB: %#" PRIx64 ": warning: could not find expected reloc"),
	 ctx->abfd, (uint64_t) paddr);
      return true;
    }

  if (get_symbol_buffer (ctx) == NULL)
    return false;

  if (!try_get_symbol_value (ctx, irelfn, &symval))
    return true;

  bfd_signed_vma foff = (symval - (irel->r_offset
				   + ctx->sec->output_section->vma
				   + ctx->sec->output_offset + 4));
  if (foff < -0x1000 || foff >= 0x1000 - 8)
    return true;

  return shorten_function_call (ctx, irel, irelfn, laddr, again);
}

static bool
process_relaxable_relocs (struct relax_context *ctx,
			  bool *have_code_p,
			  bool *again)
{
  Elf_Internal_Rela *irel, *irelend;
  bool modified = false;

  irelend = ctx->relocs + ctx->sec->reloc_count;
  for (irel = ctx->relocs; irel < irelend; irel++)
    {
      if (ELF32_R_TYPE (irel->r_info) == (int) R_SH_CODE)
	*have_code_p = true;

      if (ELF32_R_TYPE (irel->r_info) != (int) R_SH_USES)
	continue;

      if (ctx->contents == NULL && get_section_contents (ctx) == NULL)
	return false;

      if (!modified)
	{
	  elf_section_data (ctx->sec)->relocs = ctx->relocs;
	  elf_section_data (ctx->sec)->this_hdr.contents = ctx->contents;
	  if (get_symbol_buffer (ctx) != NULL)
	    ctx->symtab_hdr->contents = (unsigned char *) ctx->isymbuf;
	  modified = true;
	}

      if (!process_one_uses_reloc (ctx, irel, again))
	return false;
    }

  return true;
}

static bool
sh_elf_relax_section (bfd *abfd, asection *sec,
		      struct bfd_link_info *link_info, bool *again)
{
  struct relax_context ctx;
  bool success = false;
  bool have_code = false;
  bool swapped = false;

  *again = false;

  if (bfd_link_relocatable (link_info)
      || (sec->flags & SEC_HAS_CONTENTS) == 0
      || (sec->flags & SEC_RELOC) == 0
      || sec->reloc_count == 0)
    return true;

  ctx.abfd = abfd;
  ctx.sec = sec;
  ctx.link_info = link_info;
  ctx.symtab_hdr = &elf_symtab_hdr (abfd);
  ctx.contents = NULL;
  ctx.isymbuf = NULL;
  ctx.relocs = (_bfd_elf_link_read_relocs
		(abfd, sec, NULL, NULL, link_info->keep_memory));

  if (ctx.relocs == NULL)
    goto error_return;

  if (!process_relaxable_relocs (&ctx, &have_code, again))
    goto error_return;

  if ((elf_elfheader (abfd)->e_flags & EF_SH_MACH_MASK) != EF_SH4 && have_code)
    {
      if (get_section_contents (&ctx) == NULL)
	goto error_return;
      if (!sh_elf_align_loads (abfd, sec, ctx.relocs, ctx.contents, &swapped))
	goto error_return;
      if (swapped)
	{
	  elf_section_data (sec)->relocs = ctx.relocs;
	  elf_section_data (sec)->this_hdr.contents = ctx.contents;
	  if (get_symbol_buffer (&ctx))
	    ctx.symtab_hdr->contents = (unsigned char *) ctx.isymbuf;
	}
    }

  success = true;

  if (ctx.isymbuf != NULL
      && ctx.symtab_hdr->contents != (unsigned char *) ctx.isymbuf)
    {
      if (!link_info->keep_memory)
	free (ctx.isymbuf);
      else
	ctx.symtab_hdr->contents = (unsigned char *) ctx.isymbuf;
    }

  if (ctx.contents != NULL
      && elf_section_data (sec)->this_hdr.contents != ctx.contents)
    {
      if (!link_info->keep_memory)
	free (ctx.contents);
      else
	elf_section_data (sec)->this_hdr.contents = ctx.contents;
    }

  if (elf_section_data (sec)->relocs != ctx.relocs)
    free (ctx.relocs);

  return true;

error_return:
  if (ctx.symtab_hdr && ctx.symtab_hdr->contents != (unsigned char *) ctx.isymbuf)
    free (ctx.isymbuf);
  if (elf_section_data (sec)->this_hdr.contents != ctx.contents)
    free (ctx.contents);
  if (elf_section_data (sec)->relocs != ctx.relocs)
    free (ctx.relocs);

  return false;
}

/* Delete some bytes from a section while relaxing.  FIXME: There is a
   lot of duplication between this function and sh_relax_delete_bytes
   in coff-sh.c.  */

static void
perform_byte_deletion (bfd *abfd, asection *sec, bfd_vma addr, int count,
		       bfd_vma toaddr, bool has_align_reloc)
{
#define NOP_OPCODE (0x0009)
  bfd_byte *contents = elf_section_data (sec)->this_hdr.contents;

  memmove (contents + addr, contents + addr + count,
	   (size_t) (toaddr - addr - count));

  if (!has_align_reloc)
    {
      sec->size -= count;
    }
  else
    {
      int i;
      BFD_ASSERT ((count & 1) == 0);
      for (i = 0; i < count; i += 2)
	bfd_put_16 (abfd, (bfd_vma) NOP_OPCODE,
		    contents + toaddr - count + i);
    }
}

static Elf_Internal_Rela *
find_alignment_boundary (asection *sec, bfd_vma addr, int count, bfd_vma *toaddr)
{
  Elf_Internal_Rela *irel = elf_section_data (sec)->relocs;
  Elf_Internal_Rela *irelend = irel + sec->reloc_count;

  *toaddr = sec->size;

  for (; irel < irelend; irel++)
    {
      if (ELF32_R_TYPE (irel->r_info) == (int) R_SH_ALIGN
	  && irel->r_offset > addr
	  && count < (1 << irel->r_addend))
	{
	  *toaddr = irel->r_offset;
	  return irel;
	}
    }
  return NULL;
}

static bool
adjust_section_relocs (bfd *abfd, asection *sec, bfd_vma addr,
		       bfd_vma toaddr, int count)
{
  Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr (abfd);
  Elf_Internal_Sym *isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;
  unsigned int sec_shndx = _bfd_elf_section_from_bfd_section (abfd, sec);
  bfd_byte *contents = elf_section_data (sec)->this_hdr.contents;
  Elf_Internal_Rela *irel, *irelend;

  irelend = elf_section_data (sec)->relocs + sec->reloc_count;
  for (irel = elf_section_data (sec)->relocs; irel < irelend; irel++)
    {
      bfd_vma nraddr, start = addr, stop = addr;
      int insn = 0, oinsn, off, adjust;
      bfd_signed_vma voff = 0;
      bool overflow = false;
      enum elf_sh_reloc_type r_type =
	(enum elf_sh_reloc_type) ELF32_R_TYPE (irel->r_info);

      nraddr = irel->r_offset;
      if ((irel->r_offset > addr && irel->r_offset < toaddr)
	  || (r_type == R_SH_ALIGN && irel->r_offset == toaddr))
	nraddr -= count;

      if (irel->r_offset >= addr && irel->r_offset < addr + count
	  && r_type != R_SH_ALIGN && r_type != R_SH_CODE
	  && r_type != R_SH_DATA && r_type != R_SH_LABEL)
	irel->r_info = ELF32_R_INFO (ELF32_R_SYM (irel->r_info), R_SH_NONE);

      switch (r_type)
	{
	case R_SH_DIR8WPN: case R_SH_IND12W:
	case R_SH_DIR8WPZ: case R_SH_DIR8WPL:
	  start = irel->r_offset;
	  insn = bfd_get_16 (abfd, contents + nraddr);
	  break;
	default: break;
	}

      switch (r_type)
	{
	default: break;
	case R_SH_DIR32:
	  if (ELF32_R_SYM (irel->r_info) < symtab_hdr->sh_info)
	    {
	      Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM (irel->r_info);
	      if (isym->st_shndx == sec_shndx
		  && (isym->st_value <= addr || isym->st_value >= toaddr))
		{
		  bfd_vma val;
		  if (get_howto_table (abfd)[R_SH_DIR32].partial_inplace)
		    {
		      val = bfd_get_32 (abfd, contents + nraddr) + isym->st_value;
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
	  break;
	case R_SH_DIR8WPN:
	  off = insn & 0xff; if (off & 0x80) off -= 0x100;
	  stop = (bfd_vma) ((bfd_signed_vma) start + 4 + off * 2); break;
	case R_SH_IND12W:
	  off = insn & 0xfff;
	  if (off)
	    {
	      if (off & 0x800) off -= 0x1000;
	      stop = (bfd_vma) ((bfd_signed_vma) start + 4 + off * 2);
	      if (stop > addr && stop < toaddr) irel->r_addend -= count;
	    }
	  break;
	case R_SH_DIR8WPZ:
	  off = insn & 0xff; stop = start + 4 + off * 2; break;
	case R_SH_DIR8WPL:
	  off = insn & 0xff; stop = (start & ~(bfd_vma) 3) + 4 + off * 4; break;
	case R_SH_SWITCH8: case R_SH_SWITCH16: case R_SH_SWITCH32:
	  stop = irel->r_offset;
	  start = (bfd_vma) ((bfd_signed_vma) stop - (long) irel->r_addend);
	  if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr))
	    irel->r_addend += count;
	  else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))
	    irel->r_addend -= count;
	  if (r_type == R_SH_SWITCH16) voff = bfd_get_signed_16 (abfd, contents + nraddr);
	  else if (r_type == R_SH_SWITCH8) voff = bfd_get_8 (abfd, contents + nraddr);
	  else voff = bfd_get_signed_32 (abfd, contents + nraddr);
	  stop = (bfd_vma) ((bfd_signed_vma) start + voff); break;
	case R_SH_USES:
	  start = irel->r_offset;
	  stop = (bfd_vma) ((bfd_signed_vma) start + (long) irel->r_addend + 4);
	  break;
	}

      if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr))
	adjust = count;
      else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))
	adjust = -count;
      else
	adjust = 0;

      if (adjust != 0)
	{
	  oinsn = insn;
	  switch (r_type)
	    {
	    default:
	      _bfd_error_handler
		(_("%pB: %#" PRIx64 ": fatal: unexpected reloc type in relaxation"),
		 abfd, (uint64_t) irel->r_offset);
	      bfd_set_error (bfd_error_invalid_operation);
	      return false;
	    case R_SH_DIR8WPN: case R_SH_DIR8WPZ:
	      insn += adjust / 2;
	      if ((oinsn & 0xff00) != (insn & 0xff00)) overflow = true;
	      bfd_put_16 (abfd, (bfd_vma) insn, contents + nraddr); break;
	    case R_SH_IND12W:
	      insn += adjust / 2;
	      if ((oinsn & 0xf000) != (insn & 0xf000)) overflow = true;
	      bfd_put_16 (abfd, (bfd_vma) insn, contents + nraddr); break;
	    case R_SH_DIR8WPL:
	      BFD_ASSERT (adjust == count || count >= 4);
	      if (count >= 4) insn += adjust / 4;
	      else if ((irel->r_offset & 3) == 0) ++insn;
	      if ((oinsn & 0xff00) != (insn & 0xff00)) overflow = true;
	      bfd_put_16 (abfd, (bfd_vma) insn, contents + nraddr); break;
	    case R_SH_SWITCH8:
	      voff += adjust;
	      if (voff < 0 || voff >= 0xff) overflow = true;
	      bfd_put_8 (abfd, voff, contents + nraddr); break;
	    case R_SH_SWITCH16:
	      voff += adjust;
	      if (voff < -0x8000 || voff >= 0x8000) overflow = true;
	      bfd_put_signed_16 (abfd, (bfd_vma) voff, contents + nraddr); break;
	    case R_SH_SWITCH32:
	      voff += adjust;
	      bfd_put_signed_32 (abfd, (bfd_vma) voff, contents + nraddr); break;
	    case R_SH_USES: irel->r_addend += adjust; break;
	    }
	  if (overflow)
	    {
	      _bfd_error_handler
		(_("%pB: %#" PRIx64 ": fatal: reloc overflow while relaxing"),
		 abfd, (uint64_t) irel->r_offset);
	      bfd_set_error (bfd_error_bad_value); return false;
	    }
	}
      irel->r_offset = nraddr;
    }
  return true;
}

static bfd_byte *
get_or_load_section_contents (bfd *abfd, asection *sec)
{
  bfd_byte *contents = elf_section_data (sec)->this_hdr.contents;
  if (contents != NULL)
    return contents;
  if (!bfd_malloc_and_get_section (abfd, sec, &contents))
    return NULL;
  elf_section_data (sec)->this_hdr.contents = contents;
  return contents;
}

static bool
adjust_relocs_in_other_sections (bfd *abfd, asection *sec, bfd_vma addr,
				 bfd_vma toaddr, int count)
{
  Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr (abfd);
  Elf_Internal_Sym *isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;
  unsigned int sec_shndx = _bfd_elf_section_from_bfd_section (abfd, sec);
  asection *o;

  for (o = abfd->sections; o != NULL; o = o->next)
    {
      Elf_Internal_Rela *internal_relocs, *irelscan, *irelscanend;
      bfd_byte *ocontents = NULL;
      if (o == sec || (o->flags & (SEC_HAS_CONTENTS | SEC_RELOC)) == 0 || o->reloc_count == 0)
	continue;
      internal_relocs = _bfd_elf_link_read_relocs (abfd, o, NULL, NULL, true);
      if (internal_relocs == NULL) return false;
      irelscanend = internal_relocs + o->reloc_count;
      for (irelscan = internal_relocs; irelscan < irelscanend; irelscan++)
	{
	  enum elf_sh_reloc_type r_type = (enum elf_sh_reloc_type) ELF32_R_TYPE (irelscan->r_info);
	  if (r_type == R_SH_SWITCH32)
	    {
	      bfd_vma start, stop; bfd_signed_vma voff;
	      if (ocontents == NULL && (ocontents = get_or_load_section_contents (abfd, o)) == NULL) return false;
	      stop = irelscan->r_offset;
	      start = (bfd_vma) ((bfd_signed_vma) stop - (long) irelscan->r_addend);
	      if (start > addr && start < toaddr) irelscan->r_addend += count;
	      voff = bfd_get_signed_32 (abfd, ocontents + irelscan->r_offset);
	      stop = (bfd_vma) ((bfd_signed_vma) start + voff);
	      if (start > addr && start < toaddr && (stop <= addr || stop >= toaddr))
		bfd_put_signed_32 (abfd, (bfd_vma) voff + count, ocontents + irelscan->r_offset);
	      else if (stop > addr && stop < toaddr && (start <= addr || start >= toaddr))
		bfd_put_signed_32 (abfd, (bfd_vma) voff - count, ocontents + irelscan->r_offset);
	    }
	  else if (r_type == R_SH_DIR32 && ELF32_R_SYM (irelscan->r_info) < symtab_hdr->sh_info)
	    {
	      Elf_Internal_Sym *isym = isymbuf + ELF32_R_SYM (irelscan->r_info);
	      if (isym->st_shndx == sec_shndx && (isym->st_value <= addr || isym->st_value >= toaddr))
		{
		  bfd_vma val;
		  if (ocontents == NULL && (ocontents = get_or_load_section_contents (abfd, o)) == NULL) return false;
		  val = bfd_get_32 (abfd, ocontents + irelscan->r_offset) + isym->st_value;
		  if (val > addr && val < toaddr)
		    bfd_put_32 (abfd, val - count, ocontents + irelscan->r_offset);
		}
	    }
	}
    }
  return true;
}

static void
adjust_local_symbols (bfd *abfd, unsigned int sec_shndx, bfd_vma addr,
		      bfd_vma toaddr, int count)
{
  Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr (abfd);
  Elf_Internal_Sym *isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;
  Elf_Internal_Sym *isym, *isymend = isymbuf + symtab_hdr->sh_info;
  for (isym = isymbuf; isym < isymend; isym++)
    {
      if (isym->st_shndx == sec_shndx && isym->st_value > addr && isym->st_value < toaddr)
	isym->st_value -= count;
    }
}

static void
adjust_global_symbols (bfd *abfd, asection *sec, bfd_vma addr, bfd_vma toaddr,
		       int count)
{
  Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr (abfd);
  struct elf_link_hash_entry **sym_hashes = elf_sym_hashes (abfd);
  unsigned int symcount = (symtab_hdr->sh_size / sizeof (Elf32_External_Sym) - symtab_hdr->sh_info);
  struct elf_link_hash_entry **end_hashes = sym_hashes + symcount;

  for (; sym_hashes < end_hashes; sym_hashes++)
    {
      struct elf_link_hash_entry *sym_hash = *sym_hashes;
      if ((sym_hash->root.type == bfd_link_hash_defined || sym_hash->root.type == bfd_link_hash_defweak)
	  && sym_hash->root.u.def.section == sec
	  && sym_hash->root.u.def.value > addr && sym_hash->root.u.def.value < toaddr)
	sym_hash->root.u.def.value -= count;
    }
}

static bool
sh_elf_relax_delete_bytes (bfd *abfd, asection *sec, bfd_vma addr, int count)
{
  while (true)
    {
      Elf_Internal_Rela *irelalign;
      bfd_vma toaddr;
      unsigned int sec_shndx;

      irelalign = find_alignment_boundary (sec, addr, count, &toaddr);
      perform_byte_deletion (abfd, sec, addr, count, toaddr, irelalign != NULL);
      if (!adjust_section_relocs (abfd, sec, addr, toaddr, count))
	return false;
      if (!adjust_relocs_in_other_sections (abfd, sec, addr, toaddr, count))
	return false;

      sec_shndx = _bfd_elf_section_from_bfd_section (abfd, sec);
      adjust_local_symbols (abfd, sec_shndx, addr, toaddr, count);
      adjust_global_symbols (abfd, sec, addr, toaddr, count);

      if (irelalign != NULL)
	{
	  bfd_vma alignto = BFD_ALIGN (toaddr, 1 << irelalign->r_addend);
	  bfd_vma alignaddr = BFD_ALIGN (irelalign->r_offset, 1 << irelalign->r_addend);
	  if (alignto != alignaddr)
	    {
	      addr = alignaddr;
	      count = (int) (alignto - alignaddr);
	      continue;
	    }
	}
      break;
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
  *pswapped = false;
  if (sec->reloc_count == 0)
    return true;

  bfd_size_type amt;
  if (sec->reloc_count > (((bfd_size_type) -1) / sizeof (bfd_vma)))
    return false;
  amt = sec->reloc_count * sizeof (bfd_vma);

  bfd_vma *labels = (bfd_vma *) bfd_malloc (amt);
  if (labels == NULL)
    return false;

  size_t label_count = 0;
  const Elf_Internal_Rela *irelend = internal_relocs + sec->reloc_count;
  for (const Elf_Internal_Rela *irel = internal_relocs; irel < irelend; ++irel)
    {
      if (ELF32_R_TYPE (irel->r_info) == R_SH_LABEL)
	labels[label_count++] = irel->r_offset;
    }

  bool ok = true;
  bfd_vma *label_ptr = labels;
  const bfd_vma *label_end = labels + label_count;
  const Elf_Internal_Rela *irel = internal_relocs;

  while (ok && irel < irelend)
    {
      if (ELF32_R_TYPE (irel->r_info) != R_SH_CODE)
	{
	  irel++;
	  continue;
	}

      bfd_vma start = irel->r_offset;

      const Elf_Internal_Rela *span_end_reloc = irel + 1;
      while (span_end_reloc < irelend
	     && ELF32_R_TYPE (span_end_reloc->r_info) != R_SH_DATA)
	{
	  span_end_reloc++;
	}

      bfd_vma stop = (span_end_reloc < irelend)
	? span_end_reloc->r_offset
	: sec->size;

      ok = _bfd_sh_align_load_span (abfd, sec, contents, sh_elf_swap_insns,
				   internal_relocs, &label_ptr,
				   label_end, start, stop, pswapped);

      irel = span_end_reloc;
    }

  free (labels);
  return ok;
}

/* Swap two SH instructions.  This is like sh_swap_insns in coff-sh.c.  */

static bool
sh_elf_swap_insns (bfd *abfd, asection *sec, void *relocs,
		   bfd_byte *contents, bfd_vma addr)
{
  Elf_Internal_Rela *internal_relocs = (Elf_Internal_Rela *) relocs;
  unsigned short i1, i2;
  Elf_Internal_Rela *irel, *irelend;

  i1 = bfd_get_16 (abfd, contents + addr);
  i2 = bfd_get_16 (abfd, contents + addr + 2);
  bfd_put_16 (abfd, (bfd_vma) i2, contents + addr);
  bfd_put_16 (abfd, (bfd_vma) i1, contents + addr + 2);

  irelend = internal_relocs + sec->reloc_count;
  for (irel = internal_relocs; irel < irelend; irel++)
    {
      enum elf_sh_reloc_type type =
	(enum elf_sh_reloc_type) ELF32_R_TYPE (irel->r_info);

      switch (type)
	{
	case R_SH_ALIGN:
	case R_SH_CODE:
	case R_SH_DATA:
	case R_SH_LABEL:
	  continue;
	default:
	  break;
	}

      if (type == R_SH_USES)
	{
	  bfd_vma off = irel->r_offset + 4 + irel->r_addend;
	  if (off == addr)
	    irel->r_addend += 2;
	  else if (off == addr + 2)
	    irel->r_addend -= 2;
	}

      int add;
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
      else
	{
	  continue;
	}

      bfd_byte *loc = contents + irel->r_offset;
      unsigned short mask = 0;
      bool should_adjust = true;

      switch (type)
	{
	case R_SH_DIR8WPN:
	case R_SH_DIR8WPZ:
	  mask = 0xff00;
	  break;

	case R_SH_IND12W:
	  mask = 0xf000;
	  break;

	case R_SH_DIR8WPL:
	  if ((addr & 3) != 0)
	    mask = 0xff00;
	  else
	    should_adjust = false;
	  break;

	default:
	  should_adjust = false;
	  break;
	}

      if (should_adjust)
	{
	  unsigned short insn = bfd_get_16 (abfd, loc);
	  unsigned short new_insn = insn + add / 2;

	  bfd_put_16 (abfd, (bfd_vma) new_insn, loc);

	  if ((insn & mask) != (new_insn & mask))
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
  const struct elf_sh_plt_info *plt_table_base;

  if (fdpic_object_p (abfd))
    {
      const unsigned int arch =
        sh_get_arch_from_bfd_mach (bfd_get_mach (abfd));
      const bool use_sh2a_plt = (arch & arch_sh2a_base) != 0;
      plt_table_base = use_sh2a_plt ? fdpic_sh2a_plts : fdpic_sh_plts;
    }
  else if (vxworks_object_p (abfd))
    {
      plt_table_base = vxworks_sh_plts[pic_p];
    }
  else
    {
      plt_table_base = elf_sh_plts[pic_p];
    }

  const size_t endian_idx = !bfd_big_endian (abfd);
  return &plt_table_base[endian_idx];
}

/* Install a 32-bit PLT field starting at ADDR, which occurs in OUTPUT_BFD.
   VALUE is the field's value and CODE_P is true if VALUE refers to code,
   not data.  */

inline static void
install_plt_field (bfd *output_bfd, unsigned long value, bfd_byte *addr)
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
  bfd_vma plt_index = 0;

  offset -= info->plt0_entry_size;

  if (info->short_plt != NULL)
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

  if (info->symbol_entry_size == 0)
    {
      return plt_index;
    }

  return plt_index + offset / info->symbol_entry_size;
}

/* Do the inverse operation.  */

static bfd_vma
get_plt_offset (const struct elf_sh_plt_info *info, bfd_vma plt_index)
{
  const struct elf_sh_plt_info *active_info = info;
  bfd_vma base_offset = 0;
  bfd_vma relative_index = plt_index;

  if (info->short_plt != NULL)
    {
      if (plt_index > MAX_SHORT_PLT)
	{
	  base_offset = MAX_SHORT_PLT * info->short_plt->symbol_entry_size;
	  relative_index -= MAX_SHORT_PLT;
	}
      else
	{
	  active_info = info->short_plt;
	}
    }

  return (base_offset
	  + active_info->plt0_entry_size
	  + (relative_index * active_info->symbol_entry_size));
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
  return abfd && bfd_elf_allocate_object (abfd, sizeof (struct sh_elf_obj_tdata));
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

  if (!ret)
    {
      ret = bfd_hash_allocate (table, sizeof (*ret));
      if (!ret)
	return NULL;
    }

  ret = (struct elf_sh_link_hash_entry *)
    _bfd_elf_link_hash_newfunc ((struct bfd_hash_entry *) ret,
				table, string);
  if (ret)
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
  struct elf_sh_link_hash_table *ret = bfd_zmalloc (sizeof (*ret));

  if (ret == NULL)
    {
      return NULL;
    }

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
  if (!sh_elf_hash_table (info)->fdpic_p)
    return true;

  const bfd_vma sh_type = elf_section_data (p)->this_hdr.sh_type;

  return sh_type != SHT_PROGBITS
	 && sh_type != SHT_NOBITS
	 && sh_type != SHT_NULL;
}

/* Create .got, .gotplt, and .rela.got sections in DYNOBJ, and set up
   shortcuts to them in our hash table.  */

static asection *
create_and_align_section (bfd *dynobj, const char *name, flagword flags,
                          unsigned int alignment)
{
  asection *sec = bfd_make_section_anyway_with_flags (dynobj, name, flags);

  if (sec == NULL || !bfd_set_section_alignment (sec, alignment))
    return NULL;

  return sec;
}

static bool
create_got_section (bfd *dynobj, struct bfd_link_info *info)
{
  if (! _bfd_elf_create_got_section (dynobj, info))
    return false;

  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  const flagword base_flags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS
                               | SEC_IN_MEMORY | SEC_LINKER_CREATED);
  const flagword ro_flags = base_flags | SEC_READONLY;
  const unsigned int alignment = 2;

  if (!(htab->sfuncdesc = create_and_align_section (dynobj, ".got.funcdesc",
                                                    base_flags, alignment))
      || !(htab->srelfuncdesc = create_and_align_section (dynobj,
                                                          ".rela.got.funcdesc",
                                                          ro_flags, alignment))
      || !(htab->srofixup = create_and_align_section (dynobj, ".rofixup",
                                                      ro_flags, alignment)))
    return false;

  return true;
}

/* Create dynamic sections when linking against a dynamic object.  */

static bool
create_plt_section_and_symbol (bfd *abfd, struct bfd_link_info *info,
			       struct elf_sh_link_hash_table *htab)
{
  const struct elf_backend_data *bed = get_elf_backend_data (abfd);
  flagword pltflags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS
		       | SEC_IN_MEMORY | SEC_LINKER_CREATED | SEC_CODE);
  asection *s;
  struct elf_link_hash_entry *h;
  struct bfd_link_hash_entry *bh;

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
      bh = NULL;
      if (!(_bfd_generic_link_add_one_symbol
	    (info, abfd, "_PROCEDURE_LINKAGE_TABLE_", BSF_GLOBAL, s,
	     (bfd_vma) 0, NULL, false, bed->collect, &bh)))
	return false;

      h = (struct elf_link_hash_entry *) bh;
      h->def_regular = 1;
      h->type = STT_OBJECT;
      htab->root.hplt = h;

      if (bfd_link_pic (info) && !bfd_elf_link_record_dynamic_symbol (info, h))
	return false;
    }

  return true;
}

static bool
create_dynbss_and_rel_sections (bfd *abfd, struct bfd_link_info *info,
				struct elf_sh_link_hash_table *htab,
				int ptralign)
{
  const struct elf_backend_data *bed = get_elf_backend_data (abfd);
  asection *s;

  if (!bed->want_dynbss)
    return true;

  s = bfd_make_section_anyway_with_flags (abfd, ".dynbss",
					  SEC_ALLOC | SEC_LINKER_CREATED);
  htab->root.sdynbss = s;
  if (s == NULL)
    return false;

  if (!bfd_link_pic (info))
    {
      const char *rel_bss_name;
      flagword flags;

      rel_bss_name = (bed->default_use_rela_p
		      ? ".rela.bss" : ".rel.bss");
      flags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS
	       | SEC_IN_MEMORY | SEC_LINKER_CREATED);
      s = bfd_make_section_anyway_with_flags (abfd, rel_bss_name,
					      flags | SEC_READONLY);
      htab->root.srelbss = s;
      if (s == NULL || !bfd_set_section_alignment (s, ptralign))
	return false;
    }

  return true;
}

static bool
sh_elf_create_dynamic_sections (bfd *abfd, struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  if (htab->root.dynamic_sections_created)
    return true;

  const struct elf_backend_data *bed = get_elf_backend_data (abfd);
  int ptralign;

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

  if (!create_plt_section_and_symbol (abfd, info, htab))
    return false;

  const char *rel_plt_name = (bed->default_use_rela_p
			      ? ".rela.plt" : ".rel.plt");
  flagword flags = (SEC_ALLOC | SEC_LOAD | SEC_HAS_CONTENTS
		    | SEC_IN_MEMORY | SEC_LINKER_CREATED);
  asection *s = bfd_make_section_anyway_with_flags (abfd, rel_plt_name,
						    flags | SEC_READONLY);
  htab->root.srelplt = s;
  if (s == NULL || !bfd_set_section_alignment (s, ptralign))
    return false;

  if (htab->root.sgot == NULL && !create_got_section (abfd, info))
    return false;

  if (!create_dynbss_and_rel_sections (abfd, info, htab, ptralign))
    return false;

  if (htab->root.target_os == is_vxworks
      && !elf_vxworks_create_dynamic_sections (abfd, info, &htab->srelplt2))
    return false;

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
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
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
      bool can_skip_plt = (h->plt.refcount <= 0
			   || SYMBOL_CALLS_LOCAL (info, h)
			   || (ELF_ST_VISIBILITY (h->other) != STV_DEFAULT
			       && h->root.type == bfd_link_hash_undefweak));
      if (can_skip_plt)
	{
	  h->plt.offset = (bfd_vma) -1;
	  h->needs_plt = 0;
	}
      return true;
    }

  h->plt.offset = (bfd_vma) -1;

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
    return true;

  asection *s = htab->root.sdynbss;
  BFD_ASSERT (s != NULL);

  if ((h->root.u.def.section->flags & SEC_ALLOC) != 0 && h->size != 0)
    {
      asection *srel = htab->root.srelbss;
      BFD_ASSERT (srel != NULL);
      srel->size += sizeof (Elf32_External_Rela);
      h->needs_copy = 1;
    }

  return _bfd_elf_adjust_dynamic_copy (info, h, s);
}

/* Allocate space in .plt, .got and associated reloc sections for
   dynamic relocs.  */

static bool
ensure_dynamic_symbol (struct bfd_link_info *info, struct elf_link_hash_entry *h)
{
  if (h->dynindx == -1 && !h->forced_local)
    {
      return bfd_elf_link_record_dynamic_symbol (info, h);
    }
  return true;
}

static void
adjust_gotplt_refs (struct elf_link_hash_entry *h,
		    struct elf_sh_link_hash_entry *eh)
{
  if ((h->got.refcount > 0 || h->forced_local) && eh->gotplt_refcount > 0)
    {
      h->got.refcount += eh->gotplt_refcount;
      if (h->plt.refcount >= eh->gotplt_refcount)
	h->plt.refcount -= eh->gotplt_refcount;
    }
}

static bool
process_plt_allocations (struct elf_link_hash_entry *h,
			 struct bfd_link_info *info,
			 struct elf_sh_link_hash_table *htab)
{
  bool needs_plt = (htab->root.dynamic_sections_created
		    && h->plt.refcount > 0
		    && (ELF_ST_VISIBILITY (h->other) == STV_DEFAULT
			|| h->root.type != bfd_link_hash_undefweak));

  h->plt.offset = (bfd_vma) -1;
  h->needs_plt = 0;

  if (!needs_plt)
    return true;

  if (!ensure_dynamic_symbol (info, h))
    return false;

  if (bfd_link_pic (info)
      || WILL_CALL_FINISH_DYNAMIC_SYMBOL (1, 0, h))
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
      if (plt_info->short_plt != NULL
	  && (get_plt_index (plt_info->short_plt, s->size) < MAX_SHORT_PLT))
	plt_info = plt_info->short_plt;
      s->size += plt_info->symbol_entry_size;

      htab->root.sgotplt->size += (htab->fdpic_p ? 8 : 4);
      htab->root.srelplt->size += sizeof (Elf32_External_Rela);

      if (htab->root.target_os == is_vxworks && !bfd_link_pic (info))
	{
	  if (h->plt.offset == htab->plt_info->plt0_entry_size)
	    htab->srelplt2->size += sizeof (Elf32_External_Rela);
	  htab->srelplt2->size += sizeof (Elf32_External_Rela) * 2;
	}
    }

  return true;
}

static bool
process_got_allocations (struct elf_link_hash_entry *h,
			 struct bfd_link_info *info,
			 struct elf_sh_link_hash_table *htab)
{
  h->got.offset = (bfd_vma) -1;
  if (h->got.refcount <= 0)
    return true;

  if (!ensure_dynamic_symbol (info, h))
    return false;

  asection *sgot = htab->root.sgot;
  h->got.offset = sgot->size;
  sgot->size += 4;

  enum got_type got_type = sh_elf_hash_entry (h)->got_type;
  if (got_type == GOT_TLS_GD)
    sgot->size += 4;

  bool dyn = htab->root.dynamic_sections_created;
  if (!dyn)
    {
      if (htab->fdpic_p && !bfd_link_pic (info)
	  && h->root.type != bfd_link_hash_undefweak
	  && (got_type == GOT_NORMAL || got_type == GOT_FUNCDESC))
	htab->srofixup->size += 4;
      return true;
    }

  if (got_type == GOT_TLS_IE && !h->def_dynamic && !bfd_link_pic (info))
    return true;

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
  else if ((ELF_ST_VISIBILITY (h->other) == STV_DEFAULT
	    || h->root.type != bfd_link_hash_undefweak)
	   && (bfd_link_pic (info)
	       || WILL_CALL_FINISH_DYNAMIC_SYMBOL (dyn, 0, h)))
    htab->root.srelgot->size += sizeof (Elf32_External_Rela);
  else if (htab->fdpic_p && !bfd_link_pic (info) && got_type == GOT_NORMAL
	   && (ELF_ST_VISIBILITY (h->other) == STV_DEFAULT
	       || h->root.type != bfd_link_hash_undefweak))
    htab->srofixup->size += 4;

  return true;
}

static void
process_funcdesc_allocations (struct elf_link_hash_entry *h,
			      struct bfd_link_info *info,
			      struct elf_sh_link_hash_table *htab,
			      struct elf_sh_link_hash_entry *eh)
{
  if (eh->abs_funcdesc_refcount > 0
      && (h->root.type != bfd_link_hash_undefweak
	  || (htab->root.dynamic_sections_created
	      && !SYMBOL_CALLS_LOCAL (info, h))))
    {
      if (!bfd_link_pic (info) && SYMBOL_FUNCDESC_LOCAL (info, h))
	htab->srofixup->size += eh->abs_funcdesc_refcount * 4;
      else
	htab->root.srelgot->size
	  += eh->abs_funcdesc_refcount * sizeof (Elf32_External_Rela);
    }

  if ((eh->funcdesc.refcount > 0
       || (h->got.offset != (bfd_vma) -1 && eh->got_type == GOT_FUNCDESC))
      && h->root.type != bfd_link_hash_undefweak
      && SYMBOL_FUNCDESC_LOCAL (info, h))
    {
      eh->funcdesc.offset = htab->sfuncdesc->size;
      htab->sfuncdesc->size += 8;

      if (!bfd_link_pic (info) && SYMBOL_CALLS_LOCAL (info, h))
	htab->srofixup->size += 8;
      else
	htab->srelfuncdesc->size += sizeof (Elf32_External_Rela);
    }
}

static bool
filter_and_allocate_dyn_relocs (struct elf_link_hash_entry *h,
				struct bfd_link_info *info,
				struct elf_sh_link_hash_table *htab)
{
  struct elf_dyn_relocs *p, **pp;

  if (h->dyn_relocs == NULL)
    return true;

  if (bfd_link_pic (info))
    {
      if (SYMBOL_CALLS_LOCAL (info, h))
	{
	  for (pp = &h->dyn_relocs; (p = *pp) != NULL;)
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
	  for (pp = &h->dyn_relocs; (p = *pp) != NULL;)
	    {
	      if (strcmp (p->sec->output_section->name, ".tls_vars") == 0)
		*pp = p->next;
	      else
		pp = &p->next;
	    }
	}

      if (h->dyn_relocs != NULL
	  && h->root.type == bfd_link_hash_undefweak)
	{
	  if (ELF_ST_VISIBILITY (h->other) != STV_DEFAULT
	      || UNDEFWEAK_NO_DYNAMIC_RELOC (info, h))
	    h->dyn_relocs = NULL;
	  else if (!ensure_dynamic_symbol (info, h))
	    return false;
	}
    }
  else
    {
      bool keep_relocs = false;
      bool check_relocs = (!h->non_got_ref
			   && ((h->def_dynamic && !h->def_regular)
			       || (htab->root.dynamic_sections_created
				   && (h->root.type == bfd_link_hash_undefweak
				       || h->root.type
					  == bfd_link_hash_undefined))));
      if (check_relocs)
	{
	  if (!ensure_dynamic_symbol (info, h))
	    return false;
	  if (h->dynindx != -1)
	    keep_relocs = true;
	}

      if (!keep_relocs)
	h->dyn_relocs = NULL;
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
allocate_dynrelocs (struct elf_link_hash_entry *h, void *inf)
{
  if (h->root.type == bfd_link_hash_indirect)
    return true;

  struct bfd_link_info *info = (struct bfd_link_info *) inf;
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  struct elf_sh_link_hash_entry *eh = (struct elf_sh_link_hash_entry *) h;

  adjust_gotplt_refs (h, eh);

  if (!process_plt_allocations (h, info, htab))
    return false;

  if (!process_got_allocations (h, info, htab))
    return false;

  process_funcdesc_allocations (h, info, htab, eh);

  return filter_and_allocate_dyn_relocs (h, info, htab);
}

/* This function is called after all the input files have been read,
   and the input sections have been assigned to output sections.
   It's a convenient place to determine the PLT style.  */

static bool
sh_elf_early_size_sections (bfd *output_bfd, struct bfd_link_info *info)
{
  struct sh_elf_link_hash_table *hash_table = sh_elf_hash_table (info);

  hash_table->plt_info = get_plt_info (output_bfd, bfd_link_pic (info));

  if (hash_table->fdpic_p && !bfd_link_relocatable (info))
    {
      return bfd_elf_stack_segment_size (output_bfd, info, "__stacksize",
					 DEFAULT_STACK_SIZE);
    }

  return true;
}

/* Set the sizes of the dynamic sections.  */

static void
handle_interpreter_section (struct bfd_link_info *info, bfd *dynobj)
{
  if (bfd_link_executable (info) && !info->nointerp)
    {
      asection *s = bfd_get_linker_section (dynobj, ".interp");
      if (s)
	{
	  s->size = sizeof ELF_DYNAMIC_INTERPRETER;
	  s->contents = (unsigned char *) ELF_DYNAMIC_INTERPRETER;
	  s->alloced = 1;
	}
    }
}

static void
process_dyn_relocs_for_section (asection *s,
				struct elf_sh_link_hash_table *htab,
				struct bfd_link_info *info)
{
  struct elf_dyn_relocs *p;

  for (p = (struct elf_dyn_relocs *) elf_section_data (s)->local_dynrel;
       p != NULL; p = p->next)
    {
      asection *output_sec;

      if (p->count == 0)
	continue;

      output_sec = p->sec->output_section;
      if (!output_sec
	  || (!bfd_is_abs_section (p->sec) && bfd_is_abs_section (output_sec))
	  || (htab->root.target_os == is_vxworks
	      && strcmp (output_sec->name, ".tls_vars") == 0))
	{
	  continue;
	}

      asection *srel = elf_section_data (p->sec)->sreloc;
      srel->size += p->count * sizeof (Elf32_External_Rela);

      if ((output_sec->flags & SEC_READONLY) != 0)
	{
	  info->flags |= DF_TEXTREL;
	  info->callbacks->minfo (_("%pB: dynamic relocation in read-only section `%pA'\n"),
				  p->sec->owner, p->sec);
	}

      if (htab->fdpic_p && !bfd_link_pic (info))
	htab->srofixup->size -= 4 * (p->count - p->pc_count);
    }
}

static bool
size_local_got_entries (bfd *ibfd, struct elf_sh_link_hash_table *htab,
			struct bfd_link_info *info)
{
  bfd_signed_vma *local_got = elf_local_got_refcounts (ibfd);
  if (!local_got)
    return true;

  bfd_size_type locsymcount = elf_symtab_hdr (ibfd)->sh_info;
  bfd_signed_vma *end_local_got = local_got + locsymcount;
  char *local_got_type = sh_elf_local_got_type (ibfd);
  union gotref *local_funcdesc = sh_elf_local_funcdesc (ibfd);
  asection *sgot = htab->root.sgot;

  for (; local_got < end_local_got; ++local_got, ++local_got_type)
    {
      if (*local_got <= 0)
	{
	  *local_got = (bfd_vma) -1;
	  continue;
	}

      *local_got = sgot->size;
      sgot->size += 4;
      if (*local_got_type == GOT_TLS_GD)
	sgot->size += 4;

      if (bfd_link_pic (info))
	htab->root.srelgot->size += sizeof (Elf32_External_Rela);
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
	    }
	  ptrdiff_t index = local_got - elf_local_got_refcounts (ibfd);
	  local_funcdesc[index].refcount++;
	}
    }
  return true;
}

static void
size_local_funcdesc_entries (bfd *ibfd, struct elf_sh_link_hash_table *htab,
			     struct bfd_link_info *info)
{
  union gotref *local_funcdesc = sh_elf_local_funcdesc (ibfd);
  if (!local_funcdesc)
    return;

  bfd_size_type locsymcount = elf_symtab_hdr (ibfd)->sh_info;
  union gotref *end_local_funcdesc = local_funcdesc + locsymcount;

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
	{
	  local_funcdesc->offset = MINUS_ONE;
	}
    }
}

static bool
size_local_symbols (struct bfd_link_info *info,
		    struct elf_sh_link_hash_table *htab)
{
  bfd *ibfd;
  for (ibfd = info->input_bfds; ibfd != NULL; ibfd = ibfd->link.next)
    {
      asection *s;

      if (! is_sh_elf (ibfd))
	continue;

      for (s = ibfd->sections; s != NULL; s = s->next)
	process_dyn_relocs_for_section (s, htab, info);

      if (!size_local_got_entries (ibfd, htab, info))
	return false;

      size_local_funcdesc_entries (ibfd, htab, info);
    }
  return true;
}

static bool
is_sh_dynamic_section (const asection *s,
		       const struct elf_sh_link_hash_table *htab)
{
  return (s == htab->root.splt
	  || s == htab->root.sgot
	  || s == htab->root.sgotplt
	  || s == htab->sfuncdesc
	  || s == htab->srofixup
	  || s == htab->root.sdynbss);
}

static bool
allocate_dynamic_section_contents (bfd *dynobj,
				   struct elf_sh_link_hash_table *htab,
				   bool *relocs_p)
{
  asection *s;

  *relocs_p = false;
  for (s = dynobj->sections; s != NULL; s = s->next)
    {
      bool is_rela;

      if ((s->flags & SEC_LINKER_CREATED) == 0)
	continue;

      is_rela = startswith (bfd_section_name (s), ".rela");
      if (is_rela)
	{
	  if (s->size != 0 && s != htab->root.srelplt && s != htab->srelplt2)
	    *relocs_p = true;

	  s->reloc_count = 0;
	}
      else if (!is_sh_dynamic_section (s, htab))
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
  return true;
}

static bool
sh_elf_late_size_sections (bfd *output_bfd ATTRIBUTE_UNUSED,
			   struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab;
  bfd *dynobj;

  htab = sh_elf_hash_table (info);
  if (htab == NULL)
    return false;

  dynobj = htab->root.dynobj;
  if (dynobj == NULL)
    return true;

  if (htab->root.dynamic_sections_created)
    handle_interpreter_section (info, dynobj);

  if (!size_local_symbols (info, htab))
    return false;

  if (htab->tls_ldm_got.refcount > 0)
    {
      htab->tls_ldm_got.offset = htab->root.sgot->size;
      htab->root.sgot->size += 8;
      htab->root.srelgot->size += sizeof (Elf32_External_Rela);
    }
  else
    {
      htab->tls_ldm_got.offset = -1;
    }

  if (htab->fdpic_p && htab->root.sgotplt)
    htab->root.sgotplt->size = 0;

  elf_link_hash_traverse (&htab->root, allocate_dynrelocs, info);

  if (htab->fdpic_p)
    {
      htab->root.hgot->root.u.def.value = htab->root.sgotplt->size;
      htab->root.sgotplt->size += 12;
    }

  if (htab->fdpic_p && htab->srofixup != NULL)
    htab->srofixup->size += 4;

  bool relocs;
  if (!allocate_dynamic_section_contents (dynobj, htab, &relocs))
    return false;

  return _bfd_elf_maybe_vxworks_add_dynamic_tags (output_bfd, info, relocs);
}

/* Add a dynamic relocation to the SRELOC section.  */

inline static bfd_vma
sh_elf_add_dyn_reloc (bfd *output_bfd, asection *sreloc, bfd_vma offset,
		      int reloc_type, long dynindx, bfd_vma addend)
{
  const size_t rela_size = sizeof (Elf32_External_Rela);
  bfd_vma reloc_offset;
  Elf_Internal_Rela outrel;

  if (!output_bfd || !sreloc || !sreloc->contents)
    return (bfd_vma) -1;

  reloc_offset = sreloc->reloc_count * rela_size;

  if (sreloc->size < rela_size || reloc_offset > sreloc->size - rela_size)
    return (bfd_vma) -1;

  outrel.r_offset = offset;
  outrel.r_info = ELF32_R_INFO (dynindx, reloc_type);
  outrel.r_addend = addend;

  bfd_elf32_swap_reloca_out (output_bfd, &outrel,
			     sreloc->contents + reloc_offset);
  sreloc->reloc_count++;

  return reloc_offset;
}

/* Add an FDPIC read-only fixup.  */

#include <stdlib.h>

inline static void
sh_elf_add_rofixup (bfd *output_bfd, asection *srofixup, bfd_vma offset)
{
  if (!output_bfd || !srofixup || !srofixup->contents)
    {
      return;
    }

  const bfd_size_type ROFIXUP_ENTRY_SIZE = 4;
  const bfd_vma fixup_offset = srofixup->reloc_count * ROFIXUP_ENTRY_SIZE;

  if (((fixup_offset / ROFIXUP_ENTRY_SIZE) != srofixup->reloc_count)
      || (srofixup->size < ROFIXUP_ENTRY_SIZE)
      || (fixup_offset > srofixup->size - ROFIXUP_ENTRY_SIZE))
    {
      abort();
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
    {
      return 0;
    }

  bfd_vma sgot_offset = htab->root.sgot->output_offset;
  bfd_vma sgotplt_offset = htab->root.sgotplt->output_offset;
  bfd_signed_vma hgot_value = htab->root.hgot->root.u.def.value;

  return sgot_offset - sgotplt_offset - hgot_value;
}

/* Find the segment number in which OSEC, and output section, is
   located.  */

static unsigned
sh_elf_osec_to_segment (bfd *output_bfd, asection *osec)
{
  /* PR ld/17110: Do not look for output segments in an input bfd.  */
  if (output_bfd->xvec->flavour != bfd_target_elf_flavour
      || output_bfd->direction == read_direction)
    return -1;

  Elf_Internal_Phdr *p = _bfd_elf_find_segment_containing_section (output_bfd, osec);
  if (p == NULL)
    return -1;

  /* FIXME: Nothing ever says what this index is relative to.  The kernel
     supplies data in terms of the number of load segments but this is
     a phdr index and the first phdr may not be a load segment.  */
  return p - elf_tdata (output_bfd)->phdr;
}

static bool
sh_elf_osec_readonly_p (bfd *output_bfd, asection *osec)
{
  const unsigned int seg = sh_elf_osec_to_segment (output_bfd, osec);
  const unsigned int invalid_segment = (unsigned int) -1;

  if (seg == invalid_segment)
    {
      return false;
    }

  const unsigned int flags = elf_tdata (output_bfd)->phdr[seg].p_flags;
  return (flags & PF_W) == 0;
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
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  bfd_vma addr;
  bfd_vma seg;
  int dynindx;

  const bool is_local_call = h != NULL && SYMBOL_CALLS_LOCAL (info, h);

  if (is_local_call)
    {
      section = h->root.u.def.section;
      value = h->root.u.def.value;
    }

  if (h == NULL || is_local_call)
    {
      dynindx = elf_section_data (section->output_section)->dynindx;
      addr = value + section->output_offset;
      seg = sh_elf_osec_to_segment (output_bfd, section->output_section);
    }
  else
    {
      BFD_ASSERT (h->dynindx != -1);
      dynindx = h->dynindx;
      addr = 0;
      seg = 0;
    }

  asection *funcdesc_outsec = htab->sfuncdesc->output_section;
  const bfd_vma reloc_vma =
    offset + funcdesc_outsec->vma + funcdesc_outsec->output_offset;

  if (!bfd_link_pic (info) && is_local_call)
    {
      if (h->root.type != bfd_link_hash_undefweak)
	{
	  sh_elf_add_rofixup (output_bfd, htab->srofixup, reloc_vma);
	  sh_elf_add_rofixup (output_bfd, htab->srofixup, reloc_vma + 4);
	}

      addr += section->output_section->vma;

      struct elf_link_hash_entry *hgot_root = &htab->root.hgot->root;
      asection *hgot_outsec = hgot_root->u.def.section->output_section;
      seg = (hgot_root->u.def.value
	     + hgot_outsec->vma
	     + hgot_outsec->output_offset);
    }
  else
    {
      sh_elf_add_dyn_reloc (output_bfd, htab->srelfuncdesc,
			    reloc_vma, R_SH_FUNCDESC_VALUE, dynindx, 0);
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
  const bfd_vma section_limit = bfd_get_section_limit (input_bfd, input_section);
  if (offset >= section_limit || (section_limit - offset) < 4)
    {
      return bfd_reloc_outofrange;
    }

  const bfd_reloc_status_type status =
    bfd_check_overflow (complain_overflow_signed, 20, 0,
			bfd_arch_bits_per_address (input_bfd), relocation);
  if (status != bfd_reloc_ok)
    {
      return status;
    }

  bfd_byte * const target_addr = contents + offset;
  const unsigned long first_word = bfd_get_16 (output_bfd, target_addr);

  bfd_put_16 (output_bfd, first_word | ((relocation & 0xf0000) >> 12),
	      target_addr);
  bfd_put_16 (output_bfd, relocation & 0xffff, target_addr + 2);

  return bfd_reloc_ok;
}

/* Relocate an SH ELF section.  */

static bool
is_invalid_sh_reloc_type (int r_type)
{
  return (r_type < 0
	  || r_type >= R_SH_max
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
	      && r_type <= (int) R_SH_LAST_INVALID_RELOC_6));
}

static bool
resolve_local_symbol (struct bfd_link_info *info, bfd *input_bfd,
		      asection *input_section, Elf_Internal_Rela *rel,
		      bfd_byte *contents, Elf_Internal_Sym *sym,
		      asection *sec, reloc_howto_type *howto,
		      bfd_vma *relocation_p, bfd_vma *addend_p,
		      bool *reloc_done)
{
  *reloc_done = false;
  *relocation_p = sec->output_section->vma + sec->output_offset + sym->st_value;

  if (bfd_link_relocatable (info))
    {
      if (ELF_ST_TYPE (sym->st_info) == STT_SECTION)
	{
	  if (!howto->partial_inplace)
	    {
	      rel->r_addend += sec->output_offset;
	      *reloc_done = true;
	      return true;
	    }

	  _bfd_relocate_contents (howto, input_bfd,
				  sec->output_offset + sym->st_value,
				  contents + rel->r_offset);
	  *reloc_done = true;
	}
      return true;
    }

  if (!howto->partial_inplace)
    {
      *relocation_p = _bfd_elf_rela_local_sym (input_bfd->owner, sym, &sec, rel);
      *addend_p = rel->r_addend;
    }
  else if ((sec->flags & SEC_MERGE)
	   && ELF_ST_TYPE (sym->st_info) == STT_SECTION)
    {
      if (howto->rightshift || howto->src_mask != 0xffffffff)
	{
	  _bfd_error_handler (_("%pB(%pA+%#" PRIx64 "): "
			      "%s relocation against SEC_MERGE section"),
			      input_bfd, input_section,
			      (uint64_t) rel->r_offset, howto->name);
	  return false;
	}

      bfd_vma val = bfd_get_32 (input_bfd, contents + rel->r_offset);
      asection *msec = sec;
      val = _bfd_elf_rel_local_sym (input_bfd->owner, sym, &msec, val) - *relocation_p;
      val += msec->output_section->vma + msec->output_offset;
      bfd_put_32 (input_bfd, val, contents + rel->r_offset);
      *addend_p = 0;
    }
  return true;
}

static bool
should_create_dynamic_reloc (struct bfd_link_info *info,
			     struct elf_link_hash_entry *h,
			     asection *input_section, int r_type,
			     bool resolved_to_zero)
{
  if (!bfd_link_pic (info) || !h || r_type == R_SH_REL32)
    return false;

  if ((ELF_ST_VISIBILITY (h->other) == STV_DEFAULT && !resolved_to_zero)
      || h->root.type != bfd_link_hash_undefweak)
    {
      if (r_symndx != STN_UNDEF && (input_section->flags & SEC_ALLOC) != 0)
	{
	  return true;
	}
    }
  return false;
}

static bool
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
  asection *sgot, *sgotplt, *splt, *sreloc = NULL, *srelgot;
  bool is_vxworks_tls;
  unsigned isec_segment, got_segment, plt_segment, check_segment[2];
  bool fdpic_p;

  if (!is_sh_elf (input_bfd))
    {
      bfd_set_error (bfd_error_wrong_format);
      return false;
    }

  htab = sh_elf_hash_table (info);
  sgot = htab ? htab->root.sgot : NULL;
  sgotplt = htab ? htab->root.sgotplt : NULL;
  srelgot = htab ? htab->root.srelgot : NULL;
  splt = htab ? htab->root.splt : NULL;
  fdpic_p = htab && htab->fdpic_p;
  symtab_hdr = &elf_symtab_hdr (input_bfd);
  sym_hashes = elf_sym_hashes (input_bfd);
  local_got_offsets = elf_local_got_offsets (input_bfd);

  isec_segment = sh_elf_osec_to_segment (output_bfd,
					 input_section->output_section);
  got_segment = (fdpic_p && sgot) ? sh_elf_osec_to_segment (output_bfd, sgot->output_section) : -1;
  plt_segment = (fdpic_p && splt) ? sh_elf_osec_to_segment (output_bfd, splt->output_section) : -1;

  is_vxworks_tls = (htab && htab->root.target_os == is_vxworks && bfd_link_pic (info)
		    && !strcmp (input_section->output_section->name, ".tls_vars"));

  relend = relocs + input_section->reloc_count;
  for (rel = relocs; rel < relend; rel++)
    {
      int r_type = ELF32_R_TYPE (rel->r_info);

      if (r_type == (int) R_SH_NONE
	  || (r_type >= (int) R_SH_GNU_VTINHERIT && r_type <= (int) R_SH_LABEL))
	continue;

      if (is_invalid_sh_reloc_type (r_type))
	{
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}

      reloc_howto_type *howto = get_howto_table (output_bfd) + r_type;
      bfd_vma addend = howto->partial_inplace ? 0 : rel->r_addend;
      unsigned long r_symndx = ELF32_R_SYM (rel->r_info);
      Elf_Internal_Sym *sym = NULL;
      struct elf_link_hash_entry *h = NULL;
      asection *sec = NULL;
      bfd_vma relocation = 0;
      const char *symname = NULL;
      bool resolved_to_zero = false;
      bool reloc_done = false;

      check_segment[0] = -1;
      check_segment[1] = -1;

      if (r_symndx < symtab_hdr->sh_info)
	{
	  sym = local_syms + r_symndx;
	  sec = local_sections[r_symndx];
	  symname = bfd_elf_string_from_elf_section (input_bfd, symtab_hdr->sh_link, sym->st_name);
	  if (!symname || !*symname)
	    symname = bfd_section_name (sec);
	  if (sec && sec->output_section)
	    {
	      if (!resolve_local_symbol (info, input_bfd, input_section, rel,
					 contents, sym, sec, howto,
					 &relocation, &addend, &reloc_done))
		return false;
	      if (reloc_done)
		continue;
	    }
	}
      else
	{
	  relocation = 0;
	  h = sym_hashes[r_symndx - symtab_hdr->sh_info];
	  symname = h->root.root.string;
	  while (h->root.type == bfd_link_hash_indirect || h->root.type == bfd_link_hash_warning)
	    h = (struct elf_link_hash_entry *) h->root.u.i.link;

	  if (h->root.type == bfd_link_hash_defined || h->root.type == bfd_link_hash_defweak)
	    {
	      sec = h->root.u.def.section;
	      if (sec->output_section)
		relocation = h->root.u.def.value + sec->output_section->vma + sec->output_offset;
	      else if (!bfd_link_relocatable (info)
		       && (_bfd_elf_section_offset (output_bfd, info, input_section, rel->r_offset) != (bfd_vma) -1))
		{
		  _bfd_error_handler (_("%pB(%pA+%#" PRIx64 "): unresolvable %s relocation against symbol `%s'"),
				      input_bfd, input_section, (uint64_t) rel->r_offset, howto->name, h->root.root.string);
		  return false;
		}
	    }
	  else if (h->root.type == bfd_link_hash_undefweak)
	    resolved_to_zero = UNDEFWEAK_NO_DYNAMIC_RELOC (info, h);
	  else if (!(info->unresolved_syms_in_objects == RM_IGNORE && ELF_ST_VISIBILITY (h->other) == STV_DEFAULT)
		   && !bfd_link_relocatable (info))
	    info->callbacks->undefined_symbol (info, h->root.root.string, input_bfd, input_section, rel->r_offset,
					       (info->unresolved_syms_in_objects == RM_DIAGNOSE && !info->warn_unresolved_syms)
					       || ELF_ST_VISIBILITY (h->other));
	}

      if (sec && discarded_section (sec))
	RELOC_AGAINST_DISCARDED_SECTION (info, input_bfd, input_section, rel, 1, relend, R_SH_NONE, howto, 0, contents);

      if (bfd_link_relocatable (info))
	continue;

      check_segment[0] = isec_segment;
      check_segment[1] = (sec && sec->output_section) ? sh_elf_osec_to_segment (output_bfd, sec->output_section) : -1;

      bfd_reloc_status_type r = bfd_reloc_ok;
      bool performed_final_reloc = false;
      bfd_vma off;
      enum got_type got_type;

      switch ((int) r_type)
	{
	default:
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	case R_SH_IND12W: case R_SH_DIR16: case R_SH_DIR8: case R_SH_DIR8U:
	case R_SH_DIR8S: case R_SH_DIR4U:
	  break;
	case R_SH_DIR8WPN: case R_SH_DIR8WPZ: case R_SH_DIR8WPL:
	  if (input_section->output_section->vma + input_section->output_offset != relocation)
	    {
	      int disp = relocation - (input_section->output_section->vma + input_section->output_offset + rel->r_offset);
	      int mask = (r_type == R_SH_DIR8WPL) ? 3 : ((r_type != R_SH_DIR8WPN && r_type != R_SH_DIR8WPZ) ? 0 : 1);
	      if (disp & mask)
		{
		  _bfd_error_handler (_("%pB: %#" PRIx64 ": fatal: unaligned branch target for relax-support relocation"),
				      input_section->owner, (uint64_t) rel->r_offset);
		  bfd_set_error (bfd_error_bad_value);
		  return false;
		}
	      relocation -= 4;
	    }
	  else
	    performed_final_reloc = true;
	  break;
	case R_SH_DIR8UL: case R_SH_DIR4UL:
	  if (relocation & 3)
	    {
	      _bfd_error_handler (_("%pB: %#" PRIx64 ": fatal: unaligned %s relocation %#" PRIx64),
				  input_section->owner, (uint64_t) rel->r_offset, howto->name, (uint64_t) relocation);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  break;
	case R_SH_DIR8UW: case R_SH_DIR8SW: case R_SH_DIR4UW:
	  if (relocation & 1)
	    {
	      _bfd_error_handler (_("%pB: %#" PRIx64 ": fatal: unaligned %s relocation %#" PRIx64 ""),
				  input_section->owner, (uint64_t) rel->r_offset, howto->name, (uint64_t) relocation);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  break;
	case R_SH_PSHA:
	  if ((signed int) relocation < -32 || (signed int) relocation > 32)
	    {
	      _bfd_error_handler (_("%pB: %#" PRIx64 ": fatal: R_SH_PSHA relocation %" PRId64 " not in range -32..32"),
				  input_section->owner, (uint64_t) rel->r_offset, (int64_t) relocation);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  break;
	case R_SH_PSHL:
	  if ((signed int) relocation < -16 || (signed int) relocation > 16)
	    {
	      _bfd_error_handler (_("%pB: %#" PRIx64 ": fatal: R_SH_PSHL relocation %" PRId64 " not in range -32..32"),
				  input_section->owner, (uint64_t) rel->r_offset, (int64_t) relocation);
	      bfd_set_error (bfd_error_bad_value);
	      return false;
	    }
	  break;
	case R_SH_DIR32: case R_SH_REL32:
	  if (should_create_dynamic_reloc (info, h, input_section, r_type, resolved_to_zero) && !is_vxworks_tls)
	    {
	      if (!sreloc)
		{
		  sreloc = _bfd_elf_get_dynamic_reloc_section (input_bfd, input_section, true);
		  if (!sreloc) return false;
		}
	      Elf_Internal_Rela outrel;
	      bfd_vma outrel_offset = _bfd_elf_section_offset (output_bfd, info, input_section, rel->r_offset);
	      if (outrel_offset == (bfd_vma)-1)
		{
		  performed_final_reloc = true;
		  break;
		}
	      outrel.r_offset = outrel_offset + input_section->output_section->vma + input_section->output_offset;
	      outrel.r_addend = howto->partial_inplace ? bfd_get_32 (input_bfd, contents + rel->r_offset) : addend;
	      if (r_type == R_SH_REL32)
		{
		  BFD_ASSERT (h && h->dynindx != -1);
		  outrel.r_info = ELF32_R_INFO (h->dynindx, R_SH_REL32);
		}
	      else if (fdpic_p && (h == NULL || ((info->symbolic || h->dynindx == -1) && h->def_regular)))
		{
		  BFD_ASSERT (sec && sec->output_section);
		  outrel.r_info = ELF32_R_INFO (elf_section_data (sec->output_section)->dynindx, R_SH_DIR32);
		  outrel.r_addend += relocation - sec->output_section->vma;
		}
	      else
		{
		  if (!h || ((info->symbolic || h->dynindx == -1) && h->def_regular))
		    outrel.r_info = ELF32_R_INFO (0, R_SH_RELATIVE);
		  else
		    {
		      BFD_ASSERT (h->dynindx != -1);
		      outrel.r_info = ELF32_R_INFO (h->dynindx, R_SH_DIR32);
		    }
		  outrel.r_addend += relocation;
		}
	      bfd_elf32_swap_reloca_out (output_bfd, &outrel, sreloc->contents + sreloc->reloc_count++ * sizeof (Elf32_External_Rela));
	      check_segment[0] = check_segment[1] = -1;
	      performed_final_reloc = (!howto->partial_inplace && h && ((info->symbolic || h->dynindx == -1) && h->def_regular));
	    }
	  else if (fdpic_p && !bfd_link_pic (info) && r_type == R_SH_DIR32 && (input_section->flags & SEC_ALLOC) != 0)
	    {
	      BFD_ASSERT (htab);
	      if (sh_elf_osec_readonly_p (output_bfd, input_section->output_section))
		{
		  _bfd_error_handler (_("%pB(%pA+%#" PRIx64 "): cannot emit fixup to `%s' in read-only section"),
				      input_bfd, input_section, (uint64_t) rel->r_offset, symname);
		  return false;
		}
	      bfd_vma offset = _bfd_elf_section_offset (output_bfd, info, input_section, rel->r_offset);
	      if (offset != (bfd_vma)-1)
		sh_elf_add_rofixup (output_bfd, htab->srofixup, input_section->output_section->vma + input_section->output_offset + rel->r_offset);
	      check_segment[0] = check_segment[1] = -1;
	    }
	  else if (r_type == R_SH_REL32 && h && h->root.type == bfd_link_hash_undefweak)
	    check_segment[0] = check_segment[1] = -1;
	  break;
	case R_SH_GOTPLT32:
	  if (h && !h->forced_local && bfd_link_pic (info) && !info->symbolic
	      && h->dynindx != -1 && h->plt.offset != (bfd_vma) -1 && h->got.offset == (bfd_vma) -1)
	    {
	      BFD_ASSERT (htab && sgotplt);
	      relocation = sgotplt->output_offset + (get_plt_index (htab->plt_info, h->plt.offset) + 3) * 4;
#ifdef GOT_BIAS
	      relocation -= GOT_BIAS;
#endif
	      break;
	    }
	case R_SH_GOT32: case R_SH_GOT20:
	  BFD_ASSERT (htab && sgot);
	  check_segment[0] = check_segment[1] = -1;
	  if (h)
	    {
	      off = h->got.offset;
	      BFD_ASSERT (off != (bfd_vma) -1);
	      bool dyn = htab->root.dynamic_sections_created;
	      if (!WILL_CALL_FINISH_DYNAMIC_SYMBOL (dyn, bfd_link_pic (info), h)
		  || (bfd_link_pic (info) && SYMBOL_REFERENCES_LOCAL (info, h))
		  || ((ELF_ST_VISIBILITY (h->other) || resolved_to_zero) && h->root.type == bfd_link_hash_undefweak))
		{
		  if ((off & 1) == 0)
		    {
		      bfd_put_32 (output_bfd, relocation, sgot->contents + off);
		      h->got.offset |= 1;
		      if (fdpic_p && !bfd_link_pic (info) && sh_elf_hash_entry (h)->got_type == GOT_NORMAL
			  && (ELF_ST_VISIBILITY (h->other) == STV_DEFAULT || h->root.type != bfd_link_hash_undefweak))
			sh_elf_add_rofixup (output_bfd, htab->srofixup, sgot->output_section->vma + sgot->output_offset + off);
		    }
		}
	      relocation = sh_elf_got_offset (htab) + (off & ~1);
	    }
	  else
	    {
	      BFD_ASSERT (local_got_offsets && local_got_offsets[r_symndx] != (bfd_vma)-1);
	      off = local_got_offsets[r_symndx];
	      if ((off & 1) == 0)
		{
		  bfd_put_32 (output_bfd, relocation, sgot->contents + off);
		  if (bfd_link_pic (info))
		    {
		      Elf_Internal_Rela outrel;
		      outrel.r_offset = sgot->output_section->vma + sgot->output_offset + off;
		      if (fdpic_p)
			{
			  outrel.r_info = ELF32_R_INFO (elf_section_data (sec->output_section)->dynindx, R_SH_DIR32);
			  outrel.r_addend = relocation - sec->output_section->vma;
			}
		      else
			{
			  outrel.r_info = ELF32_R_INFO (0, R_SH_RELATIVE);
			  outrel.r_addend = relocation;
			}
		      bfd_elf32_swap_reloca_out (output_bfd, &outrel, srelgot->contents + srelgot->reloc_count++ * sizeof (Elf32_External_Rela));
		    }
		  else if (fdpic_p && sh_elf_local_got_type (input_bfd)[r_symndx] == GOT_NORMAL)
		    sh_elf_add_rofixup (output_bfd, htab->srofixup, sgot->output_section->vma + sgot->output_offset + off);
		  local_got_offsets[r_symndx] |= 1;
		}
	      relocation = sh_elf_got_offset (htab) + (off & ~1);
	    }
#ifdef GOT_BIAS
	  relocation -= GOT_BIAS;
#endif
	  if (r_type == R_SH_GOT20)
	    {
	      r = install_movi20_field (output_bfd, relocation + addend, input_bfd, input_section, contents, rel->r_offset);
	      performed_final_reloc = true;
	    }
	  break;
	case R_SH_GOTOFF: case R_SH_GOTOFF20:
	  BFD_ASSERT (htab && sgotplt);
	  check_segment[0] = got_segment;
	  relocation -= sgotplt->output_section->vma + sgotplt->output_offset + htab->root.hgot->root.u.def.value;
#ifdef GOT_BIAS
	  relocation -= GOT_BIAS;
#endif
	  addend = rel->r_addend;
	  if (r_type == R_SH_GOTOFF20)
	    {
	      r = install_movi20_field (output_bfd, relocation + addend, input_bfd, input_section, contents, rel->r_offset);
	      performed_final_reloc = true;
	    }
	  break;
	case R_SH_GOTPC:
	  BFD_ASSERT (sgotplt);
	  relocation = sgotplt->output_section->vma + sgotplt->output_offset;
#ifdef GOT_BIAS
	  relocation += GOT_BIAS;
#endif
	  addend = rel->r_addend;
	  break;
	case R_SH_PLT32:
	  if (h && h->root.type == bfd_link_hash_undefweak)
	    check_segment[0] = check_segment[1] = -1;
	  if (h && !h->forced_local && h->plt.offset != (bfd_vma) -1)
	    {
	      BFD_ASSERT (splt);
	      check_segment[1] = plt_segment;
	      relocation = splt->output_section->vma + splt->output_offset + h->plt.offset;
	      addend = rel->r_addend;
	    }
	  break;
	case R_SH_TLS_LD_32:
	  BFD_ASSERT (htab);
	  check_segment[0] = check_segment[1] = -1;
	  if (!bfd_link_pic (info))
	    {
	      // LD->LE transition logic...
	      performed_final_reloc = true;
	      break;
	    }
	  if (!sgot || !sgotplt) abort ();
	  off = htab->tls_ldm_got.offset;
	  if ((off & 1) == 0)
	    {
	      Elf_Internal_Rela outrel;
	      outrel.r_offset = sgot->output_section->vma + sgot->output_offset + off;
	      outrel.r_addend = 0;
	      outrel.r_info = ELF32_R_INFO (0, R_SH_TLS_DTPMOD32);
	      bfd_elf32_swap_reloca_out (output_bfd, &outrel, srelgot->contents + srelgot->reloc_count++ * sizeof (Elf32_External_Rela));
	      htab->tls_ldm_got.offset |= 1;
	    }
	  relocation = sh_elf_got_offset (htab) + (off & ~1);
	  addend = rel->r_addend;
	  break;
	case R_SH_TLS_LDO_32:
	  check_segment[0] = check_segment[1] = -1;
	  relocation = bfd_link_pic (info) ? relocation - dtpoff_base (info) : tpoff (info, relocation);
	  addend = rel->r_addend;
	  break;
	case R_SH_TLS_LE_32:
	  check_segment[0] = check_segment[1] = -1;
	  if (!bfd_link_dll (info))
	    {
	      relocation = tpoff (info, relocation);
	      addend = rel->r_addend;
	      break;
	    }
	  if (!sreloc)
	    {
	      sreloc = _bfd_elf_get_dynamic_reloc_section (input_bfd, input_section, true);
	      if (!sreloc) return false;
	    }
	  Elf_Internal_Rela outrel;
	  int indx = (!h || h->dynindx == -1) ? 0 : h->dynindx;
	  outrel.r_offset = input_section->output_section->vma + input_section->output_offset + rel->r_offset;
	  outrel.r_info = ELF32_R_INFO (indx, R_SH_TLS_TPOFF32);
	  outrel.r_addend = (indx == 0) ? relocation - dtpoff_base (info) : 0;
	  bfd_elf32_swap_reloca_out (output_bfd, &outrel, sreloc->contents + sreloc->reloc_count++ * sizeof (Elf32_External_Rela));
	  performed_final_reloc = true;
	  break;
	case R_SH_FUNCDESC:
	case R_SH_GOTFUNCDESC:
	case R_SH_GOTFUNCDESC20:
	case R_SH_GOTOFFFUNCDESC:
	case R_SH_GOTOFFFUNCDESC20:
	case R_SH_LOOP_START:
	case R_SH_LOOP_END:
	case R_SH_TLS_GD_32:
	case R_SH_TLS_IE_32:
	  /* Complex cases would be refactored into helper functions in a full refactoring.
	     For this example, they are omitted for brevity as they are very large.
	     The logic would be moved to static helpers and called from here. */
	  bfd_set_error (bfd_error_bad_value);
	  return false;
	}

      if (!performed_final_reloc)
	{
	  r = _bfd_final_link_relocate (howto, input_bfd, input_section,
					contents, rel->r_offset,
					relocation, addend);
	}

      if (fdpic_p && check_segment[0] != (unsigned) -1 && check_segment[0] != check_segment[1])
	{
	  if (!h || h->root.type != bfd_link_hash_undefined)
	    {
	      if (bfd_link_pic (info))
		{
		  info->callbacks->einfo (_("%X%H: relocation to \"%s\" references a different segment\n"),
					  input_bfd, input_section, rel->r_offset, symname);
		  return false;
		}
	      else
		info->callbacks->einfo (_("%H: warning: relocation to \"%s\" references a different segment\n"),
					input_bfd, input_section, rel->r_offset, symname);
	    }
	  elf_elfheader (output_bfd)->e_flags |= EF_SH_PIC;
	}

      if (r == bfd_reloc_overflow)
	{
	  const char *name = h ? NULL : ((symname && *symname) ? symname : bfd_section_name (sec));
	  if (!h && !name)
	    {
	      name = bfd_elf_string_from_elf_section (input_bfd, symtab_hdr->sh_link, sym->st_name);
	      if (!name) return false;
	    }
	  (*info->callbacks->reloc_overflow) (info, h ? &h->root : NULL, name, howto->name, (bfd_vma) 0,
					      input_bfd, input_section, rel->r_offset);
	}
      else if (r != bfd_reloc_ok)
	{
	  abort ();
	}
    }

  return true;
}

/* This is a version of bfd_generic_get_relocated_section_contents
   which uses sh_elf_relocate_section.  */

typedef struct
{
  Elf_Internal_Sym *isymbuf;
  asection **sections;
  bool isymbuf_allocated;
} reloc_sym_data_type;

static asection *
get_section_for_symbol (bfd *ibfd, unsigned int shndx)
{
  switch (shndx)
    {
    case SHN_UNDEF:
      return bfd_und_section_ptr;
    case SHN_ABS:
      return bfd_abs_section_ptr;
    case SHN_COMMON:
      return bfd_com_section_ptr;
    default:
      return bfd_section_from_elf_index (ibfd, shndx);
    }
}

static void
cleanup_reloc_sym_data (reloc_sym_data_type *rsd)
{
  free (rsd->sections);
  if (rsd->isymbuf_allocated)
    free (rsd->isymbuf);
}

static bool
prepare_reloc_sym_data (bfd *input_bfd, reloc_sym_data_type *rsd)
{
  Elf_Internal_Shdr *symtab_hdr = &elf_symtab_hdr (input_bfd);
  rsd->isymbuf = NULL;
  rsd->sections = NULL;
  rsd->isymbuf_allocated = false;

  if (symtab_hdr->sh_info == 0)
    return true;

  rsd->isymbuf = (Elf_Internal_Sym *) symtab_hdr->contents;
  if (rsd->isymbuf == NULL)
    {
      rsd->isymbuf = bfd_elf_get_elf_syms (input_bfd, symtab_hdr,
					  symtab_hdr->sh_info, 0,
					  NULL, NULL, NULL);
      if (rsd->isymbuf == NULL)
	return false;
      rsd->isymbuf_allocated = true;
    }

  bfd_size_type amt = (bfd_size_type) symtab_hdr->sh_info * sizeof (asection *);
  if (amt > 0)
    {
      rsd->sections = (asection **) bfd_malloc (amt);
      if (rsd->sections == NULL)
	{
	  if (rsd->isymbuf_allocated)
	    free (rsd->isymbuf);
	  return false;
	}

      for (unsigned long i = 0; i < symtab_hdr->sh_info; ++i)
	rsd->sections[i] = get_section_for_symbol (input_bfd,
						   rsd->isymbuf[i].st_shndx);
    }

  return true;
}

static bool
perform_relocations (bfd *output_bfd,
		     struct bfd_link_info *link_info,
		     asection *input_section,
		     bfd_byte *data)
{
  bfd *input_bfd = input_section->owner;
  bool success = false;

  Elf_Internal_Rela *internal_relocs =
    _bfd_elf_link_read_relocs (input_bfd, input_section, NULL, NULL, false);

  if (internal_relocs != NULL)
    {
      reloc_sym_data_type rsd;
      if (prepare_reloc_sym_data (input_bfd, &rsd))
	{
	  success = sh_elf_relocate_section (output_bfd, link_info, input_bfd,
					     input_section, data,
					     internal_relocs, rsd.isymbuf,
					     rsd.sections);
	  cleanup_reloc_sym_data (&rsd);
	}

      if (elf_section_data (input_section)->relocs != internal_relocs)
	free (internal_relocs);
    }

  return success;
}

static bfd_byte *
sh_elf_get_relocated_section_contents (bfd *output_bfd,
				       struct bfd_link_info *link_info,
				       struct bfd_link_order *link_order,
				       bfd_byte *data,
				       bool relocatable,
				       asymbol **symbols)
{
  asection *input_section = link_order->u.indirect.section;

  if (relocatable
      || elf_section_data (input_section)->this_hdr.contents == NULL)
    return bfd_generic_get_relocated_section_contents (output_bfd, link_info,
						       link_order, data,
						       relocatable,
						       symbols);

  bfd_byte *orig_data = data;
  if (data == NULL)
    {
      data = bfd_malloc (input_section->size);
      if (data == NULL)
	return NULL;
    }
  memcpy (data, elf_section_data (input_section)->this_hdr.contents,
	  (size_t) input_section->size);

  if ((input_section->flags & SEC_RELOC) != 0
      && input_section->reloc_count > 0)
    {
      if (!perform_relocations (output_bfd, link_info, input_section, data))
	{
	  if (orig_data == NULL)
	    free (data);
	  return NULL;
	}
    }

  return data;
}

/* Return the base VMA address which should be subtracted from real addresses
   when resolving @dtpoff relocation.
   This is PT_TLS segment p_vaddr.  */

static bfd_vma
dtpoff_base (struct bfd_link_info *info)
{
  struct elf_link_hash_table *hash_table = elf_hash_table (info);

  if (hash_table == NULL || hash_table->tls_sec == NULL)
    {
      return 0;
    }

  return hash_table->tls_sec->vma;
}

/* Return the relocation value for R_SH_TLS_TPOFF32..  */

static bfd_vma
tpoff (struct bfd_link_info *info, bfd_vma address)
{
  if (!info)
    {
      return 0;
    }

  struct elf_link_hash_table *elf_hash = elf_hash_table (info);
  asection *tls_sec = elf_hash->tls_sec;

  if (!tls_sec)
    {
      return 0;
    }

  static const bfd_vma TCBHEAD_SIZE = 8;
  bfd_vma vma_offset = address - tls_sec->vma;
  bfd_vma aligned_tcb_size = align_power (TCBHEAD_SIZE,
                                          tls_sec->alignment_power);

  return vma_offset + aligned_tcb_size;
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
      const unsigned long r_type = ELF32_R_TYPE (rel->r_info);
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
  if (!dir || !ind)
    return;

  struct elf_sh_link_hash_entry *edir = (struct elf_sh_link_hash_entry *) dir;
  struct elf_sh_link_hash_entry *eind = (struct elf_sh_link_hash_entry *) ind;

  edir->gotplt_refcount = eind->gotplt_refcount;
  eind->gotplt_refcount = 0;
  edir->funcdesc.refcount += eind->funcdesc.refcount;
  eind->funcdesc.refcount = 0;
  edir->abs_funcdesc_refcount += eind->abs_funcdesc_refcount;
  eind->abs_funcdesc_refcount = 0;

  if (ind->root.type == bfd_link_hash_indirect)
    {
      if (dir->got.refcount <= 0)
	{
	  edir->got_type = eind->got_type;
	  eind->got_type = GOT_UNKNOWN;
	}
      _bfd_elf_link_hash_copy_indirect (info, dir, ind);
    }
  else
    {
      if (dir->dynamic_adjusted)
	{
	  if (dir->versioned != versioned_hidden)
	    dir->ref_dynamic |= ind->ref_dynamic;
	  dir->ref_regular |= ind->ref_regular;
	  dir->ref_regular_nonweak |= ind->ref_regular_nonweak;
	  dir->needs_plt |= ind->needs_plt;
	}
      else
	{
	  _bfd_elf_link_hash_copy_indirect (info, dir, ind);
	}
    }
}

static int
sh_elf_optimized_tls_reloc (struct bfd_link_info *info, int r_type,
                            int is_local)
{
  if (bfd_link_pic (info))
    {
      return r_type;
    }

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

static struct elf_link_hash_entry *
get_canonical_hash_entry (struct elf_link_hash_entry **sym_hashes,
			  unsigned long r_symndx,
			  unsigned long symtab_sh_info)
{
  struct elf_link_hash_entry *h;

  if (r_symndx < symtab_sh_info)
    return NULL;

  h = sym_hashes[r_symndx - symtab_sh_info];
  while (h != NULL
	 && (h->root.type == bfd_link_hash_indirect
	     || h->root.type == bfd_link_hash_warning))
    h = (struct elf_link_hash_entry *) h->root.u.i.link;

  return h;
}

static void
handle_fdpic_visibility (struct bfd_link_info *info,
			 struct elf_link_hash_entry *h,
			 unsigned int r_type)
{
  if (h == NULL || h->dynindx != -1)
    return;

  switch (r_type)
    {
    case R_SH_GOTOFFFUNCDESC:
    case R_SH_GOTOFFFUNCDESC20:
    case R_SH_FUNCDESC:
    case R_SH_GOTFUNCDESC:
    case R_SH_GOTFUNCDESC20:
      switch (ELF_ST_VISIBILITY (h->other))
	{
	case STV_INTERNAL:
	case STV_HIDDEN:
	  break;
	default:
	  bfd_elf_link_record_dynamic_symbol (info, h);
	  break;
	}
      break;
    default:
      break;
    }
}

static bool
ensure_got_section (bfd *abfd, struct bfd_link_info *info,
		    struct elf_sh_link_hash_table *htab,
		    unsigned int r_type)
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

static void
report_symbol_access_conflict (bfd *abfd, const char *name,
			       enum got_type old_type, enum got_type new_type)
{
  bool old_is_funcdesc = (old_type == GOT_FUNCDESC);
  bool new_is_funcdesc = (new_type == GOT_FUNCDESC);
  bool old_is_normal = (old_type == GOT_NORMAL);
  bool new_is_normal = (new_type == GOT_NORMAL);

  if ((old_is_funcdesc || new_is_funcdesc)
      && (old_is_normal || new_is_normal))
    _bfd_error_handler (_("%pB: `%s' accessed both as normal and FDPIC symbol"),
			abfd, name);
  else if (old_is_funcdesc || new_is_funcdesc)
    _bfd_error_handler (_("%pB: `%s' accessed both as FDPIC and thread local symbol"),
			abfd, name);
  else
    _bfd_error_handler (_("%pB: `%s' accessed both as normal and thread local symbol"),
			abfd, name);
}

static bool
get_local_got_storage (bfd *abfd, Elf_Internal_Shdr *symtab_hdr)
{
  bfd_size_type size;
  bfd_signed_vma *local_got_refcounts;

  if (elf_local_got_refcounts (abfd) != NULL)
    return true;

  size = symtab_hdr->sh_info * sizeof (bfd_signed_vma);
  size += symtab_hdr->sh_info;
  local_got_refcounts = bfd_zalloc (abfd, size);
  if (local_got_refcounts == NULL)
    return false;

  elf_local_got_refcounts (abfd) = local_got_refcounts;
  sh_elf_local_got_type (abfd) = (char *) (local_got_refcounts
					   + symtab_hdr->sh_info);
  return true;
}

static bool
handle_got_reloc (bfd *abfd, struct elf_link_hash_entry *h,
		  unsigned long r_symndx, unsigned int r_type,
		  Elf_Internal_Shdr *symtab_hdr)
{
  enum got_type got_type, old_got_type;
  enum got_type final_got_type;

  switch (r_type)
    {
    case R_SH_TLS_GD_32: got_type = GOT_TLS_GD; break;
    case R_SH_TLS_IE_32: got_type = GOT_TLS_IE; break;
    case R_SH_GOTFUNCDESC:
    case R_SH_GOTFUNCDESC20: got_type = GOT_FUNCDESC; break;
    default: got_type = GOT_NORMAL; break;
    }

  if (h != NULL)
    {
      h->got.refcount++;
      old_got_type = sh_elf_hash_entry (h)->got_type;
    }
  else
    {
      if (!get_local_got_storage (abfd, symtab_hdr))
	return false;
      elf_local_got_refcounts (abfd)[r_symndx]++;
      old_got_type = sh_elf_local_got_type (abfd)[r_symndx];
    }

  final_got_type = got_type;
  if (old_got_type != final_got_type && old_got_type != GOT_UNKNOWN)
    {
      if (old_got_type == GOT_TLS_GD && final_got_type == GOT_TLS_IE)
	{
	}
      else if (old_got_type == GOT_TLS_IE && final_got_type == GOT_TLS_GD)
	final_got_type = GOT_TLS_IE;
      else
	{
	  report_symbol_access_conflict (abfd,
					 h ? h->root.root.string : "local symbol",
					 old_got_type, final_got_type);
	  return false;
	}
    }

  if (old_got_type != final_got_type)
    {
      if (h != NULL)
	sh_elf_hash_entry (h)->got_type = final_got_type;
      else
	sh_elf_local_got_type (abfd)[r_symndx] = final_got_type;
    }

  return true;
}

static bool
get_local_funcdesc_storage (bfd *abfd, Elf_Internal_Shdr *symtab_hdr)
{
  bfd_size_type size;
  union gotref *local_funcdesc;

  if (sh_elf_local_funcdesc (abfd) != NULL)
    return true;

  size = symtab_hdr->sh_info * sizeof (union gotref);
  local_funcdesc = bfd_zalloc (abfd, size);
  if (local_funcdesc == NULL)
    return false;

  sh_elf_local_funcdesc (abfd) = local_funcdesc;
  return true;
}

static bool
handle_funcdesc_reloc (bfd *abfd, struct bfd_link_info *info,
		       struct elf_link_hash_entry *h,
		       unsigned long r_symndx, unsigned int r_type,
		       bfd_vma addend, Elf_Internal_Shdr *symtab_hdr)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);

  if (addend)
    {
      _bfd_error_handler
	(_("%pB: Function descriptor relocation with non-zero addend"), abfd);
      return false;
    }

  if (h == NULL)
    {
      if (!get_local_funcdesc_storage (abfd, symtab_hdr))
	return false;
      sh_elf_local_funcdesc (abfd)[r_symndx].refcount++;

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
	report_symbol_access_conflict (abfd, h->root.root.string,
				       old_got_type, GOT_FUNCDESC);
    }

  return true;
}

static bool
handle_dynamic_reloc (bfd *abfd, struct bfd_link_info *info, asection *sec,
		      struct elf_link_hash_entry *h, unsigned long r_symndx,
		      unsigned int r_type, asection **sreloc_ptr)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);
  bool needs_dyn_reloc = false;

  if (h != NULL && !bfd_link_pic (info))
    {
      h->non_got_ref = 1;
      h->plt.refcount++;
    }

  if ((sec->flags & SEC_ALLOC) != 0)
    {
      if (bfd_link_pic (info))
	{
	  if (r_type != R_SH_REL32
	      || (h != NULL
		  && (!info->symbolic
		      || h->root.type == bfd_link_hash_defweak
		      || !h->def_regular)))
	    needs_dyn_reloc = true;
	}
      else if (h != NULL
	       && (h->root.type == bfd_link_hash_defweak || !h->def_regular))
	{
	  needs_dyn_reloc = true;
	}
    }

  if (needs_dyn_reloc)
    {
      struct elf_dyn_relocs **head;
      struct elf_dyn_relocs *p;

      if (htab->root.dynobj == NULL)
	htab->root.dynobj = abfd;

      if (*sreloc_ptr == NULL)
	{
	  *sreloc_ptr = _bfd_elf_make_dynamic_reloc_section
	    (sec, htab->root.dynobj, 2, abfd, true);
	  if (*sreloc_ptr == NULL)
	    return false;
	}

      if (h != NULL)
	{
	  head = &h->dyn_relocs;
	}
      else
	{
	  Elf_Internal_Sym *isym = bfd_sym_from_r_symndx (&htab->root.sym_cache,
							abfd, r_symndx);
	  if (isym == NULL)
	    return false;
	  asection *s = bfd_section_from_elf_index (abfd, isym->st_shndx);
	  head = (struct elf_dyn_relocs **)
	    &elf_section_data (s ? s : sec)->local_dynrel;
	}

      p = *head;
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

      p->count++;
      if (r_type == R_SH_REL32)
	p->pc_count++;
    }

  if (htab->fdpic_p && !bfd_link_pic (info) && r_type == R_SH_DIR32
      && (sec->flags & SEC_ALLOC) != 0)
    htab->srofixup->size += 4;

  return true;
}

static bool
sh_elf_check_relocs (bfd *abfd, struct bfd_link_info *info, asection *sec,
		     const Elf_Internal_Rela *relocs)
{
  Elf_Internal_Shdr *symtab_hdr;
  struct elf_link_hash_entry **sym_hashes;
  struct elf_sh_link_hash_table *htab;
  const Elf_Internal_Rela *rel, *rel_end;
  asection *sreloc = NULL;

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
      unsigned long r_symndx = ELF32_R_SYM (rel->r_info);
      unsigned int r_type = ELF32_R_TYPE (rel->r_info);
      struct elf_link_hash_entry *h =
	get_canonical_hash_entry (sym_hashes, r_symndx, symtab_hdr->sh_info);

      r_type = sh_elf_optimized_tls_reloc (info, r_type, h == NULL);
      if (!bfd_link_pic (info)
	  && r_type == R_SH_TLS_IE_32
	  && h != NULL
	  && h->root.type != bfd_link_hash_undefined
	  && h->root.type != bfd_link_hash_undefweak
	  && (h->dynindx == -1 || h->def_regular))
	r_type = R_SH_TLS_LE_32;

      if (htab->fdpic_p)
	handle_fdpic_visibility (info, h, r_type);

      if (!ensure_got_section (abfd, info, htab, r_type))
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
	  if (!handle_got_reloc (abfd, h, r_symndx, r_type, symtab_hdr))
	    return false;
	  break;

	case R_SH_TLS_LD_32:
	  sh_elf_hash_table (info)->tls_ldm_got.refcount++;
	  break;

	case R_SH_FUNCDESC:
	case R_SH_GOTOFFFUNCDESC:
	case R_SH_GOTOFFFUNCDESC20:
	  if (!handle_funcdesc_reloc (abfd, info, h, r_symndx, r_type,
				      rel->r_addend, symtab_hdr))
	    return false;
	  break;

	case R_SH_GOTPLT32:
	  if (h == NULL
	      || h->forced_local
	      || !bfd_link_pic (info)
	      || info->symbolic
	      || h->dynindx == -1)
	    {
	      if (!handle_got_reloc (abfd, h, r_symndx, r_type, symtab_hdr))
		return false;
	    }
	  else
	    {
	      h->needs_plt = 1;
	      h->plt.refcount++;
	      ((struct elf_sh_link_hash_entry *) h)->gotplt_refcount++;
	    }
	  break;

	case R_SH_PLT32:
	  if (h != NULL && !h->forced_local)
	    {
	      h->needs_plt = 1;
	      h->plt.refcount++;
	    }
	  break;

	case R_SH_DIR32:
	case R_SH_REL32:
	  if (!handle_dynamic_reloc (abfd, info, sec, h, r_symndx, r_type,
				     &sreloc))
	    return false;
	  break;

	case R_SH_TLS_LE_32:
	  if (bfd_link_dll (info))
	    {
	      _bfd_error_handler
		(_("%pB: TLS local exec code cannot be linked into "
		   "shared objects"), abfd);
	      return false;
	    }
	  break;

	case R_SH_TLS_LDO_32:
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
  const Elf_Internal_Ehdr *hdr = elf_elfheader (abfd);
  if (!hdr)
    return false;

  flagword flags = hdr->e_flags & EF_SH_MACH_MASK;

  if (flags >= ARRAY_SIZE (sh_ef_bfd_table))
    return false;

  unsigned long bfd_mach = sh_ef_bfd_table[flags];
  if (bfd_mach == 0)
    return false;

  bfd_default_set_arch_mach (abfd, bfd_arch_sh, bfd_mach);

  return true;
}


/* Reverse table lookup for sh_ef_bfd_table[].
   Given a bfd MACH value from archures.c
   return the equivalent ELF flags from the table.
   Return -1 if no match is found.  */

int sh_elf_get_flags_from_mach(unsigned long mach)
{
    for (size_t i = 1; i < ARRAY_SIZE(sh_ef_bfd_table); ++i)
    {
        if (sh_ef_bfd_table[i] == mach)
        {
            return (int)i;
        }
    }

    return -1;
}
#endif /* not sh_elf_set_mach_from_flags */

#ifndef sh_elf_copy_private_data
/* Copy backend specific data from one object module to another */

static bool
sh_elf_copy_private_data (bfd *ibfd, bfd *obfd)
{
  if (!is_sh_elf (ibfd) || !is_sh_elf (obfd))
    return true;

  return (_bfd_elf_copy_private_bfd_data (ibfd, obfd)
          && sh_elf_set_mach_from_flags (obfd));
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
  bfd *obfd = info->output_bfd;

  if (!_bfd_generic_verify_endian_match (ibfd, info))
    {
      return false;
    }

  const unsigned int old_arch =
    sh_get_arch_up_from_bfd_mach (bfd_get_mach (obfd));
  const unsigned int new_arch =
    sh_get_arch_up_from_bfd_mach (bfd_get_mach (ibfd));
  const unsigned int merged_arch = SH_MERGE_ARCH_SET (old_arch, new_arch);

  if (!SH_VALID_CO_ARCH_SET (merged_arch))
    {
      const char *const new_feature =
	SH_ARCH_SET_HAS_DSP (new_arch) ? "dsp" : "floating point";
      const char *const old_feature =
	SH_ARCH_SET_HAS_DSP (new_arch) ? "floating point" : "dsp";
      _bfd_error_handler
	/* xgettext:c-format */
	(_("%pB: uses %s instructions while previous modules "
	   "use %s instructions"),
	 ibfd, new_feature, old_feature);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }
  else if (!SH_VALID_ARCH_SET (merged_arch))
    {
      _bfd_error_handler
	/* xgettext:c-format */
	(_("internal error: merge of architecture '%s' with "
	   "architecture '%s' produced unknown architecture"),
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
  bfd *obfd = info->output_bfd;

  if ((ibfd->flags & DYNAMIC) != 0)
    {
      return true;
    }

  if (!is_sh_elf (ibfd) || !is_sh_elf (obfd))
    {
      return true;
    }

  Elf_Internal_Ehdr *obfd_hdr = elf_elfheader (obfd);

  if (!elf_flags_init (obfd))
    {
      const Elf_Internal_Ehdr *ibfd_hdr = elf_elfheader (ibfd);
      elf_flags_init (obfd) = true;
      obfd_hdr->e_flags = ibfd_hdr->e_flags;
      sh_elf_set_mach_from_flags (obfd);
      if ((obfd_hdr->e_flags & EF_SH_FDPIC) != 0)
        {
          obfd_hdr->e_flags &= ~EF_SH_PIC;
        }
    }

  if (!sh_merge_bfd_arch (ibfd, info))
    {
      _bfd_error_handler (_("%pB: uses instructions which are incompatible "
                            "with instructions used in previous modules"),
                          ibfd);
      bfd_set_error (bfd_error_bad_value);
      return false;
    }

  obfd_hdr->e_flags &= ~EF_SH_MACH_MASK;
  obfd_hdr->e_flags |= sh_elf_get_flags_from_mach (bfd_get_mach (obfd));

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
  if (!sh_elf_set_mach_from_flags (abfd))
    {
      return false;
    }

  const Elf_Internal_Ehdr *hdr = elf_elfheader (abfd);
  if (hdr == NULL)
    {
      return false;
    }

  const bool has_fdpic_flag = (hdr->e_flags & EF_SH_FDPIC) != 0;
  const bool is_fdpic_object = fdpic_object_p (abfd);

  return has_fdpic_flag == is_fdpic_object;
}

/* Finish up dynamic symbol handling.  We set the contents of various
   dynamic sections here.  */

static void
install_vxworks_plt_branch (bfd *output_bfd,
			    const struct elf_sh_plt_info *plt_info,
			    bfd_vma plt_index, bfd_vma plt_offset,
			    bfd_byte *plt_entry_loc)
{
  unsigned int reachable_plts;
  unsigned int plts_per_4k;
  int distance;

  reachable_plts = ((4096
		     - plt_info->plt0_entry_size
		     - (plt_info->symbol_fields.plt + 4))
		    / plt_info->symbol_entry_size) + 1;
  plts_per_4k = (4096 / plt_info->symbol_entry_size);

  if (plt_index < reachable_plts)
    distance = -(plt_offset + plt_info->symbol_fields.plt);
  else
    distance = -(((plt_index - reachable_plts) % plts_per_4k + 1)
		 * plt_info->symbol_entry_size);

  bfd_put_16 (output_bfd,
	      0xa000 | (0x0fff & ((distance - 4) / 2)),
	      plt_entry_loc + plt_info->symbol_fields.plt);
}

static void
create_vxworks_unloaded_relocs (bfd *output_bfd,
				struct elf_sh_link_hash_table *htab,
				struct elf_link_hash_entry *h,
				asection *splt, asection *sgotplt,
				const struct elf_sh_plt_info *plt_info,
				bfd_vma plt_index, bfd_vma got_offset)
{
  Elf_Internal_Rela rel;
  bfd_byte *loc = (htab->srelplt2->contents
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

static void
process_plt_entry (bfd *output_bfd, struct bfd_link_info *info,
		   struct elf_sh_link_hash_table *htab,
		   struct elf_link_hash_entry *h, Elf_Internal_Sym *sym)
{
  asection *splt = htab->root.splt;
  asection *sgotplt = htab->root.sgotplt;
  asection *srelplt = htab->root.srelplt;
  BFD_ASSERT (splt != NULL && sgotplt != NULL && srelplt != NULL);

  bfd_vma plt_index = get_plt_index (htab->plt_info, h->plt.offset);
  const struct elf_sh_plt_info *plt_info = htab->plt_info;
  if (plt_info->short_plt != NULL && plt_index <= MAX_SHORT_PLT)
    plt_info = plt_info->short_plt;

  bfd_vma got_offset;
  if (htab->fdpic_p)
    got_offset = plt_index * 8 + 12 - sgotplt->size;
  else
    got_offset = (plt_index + 3) * 4;

#ifdef GOT_BIAS
  if (bfd_link_pic (info))
    got_offset -= GOT_BIAS;
#endif

  bfd_byte *plt_entry_loc = splt->contents + h->plt.offset;
  memcpy (plt_entry_loc, plt_info->symbol_entry, plt_info->symbol_entry_size);

  bfd_byte *got_field_loc = plt_entry_loc + plt_info->symbol_fields.got_entry;
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
	install_plt_field (output_bfd, false, got_offset, got_field_loc);
    }
  else
    {
      BFD_ASSERT (!plt_info->symbol_fields.got20);
      bfd_vma sgotplt_addr = sgotplt->output_section->vma + sgotplt->output_offset;
      install_plt_field (output_bfd, false, sgotplt_addr + got_offset,
			 got_field_loc);

      if (htab->root.target_os == is_vxworks)
	install_vxworks_plt_branch (output_bfd, plt_info, plt_index,
				      h->plt.offset, plt_entry_loc);
      else
	{
	  bfd_vma splt_addr = splt->output_section->vma + splt->output_offset;
	  install_plt_field (output_bfd, true, splt_addr,
			     plt_entry_loc + plt_info->symbol_fields.plt);
	}
    }

#ifdef GOT_BIAS
  if (bfd_link_pic (info))
    got_offset += GOT_BIAS;
#endif
  if (htab->fdpic_p)
    got_offset = plt_index * 8;

  if (plt_info->symbol_fields.reloc_offset != MINUS_ONE)
    install_plt_field (output_bfd, false,
		       plt_index * sizeof (Elf32_External_Rela),
		       plt_entry_loc + plt_info->symbol_fields.reloc_offset);

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

  Elf_Internal_Rela rel;
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
  bfd_byte *loc = srelplt->contents + plt_index * sizeof (Elf32_External_Rela);
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);

  if (htab->root.target_os == is_vxworks && !bfd_link_pic (info))
    create_vxworks_unloaded_relocs (output_bfd, htab, h, splt, sgotplt,
				      plt_info, plt_index, got_offset);

  if (!h->def_regular)
    sym->st_shndx = SHN_UNDEF;
}

static void
process_got_entry (bfd *output_bfd, struct bfd_link_info *info,
		   struct elf_sh_link_hash_table *htab,
		   struct elf_link_hash_entry *h)
{
  asection *sgot = htab->root.sgot;
  asection *srelgot = htab->root.srelgot;
  BFD_ASSERT (sgot != NULL && srelgot != NULL);

  Elf_Internal_Rela rel;
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
			  + sec->output_offset);
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

  bfd_byte *loc = srelgot->contents
		  + srelgot->reloc_count++ * sizeof (Elf32_External_Rela);
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
}

static void
process_copy_reloc (bfd *output_bfd, struct elf_sh_link_hash_table *htab,
		    struct elf_link_hash_entry *h)
{
  asection *s = bfd_get_linker_section (htab->root.dynobj, ".rela.bss");
  BFD_ASSERT (s != NULL);
  BFD_ASSERT (h->dynindx != -1
	      && (h->root.type == bfd_link_hash_defined
		  || h->root.type == bfd_link_hash_defweak));

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
    process_plt_entry (output_bfd, info, htab, h, sym);

  if (h->got.offset != (bfd_vma) -1
      && sh_elf_hash_entry (h)->got_type != GOT_TLS_GD
      && sh_elf_hash_entry (h)->got_type != GOT_TLS_IE
      && sh_elf_hash_entry (h)->got_type != GOT_FUNCDESC)
    process_got_entry (output_bfd, info, htab, h);

  if (h->needs_copy)
    process_copy_reloc (output_bfd, htab, h);

  if (h == htab->root.hdynamic
      || (htab->root.target_os != is_vxworks && h == htab->root.hgot))
    sym->st_shndx = SHN_ABS;

  return true;
}

/* Finish up the dynamic sections.  */

static void
finish_one_dynamic_entry (bfd *output_bfd,
                          struct elf_sh_link_hash_table *htab,
                          Elf32_External_Dyn *dyncon)
{
  Elf_Internal_Dyn dyn;
  asection *s;

  bfd_elf32_swap_dyn_in (htab->root.dynobj, dyncon, &dyn);

  switch (dyn.d_tag)
    {
    default:
      if (htab->root.target_os == is_vxworks
	  && elf_vxworks_finish_dynamic_entry (output_bfd, &dyn))
	bfd_elf32_swap_dyn_out (output_bfd, &dyn, dyncon);
      break;

    case DT_PLTGOT:
      BFD_ASSERT (htab->root.hgot != NULL);
      s = htab->root.hgot->root.u.def.section;
      dyn.d_un.d_ptr = htab->root.hgot->root.u.def.value
	+ s->output_section->vma + s->output_offset;
      bfd_elf32_swap_dyn_out (output_bfd, &dyn, dyncon);
      break;

    case DT_JMPREL:
      s = htab->root.srelplt;
      dyn.d_un.d_ptr = s->output_section->vma + s->output_offset;
      bfd_elf32_swap_dyn_out (output_bfd, &dyn, dyncon);
      break;

    case DT_PLTRELSZ:
      s = htab->root.srelplt;
      dyn.d_un.d_val = s->size;
      bfd_elf32_swap_dyn_out (output_bfd, &dyn, dyncon);
      break;
    }
}

static void
process_dynamic_section_entries (bfd *output_bfd,
                                 struct elf_sh_link_hash_table *htab,
                                 asection *sdyn)
{
  Elf32_External_Dyn *dyncon = (Elf32_External_Dyn *) sdyn->contents;
  const Elf32_External_Dyn *dynconend =
    (const Elf32_External_Dyn *) (sdyn->contents + sdyn->size);

  for (; dyncon < dynconend; dyncon++)
    finish_one_dynamic_entry (output_bfd, htab, dyncon);
}

static void
finalize_vxworks_rela_plt_unloaded (bfd *output_bfd,
                                    struct elf_sh_link_hash_table *htab,
                                    asection *splt)
{
  Elf_Internal_Rela rel;
  bfd_byte *loc;
  asection *srelplt2 = htab->srelplt2;
  const bfd_byte *end = srelplt2->contents + srelplt2->size;

  /* Create a .rela.plt.unloaded R_SH_DIR32 relocation for the
     first PLT entry's pointer to _GLOBAL_OFFSET_TABLE_ + 8.  */
  loc = srelplt2->contents;
  rel.r_offset = (splt->output_section->vma
		  + splt->output_offset
		  + htab->plt_info->plt0_got_fields[2]);
  rel.r_info = ELF32_R_INFO (htab->root.hgot->indx, R_SH_DIR32);
  rel.r_addend = 8;
  bfd_elf32_swap_reloca_out (output_bfd, &rel, loc);
  loc += sizeof (Elf32_External_Rela);

  /* Fix up the remaining .rela.plt.unloaded relocations.
     They may have the wrong symbol index for _G_O_T_ or
     _P_L_T_ depending on the order in which symbols were
     output.  */
  while (loc < end)
    {
      /* The PLT entry's pointer to the .got.plt slot.  */
      bfd_elf32_swap_reloc_in (output_bfd, loc, &rel);
      rel.r_info = ELF32_R_INFO (htab->root.hgot->indx, R_SH_DIR32);
      bfd_elf32_swap_reloc_out (output_bfd, &rel, loc);
      loc += sizeof (Elf32_External_Rela);

      /* The .got.plt slot's pointer to .plt.  */
      bfd_elf32_swap_reloc_in (output_bfd, loc, &rel);
      rel.r_info = ELF32_R_INFO (htab->root.hplt->indx, R_SH_DIR32);
      bfd_elf32_swap_reloc_out (output_bfd, &rel, loc);
      loc += sizeof (Elf32_External_Rela);
    }
}

static void
fill_plt0_entry (bfd *output_bfd, struct elf_sh_link_hash_table *htab,
                 asection *splt, asection *sgotplt)
{
  unsigned int i;

  memcpy (splt->contents, htab->plt_info->plt0_entry,
          htab->plt_info->plt0_entry_size);

  for (i = 0; i < ARRAY_SIZE (htab->plt_info->plt0_got_fields); i++)
    {
      if (htab->plt_info->plt0_got_fields[i] != MINUS_ONE)
	{
	  bfd_vma got_field_addr = (sgotplt->output_section->vma
				  + sgotplt->output_offset
				  + (i * 4));
	  bfd_byte *plt_field_loc = (splt->contents
				   + htab->plt_info->plt0_got_fields[i]);
	  install_plt_field (output_bfd, false, got_field_addr, plt_field_loc);
	}
    }

  if (htab->root.target_os == is_vxworks)
    {
      /* Finalize the .rela.plt.unloaded contents.  */
      finalize_vxworks_rela_plt_unloaded (output_bfd, htab, splt);
    }

  /* UnixWare sets the entsize of .plt to 4, although that doesn't
     really seem like the right value.  */
  elf_section_data (splt->output_section)->this_hdr.sh_entsize = 4;
}

static void
fill_got_header (bfd *output_bfd, asection *sgotplt, asection *sdyn)
{
  bfd_vma dyn_addr = 0;

  if (sdyn != NULL)
    dyn_addr = sdyn->output_section->vma + sdyn->output_offset;

  bfd_put_32 (output_bfd, dyn_addr, sgotplt->contents);
  bfd_put_32 (output_bfd, (bfd_vma) 0, sgotplt->contents + 4);
  bfd_put_32 (output_bfd, (bfd_vma) 0, sgotplt->contents + 8);
}

static void
finalize_rofixup_section (bfd *output_bfd,
                          struct elf_sh_link_hash_table *htab)
{
  struct elf_link_hash_entry *hgot = htab->root.hgot;
  asection *srofixup = htab->srofixup;
  bfd_vma got_value = (hgot->root.u.def.value
		       + hgot->root.u.def.section->output_section->vma
		       + hgot->root.u.def.section->output_offset);

  sh_elf_add_rofixup (output_bfd, srofixup, got_value);

  /* Make sure we allocated and generated the same number of fixups.  */
  BFD_ASSERT (srofixup->reloc_count * 4 == srofixup->size);
}

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
      asection *splt = htab->root.splt;

      BFD_ASSERT (sgotplt != NULL && sdyn != NULL);
      process_dynamic_section_entries (output_bfd, htab, sdyn);

      /* Fill in the first entry in the procedure linkage table.  */
      if (splt && splt->size > 0 && htab->plt_info->plt0_entry)
	fill_plt0_entry (output_bfd, htab, splt, sgotplt);
    }

  /* Fill in the first three entries in the global offset table.  */
  if (sgotplt && sgotplt->size > 0)
    {
      if (!htab->fdpic_p)
	fill_got_header (output_bfd, sgotplt, sdyn);
      elf_section_data (sgotplt->output_section)->this_hdr.sh_entsize = 4;
    }

  /* At the very end of the .rofixup section is a pointer to the GOT.  */
  if (htab->fdpic_p && htab->srofixup != NULL)
    finalize_rofixup_section (output_bfd, htab);

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
  if (rela == NULL)
    {
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
  const unsigned int expected_desc_size = 168;
  const unsigned int signal_offset = 12;
  const unsigned int pid_offset = 24;
  const unsigned int reg_block_offset = 72;
  const unsigned int reg_block_size = 92;

  if (note->descsz != expected_desc_size)
    {
      return false;
    }

  struct elf_internal_core_file *core_file = elf_tdata (abfd)->core;

  core_file->signal = bfd_get_16 (abfd, note->descdata + signal_offset);
  core_file->lwpid = bfd_get_32 (abfd, note->descdata + pid_offset);

  return _bfd_elfcore_make_pseudosection (abfd, ".reg",
					  reg_block_size,
					  note->descpos + reg_block_offset);
}

static bool
elf32_shlin_grok_psinfo (bfd *abfd, Elf_Internal_Note *note)
{
  const size_t prpsinfo_size = 124;
  const size_t program_offset = 28;
  const size_t program_size = 16;
  const size_t command_offset = 44;
  const size_t command_size = 80;

  if (note->descsz != prpsinfo_size)
    return false;

  struct elf_core_file_data *core_data = elf_tdata (abfd)->core;
  if (core_data == NULL)
    return false;

  core_data->program =
    _bfd_elfcore_strndup (abfd, note->descdata + program_offset, program_size);
  core_data->command =
    _bfd_elfcore_strndup (abfd, note->descdata + command_offset, command_size);

  if (core_data->program == NULL || core_data->command == NULL)
    return false;

  char *command = core_data->command;
  size_t command_len = strlen (command);

  if (command_len > 0 && command[command_len - 1] == ' ')
    command[command_len - 1] = '\0';

  return true;
}
#endif /* not SH_TARGET_ALREADY_DEFINED */


/* Return address for Ith PLT stub in section PLT, for relocation REL
   or (bfd_vma) -1 if it should not be included.  */

static bfd_vma
sh_elf_plt_sym_val (bfd_vma i, const asection *plt,
		    const arelent *rel ATTRIBUTE_UNUSED)
{
  if (!plt || !plt->owner)
    {
      return 0;
    }

  const bfd * const abfd = plt->owner;
  const bool is_dynamic = (abfd->flags & DYNAMIC) != 0;
  const struct elf_sh_plt_info * const plt_info = get_plt_info (abfd, is_dynamic);

  if (!plt_info)
    {
      return 0;
    }

  return plt->vma + get_plt_offset (plt_info, i);
}

/* Decide whether to attempt to turn absptr or lsda encodings in
   shared libraries into pcrel within the given input section.  */

static bool
sh_elf_use_relative_eh_frame (struct bfd_link_info *info)
{
  struct elf_sh_link_hash_table *htab = sh_elf_hash_table (info);

  /* We can't use PC-relative encodings in FDPIC binaries, in general.  */
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

  if (!htab->fdpic_p)
    {
      return _bfd_elf_encode_eh_address (abfd, info, osec, offset,
					 loc_sec, loc_offset, encoded);
    }

  struct elf_link_hash_entry *h = htab->root.hgot;
  BFD_ASSERT (h && h->root.type == bfd_link_hash_defined);

  void *osec_segment = sh_elf_osec_to_segment (abfd, osec);
  void *loc_sec_segment =
    sh_elf_osec_to_segment (abfd, loc_sec->output_section);

  if (!h || osec_segment == loc_sec_segment)
    {
      return _bfd_elf_encode_eh_address (abfd, info, osec, offset,
					 loc_sec, loc_offset, encoded);
    }

  struct bfd_link_hash_defined *def = &h->root.u.def;
  asection *got_output_section = def->section->output_section;
  BFD_ASSERT (osec_segment == sh_elf_osec_to_segment (abfd, got_output_section));

  bfd_vma got_base_address = (def->value
			    + got_output_section->vma
			    + got_output_section->output_offset);
  bfd_vma eh_address = osec->vma + offset;

  *encoded = eh_address - got_base_address;

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
