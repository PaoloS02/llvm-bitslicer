//===- Binary.cpp - A generic binary file ---------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the Binary class.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/StringRef.h"
#include "llvm/Object/Archive.h"
#include "llvm/Object/Binary.h"
#include "llvm/Object/Error.h"
#include "llvm/Object/MachOUniversal.h"
#include "llvm/Object/ObjectFile.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/ErrorOr.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include <algorithm>
#include <memory>
#include <system_error>

using namespace llvm;
using namespace object;

Binary::~Binary() = default;

Binary::Binary(unsigned int Type, MemoryBufferRef Source)
    : TypeID(Type), Data(Source) {}

StringRef Binary::getData() const { return Data.getBuffer(); }

StringRef Binary::getFileName() const { return Data.getBufferIdentifier(); }

MemoryBufferRef Binary::getMemoryBufferRef() const { return Data; }

Expected<std::unique_ptr<Binary>> object::createBinary(MemoryBufferRef Buffer,
                                                      LLVMContext *Context) {
  sys::fs::file_magic Type = sys::fs::identify_magic(Buffer.getBuffer());

  switch (Type) {
    case sys::fs::file_magic::archive:
      return Archive::create(Buffer);
    case sys::fs::file_magic::elf:
    case sys::fs::file_magic::elf_relocatable:
    case sys::fs::file_magic::elf_executable:
    case sys::fs::file_magic::elf_shared_object:
    case sys::fs::file_magic::elf_core:
    case sys::fs::file_magic::macho_object:
    case sys::fs::file_magic::macho_executable:
    case sys::fs::file_magic::macho_fixed_virtual_memory_shared_lib:
    case sys::fs::file_magic::macho_core:
    case sys::fs::file_magic::macho_preload_executable:
    case sys::fs::file_magic::macho_dynamically_linked_shared_lib:
    case sys::fs::file_magic::macho_dynamic_linker:
    case sys::fs::file_magic::macho_bundle:
    case sys::fs::file_magic::macho_dynamically_linked_shared_lib_stub:
    case sys::fs::file_magic::macho_dsym_companion:
    case sys::fs::file_magic::macho_kext_bundle:
    case sys::fs::file_magic::coff_object:
    case sys::fs::file_magic::coff_import_library:
    case sys::fs::file_magic::pecoff_executable:
    case sys::fs::file_magic::bitcode:
    case sys::fs::file_magic::wasm_object:
      return ObjectFile::createSymbolicFile(Buffer, Type, Context);
    case sys::fs::file_magic::macho_universal_binary:
      return MachOUniversalBinary::create(Buffer);
    case sys::fs::file_magic::unknown:
    case sys::fs::file_magic::coff_cl_gl_object:
    case sys::fs::file_magic::windows_resource:
      // Unrecognized object file format.
      return errorCodeToError(object_error::invalid_file_type);
  }
  llvm_unreachable("Unexpected Binary File Type");
}

Expected<OwningBinary<Binary>> object::createBinary(StringRef Path) {
  ErrorOr<std::unique_ptr<MemoryBuffer>> FileOrErr =
      MemoryBuffer::getFileOrSTDIN(Path);
  if (std::error_code EC = FileOrErr.getError())
    return errorCodeToError(EC);
  std::unique_ptr<MemoryBuffer> &Buffer = FileOrErr.get();

  Expected<std::unique_ptr<Binary>> BinOrErr =
      createBinary(Buffer->getMemBufferRef());
  if (!BinOrErr)
    return BinOrErr.takeError();
  std::unique_ptr<Binary> &Bin = BinOrErr.get();

  return OwningBinary<Binary>(std::move(Bin), std::move(Buffer));
}