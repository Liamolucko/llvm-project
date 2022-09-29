//===- Cabi.h ---------------------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLD_WASM_CABI_H
#define LLD_WASM_CABI_H

#include "llvm/Object/Wasm.h"

namespace lld {
namespace wasm {
namespace cabi {

/// A kind of `LoweredType`.
enum class LoweredTypeKind {
  U8,
  U16,
  U32,
  S8,
  S16,
  S32,
  // We don't care about the signedness of this, because we'll only ever have
  // to go between an `i64` in memory and an `i64` wasm value.
  // The signedness of the others matters because it determines whether they
  // get sign-extended when they're loaded from memory into a larger wasm value.
  I64,
  Float32,
  Float64,
  Union,
};

/// A lowered interface type.
///
/// This represents the smallest encoded chunk a type can have.
/// It's either a scalar or a union of multiple lists of `LoweredType`s.
struct LoweredType {
  LoweredTypeKind kind;

  // Although we can derive alignment from `LoweredTypeKind`, this is here
  // so that we can artificially increase the alignment of types.
  // This is used to flatten out records into the `LoweredType`s of their
  // fields; the alignment of a record is the maximum alignment of its fields,
  // so to get the layout right we increase the alignment of the first field
  // to the aligment of the record.
  //
  // Encoded as the exponent of a power of two.
  uint8_t alignment;

  // If this is a `Union`, the cases of the `Union`.
  // Otherwise, this is empty.
  llvm::SmallVector<std::vector<LoweredType>, 0> cases;

  /// Make an `InterfaceType` from an `InterfaceTypeKind`, with no cases and
  /// default alignment.
  LoweredType(LoweredTypeKind kind) {
    this->kind = kind;
    switch (kind) {
    case LoweredTypeKind::U8:
    case LoweredTypeKind::S8:
      // 2^0 = 1
      this->alignment = 0;
      break;
    case LoweredTypeKind::U16:
    case LoweredTypeKind::S16:
      this->alignment = 1;
      break;
    case LoweredTypeKind::U32:
    case LoweredTypeKind::S32:
    case LoweredTypeKind::Float32:
      this->alignment = 2;
      break;
    case LoweredTypeKind::I64:
    case LoweredTypeKind::Float64:
      this->alignment = 3;
      break;
    case LoweredTypeKind::Union:
      // Start this off as the minimum; it'll be increased as cases
      // with higher alignment are added.
      this->alignment = 0;
      break;
    }
  }
};

/// A list of interface types.
class InterfaceTypeList {
private:
  std::vector<LoweredType> members;

  void addFlatType(size_t index, llvm::wasm::ValType ty);
  size_t computeFlatTypes(size_t startIndex, std::vector<LoweredType> &types);
  size_t computeUnionFlatTypes(size_t startIndex, LoweredType &ty);

public:
  /// Parse an `InterfaceTypeList` from a param or result list.
  static llvm::Optional<InterfaceTypeList> parse(llvm::StringRef s);

  /// The flattened representation of this list of interface types.
  llvm::SmallVector<llvm::wasm::ValType, 16> flatTypes;

  /// Write out instructions to load this list of interface types onto the
  /// stack as flat types.
  ///
  /// `ptr` is the index of the local holding the pointer to load from.
  /// `offset` is the offset from that pointer at which the load should occur.
  void writeLoad(uint32_t ptr, uint32_t offset);

  /// Write out instructions to store this list of interface types into memory
  /// from their corresponding flat types on the stack.
  ///
  /// `ptr` is the index of the local holding the pointer to write to.
  /// `offset` is the offset from that pointer at which the write should occur.
  void writeStore(uint32_t ptr, uint32_t offset);
};

#define MAX_FLAT_PARAMS 16
#define MAX_FLAT_RESULTS 1

struct Signature {
  InterfaceTypeList params;
  InterfaceTypeList results;

  std::string paramsStr;
  std::string resultsStr;

  /// Parse a function signature, starting after the ':'.
  static llvm::Optional<Signature> parse(llvm::StringRef s);

  /// Returns whether the core wasm signature `sig` is the correct lowered
  /// version of this signature.
  // bool isLoweredSignatureCorrect(const WasmSignature *sig);

  const llvm::SmallVector<llvm::wasm::ValType, 16> &coreParams();
  const llvm::SmallVector<llvm::wasm::ValType, 16> &coreResults();
};

} // namespace cabi
} // namespace wasm
} // namespace lld

#endif