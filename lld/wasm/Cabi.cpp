//===- Cabi.h ---------------------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "Cabi.h"
#include "llvm/Support/ConvertUTF.h"
#include "llvm/Support/UnicodeCharRanges.h"
#include "llvm/Support/UnicodeXID.h"

namespace lld {
namespace wasm {
namespace cabi {

using namespace llvm;
using namespace llvm::wasm;

#define WIT_WHITESPACE " \n\r\t"

/// Consume whitespace from `s`.
void consumeWhitespace(StringRef &s) { s = s.ltrim(WIT_WHITESPACE); }

/// Attempts to consume a WIT identifier from `s`, and returns a boolean of
/// whether an identifier was consumed.
///
/// This doesn't fully validate the identifier, though.
/// TODO: maybe do that.
bool consumeIdent(StringRef &s) {
  consumeWhitespace(s);

  static const llvm::sys::UnicodeCharSet XIDStartChars(XIDStartRanges);
  static const llvm::sys::UnicodeCharSet XIDContinueChars(XIDContinueRanges);

  auto ptr = s.bytes_begin();
  bool start = true;
  while (true) {
    UTF32 codePoint;
    // Read a code point from the string.
    auto result =
        convertUTF8Sequence(&ptr, s.bytes_end(), &codePoint, strictConversion);
    if (result != conversionOK) {
      return false;
    }

    if (XIDStartChars.contains(codePoint) ||
        (!start && XIDContinueChars.contains(codePoint))) {
      start = false;
    } else if (!start && codePoint == '-') {
      start = true;
    } else if (!start) {
      // It's the end of the identifier.
      // `start` has to be false because each 'part' must be at least one
      // character long.
      break;
    } else {
      // The first character of a part wasn't an `XID_Start` character, so this
      // is invalid.
      return false;
    }
  }

  s = StringRef((const char *)ptr, s.bytes_end() - ptr);
  return true;
}

/// Attempts to consume `target` from the front of `s`, returning whether it was
/// there. Also consumes any whitespace prior to `target`.
bool consume(StringRef &s, StringRef target) {
  consumeWhitespace(s);
  return s.consume_front(target);
}

/// Returns the alignment of a list of lowered types, aka the maximum of the
/// alignments of all the individual types.
uint8_t alignment(std::vector<LoweredType> &types) {
  uint8_t result = 0;
  for (LoweredType &ty : types) {
    if (ty.alignment > result) {
      result = ty.alignment;
    }
  }
  return result;
}

bool parseType(std::vector<LoweredType> &out, StringRef &s,
               bool optional = false) {
  if (consume(s, "u8") || consume(s, "bool")) {
    out.push_back(LoweredType(LoweredTypeKind::U8));
  } else if (consume(s, "s8")) {
    out.push_back(LoweredType(LoweredTypeKind::S8));
  } else if (consume(s, "u16")) {
    out.push_back(LoweredType(LoweredTypeKind::U16));
  } else if (consume(s, "s16")) {
    out.push_back(LoweredType(LoweredTypeKind::S16));
  } else if (consume(s, "u32") || consume(s, "char")) {
    out.push_back(LoweredType(LoweredTypeKind::U32));
  } else if (consume(s, "s32")) {
    out.push_back(LoweredType(LoweredTypeKind::S32));
  } else if (consume(s, "u64") || consume(s, "s64")) {
    out.push_back(LoweredType(LoweredTypeKind::I64));
  } else if (consume(s, "float32")) {
    out.push_back(LoweredType(LoweredTypeKind::I64));
  } else if (consume(s, "float64")) {
    out.push_back(LoweredType(LoweredTypeKind::I64));
  } else if (consume(s, "string")) {
    // Strings are ptr + len pairs.
    out.push_back(LoweredType(LoweredTypeKind::U32));
    out.push_back(LoweredType(LoweredTypeKind::U32));
  } else if (consume(s, "list")) {
    // So are lists.
    out.push_back(LoweredType(LoweredTypeKind::U32));
    out.push_back(LoweredType(LoweredTypeKind::U32));

    if (!consume(s, "<")) {
      return false;
    }

    // We don't care about the type of list, but we still want to validate it.
    // So, make a dummy list of `InterfaceType`s to parse it into.
    std::vector<LoweredType> dummy;
    if (!parseType(dummy, s)) {
      return false;
    }

    if (!consume(s, ">")) {
      return false;
    }
  } else if (consume(s, "option")) {
    // Options are desugared to variants, which we desugar to unions.
    LoweredType ty = LoweredType(LoweredTypeKind::Union);
    ty.cases = {{}, {}};

    if (!consume(s, "<")) {
      return false;
    }

    // The `some` case is the second case.
    if (!parseType(ty.cases[1], s)) {
      return false;
    }

    if (!consume(s, ">")) {
      return false;
    }

    // The alignment of an `option` is the alignment of its payload.
    ty.alignment = alignment(ty.cases[1]);

    out.push_back(ty);
  } else if (consume(s, "result")) {
    // Options are desugared to variants, which we desugar to unions.
    LoweredType ty = LoweredType(LoweredTypeKind::Union);
    ty.cases = {{}, {}};

    if (consume(s, "<")) {
      // Parse the `ok` type.
      // WIT is a bit more strict about when this is optional; it's only
      // supposed to be optional if an `err` payload is specified, but that's
      // not adhered to by the canonical ABI as currently spec'd so be a bit
      // looser with parsing.
      if (!parseType(ty.cases[0], s, optional = true)) {
        return false;
      }

      auto align = alignment(ty.cases[0]);
      if (align > ty.alignment) {
        ty.alignment = align;
      }

      if (consume(s, ",")) {
        // Parse the `err` type.
        if (!parseType(ty.cases[1], s, optional = true)) {
          return false;
        }

        auto align = alignment(ty.cases[1]);
        if (align > ty.alignment) {
          ty.alignment = align;
        }

        if (!consume(s, ">")) {
          return false;
        }
      }
      // If there's only one type specified, that means there's no `err`
      // payload, so we don't have to do anything more.
    }
    // If there's no leading `<`, it's a result with no `ok` nor `err` payload.
    // That's already what we initialised the cases to, so we don't have to do
    // anything more.

    out.push_back(ty);
  } else if (consume(s, "tuple")) {
    if (!consume(s, "<")) {
      return false;
    }

    // The index of the first lowered type of this type.
    size_t firstIndex = out.size();

    while (!consume(s, ">")) {
      if (!parseType(out, s)) {
        return false;
      }

      if (!consume(s, ",")) {
        // If there's no comma, this has to be the end of the tuple.
        if (!consume(s, ">")) {
          return false;
        }
        break;
      }
    }

    // Artificially increase the alignment of the first element to the
    // alignment of the tuple, which is the maximum alignment of its fields.
    for (size_t i = firstIndex + 1; i < out.size(); i++) {
      if (out[i].alignment > out[firstIndex].alignment) {
        out[firstIndex].alignment = out[i].alignment;
      }
    }
  } else if (consume(s, "record")) {
    if (!consume(s, "{")) {
      return false;
    }

    // The index of the first lowered type of this type.
    size_t firstIndex = out.size();

    while (!consume(s, "}")) {
      // Consume the field's name.
      if (!consumeIdent(s)) {
        return false;
      }

      if (!consume(s, ":")) {
        return false;
      }

      // Parse the field's type.
      if (!parseType(out, s)) {
        return false;
      }

      if (!consume(s, ",")) {
        // If there's no comma, this has to be the end of the record.
        if (!consume(s, "}")) {
          return false;
        }
        break;
      }
    }

    // Artificially increase the alignment of the first element to the
    // alignment of the record, which is the maximum alignment of its fields.
    for (size_t i = firstIndex + 1; i < out.size(); i++) {
      if (out[i].alignment > out[firstIndex].alignment) {
        out[firstIndex].alignment = out[i].alignment;
      }
    }
  } else if (consume(s, "flags")) {
    // We only care about the number of flags.
    uint numFlags = 0;

    if (!consume(s, "{")) {
      return false;
    }

    while (!consume(s, "}")) {
      if (!consumeIdent(s)) {
        return false;
      }

      numFlags += 1;

      if (!consume(s, ",")) {
        // This has to be the end of the `flags`.
        if (!consume(s, "}")) {
          return false;
        }
        break;
      }
    }

    if (numFlags == 0) {
      // Do nothing; a `flags` with 0 flags is ignored.
    } else if (numFlags <= 8) {
      out.push_back(LoweredType(LoweredTypeKind::U8));
    } else if (numFlags <= 16) {
      out.push_back(LoweredType(LoweredTypeKind::U16));
    } else {
      // The number of bits we've added for the flags thus far.
      uint bits = 0;
      while (bits < numFlags) {
        out.push_back(LoweredType(LoweredTypeKind::U32));
        bits += 32;
      }
    }
  } else if (consume(s, "variant")) {
    // TODO: variants with 0 cases are illegal

    if (!consume(s, "{")) {
      return false;
    }

    LoweredType ty = LoweredType(LoweredTypeKind::Union);

    while (!consume(s, "}")) {
      // Consume the name of the case.
      if (!consumeIdent(s)) {
        return false;
      }
      ty.cases.push_back({});
      if (consume(s, "(")) {
        // The variant has a payload.
        // Consume the payload type.
        // TODO: This shouldn't be optional according to WIT, but the Canonical
        // ABI is currently spec'd to emit it that way.
        // See https://github.com/WebAssembly/component-model/issues/86.
        if (!parseType(ty.cases.back(), s, optional = true)) {
          return false;
        }

        // Increase the alignment of the union to the alignment of the type we
        // just added, if it's higher that the alignment so far.
        auto align = alignment(ty.cases.back());
        if (align > ty.alignment) {
          ty.alignment = align;
        }

        if (!consume(s, ")")) {
          return false;
        }
      }

      if (!consume(s, ",")) {
        // If there's no comma, it's the end of the `variant`.
        if (!consume(s, "}")) {
          return false;
        }
        break;
      }
    }

    out.push_back(ty);
  } else if (consume(s, "enum")) {
    if (!consume(s, "{")) {
      return false;
    }

    LoweredType ty = LoweredType(LoweredTypeKind::Union);

    while (!consume(s, "}")) {
      // Consume the name of the case.
      if (!consumeIdent(s)) {
        return false;
      }

      ty.cases.push_back({});

      if (!consume(s, ",")) {
        // If there's no comma, it's the end of the `enum`.
        if (!consume(s, "}")) {
          return false;
        }
        break;
      }
    }

    out.push_back(ty);
  } else if (consume(s, "union")) {
    if (!consume(s, "{")) {
      return false;
    }

    LoweredType ty = LoweredType(LoweredTypeKind::Union);

    while (!consume(s, "}")) {
      ty.cases.push_back({});

      // Consume the case's type.
      if (!parseType(ty.cases.back(), s, optional = true)) {
        return false;
      }

      // Increase the alignment of the union to the alignment of the type we
      // just added, if it's higher that the alignment so far.
      auto align = alignment(ty.cases.back());
      if (align > ty.alignment) {
        ty.alignment = align;
      }

      if (!consume(s, ",")) {
        // If there's no comma, it's the end of the `union`.
        if (!consume(s, "}")) {
          return false;
        }
        break;
      }
    }

    out.push_back(ty);
  } else if (optional && consume(s, "_")) {
    // Do nothing; if there's no type, there's no lowered types.
  } else {
    return false;
  }

  return true;
}

Optional<InterfaceTypeList> InterfaceTypeList::parse(StringRef s) {
  InterfaceTypeList result;

  // Note: we intentionally don't allow unnamed params here because the only
  // place this is used is `cabi_start` parsing, where that's not allowed.
  if (!consume(s, "(")) {
    return None;
  }

  while (true) {
    // Consume the argument name.
    if (!consumeIdent(s)) {
      return None;
    }

    if (!consume(s, ":")) {
      return None;
    }

    // Parse the argument type.
    if (!parseType(result.members, s)) {
      return None;
    }

    if (!consume(s, ",")) {
      // If there's no comma, this is the end of the function.
      // Note that this differs from most other parts of WIT in that trailing
      // commas are not allowed.
      if (!consume(s, ")")) {
        return None;
      }
    }
  }

  // Compute the flat types of the type list.
  result.computeFlatTypes(0, result.members);

  return result;
}

/// Returns the flat type that should be used to represent both the flat types
/// `a` and `b` in different union cases.
ValType join(ValType a, ValType b) {
  if (a == b) {
    return a;
  } else if ((a == ValType::F32 && b == ValType::I32) ||
             (a == ValType::I32 && b == ValType::F32)) {
    return ValType::I32;
  } else {
    // The types aren't the same, and we've already checked that they aren't
    // `i32` and `f32`, therefore one of them must be 64-bit and we want `i64`.
    return ValType::I64;
  }
}

/// Adds `ty` to `this->flatTypes` at index `i`.
void InterfaceTypeList::addFlatType(size_t index, ValType ty) {
  if (index < this->flatTypes.size()) {
    this->flatTypes[index] = join(this->flatTypes[index], ty);
  } else {
    if (index != this->flatTypes.size()) {
      llvm_unreachable("should only be adding flat types to the end");
    }
    this->flatTypes.push_back(ty);
  }
}

/// Computes the flat types for a list of lowered types, adding them to
/// `this->flatTypes` starting at `startIndex`.
///
/// Returns the number of flat types that ended up representing the type list.
size_t InterfaceTypeList::computeFlatTypes(size_t startIndex,
                                           std::vector<LoweredType> &types) {
  size_t flatIndex = startIndex;
  for (auto &ty : types) {
    switch (ty.kind) {
    case LoweredTypeKind::U8:
    case LoweredTypeKind::U16:
    case LoweredTypeKind::U32:
    case LoweredTypeKind::S8:
    case LoweredTypeKind::S16:
    case LoweredTypeKind::S32:
      this->addFlatType(flatIndex, ValType::I32);
      flatIndex += 1;
      break;
    case LoweredTypeKind::I64:
      this->addFlatType(flatIndex, ValType::I64);
      flatIndex += 1;
      break;
    case LoweredTypeKind::Float32:
      this->addFlatType(flatIndex, ValType::F32);
      flatIndex += 1;
      break;
    case LoweredTypeKind::Float64:
      this->addFlatType(flatIndex, ValType::F64);
      flatIndex += 1;
      break;
    case LoweredTypeKind::Union:
      flatIndex += this->computeUnionFlatTypes(flatIndex, ty);
      break;
    }
  }

  return flatIndex - startIndex;
}

/// Compute the flat types for the union `ty` and put them into
/// `this->flatTypes` starting at `startIndex`.
///
/// Returns the number of flat types the union took up.
size_t InterfaceTypeList::computeUnionFlatTypes(size_t startIndex,
                                                LoweredType &ty) {
  size_t maxCaseSize = 0;

  // Add the discriminant.
  this->addFlatType(startIndex, ValType::I32);

  for (auto &types : ty.cases) {
    size_t caseSize = this->computeFlatTypes(startIndex + 1, types);
    if (caseSize > maxCaseSize) {
      maxCaseSize = caseSize;
    }
  }

  return 1 + maxCaseSize;
}

Optional<Signature> Signature::parse(StringRef s) {
  if (!consume(s, "func")) {
    return None;
  }

  auto [paramsStr, resultsStr] = s.split("->");

  Signature result;

  Optional<InterfaceTypeList> params = InterfaceTypeList::parse(paramsStr);
  if (!params.has_value()) {
    return None;
  }

  Optional<InterfaceTypeList> results = InterfaceTypeList::parse(resultsStr);
  if (!results.has_value()) {
    return None;
  }

  result.paramsStr = paramsStr.trim("() \n\r\t");
  result.resultsStr = resultsStr.trim("() \n\r\t");
  result.params = params.value();
  result.results = results.value();

  return result;
}

static const SmallVector<ValType, 16> ptrSig = {ValType::I32};

const SmallVector<ValType, 16> &Signature::coreParams() {
  if (this->params.flatTypes.size() > MAX_FLAT_PARAMS) {
    return ptrSig;
  } else {
    return this->params.flatTypes;
  }
}

const SmallVector<ValType, 16> &Signature::coreResults() {
  if (this->results.flatTypes.size() > MAX_FLAT_RESULTS) {
    return ptrSig;
  } else {
    return this->results.flatTypes;
  }
}

} // namespace cabi
} // namespace wasm
} // namespace lld
