//===- bolt/Core/AddressMap.h - Input-output address map --------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the declaration of the AddressMap class used for looking
// up addresses in the output object.
//
//===----------------------------------------------------------------------===//

#ifndef BOLT_CORE_ADDRESS_MAP_H
#define BOLT_CORE_ADDRESS_MAP_H

#include "llvm/MC/MCSymbol.h"

#include <optional>
#include <unordered_map>

namespace llvm {

class MCStreamer;

namespace bolt {

class BinaryContext;

/// Helper class to create a mapping from input entities to output addresses
/// needed for updating debugging symbols and BAT. We emit a section containing
/// <Input entity, Output MCSymbol> pairs to the object file and JITLink will
/// transform this in <Input entity, Output address> pairs. The linker output
/// can then be parsed and used to establish the mapping.
///
/// The entities that can be mapped to output address are input addresses and
/// labels (MCSymbol). Input addresses support one-to-many mapping.

// 映射点：记录输入/输出起点与各自跨度
struct IOMappingPoint {
  uint64_t InputAddr;     // 原始指令起始地址（绝对地址）
  uint64_t OutputAddr;    // 输出指令起始地址（绝对地址）
  uint32_t InputSpan;     // 原始指令大小（字节）
  uint32_t OutputSpan;    // 输出指令大小（字节）

  bool operator<(const IOMappingPoint &Other) const {
    return InputAddr < Other.InputAddr;
  }
};

class AddressMap {
  static const char *const AddressSectionName;
  static const char *const LabelSectionName;

  // 按 InputAddr 升序排列，不允许重叠。
  std::vector<IOMappingPoint> Points;
  bool Finalized{false};

  /// Map multiple <input address> to <output address>.
  using Addr2AddrMapTy = std::unordered_multimap<uint64_t, uint64_t>;
  Addr2AddrMapTy Address2AddressMap;

  /// Map MCSymbol to its output address. Normally used for temp symbols that
  /// are not updated by the linker.
  using Label2AddrMapTy = DenseMap<const MCSymbol *, uint64_t>;
  Label2AddrMapTy Label2AddrMap;

public:
  static void emit(MCStreamer &Streamer, BinaryContext &BC);
  static std::optional<AddressMap> parse(BinaryContext &BC);

  void clear() {
    Points.clear();
    Finalized = false;
  }
  // 添加映射点。允许同一个输入地址多次 add（例如多份副本），由策略决定最后保留哪一个。
  void addPoint(uint64_t InputAddr, uint64_t OutputAddr, uint32_t InputSpan, uint32_t OutputSpan) {
    if (Finalized)
      Finalized = false;
    Points.push_back({InputAddr, OutputAddr, InputSpan, OutputSpan});
  }
  // 若存在重复输入地址，按策略去重（默认：选择输出地址最小者或热度最高者，下面先选最小者）。
  // 然后按输入地址排序并去重。
  void finalize() {
    if (Finalized)
      return;

    std::sort(Points.begin(), Points.end(),
              [](const IOMappingPoint &A, const IOMappingPoint &B) {
                if (A.InputAddr != B.InputAddr) return A.InputAddr < B.InputAddr;
                // 简单策略：同一输入地址，取输出地址更小的条目（可换为热度策略）
                if (A.OutputAddr != B.OutputAddr) return A.OutputAddr < B.OutputAddr;
                return A.InputSpan < B.InputSpan;
              });

    // 去重，保留首个（根据上面排序策略）
    std::vector<IOMappingPoint> Unique;
    Unique.reserve(Points.size());
    for (const auto &P : Points) {
      if (!Unique.empty() && Unique.back().InputAddr == P.InputAddr)
        continue;
      Unique.push_back(P);
    }
    Points.swap(Unique);
    Finalized = true;
  }

  // 精确查找输入地址的映射点（指令起点），不存在返回空。
  std::optional<IOMappingPoint> lookupExact(uint64_t InputAddr) const {
    if (Points.empty()) return std::nullopt;
    auto It = std::lower_bound(Points.begin(), Points.end(), IOMappingPoint{InputAddr,0,0,0});
    if (It != Points.end() && It->InputAddr == InputAddr) return *It;
    return std::nullopt;
  }

  // 近似翻译：找到最近的“起点<=In”的映射点，若 In 落在该原始指令的 InputSpan 内，
  // 则用“起点常量偏移”进行映射，并夹到输出指令范围内。
  // 这比“基本块线性平移”细粒度得多，且仅在“指令内部”使用线性偏移。
  std::optional<uint64_t> translate(uint64_t InputAddr) const {
    if (Points.empty()) return std::nullopt;
    auto It = std::upper_bound(
        Points.begin(), Points.end(), IOMappingPoint{InputAddr,0,0,0},
        [](const IOMappingPoint &Key, const IOMappingPoint &Val) {
          return Key.InputAddr < Val.InputAddr;
        });
    if (It == Points.begin())
      return std::nullopt;
    --It; // now It->InputAddr <= In
    const auto &P = *It;
    const uint64_t DeltaIn = InputAddr - P.InputAddr;
    if (DeltaIn >= P.InputSpan)
      return std::nullopt; // 落在指令之间，保守返回空（可选择退回基本块线性映射）

    const uint64_t Out = P.OutputAddr + std::min<uint64_t>(DeltaIn, P.OutputSpan ? (P.OutputSpan - 1) : 0);
    // 为避免落到输出指令之外，做一次 clamp（允许最后一个字节内）
    return std::min<uint64_t>(Out, P.OutputAddr + (P.OutputSpan ? (P.OutputSpan - 1) : 0));
  }

  const std::vector<IOMappingPoint> &data() const { return Points; }

  std::optional<uint64_t> lookup(uint64_t InputAddress) const {
    auto It = Address2AddressMap.find(InputAddress);
    if (It != Address2AddressMap.end())
      return It->second;
    return std::nullopt;
  }

  std::optional<uint64_t> lookup(const MCSymbol *Symbol) const {
    auto It = Label2AddrMap.find(Symbol);
    if (It != Label2AddrMap.end())
      return It->second;
    return std::nullopt;
  }

  std::pair<Addr2AddrMapTy::const_iterator, Addr2AddrMapTy::const_iterator>
  lookupAll(uint64_t InputAddress) const {
    return Address2AddressMap.equal_range(InputAddress);
  }
};

} // namespace bolt
} // namespace llvm

#endif
