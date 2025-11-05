#include <cstdint>
#include <unordered_map>
#include "llvm/MC/MCInst.h"

namespace llvm {

namespace bolt {

// 为每条 MCInst 存原始指令的“输入起点地址/大小”注解。
// 实现为侧表，避免改动 MCInst 本体。
struct InstInputAnno {
  uint64_t InputAddr{0};
  uint32_t InputSpan{0};
  bool has() const { return InputSpan != 0; }
};

class InstructionAnnotations {
  // 注意：指针作为 key 依赖 MCInst 生命周期在发射前有效
  std::unordered_map<const MCInst*, InstInputAnno> Map;

public:
  void set(const MCInst *I, uint64_t InputAddr, uint32_t InputSpan) {
    Map[I] = {InputAddr, InputSpan};
  }
  InstInputAnno get(const MCInst *I) const {
    auto It = Map.find(I);
    return (It == Map.end()) ? InstInputAnno{} : It->second;
  }
  void erase(const MCInst *I) { Map.erase(I); }
  void clear() { Map.clear(); }
};

} // namespace bolt
} // namespace llvm