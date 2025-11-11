
#pragma once

#include <utility>

namespace parlay {

// A basic single-thread private linked list.  The values are required to expose a public next_ field.
template<typename NodeType>
class IntrusiveFreeList {
  using node_type = NodeType;
public:
  IntrusiveFreeList() : head(nullptr) {}

  void push(node_type* node) noexcept { node->next_ = std::exchange(head, node); }
  node_type* pop() noexcept {
    assert(!empty());
    return std::exchange(head, head->next_);
  }
  [[nodiscard]] bool empty() const noexcept { return head == nullptr; }

  template<typename F>
  void for_each(F&& f) {
    for (auto current = head; current != nullptr; current = current->next_) {
      f(current);
    }
  }

private:
  node_type* head;
};

}  // namespace parlay
