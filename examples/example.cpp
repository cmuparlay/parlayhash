#include <iostream>
#include <string>
#include "unordered_map.h"

using K = std::string;
using V = unsigned long;
using map_type = parlay::parlay_unordered_map<K,V>;

int main() {
  map_type my_map(100);
  my_map.Insert("sue", 1);
  my_map.Insert("sam", 5);

  std::cout << "value before increment: " << *my_map.Find("sue") << std::endl;
  auto increment = [] (std::optional<V> v) -> V {return v.has_value() ? 1 + *v : 1;};
  my_map.Upsert("sue", increment);
  std::cout << "new contents of map: " << std::endl;
  for (auto [k,v] : my_map) std::cout << k << ":" << v << std::endl;
  
  std::cout << "size before remove: " << my_map.size() << std::endl;
  my_map.Remove("sue");
  std::cout << "size after remove: " << my_map.size() << std::endl;
}
