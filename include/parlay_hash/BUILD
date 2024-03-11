licenses(["notice"])

package(
    default_visibility = ["//visibility:public"],
)

package_group(
    name = "clients",
    packages = [
        # Add client packages here.
    ],
)

cc_library(
    name = "bigatomic",
    hdrs = ["bitatomic.h"],
    deps = [
      "@parlaylib//parlay:primitives",
      "@parlaylib//parlay:sequence",
      "@parlaylib//parlay:range",
      "//include/utils:lock"
    ],
)

cc_library(
    name = "parallel",
    hdrs = ["parallel.h"],
    deps = [
      "@parlaylib//parlay:delayed",
      "@parlaylib//parlay:primitives",
      "@parlaylib//parlay:sequence",
    ],
)

cc_library(
    name = "parlay_hash",
    hdrs = ["parlay_hash.h"],
    deps = [
      ":bigatomic",
      ":parallel",
      "@parlaylib//parlay:delayed",
      "@parlaylib//parlay:primitives",
      "@parlaylib//parlay:sequence",
      "//include/utils:epoch"
    ],
)

cc_library(
    name = "unordered_map",
    hdrs = ["unordered_map.h"],
    deps = [":parlay_hash"],
)

cc_library(
    name = "unordered_set",
    hdrs = ["unordered_set.h"],
    deps = [
      ":parlay_hash",
      "//include/utils:epoch"
    ],
)
