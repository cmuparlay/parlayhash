licenses(["notice"])

package(
    default_visibility = ["//visibility:public"],
)

cc_library(
    name = "epoch",
    hdrs = ["epoch.h"],
    deps = [
        "//include/utils/threads:thread_specific",
        "@parlaylib//parlay:alloc",
    ],
)

cc_library(
    name = "lock",
    hdrs = ["lock.h"],
    deps = [],
)

cc_library(
    name = "thread_specific",
    hdrs = ["thread_specific.h"],
    deps = [
        "//include/utils/threads:portability",
        "//include/utils/threads:thread_id_pool",
        "//include/utils/threads:type_traits",
    ],
)
