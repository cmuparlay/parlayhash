licenses(["notice"])

package(
    default_visibility = ["//visibility:public"],
)

cc_library(
    name = "portability",
    hdrs = ["portability.h"],
    deps = [
    ],
)

cc_library(
    name = "thread_id_pool",
    hdrs = ["thread_id_pool.h"],
    deps = [],
)

cc_library(
    name = "thread_specific",
    hdrs = ["thread_specific.h"],
    deps = [
        ":portability",
        ":type_traits",
        ":thread_id_pool",
    ],
)

cc_library(
    name = "type_traits",
    hdrs = ["type_traits.h"],
    deps = [],
)
