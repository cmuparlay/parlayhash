load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

#http_archive(
#    name = "parlaylib",
#    sha256 = "56965552ff3a97b0e499614dc15877275f87069d47842d1318e52491176cf35f",
#    strip_prefix = "parlaylib-bazel_v2/include/",
#    urls = ["https://github.com/cmuparlay/parlaylib/archive/refs/heads/master.zip"],
#)

git_repository(
    name = "parlaylib",
    branch = "bazel_v2",
    strip_prefix = "include/",
    remote = "https://github.com/cmuparlay/parlaylib",
)
