maps = [("parlay_hash", "./README.md"),
        ("tbb_hash", "https://spec.oneapi.io/versions/latest/elements/oneTBB/source/containers/concurrent_unordered_map_cls.html"),
        ("libcuckoo", "https://github.com/efficient/libcuckoo" ),
        ("folly_hash", "https://github.com/facebook/folly/blob/main/folly/concurrency/ConcurrentHashMap.h"),
        ("folly_sharded", "other/folly_sharded/unordered_map.h"),
        ("boost_hash", "https://www.boost.org/doc/libs/1_83_0/libs/unordered/doc/html/unordered.html#concurrent"),
        ("parallel_hashmap", "https://github.com/greg7mdp/parallel-hashmap"),
        ("seq_hash", "https://github.com/Thermadiag/seq/blob/main/docs/concurrent_map.md")
]

seq_maps = [("abseil", "https://abseil.io/docs/cpp/guides/container"),
            ("folly_F14", "https://engineering.fb.com/2019/04/25/developer-tools/f14/"),
            ("std_hash", "https://en.cppreference.com/w/cpp/container/unordered_map")
]

def t_float(float_number, decimal_places):
    if decimal_places == 0 :
        return str(int(round(float_number,0)))
    return str(round(float_number, decimal_places))

def get_nums(name, p) :
    filename = "../timings/" + name + "_" + str(p)
    with open(filename) as f:
        lines = [line.rstrip() for line in f]
    insert_mops = float(lines[len(lines)-3].split()[-1])
    exp_mops = float(lines[len(lines)-2].split()[-1])
    size_pe = float(lines[len(lines)-1].split()[-1])
    return [insert_mops, exp_mops, size_pe]

def gen_entry(val, ptr) :
    return "[" + val + "](" + ptr + ") | "

def ptr_name(name, p) :
    return "timings/" + name + "_" + str(p)

def gen_line(ht) :
    [name, url] = ht
    [im1, em1, s1] = get_nums(name, 1)
    [im16, em16, s16] = get_nums(name, 16)
    [im128, em128, s128] = get_nums(name, 128)
    x = [(name, url),
         (t_float(s1,1), ptr_name(name, 1)),
         (t_float(em1, 1), ptr_name(name, 1)),
         (t_float(em16,0), ptr_name(name, 16)),
         (t_float(em128,0),ptr_name(name, 128)),
         (t_float(im128,0),ptr_name(name, 128))]
    r = "| " + "".join([gen_entry(a[0],a[1]) for a in x]) + "\n"
    return r

def gen_line_1(ht) :
    [name, url] = ht
    fullname = name + " (sequential)"
    [im1, em1, s1] = get_nums(name, 1)
    x = [(fullname, url),
         (t_float(s1,1), ptr_name(name, 1)),
         (t_float(em1, 1), ptr_name(name, 1))]
    r = "| " + "".join([gen_entry(a[0],a[1]) for a in x]) + " --- | --- | --- |\n"
    return r

header = ["| Hash Map | Memory | 1 thread | 16 threads | 128 threads | 128 insert | \n",
          "| - | - | - | - | - | - | \n",
          "| - | bytes/elt | Mops/sec | Mops/sec | Mops/sec | Mops/sec | \n"]

def gen_lines() :
    file = open("../timings/timing_table",'w')
    lines = header + [gen_line(x) for x in maps] + [gen_line_1(x) for x in seq_maps]
    for l in lines: file.write(l)
    file.close()
    
