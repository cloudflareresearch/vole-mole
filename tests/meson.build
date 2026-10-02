test_deps = [vole_mole_dep, faest_dep]
test_inc = include_directories('.', '../src')

gtest_dep = dependency('gtest_main', default_options : ['warning_level=0']).as_system()

tests = [
  ['keccak', 'keccak/test_keccak.cpp'],
  ['moussaka-issue', 'moussaka/test_issue.cpp'],
  ['moussaka-redeem', 'moussaka/test_redeem.cpp'],
  ['moussaka', 'moussaka/test_moussaka.cpp'],
  ['pomfrit', 'pomfrit/test_pomfrit.cpp'],
  ['uov', 'uov/test_uov.cpp'],
  ['voleith', 'voleith/test_voleith.cpp'],
]

# Test data files (e.g., known answers) are read from the source tree; see `data_path` in
# keccak/test_keccak.cpp and moussaka/test_moussaka.cpp.
test_data_arg = '-DVOLE_MOLE_TEST_DATA_DIR="@0@"'.format(meson.current_source_dir())

foreach t : tests
  exe = executable('test_' + t[0].replace('-', '_'), t[1],
    include_directories : test_inc,
    dependencies : test_deps + [gtest_dep],
    cpp_args : test_data_arg,
  )
  # protocol 'gtest' lets Meson report the individual GoogleTest test cases.
  test(t[0], exe, protocol : 'gtest', timeout : 300)
endforeach

# Run explicitly to regenerate Moussaka known answers, never as part of the test suite.
executable('gen_moussaka_kat', 'moussaka/gen_moussaka_kat.cpp',
  include_directories : test_inc,
  dependencies : test_deps,
)

benchmark_dep = dependency('benchmark_main',
  default_options : ['warning_level=0', 'tests=disabled'],
).as_system()

benchmarks = [
  ['moussaka', 'moussaka/bench_moussaka.cpp'],
  ['pomfrit', 'pomfrit/bench_pomfrit.cpp'],
  ['uov', 'uov/bench_uov.cpp'],
]

foreach b : benchmarks
  exe = executable('bench_' + b[0], b[1],
    include_directories : test_inc,
    dependencies : test_deps + [benchmark_dep],
    # The BENCHMARK() macro uses __COUNTER__, which clang flags as an extension under -Wpedantic.
    cpp_args : meson.get_compiler('cpp').get_supported_arguments('-Wno-c2y-extensions'),
  )
  benchmark(b[0], exe, timeout : 600)
endforeach
