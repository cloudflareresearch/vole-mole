test_deps = [vole_mole_dep, faest_dep]
test_inc = include_directories('.', '../src')

if get_option('tests')
  gtest_dep = dependency('gtest_main', default_options : ['warning_level=0']).as_system()

  tests = [
    ['act-issue', 'act/test_issue.cpp'],
    ['act-spend', 'act/test_spend.cpp'],
    ['act', 'act/test_act.cpp'],
    ['ihat-issue', 'ihat/test_issue.cpp'],
    ['unbound-ihat-issue', 'ihat/test_unbound_issue.cpp'],
    ['ihat-redeem', 'ihat/test_redeem.cpp'],
    ['unbound-ihat-redeem', 'ihat/test_unbound_redeem.cpp'],
    ['ihat', 'ihat/test_ihat.cpp'],
    ['unbound-ihat', 'ihat/test_unbound_ihat.cpp'],
    ['keccak', 'keccak/test_keccak.cpp'],
    ['pomfrit', 'pomfrit/test_pomfrit.cpp'],
    ['poly2d', 'poly2d/test_poly2d.cpp'],
    ['random', 'random/test_random.cpp'],
    ['uov', 'uov/test_uov.cpp'],
    ['voleith', 'voleith/test_voleith.cpp'],
  ]

  # Test data files (e.g., known answers) are read from the source tree; see `data_path` in
  # keccak/test_keccak.cpp, ihat/test_ihat.cpp, ihat/test_unbound_ihat.cpp, and act/test_act.cpp.
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

  # Run explicitly to regenerate VOLE-IHAT and VOLE-ACT known answers, never as part of the test
  # suite.
  foreach g : [['act', 'act'], ['ihat', 'ihat'], ['ihat', 'unbound_ihat']]
    executable('gen_@0@_kat'.format(g[1]), '@0@/gen_@1@_kat.cpp'.format(g[0], g[1]),
      include_directories : test_inc,
      dependencies : test_deps,
    )
  endforeach
endif

if get_option('benchmarks')
  benchmark_dep = dependency('benchmark_main',
    default_options : ['warning_level=0', 'tests=disabled'],
  ).as_system()

  benchmarks = [
    ['act', 'act/bench_act.cpp'],
    ['ihat', 'ihat/bench_ihat.cpp'],
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
endif
