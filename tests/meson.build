test_deps = [vole_mole_dep, faest_dep]
test_inc = include_directories('.', '../src')

if get_option('tests')
  gtest_dep = dependency('gtest_main', default_options : ['warning_level=0']).as_system()

  tests = [
    ['keccak', 'keccak/test_keccak.cpp'],
    ['moussaka-issue', 'moussaka/test_issue.cpp'],
    ['moussaka-redeem', 'moussaka/test_redeem.cpp'],
    ['moussaka', 'moussaka/test_moussaka.cpp'],
    ['pomfrit', 'pomfrit/test_pomfrit.cpp'],
    ['poly2d', 'poly2d/test_poly2d.cpp'],
    ['random', 'random/test_random.cpp'],
    ['ratatouille-issue', 'ratatouille/test_issue.cpp'],
    ['ratatouille-spend', 'ratatouille/test_spend.cpp'],
    ['ratatouille', 'ratatouille/test_ratatouille.cpp'],
    ['uov', 'uov/test_uov.cpp'],
    ['voleith', 'voleith/test_voleith.cpp'],
  ]

  # Test data files (e.g., known answers) are read from the source tree; see `data_path` in
  # keccak/test_keccak.cpp, moussaka/test_moussaka.cpp, and ratatouille/test_ratatouille.cpp.
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

  # Run explicitly to regenerate Moussaka and Ratatouille known answers, never as part of the test
  # suite.
  foreach g : ['moussaka', 'ratatouille']
    executable('gen_@0@_kat'.format(g), '@0@/gen_@0@_kat.cpp'.format(g),
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
    ['moussaka', 'moussaka/bench_moussaka.cpp'],
    ['pomfrit', 'pomfrit/bench_pomfrit.cpp'],
    ['ratatouille', 'ratatouille/bench_ratatouille.cpp'],
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
