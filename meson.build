project('vole-mole', ['c', 'cpp'],
  version : '0.1.0',
  license : 'BSD-3-Clause',
  license_files : 'LICENSE',
  meson_version : '>= 1.4.0',
  default_options : [
    'cpp_std=c++23',
    'c_std=c23',
    'warning_level=3',
    'b_ndebug=if-release',
    'buildtype=debugoptimized',
  ],
)

# faest-arch-opt uses hardware AES/carry-less multiplication intrinsics in its headers, so any
# translation unit that includes them must be compiled for the same ISA.
cpu_family = host_machine.cpu_family()
if cpu_family == 'aarch64'
  arch_args = ['-march=armv8.2-a+crypto']
elif cpu_family == 'x86_64'
  arch_args = ['-march=native']
else
  error('Unsupported CPU family: ' + cpu_family)
endif
add_project_arguments(arch_args + ['-Wno-psabi'], language : ['c', 'cpp'])

faest_proj = subproject('faest-arch-opt')
faest_dep = faest_proj.get_variable('faest_dep').as_system()
randomness_dep = faest_proj.get_variable('randomness_os_dep')

pqov_proj = subproject('pqov')
pqov_dep = pqov_proj.get_variable('pqov_dep').as_system()

vole_mole_inc = include_directories('include')
vole_mole_src_inc = include_directories('src')

vole_mole_lib = static_library('vole-mole',
  'src/keccak/keccak.cpp',
  'src/moussaka/moussaka.cpp',
  'src/uov/uov.cpp',
  include_directories : [vole_mole_inc, vole_mole_src_inc],
  dependencies : [faest_dep, randomness_dep, pqov_dep],
)

vole_mole_dep = declare_dependency(
  link_with : vole_mole_lib,
  include_directories : vole_mole_inc,
)

subdir('tests')
