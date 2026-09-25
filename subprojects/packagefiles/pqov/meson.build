# Meson build for pqov, the reference and optimized implementations of UOV (uov-Ip-pkc).

project('pqov', 'c',
  license : 'CC0-1.0 OR Apache-2.0',
  meson_version : '>= 1.4.0',
  default_options : [
    'c_std=c99',
    'warning_level=3',
  ],
)

pqov_args = ['-D_UTILS_BUILTIN_', '-D_OV256_119_45', '-D_OV_PKC']

cpu_family = host_machine.cpu_family()
impl = get_option('impl')
if impl == 'auto'
  if cpu_family == 'aarch64'
    impl = 'neon'
  elif cpu_family == 'x86_64'
    impl = 'avx2'
  else
    impl = 'ref'
  endif
endif

ext_dirs = []
# Flags that are only needed to compile pqov itself.
private_args = []
if impl == 'ref'
  ext_dirs = ['src/ref']
elif impl == 'neon'
  ext_dirs = ['src/ref', 'src/amd64', 'src/neon']
  pqov_args += ['-D_BLAS_NEON_']
  private_args += ['-flax-vector-conversions']
  if host_machine.system() == 'darwin'
    # Apple silicon has the AES instructions.
    pqov_args += ['-D_APPLE_SILICON_']
    ext_dirs += ['utils/neon_aesinst']
    private_args += ['-march=armv8-a+crypto+aes']
  else
    # Bitsliced AES (src/config.h selects _UTILS_NEONBSAES_).
    ext_dirs += ['utils/neon_aesffs']
    private_args += ['-march=armv8-a']
  endif
elif impl == 'avx2'
  ext_dirs = ['src/ref', 'src/amd64', 'src/ssse3', 'src/avx2', 'utils/x86aesni']
  pqov_args += ['-D_BLAS_AVX2_', '-D_MUL_WITH_MULTAB_', '-D_UTILS_AESNI_']
  private_args += ['-mavx2', '-maes']
else
  error('Unsupported pqov implementation: ' + impl)
endif

ext_sources = {
  'src/ref' : ['blas_matrix_ref.c'],
  'src/amd64' : [],
  'src/ssse3' : ['blas_matrix_sse.c', 'gf16_tabs.c'],
  'src/avx2' : ['blas_matrix_avx2.c', 'gf256_tabs.c'],
  'src/neon' : ['blas_matrix_neon.c', 'gf16_tabs_neon.c'],
  'utils/neon_aesinst' : ['aes_neonaes.c'],
  'utils/neon_aesffs' : ['neon_aesffs.c'],
  'utils/x86aesni' : ['x86aesni.c'],
}

pqov_sources = files(
  'src/blas_matrix.c',
  'src/ov.c',
  'src/ov_keypair.c',
  'src/ov_keypair_computation.c',
  'src/ov_publicmap.c',
  'src/parallel_matrix_op.c',
  'utils/aes128_4r_ffs.c',
  'utils/fips202.c',
  'utils/utils_hash.c',
  'utils/utils_prng.c',
  'utils/utils_randombytes.c',
)
foreach d : ext_dirs
  foreach f : ext_sources[d]
    pqov_sources += files(d / f)
  endforeach
endforeach

pqov_inc = include_directories(['src', 'utils'] + ext_dirs)

pqov_lib = static_library('pqov', pqov_sources,
  include_directories : pqov_inc,
  c_args : pqov_args + private_args,
)

pqov_dep = declare_dependency(
  link_with : pqov_lib,
  include_directories : include_directories('src'),
  compile_args : pqov_args,
)
