foreach e : ['keys', 'pomfrit', 'ihat', 'unbound_ihat', 'act']
  exe = executable('example_' + e, e + '.cpp',
    dependencies : vole_mole_dep,
  )
  test('example-' + e.replace('_', '-'), exe, suite : 'examples', timeout : 300)
endforeach
