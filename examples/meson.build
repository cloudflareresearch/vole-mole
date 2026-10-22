foreach e : ['keys', 'pomfrit', 'moussaka', 'unbound_moussaka', 'ratatouille']
  exe = executable('example_' + e, e + '.cpp',
    dependencies : vole_mole_dep,
  )
  test('example-' + e.replace('_', '-'), exe, suite : 'examples', timeout : 300)
endforeach
