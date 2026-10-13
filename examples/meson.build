foreach e : ['keys', 'pomfrit', 'moussaka', 'ratatouille', 'mlkem_pop']
  exe = executable('example_' + e, e + '.cpp',
    dependencies : vole_mole_dep,
  )
  test('example-' + e, exe, suite : 'examples', timeout : 300)
endforeach
