# Do not explicitly specify '-fhpc' in extra_hc_opts, unless also setting
# '-hpcdir' to a different value for each test. Only the `hpc` way does this
# automatically. This way the tests in this directory can be run concurrently
# (Main.mix might overlap otherwise).

setTestOpts([only_compiler_types(['ghc']),
             only_ways(['hpc']),
             ])

def T2991(cmd):
  # The .mix file for the literate module should have non-zero entries.
  # The `grep` should exit with exit code 0.
  return(cmd + " && grep -q cover_me .hpc.T2991/T2991LiterateModule.mix")
test('T2991', [cmd_wrapper(T2991), extra_clean(['T2991LiterateModule.hi',
                                                'T2991LiterateModule.o'])],
              # Run with 'ghc --main'. Do not list other modules explicitly.
              multimod_compile_and_run, ['T2991', ''])
