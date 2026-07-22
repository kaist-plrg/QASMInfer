QASM2 and QASM3 conversion is quiet, emits reparsable canonical QASM2, and is
stable when applied a second time.  The three invocations also cover the mode
option before, between, and after the two positional paths.

  $ qasminfer --unoptimize qasm2.qasm qasm2.once.qasm >qasm2.stdout 2>qasm2.stderr
  $ test ! -s qasm2.stdout
  $ test ! -s qasm2.stderr
  $ head -n 1 qasm2.once.qasm
  OPENQASM 2.0;
  $ qasminfer --unopt qasm2.qasm qasm2.alias.qasm >qasm2-alias.stdout 2>qasm2-alias.stderr
  $ test ! -s qasm2-alias.stdout
  $ test ! -s qasm2-alias.stderr
  $ cmp qasm2.once.qasm qasm2.alias.qasm
  $ qasminfer qasm2.once.qasm --unoptimize qasm2.twice.qasm >qasm2-twice.stdout 2>qasm2-twice.stderr
  $ test ! -s qasm2-twice.stdout
  $ test ! -s qasm2-twice.stderr
  $ cmp qasm2.once.qasm qasm2.twice.qasm
  $ cp qasm2.qasm qasm2.in-place.qasm
  $ chmod u+w qasm2.in-place.qasm
  $ qasminfer --unoptimize qasm2.in-place.qasm qasm2.in-place.qasm >in-place.stdout 2>in-place.stderr
  $ test ! -s in-place.stdout
  $ test ! -s in-place.stderr
  $ cmp qasm2.once.qasm qasm2.in-place.qasm

  $ qasminfer --json qasm2.qasm >qasm2-source.json 2>qasm2-source.stderr
  $ qasminfer --json qasm2.once.qasm >qasm2-generated.json 2>qasm2-generated.stderr
  $ test ! -s qasm2-source.stderr
  $ test ! -s qasm2-generated.stderr
  $ cmp qasm2-source.json qasm2-generated.json

  $ qasminfer qasm3.qasm qasm3.once.qasm --unoptimize >qasm3.stdout 2>qasm3.stderr
  $ test ! -s qasm3.stdout
  $ test ! -s qasm3.stderr
  $ head -n 1 qasm3.once.qasm
  OPENQASM 2.0;
  $ grep -F 'qreg qasm3_physical_1[1];' qasm3.once.qasm
  qreg qasm3_physical_1[1];
  $ grep -F '$' qasm3.once.qasm >/dev/null; test $? -ne 0
  $ qasminfer --unoptimize qasm3.once.qasm qasm3.twice.qasm >qasm3-twice.stdout 2>qasm3-twice.stderr
  $ test ! -s qasm3-twice.stdout
  $ test ! -s qasm3-twice.stderr
  $ cmp qasm3.once.qasm qasm3.twice.qasm

Verbose conversion diagnostics stay on stderr and do not contaminate either
stdout or the QASM destination.

  $ qasminfer --unoptimize qasm2.qasm verbose.qasm --verbose >verbose.stdout 2>verbose.stderr
  $ test ! -s verbose.stdout
  $ test -s verbose.stderr
  $ cmp qasm2.once.qasm verbose.qasm

Invalid path counts and execution-only output flags fail before creating a
destination.

  $ qasminfer --unoptimize qasm2.qasm >missing.stdout 2>missing.stderr
  [2]
  $ test ! -s missing.stdout
  $ head -n 1 missing.stderr
  --unoptimize expects exactly two positional arguments: SOURCE DESTINATION

  $ qasminfer --unoptimize qasm2.qasm extra.qasm unexpected.qasm >extra.stdout 2>extra.stderr
  [2]
  $ test ! -e extra.qasm
  $ test ! -s extra.stdout
  $ head -n 1 extra.stderr
  --unoptimize expects exactly two positional arguments: SOURCE DESTINATION

  $ qasminfer qasm2.qasm accidental-output.qasm >two-paths.stdout 2>two-paths.stderr
  [2]
  $ test ! -e accidental-output.qasm
  $ test ! -s two-paths.stdout
  $ head -n 1 two-paths.stderr
  execution expects exactly one positional SOURCE

  $ qasminfer --unoptimize qasm2.qasm conflict.qasm --output probabilities.txt >conflict.stdout 2>conflict.stderr
  [2]
  $ test ! -e conflict.qasm
  $ test ! -e probabilities.txt
  $ test ! -s conflict.stdout
  $ head -n 1 conflict.stderr
  --output/-o cannot be used with --unoptimize

  $ qasminfer qasm2.qasm --unoptimize short-conflict.qasm -o probabilities-short.txt >short-conflict.stdout 2>short-conflict.stderr; test $? -ne 0
  $ test ! -e short-conflict.qasm
  $ test ! -e probabilities-short.txt
  $ test ! -s short-conflict.stdout
  $ test -s short-conflict.stderr

  $ qasminfer --json qasm2.qasm --unoptimize json-conflict.qasm >json-conflict.stdout 2>json-conflict.stderr
  [2]
  $ test ! -e json-conflict.qasm
  $ test ! -s json-conflict.stdout
  $ head -n 1 json-conflict.stderr
  --json cannot be used with --unoptimize

No-argument invocation retains its legacy exit status and displays usage.

  $ qasminfer >no-arguments.stdout 2>no-arguments.stderr
  [1]
  $ test ! -s no-arguments.stdout
  $ head -n 1 no-arguments.stderr
  usage: qasminfer [OPTIONS] SOURCE

A conversion failure leaves an existing destination untouched.

  $ printf 'sentinel\n' > protected.qasm
  $ qasminfer --unoptimize conversion_error.qasm protected.qasm >conversion-error.stdout 2>conversion-error.stderr; test $? -ne 0
  $ cat protected.qasm
  sentinel
  $ test ! -s conversion-error.stdout
  $ test -s conversion-error.stderr

Lexical failures in both parsers return a clear diagnostic without creating or
overwriting a destination.

  $ printf 'sentinel\n' > lexical-protected.qasm
  $ qasminfer --unoptimize lexical_error_qasm2.qasm lexical-protected.qasm >lexical-qasm2.stdout 2>lexical-qasm2.stderr
  [1]
  $ cat lexical-protected.qasm
  sentinel
  $ test ! -s lexical-qasm2.stdout
  $ cat lexical-qasm2.stderr
  qasminfer: lexical_error_qasm2.qasm:3:1: Unexpected char: @

  $ qasminfer --unoptimize lexical_error_qasm3.qasm lexical-created.qasm >lexical-qasm3.stdout 2>lexical-qasm3.stderr
  [1]
  $ test ! -e lexical-created.qasm
  $ test ! -s lexical-qasm3.stdout
  $ cat lexical-qasm3.stderr
  qasminfer: lexical_error_qasm3.qasm:3:1: Unexpected char: @

The pre-existing execution interface retains its exact text and JSON output,
file redirection, and verbose stream separation.

  $ qasminfer execution.qasm >execution.stdout 2>execution.stderr
  $ cat execution.stdout
  00 : 5.0000000000000011e-01
  01 : 4.9999999999999989e-01
  10 : 0.0000000000000000e+00
  11 : 0.0000000000000000e+00
  $ test ! -s execution.stderr

  $ qasminfer --json execution.qasm >execution.json 2>json.stderr
  $ cat execution.json
  {
    "qubits": 1,
    "clbits": 2,
    "probabilities": [
      {"state": "00", "probability": 5.0000000000000011e-01},
      {"state": "01", "probability": 4.9999999999999989e-01},
      {"state": "10", "probability": 0.0000000000000000e+00},
      {"state": "11", "probability": 0.0000000000000000e+00}
    ]
  }
  $ test ! -s json.stderr

  $ qasminfer execution.qasm --output execution.file >output.stdout 2>output.stderr
  $ test ! -s output.stdout
  $ test ! -s output.stderr
  $ cmp execution.stdout execution.file

  $ qasminfer --json execution.qasm --output execution-json.file >json-output.stdout 2>json-output.stderr
  $ test ! -s json-output.stdout
  $ test ! -s json-output.stderr
  $ cmp execution.json execution-json.file

  $ qasminfer execution.qasm --verbose >execution-verbose.stdout 2>execution-verbose.stderr
  $ cmp execution.stdout execution-verbose.stdout
  $ grep -F 'QASMCore ========================================' execution-verbose.stderr
  QASMCore ========================================
  $ grep -F 'RESULT ==========================================' execution-verbose.stderr
  RESULT ==========================================
