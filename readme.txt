You can generate a makefile using
```
coq_makefile -f _CoqProject -o Makefile
```

simple example of a `_CoqProject` file:
```
-Q src Lib
-R theories Theories

src/Lib/<your_library_module>.v
src/Theory/<your_theory_module>.v
src/Main.v
```

`src/` is a directory containing my Coq source code. Organize my source files in subdirectories,
such as `Lib/` for library modules and `Theory` for theory modules.

`doc/` is a directory containing my project's documentation,
such as design documents, user guides, or any other relevant materials.
