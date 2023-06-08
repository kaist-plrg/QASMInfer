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