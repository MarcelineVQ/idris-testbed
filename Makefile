# literally just convenience

.PHONY: build

build:
	idris2 --build evo.ipkg

support:
	@c99 -L/opt/intel/mkl/lib/intel64 -lmkl_avx2 -laf -shared arrayfire.c -o libarrayfire.so

repl:
	@rlwrap idris2 --repl evo.ipkg

# install:
#   idris2 --install package.ipkg

clean:
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
