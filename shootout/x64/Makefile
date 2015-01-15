test: test-fib test-ack test-tak test-harmonic test-mandelbrot
clean:
	rm -f *.s *.min-caml *.ocamlopt *.gcc *.cmi *.cmx *.o *.out

test-fib: fib.min-caml fib.ocamlopt fib.gcc
	time ./fib.min-caml > fib.min-caml.out
	time ./fib.ocamlopt > fib.ocamlopt.out
	time ./fib.gcc > fib.gcc.out
	diff fib.min-caml.out fib.ocamlopt.out
	diff fib.min-caml.out fib.gcc.out

fib.ocamlopt: fib.ml
	ocamlopt -pp ../min-rt/preprocess.sh -unsafe -inline 100 fib.ml -o fib.ocamlopt

fib.min-caml: fib.ml ../min-caml
	../min-caml -inline 100 fib
	gcc -g -O2 -Wall fib.s ../libmincaml.S ../stub.c -lm -o fib.min-caml

fib.gcc: fib.c
	gcc -O3 -Wall fib.c -o fib.gcc

test-ack: ack.min-caml ack.ocamlopt ack.gcc
	time ./ack.min-caml > ack.min-caml.out
	time ./ack.ocamlopt > ack.ocamlopt.out
	time ./ack.gcc > ack.gcc.out
	diff ack.min-caml.out ack.ocamlopt.out
	diff ack.min-caml.out ack.gcc.out

ack.ocamlopt: ack.ml
	ocamlopt -pp ../min-rt/preprocess.sh -unsafe -inline 100 ack.ml -o ack.ocamlopt

ack.min-caml: ack.ml ../min-caml
	../min-caml -inline 100 ack
	gcc -g -O2 -Wall ack.s ../libmincaml.S ../stub.c -lm -o ack.min-caml

ack.gcc: ack.c
	gcc -O3 -Wall ack.c -o ack.gcc

test-harmonic: harmonic.min-caml harmonic.ocamlopt harmonic.gcc
	time ./harmonic.min-caml > harmonic.min-caml.out
	time ./harmonic.ocamlopt > harmonic.ocamlopt.out
	time ./harmonic.gcc > harmonic.gcc.out
	diff harmonic.min-caml.out harmonic.ocamlopt.out
	diff harmonic.min-caml.out harmonic.gcc.out

harmonic.ocamlopt: harmonic.ml
	ocamlopt -pp ../min-rt/preprocess.sh -unsafe -inline 100 harmonic.ml -o harmonic.ocamlopt

harmonic.min-caml: harmonic.ml ../min-caml
	../min-caml -inline 100 harmonic
	gcc -g -O2 -Wall harmonic.s ../libmincaml.S ../stub.c -lm -o harmonic.min-caml

harmonic.gcc: harmonic.c
	gcc -O3 -Wall harmonic.c -o harmonic.gcc

test-mandelbrot: mandelbrot.min-caml mandelbrot.ocamlopt mandelbrot.gcc
	time ./mandelbrot.min-caml > mandelbrot.min-caml.out
	time ./mandelbrot.ocamlopt > mandelbrot.ocamlopt.out
	time ./mandelbrot.gcc > mandelbrot.gcc.out
#	diff mandelbrot.min-caml.out mandelbrot.ocamlopt.out
#	diff mandelbrot.min-caml.out mandelbrot.gcc.out
	ocaml mandelbrot.ml > mandelbrot.ocamlc.out # avoid 80-bit float on x86
	diff mandelbrot.min-caml.out mandelbrot.ocamlc.out

mandelbrot.ocamlopt: mandelbrot.ml
	ocamlopt -pp ../min-rt/preprocess.sh -unsafe -inline 100 mandelbrot.ml -o mandelbrot.ocamlopt

mandelbrot.min-caml: mandelbrot.ml ../min-caml
	../min-caml -inline 100 mandelbrot
	gcc -g -O2 -Wall mandelbrot.s ../libmincaml.S ../stub.c -lm -o mandelbrot.min-caml

mandelbrot.gcc: mandelbrot.c
	gcc -O3 -Wall mandelbrot.c -o mandelbrot.gcc

test-tak: tak.min-caml tak.ocamlopt tak.gcc
	time ./tak.min-caml > tak.min-caml.out
	time ./tak.ocamlopt > tak.ocamlopt.out
	time ./tak.gcc > tak.gcc.out
	diff tak.min-caml.out tak.ocamlopt.out
	diff tak.min-caml.out tak.gcc.out

tak.ocamlopt: tak.ml
	ocamlopt -pp ../min-rt/preprocess.sh -unsafe -inline 100 tak.ml -o tak.ocamlopt

tak.min-caml: tak.ml ../min-caml
	../min-caml -inline 100 tak
	gcc -g -O2 -Wall tak.s ../libmincaml.S ../stub.c -lm -o tak.min-caml

tak.gcc: tak.c
	gcc -O3 -Wall tak.c -o tak.gcc
