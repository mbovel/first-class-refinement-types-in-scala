ROCQFLAGS = -Q . SystemF

all: compile extract

compile: systemf.vo

systemf.vo: systemf.v
	rocq compile $(ROCQFLAGS) systemf.v

extract: systemf_eval.ml

systemf_eval.ml: systemf_extract.v systemf.vo
	rocq compile $(ROCQFLAGS) systemf_extract.v -output-directory .

systemf_eval_test: systemf_eval.ml systemf_eval_test.ml
	rm -f systemf_eval.mli
	ocamlc -o systemf_eval_test systemf_eval.ml systemf_eval_test.ml

run: systemf_eval_test
	./systemf_eval_test

clean:
	rm -f systemf_eval.ml systemf_eval_test *.cmi *.cmo *.glob *.vo *.vok *.vos *.mli

test: all run

.PHONY: all compile extract run clean test
