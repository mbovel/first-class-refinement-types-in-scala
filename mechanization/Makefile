all: refinement_types

refinement_types/Makefile:
	cd refinement_types && rocq makefile -f _CoqProject -o Makefile

refinement_types: refinement_types/Makefile
	$(MAKE) -C refinement_types

clean:
	$(if $(wildcard refinement_types/Makefile),$(MAKE) -C refinement_types clean)
	rm -f refinement_types/Makefile refinement_types/Makefile.conf

.PHONY: all refinement_types clean
