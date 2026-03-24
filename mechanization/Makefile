all: systemf refinement_types

systemf:
	$(MAKE) -C systemf

refinement_types/Makefile:
	cd refinement_types && rocq makefile -f _CoqProject -o Makefile

refinement_types: refinement_types/Makefile
	$(MAKE) -C refinement_types

clean: refinement_types/Makefile
	$(MAKE) -C systemf clean
	$(MAKE) -C refinement_types clean

.PHONY: all systemf refinement_types clean
