# Compiles the mechanization from clean sources under Rocq 9.2.
#
#   docker build -t refinement-mech mechanization
#   docker run --rm refinement-mech
#
# Building the image only sets up the environment and sources; the proofs
# are checked when the container runs (exit code 0 = everything compiles).

FROM rocq/rocq-prover:9.2

WORKDIR /home/rocq/mechanization
COPY --chown=rocq:rocq . .

CMD ["opam", "exec", "--", "make", "-j4"]
