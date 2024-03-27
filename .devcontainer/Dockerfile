FROM mathcomp/mathcomp:2.2.0-coq-8.19
RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN git clone -b main --depth 1 https://github.com/CohenCyril/LFTCM2024_Rocq
RUN opam install -y --deps-only ./LFTCM2024_Rocq