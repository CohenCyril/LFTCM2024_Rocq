FROM coqorg/coq:8.19.1
RUN eval $(opam env "--switch=${COMPILER}" --set-switch)
RUN opam update -y
RUN opam install -y coq-lsp
RUN opam install -y coq-mathcomp-character
RUN opam install -y coq-mathcomp-algebra-tactics
RUN opam install -y coq-mathcomp-analysis
