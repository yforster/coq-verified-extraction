# Verified Extraction from Coq to Malfunctional

This repository contains the current development state of a new verified extraction from Coq to OCaml, based on MetaCoq.
Technically, the extraction targets Malfunction, which is a specification of Lambda, the internal language of the OCaml compiler.
We use Malfunction as target for extraction from Coq, and rely on the Malfunction and OCaml compilers to obtain `.cmx` files that will behave like `.cmx` files created by Coq's current extraction process and the Ocaml compiler.
In particular, Coq programs extracted like this can interact with other OCaml programs and with Coq programs extracted using the existing extraction.

The implementation of extraction is fully functional and supports primitive integers and floats, but no cofixpoints yet.
Verification is work in progress.

## Installation

```
opam switch create coq-malfunction --packages="ocaml-variants.4.13.1+options,ocaml-option-flambda"
eval $(opam env --switch=coq-malfunction)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-metacoq-erasure+unshadowing+dev https://github.com/yforster/template-coq.git#unshadowing
make
```

## Usage

The commands `MetaCoq Extract <definition>`, `MetaCoq Extract Module <module>`, and `MetaCoq Extract Module <module> "<file>"` can be used to run the new extraction process.

## Team & Credits

The project is developed by Yannick Forster, Matthieu Sozeau, Pierre-Marie Pédrot, and Nicolas Tabareau.

```
Copyright (c) 2022 Yannick Forster, Matthieu Sozeau
```
