# Verified Extraction from Coq to OCaml

This repository contains the current development state of a new verified extraction from Coq to OCaml, based on MetaCoq.
Technically, the extraction targets [Malfunction](https://github.com/stedolan/malfunction), which is a specification of Lambda, the internal language of the OCaml compiler.
We use Malfunction as target for extraction from Coq, and rely on the Malfunction and OCaml compilers to obtain `.cmx` files that will behave like `.cmx` files created by Coq's current extraction process and the Ocaml compiler.
In particular, Coq programs extracted like this can interact with other OCaml programs and with Coq programs extracted using the existing extraction.

The implementation of extraction is fully functional and supports primitive integers and floats, but no cofixpoints yet.
Verification is work in progress.

## Installation

```
opam switch create coq-malfunction --packages="ocaml-variants.4.14.1+options,ocaml-option-flambda"
eval $(opam env --switch=coq-malfunction)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin -n -y "https://github.com/MetaCoq/metacoq.git#v1.3.1-8.19"
opam pin -n -y "https://github.com/stedolon/malfunction.git#master"
opam install . --deps-only
make -j 4
```

## Usage

After `From VerifiedExtraction Require Import Extraction.`
the commands `Verified Extraction <definition>` and `Verified Extraction <definition> "<file>.mlf"` can be used to run the new extraction process.
Multiple functions can be extracted at the same time with `MetaCoq Extraction (<d1>,<d2>,...)`.
To add an `mli` file one can add the output of the (unverified) generator `MetaCoq Run Print mli <definition>.` to a `.mli` file.

## Structure

- [`Malfunction.v`](theories/Malfunction.v) contains the syntax definition of Malfunction. It is a direct, line-to-line port of the OCaml file [`malfunction.ml`](https://github.com/stedolan/malfunction/blob/master/src/malfunction.ml) to Coq.
- [`SemanticsSpec.v`](theories/SemanticsSpec.v) defines an inductive big-step evaluation predicate.
- [`Compile.v`](theories/Compile.v) defines a compilation function of lambda box to Malfunction.
- [`CompileCorrect.v`](theories/CompileCorrect.v) proves the correctness of this function, using the correctness proof of case analysis in [`Mcase.v`](theories/Mcase.v)
- [`Interpreter.v`](theories/Interpreter.v) contains an interpretation function, which is close to [`malfunction_interpreter.ml`](https://github.com/stedolan/malfunction/blob/master/src/malfunction_interpreter.ml), and a proof that values according to the evaluation predicate are also found by the interpreter. Note that since the interpreter is not necessarily terminating we switch of Coq's termination checker, meaning this proof can only be seen as a sanity check.
- [`Serialize.v`](theories/Serialize.v) contains seralization functions into s-expressions. There is also a parser in [`Deserialize.v`](theories/Deserialize.v), used for testing.
- [`Pipeline.v`](theories/Pipeline.v) composes the full extraction pipeline from Coq to Malfunction
- [`Firstorder.v`](theories/Firstorder.v) derives interoperability results for first-order functions

## Team & Credits

The project is developed by Yannick Forster, Matthieu Sozeau, Pierre-Marie Pédrot, and Nicolas Tabareau.

```
Copyright (c) 2022--2024 Yannick Forster, Matthieu Sozeau, Nicolas Tabareau
```
