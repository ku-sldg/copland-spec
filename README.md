<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Copland Specification

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/ku-sldg/copland-spec/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/ku-sldg/copland-spec/actions/workflows/docker-action.yml




Specification for the Copland DSL for Attestation Protocols

## Meta

- Author(s):
  - Adam Petz
  - Will Thomas
  - KU-SLDG Lab
- License: [Creative Commons Attribution Share Alike 4.0 International](LICENSE)
- Compatible Rocq/Coq versions: 8.20 later
- Compatible OCaml versions: 4.12 or later
- Additional dependencies:
  - [Rocq-Candy](https://github.com/ku-sldg/RocqCandy)
  - [RocqJSON](https://github.com/ku-sldg/rocq-json)
  - [Dune](https://dune.build) 3.17 or later
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Copland Specification
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add -a --set-default ku-sldg/opam-repo https://github.com/ku-sldg/opam-repo.git
opam repo add coq-released https://coq.inria.fr/opam/released
opam install rocq-copland-spec
```

To instead build and install manually, do:

``` shell
git clone https://github.com/ku-sldg/copland-spec.git
cd copland-spec
dune build
dune install
```



