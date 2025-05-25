# Turbo-Guacamole
The name of the repository is generated randomly.

This repoitory is for "야수연 오마카세."

## Setup
This version is known to compile with

- coq 8.20.1
- coq-stdpp 1.11.0
- coq-ext-lib 0.13.0

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create Intro2TT 5.2.0
opam switch link Intro2TT .
```
3. Add the Coq opam repository.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
```
4. Install the right version of the dependencies.
```
opam install coq.8.20.1 coq-stdpp.1.11.0 coq-ext-lib.0.13.0
```

## How to Compile
You can compile this with the command below:
```
make all
```