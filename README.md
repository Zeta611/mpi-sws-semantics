# Coq development for the Semantics course at Saarland University

This repository contains the Coq code for the Semantics course taught by Derek Dreyer at Saarland University.

## Installation Instructions

### Windows
Unfortunately, Windows does not support the libraries we use for the course very well. If you can use one of the other operating systems (macOS or Linux), we recommend you do so and follow the instructions below.
Otherwise, you can either use Windows's WSL (Windows Subsystem for Linux) or a VM.

TODO: put instructions for WSL here.

### Linux/macOS

Clone this repository:
```
git clone https://gitlab.mpi-sws.org/FP/semantics-course.git semantics-code
```

For the course, we recommend installing Coq through [opam](https://opam.ocaml.org), the OCaml package manager.
To do so, please visit [the `opam` installation guide](https://opam.ocaml.org/doc/Install.html) and follow the instructions.
(Typically, this means you just have to execute the following script:)
```bash
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
```

Now opam is installed on your machine and we can proceed to install the dependencies for the course.
To do so, please execute the following instructions:

```
# we enter the semantics folder we just cloned
cd semantics-code

# we create a new "switch", where we will install the dependencies
opam switch create semantics ocaml-base-compiler.4.14.0
eval $(opam env)
opam switch link semantics .

# we tell opam where to find the dependencies
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

# we install the dependencies
# you can ignore the warnings that will appear concerning missing fields and the license
make builddep
```

Congratulations, you have now installed all the dependencies and you can start to work with the course materials 🎉


## Using the Coq code

In this repository, you will find all the files from the lecture and templates for exercises.
We usually make these files available over the course of the semester, together with exercise sheets.
All exercises are also present in the lecture notes.
In the file `STRUCTURE.md`, you can find a rough mapping of chapters in the lecture notes to the Coq code.

The Coq code is organized in multiple folders and multiple files. To compile, please execute:

```
make
```

**NOTE** Since there are dependencies between the files in this development, you may need to compile some files first (by typing `make`) before you can interactively do proofs other files.



## Modifying the Coq code

To edit the Coq code and complete the exercises, you will need an editor.
There are a number of editors and editor extensions for working with Coq code.
We recommend one of the following four options:

- **VS Coq** VSCoq is an extension of the editor [VS Code](https://code.visualstudio.com). Download [the extension](https://github.com/coq-community/vscoq) and change the the following setting in VS Code:

Change `Coqtop: Bin Path` to `~/.opam/semantics/bin/`.
(That's where your semantics switch should be installed now.)

- **CoqIDE** is the "default" IDE for Coq. If you have installed Coq via `opam`, you can run `opam install coqide` to install it. You need the GTK+-development libraries installed for that on your system (`gtksourceview3`). Starting with version 2.1, `opam` should automatically ensure that on most operating systems. If that does not work, you may need to install them yourself, depending on your system.
- **Proof General** adds Coq support to Emacs. You can find it [here](https://github.com/ProofGeneral/PG).
- **Coqtail** adds Coq support to vim. You can find it [here](https://github.com/whonore/Coqtail).



**NOTE** Many of the Coq files use unicode notation for symbols. For example,
instead of writing `nat -> nat -> nat`, we typically write `nat → nat → nat`.
You can find out [here how to configure them for your editor](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/editor.md).
