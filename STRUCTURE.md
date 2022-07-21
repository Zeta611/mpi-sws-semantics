# Structure of the Coq development

This document roughly maps the lecture notes and exercises to the Coq development.

## Chapter 1
* The `warmup` folder contains a quick reminder of some concepts of Coq as well as an introduction to some features of `stdpp`.
* The `stlc` folder contains an implementation of the untyped lambda-calculus and the simply-typed lambda-calculus, with different reduction semantics, including syntactic and semantic type safety proofs.
* The `stlc_extended` folder features an extended version of our core calculus with products, sums, and more operators. You can get more practice with the core concepts by completing the extensions, e.g. extending the type soundness proofs.

| Section | Coq entry point          |
|---------|--------------------------|
| 1.0     | `stlc/lang.v`            |
| 1.1     | `stlc/lang.v`            |
| 1.2     | `stlc/untyped.v`         |
| 1.3     | `stlc/types.v`           |
| 1.4     | `stlc/logrel.v`          |

Exercises can be found in `stlc/exercises01.v` and `stlc/exercises02.v`. Note that the numbering in these files is different from the lecture notes, but where applicable, the exercise it corresponds to in the lecture notes can be found in parantheses.

Special notes on some exercises:
* Exercises 12, 13, and 15 are included in the `stlc_extended` folder.
* Exercise 16 consists of `stlc/cbn_logrel.v`.


## Chapter 2
* The development and exercises for Chapter 2 can be found in folder `systemf`.

| Section | Coq entry point                             |
|---------|---------------------------------------------|
| 2.1     | `systemf/lang.v`, `systemf/bigstep.v`       |
| 2.3     | `systemf/types.v`                           |
| 2.4     | `systemf/types.v`                           |
| 2.5     | `systemf/church_encodings.v`                |
| 2.6     | `systemf/logrel.v`                          |
| 2.7     | `systemf/free_theorems.v`                   |
| 2.8     | `systemf/existential_invariants.v`          |
| 2.9     | `systemf/binary_logrel.v`                   |

Special notes on some exercises:
* Exercises from Sections 2.1 - 2.3 are not present in Coq, except for Exercises 18 and 19.
* For Exercise 21, gaps are present in `systemf/types.v`.
* For Exercise 26, gaps are present in `systemf/logrel.v`.
* Exercise 32 is not present in the Coq code.
* For Exercise 33, gaps have been left in `systemf/binary_logrel.v`.
* Exercise 34 is not present in the Coq code.

## Chapter 3
* The development and exercises for Chapter 3 can be found in folder `systemf_mu`.

| Section | Coq entry point                             |
|---------|---------------------------------------------|
| 3.0     | `systemf_mu/lang.v`, `systemf_mu/types.v`   |
| 3.1     | `systemf_mu/untyped_encoding.v`             |
| 3.3     | `systemf_mu/pure.v`, `systemf_mu/logrel.v`  |
| 3.4     | `systemf_mu/z_combinator.v`                 |


Special notes on some exercises:
* Exercise 36 is not present in the Coq development.
* For Exercise 37, gaps are left in `systemf_mu/types.v`.
* Exercise 39 is not present in the Coq development.
* For Exercises 40, gaps are left in `systemf_mu/pure.v`.
* Exercise 41 is already proved for you in Coq.
* For Exercise 42, gaps are left in `systemf_mu/logrel.v`.
* Exercise 44 is already proved for you in Coq.

## Chapter 4
* The development and exercises for Chapter 4 can be found in folder `systemf_mu_state`.
  Sections 4.7 and 4.8 are not treated in the Coq development.

| Section | Coq entry point                                                   |
|---------|-------------------------------------------------------------------|
| 4.0     | `systemf_mu_state/lang.v`, `systemf_mu_state/types.v`             |
| 4.3     | `systemf_mu_state/types.v`                                        |
| 4.6     | `systemf_mu_state/logrel.v`, `systemf_mu_state/mutbit.v`          |
| 4.9     | `systemf_mu_state/logrel.v`                                       |

Special notes on some exercises:
* Exercises 51, 52, and 55 have already been proved for you.
* For Exercises 54, gaps are left in `systemf_mu_state/logrel.v`.
* Exercise 56 is not present in the Coq development.

## Chapter 5
* The development for Chapter 5 can be found in the file `axiomatic/hoare.v`.
* Exercises are provided in-line with the material.

## Chapter 6
* The development for Chapter 6 can be found in the file `axiomatic/ipm.v`.
* Exercises are provided in-line with the material.

## Chapter 7
* The development for Chapter 7 can be found in the folder `axiomatic/logrel.v`, in files:
  + `syntactic.v` defines a syntactic type system for our language.
  + `logrel.v` defines the logical relation and proves the fundamental theorem.
  + `adequacy.v` proves adequacy of the logical relation.
* Exercises are provided in-line with the material.

## Chapter 8
* The development for Chapter 8 is distributed over multiple files and folders.
* Exercises are provided in-line with the material.

| Section | Coq entry point                                                   |
|---------|-------------------------------------------------------------------|
| 8.0     | `axiomatic/logrel/ghost_state.v`                                  |
| 8.1     | `axiomatic/resource_algebras.v`                                   |
| 8.2     | `axiomatic/resource_algebras.v`                                   |
| 8.3     | `axiomatic/resource_algebras.v`                                   |
| 8.4     | `axiomatic/reloc` and `axiomatic/fupd.v`                          |

In particular, for ReLoC/ the binary logical relation, the following files are of interest:
- `axiomatic/reloc/ghost_state.v` defines the ghost theory (Section 8.4.3),
- `axiomatic/fupd.v` introduces the fancy update modality (Section 8.4.2),
- `axiomatic/reloc/src_rules.v` proves the ghost program rules (Section 8.4.1/8.4.3),
- `axiomatic/reloc/logrel.v` defines the logical relation (Section 8.4.1),
- `axiomatic/reloc/fundamental.v` proves the fundamental property (Section 8.4.4),
- `axiomatic/reloc/adequacy.v` proves the contextual refinement result (Section 8.4.4).

Notes on exercises:
* Exercise 116 (coming up with an interesting refinement and proving it) is not present in the Coq development.

## Chapter 9
* Chapter 9 is not explicitly formalized in the Coq development. We recommend that you look at the Iris source code if you are interested.

## Chapter 10
* The development for Chapter 10 is distributed over multiple files and folders.

| Section | Coq entry point                                                   |
|---------|-------------------------------------------------------------------|
| 10.0    | `axiomatic/concurrency.v`                                         |
| 10.1    | `axiomatic/concurrency.v`                                         |
| 10.2    | `axiomatic/concurrency.v`                                         |
| 10.3    | `axiomatic/concurrent_logrel/`                                    |

Notes on exercises:
* The exercise for verifying the channel implementation (Section 10.3) is located in `axiomatic/concurrency.v`.
