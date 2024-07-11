# Rωμ (Rome) supplementary materials

## Index
Directies in this development follow the same structure as the Agda standard lib: The folder `Foo` houses Foo-related submodules, which `Foo.agda` groups and re-exports.

- [./IndexCalculus](./IndexCalculus) contains the Index Calculus, which is the subset of Agda we choose as a target of Rome denotation.
- [./Preludes](./Preludes) and [Prelude.agda](./Prelude.agda) each bundle common Agda libraries together, to make imports accross all modules simpler.
- [./Shared](./Shared) contains a handful of utility functions spread accross other modules. Notable is the postulate for functional extensionality, which is necessary to denote equivalence of functional types.
- [./Rome](./Rome) houses our mechanization of Rωμ. Modules are split by term-type-kind stratification; each module is then split along _syntax_ and _semantic_ components. Each semantic component contains the denotation of Rωμ intrinsic representations into Index Calculus terms.


