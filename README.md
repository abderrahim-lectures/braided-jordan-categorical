# Derivations of the Symmetrized Product in a Braided Monoidal Category

Author: Abderrahim Adrabi, Mohammed V University in Rabat.  
Current version: **v2**.

## The idea of the paper

Let A be an algebra in a braided monoidal category in which morphisms can be added. Let c be the braiding on A ⊗ A. The symmetrized product of A is (1 + c), and the antisymmetrized product is (1 - c). A derivation of a product is a morphism D A A that satisfies the Leibniz rule for that product. The Leibniz defect of D decides all cases. It shows that D is a derivation of (1 c) exactly when the defect composed with 1 c vanishes. If no nonzero morphism is killed by 2, a derivation of both products is a derivation of . For a commutative product, the derivations of (1 + c) and of coincide. In a symmetric category the derivations form an object that contains the derivation object of Pareigis. Let be an involution of A and let = ( ⊗ )c be the twisted braiding. If is commutative and D commutes with , then a derivation of _ has a defect that is killed by 1 + ( ⊗ ), and it vanishes on pairs of eigenvectors of with the same eigenvalue.

### Contents

1. Introduction
2. Preliminaries
3. The Leibniz defect
4. The commutative case and the derivation object
5. A twisted involution

## Repository layout

| Path | Content |
|---|---|
| `paper/braided-jordan-categorical.tex` | LaTeX source (class files in `cls/`) |
| `pdf/` | the PDF of the latest release |
| `lean/Research/BraidedJordanCategorical/` | Lean 4 files that check computations and lemmas of the paper (mathlib only) |

Build the paper with `cd paper && latexmk -pdf braided-jordan-categorical.tex`. Build the Lean files with `cd lean && lake build`.

## Change log

One entry per released version, newest first. Each version is also a tag of this repository.

- **v2** (2026-10-30): Ion 2010 (arXiv 1004.5022) fetched and cited: Definition 1.5 (braided commutator, recalled; the antisymmetrized product is the braided commutator of an associative algebra) and Definition 1.4 (c-commutative, now the source of the name commutative). No result changed.
- **v1** (2026-10-29): first version. Four sections: the Leibniz defect, the commutative case and the derivation object, a twisted involution, with four commutative diagrams. Results proved in Lean in lean/Research/BraidedJordanCategorical (see formalization-debt.md).

## References

Citations of the works the paper uses. The works themselves are not part of this repository.

1. Adrabi, A.: Braided-symmetric derivations of algebras. Preprint (2026). https://github.com/abderrahim-lectures/braided-sym-deriv.
2. Adrabi, A.: Jordan and Lie derivations as derivations of the symmetrized and antisymmetrized products. Preprint (2026). https://github.com/abderrahim-lectures/jordan-lie-symmetrized.
3. G. E. Barnes, A. Schenkel and R. J. Szabo, Nonassociative geometry in quasi-Hopf representation categories II: connections and curvature, J. Geom. Phys. 106 (2016), 234–255.
4. Brešar, M.: Jordan derivations on semiprime rings. Proc. Amer. Math. Soc. 104(4), 1003–1006 (1988).
5. Brešar, M., Zelmanov, E.: Jordan homomorphisms: a survey. Serdica Math. J. 51, 203–230 (2025).
6. Cusack, J.M.: Jordan derivations on rings. Proc. Amer. Math. Soc. 53(2), 321–324 (1975).
7. Fuchs, J., Runkel, I., Schweigert, C.: Ribbon categories and (unoriented) CFT: Frobenius algebras, automorphisms, reversions. arXiv:math/0511590 (2005).
8. Graziani, G., Makhlouf, A., Menini, C., Panaite, F.: BiHom-associative algebras, BiHom-Lie algebras and BiHom-bialgebras. SIGMA 11, 086 (2015).
9. Herstein, I.N.: Jordan derivations of prime rings. Proc. Amer. Math. Soc. 8, 1104–1110 (1957).
10. Ion, B.: Relative PBW type theorems for symmetrically braided Hopf algebras. Preprint (2010). https://arxiv.org/abs/1004.5022.
11. Jacobson, N.: Abstract derivation and Lie algebras. Trans. Amer. Math. Soc. 42(2), 206–224 (1937).
12. Jordan, P., von Neumann, J., Wigner, E.: On an algebraic generalization of the quantum mechanical formalism. Ann. of Math. 35(1), 29–64 (1934).
13. Joyal, A., Street, R.: Braided tensor categories. Adv. Math. 102(1), 20–78 (1993).
14. Martindale, W.S., III: Lie derivations of primitive rings. Michigan Math. J. 11, 183–187 (1964).
15. Pareigis, B.: On Lie algebras in the category of Yetter–Drinfeld modules. arXiv:q-alg/9612023 (1998).

## About this repository

The repository is updated after every release of the paper. The research workspace that produced it is private; the final source, PDF and Lean code are published here.
