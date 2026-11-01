# Derivations of the Symmetrized Product in a Braided Monoidal Category

Author: Abderrahim Adrabi, Mohammed V University in Rabat.  
Current version: **v3**.

## The idea of the paper

Let $A$ be an object of a braided monoidal category in which morphisms can be added, and let
$\mu \colon A \otimes A \to A$ be a product on $A$. Let $c$ be the braiding on $A \otimes A$.
The symmetrized product of $A$ is $\mu(1 + c)$, and the antisymmetrized product is $\mu(1 - c)$.
A derivation of a product is a morphism $D \colon A \to A$ that satisfies the Leibniz rule for
that product. The Leibniz defect $E_D$ of $D$ decides all cases. It shows that $D$ is a derivation
of $\mu(1 \pm c)$ exactly when $E_D \circ (1 \pm c)$ vanishes. If no nonzero morphism is killed by
$2$, a derivation of both products is a derivation of $\mu$, and for a commutative product the
derivations of $\mu(1 + c)$ and of $\mu$ coincide. In a symmetric closed category with kernels the
derivations form an object that contains the derivation object of Pareigis. Let $\alpha$ be an
endomorphism of $A$ with $\alpha^2 = \mathrm{id}_A$ and let $\sigma = (\alpha \otimes \alpha)c$ be
the twist. If $\mu$ is commutative and $D$ commutes with $\alpha$, then a derivation of
$\mu_\sigma$ has a defect that is killed by $1 + (\alpha \otimes \alpha)$; if moreover no nonzero
morphism is killed by $2$, it vanishes on pairs of eigenvectors of $\alpha$ with the same
eigenvalue.

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
| `pdf/` | the PDFs of the released versions |
| `lean/Research/BraidedJordanCategorical/` | Lean 4: Lemma 3.1, Proposition 3.2, Corollary 3.3, Theorems 3.4, 4.1, 4.3 and 5.1 and Lemma 4.2, in Mathlib only |
| `lean/Research.lean` | root module of the formalization; builds the results above in dependency order |
| `lean/Research/BraidedJordanCategorical/DerivationObject.lean` | Theorem 4.3: the derivation object, its universal property and its naturality, and `Der(μ) ↪ Der(μ(1+c))` |
| `lean/Research/BraidedJordanCategorical/Symmetric.lean` | the specialisation to symmetric monoidal categories: `μ(1 ± c) = μ ± μc`, `(1 ± c)(1 ∓ c) = 0`, and the twist of an involution is an involution |
| `formalization-debt.md` | what the Lean code does not formalize, and why |
| `results/` | the review reports and the record of the fixes (local, not versioned) |
| `braided-jordan-categorical-v2-references.zip` | the thirteen cited works that are in the archive, as PDFs (local archive, not versioned); the two remaining citations are the author's own preprints [1] and [2], which live in public repositories |

Build the paper with `cd paper && latexmk -pdf braided-jordan-categorical.tex`; the PDF is written
to `paper/build/`, named after the version.

Build the Lean files with

```bash
cd lean
lake exe cache get   # once: downloads the prebuilt Mathlib oleans
lake build
```

The Lean development is pinned: `lean/lean-toolchain` is `leanprover/lean4:v4.33.1`, the Mathlib
dependency is the tag `v4.33.1`, and `lean/lake-manifest.json` records the exact commit
(`0df444a`). It imports Mathlib only, with no `sorry`, no added axiom and no `maxHeartbeats`
override; the `#print axioms` output for all 54 theorems is `propext`, `Classical.choice`,
`Quot.sound`.

## Change log

One entry per released version, newest first. The tagged releases in this repository are `v1` and
`v2`; the entry for `v3` describes the current working tree, to be tagged with its commit.

- **v3** (2026-11-01): corrections from the review in `results/deep-review-v2.pdf`, listed one by
  one in `results/fixes-applied.md` and summarised in the header comment of the `.tex`. The two
  statements that were false as printed are in the abstract: the commutative case and the vanishing
  on pairs of eigenvectors both need the $2$-torsion freeness that Theorems 4.1 and 5.1 assume (the
  counterexample is $A = \mathbb{F}_2$ over $\mathbb{F}_2$), and "in a symmetric category" is not
  enough for the derivation object, which needs closedness and kernels. The kernel diagram of
  Theorem 4.3 is redrawn: its second diagonal was the zero morphism drawn as a monomorphism, and
  $\Der(\mu_+)$ was missing. Definition 4.5 writes the second morphism of the equalizer as
  $\zeta(\hat l \circ \mathrm{ev})$ with $\hat l = \zeta(l)$, as in Barnes--Schenkel--Szabo, where
  $l \circ \mathrm{ev}$ is not composable. Definition 2.1 is glossed ($K$, the antipode $S$,
  Sweedler notation, and Pareigis' own well-typed form of the Leibniz rule), and $\mu_-$ is
  identified with Ion's braided commutator only for a braided algebra, as Ion's Definition 1.4
  requires. The standing hypothesis of Section 2 is stated as enrichment over abelian groups
  instead of "every set of morphisms is an abelian group". Theorem 5.1 now attaches to each part the
  hypotheses its proof uses, $A_\pm$ is defined, and $\sigma$ is no longer called a braiding. The
  introduction no longer claims that the proofs use only naturality and addition, and its novelty
  claim is restricted to a general braided monoidal category. Section 2 records the specialisation
  to symmetric monoidal categories ($\mu(1 \pm c) = \mu \pm \mu c$, $(1 \pm c)(1 \mp c) = 0$, and the twist
  of an involution is an involution), which is what `Symmetric.lean` formalizes. The Lean development was rewritten
  (the topic files `Defect`/`Family`/`Twisted`/`DerivationObject`/`Symmetric`, plus `Examples`) and now builds
  with `lake build` against a pinned Mathlib; it covers the results of Sections 3--5 that are
  formalized, including the
  derivation object of Theorem 4.3 (`DerivationObject.lean`: the defect map as a morphism
  `Φ : [A,A] ⟶ [A⊗A,A]`, `Der μ = ker Φ`, the isomorphism `(T ⟶ Der μ) ≃ {f : T⊗A → A | E_f = 0}`
  natural in `T`, and `Der μ ↪ Der μ(1+c)`), and records the sharper hypotheses of Theorem 5.1 (i)
  and (ii). The README regained
  its mathematics, its Lean instructions now reproduce the build, and the missing
  `formalization-debt.md` exists. A second pass over the same tree, against the sources themselves,
  is `results/deep-review-v3.pdf`, with the line-by-line ledger in `results/fixes-applied-v3.md`.
  What it changed: the abstract states the standing hypothesis of Section 2 (enrichment over abelian
  groups) and says "every case treated here" instead of "all cases"; Definition 4.5 restores the
  hypotheses of Barnes--Schenkel--Szabo's Definition 3.4 (a quasitriangular quasi-Hopf algebra and a
  braided commutative algebra in its module category) and types its first morphism as
  $\zeta([\cdot,\cdot]\circ(\mathrm{id}\otimes\hat l))$; the sentences introducing Ion's Definition 1.5
  and Claim 2.14 of Graziani et al. are faithful to those sources (a braided algebra, and a claim
  recalled there from Goyvaerts--Vercruysse); the Fuchs--Runkel--Schweigert map is renamed (their
  $\varsigma$ is an endomorphism of $A$, not of $A \otimes A$); the label of the middle vertical in
  the kernel diagram after Theorem 4.3 is the identity instead of $\Phi_+$, which is not an
  endomorphism of $[A,A]$, and the paragraph after that diagram records that only Lemma 4.2 uses the
  symmetry; "closed" is defined before Theorem 4.3, and Remark 4.4 no longer assumes a symmetry the
  identification does not use (it gives the one-line argument from Pareigis' Corollary 5.6); the
  family defect is identified with Pareigis' rule at the universal family $f = \mathrm{ev}$, not at
  the unit object, where the braiding disappears; Section 2 no longer claims to hold in every
  symmetric category without its further hypotheses, nor to contain no new results; the sentence on
  Jordan derivations of rings names its hypothesis and gives Cusack the priority the survey gives
  him; Theorem 5.2 carries the associativity and the characteristic its source assumes, and semiprime
  is defined; the two stale `% claim-ok` comments in Section 5 are corrected; and the Pareigis entry
  of the bibliography carries its journal data. The Lean docstrings were corrected in the same pass:
  the twist is $\sigma = (\alpha \otimes \alpha) \circ c$ (not its reverse), the family lemma is
  Lemma 4.2 (not 4.1), $E_f$ is written in the order in which it composes, and the summary of
  Section 5 keeps the $2$-torsion-freeness its eigenvector statement needs.
  `comp_antisymmetrized_symmetrized` was added, so that both halves of $(1 \pm c)(1 \mp c) = 0$ that
  Section 2 states are formalized (54 theorems); the README's claim that the Lean code covers every
  result of Sections 3--5 is qualified, and three entries of `formalization-debt.md` were corrected.
- **v2** (2026-10-30): Ion 2010 (arXiv 1004.5022) fetched and cited: Definition 1.5 (braided
  commutator, recalled; the antisymmetrized product is the braided commutator of an associative
  algebra) and Definition 1.4 (c-commutative, now the source of the name commutative). No result
  changed.
- **v1** (2026-10-29): first version. Four sections: the Leibniz defect, the commutative case and
  the derivation object, a twisted involution, with four commutative diagrams. Results proved in
  Lean in `lean/Research/BraidedJordanCategorical` (see `formalization-debt.md`).

## References

Citations of the works the paper uses. The works themselves are collected in
`braided-jordan-categorical-v2-references.zip`.

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

The repository is updated after every release of the paper. The research workspace that produced it
is private; the final source, PDF and Lean code are published here.
