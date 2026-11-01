# Formalization debt

What the Lean development in `lean/` checks, what it does not, and where its statements differ from
the paper's. The paper is `paper/braided-jordan-categorical.tex` (v3); the Lean code is
`lean/Research/BraidedJordanCategorical/` and is built by `lake build` (Lean v4.33.1, Mathlib
`v4.33.1`).

## What is checked

The conventions of the Lean code are the paper's: `leibnizMap D = D ▷ A + A ◁ D` is `Δ_D`,
`leibnizDefect μ D = μ ≫ D - leibnizMap D ≫ μ` is `E_D`, `IsDerivation μ D` is `E_D = 0`,
`symmetrizedProduct μ = μ(1 + c)` and `antisymmetrizedProduct μ = μ(1 - c)`; a `T`-family is a
morphism `T ⊗ A ⟶ A` with defect `familyDefect μ f`.

| Paper | Lean |
|---|---|
| Definition 2.2 (derivation) | `IsDerivation` |
| Definition 2.4 (Leibniz defect) | `leibnizDefect` |
| Lemma 3.1 | `braiding_leibnizMap` |
| Proposition 3.2 | `leibnizDefect_symmetrized`, `leibnizDefect_antisymmetrized`, `isDerivation_symmetrized_iff`, `isDerivation_antisymmetrized_iff` |
| Corollary 3.3 | `isDerivation_symmetrized_of_isDerivation`, `isDerivation_antisymmetrized_of_isDerivation` |
| Theorem 3.4 | `isDerivation_of_symmetrized_of_antisymmetrized` |
| Theorem 4.1 | `braiding_leibnizDefect`, `isDerivation_symmetrized_iff_of_commutative` |
| Lemma 4.2 | `familyLeft_braiding`, `familyRight_braiding`, `familyDefect_symmetrized` |
| Theorem 4.3 | `familyDefect_comp_tensor` (naturality of `f ↦ E_f` in `T`), `derivationMorphism` (`Φ`), `familyDefect_eq_zero_iff`, `DerivationObject` (`ker Φ`), `derivationObjectEquiv` (the isomorphism `(T ⟶ Der μ) ≃ {f // E_f = 0}`), `derivationObjectEquiv_natural` (naturality in `T`), `derivationInclusion` with `Mono` (`Der μ ↪ Der μ(1+c)`), `derivationObject` (the three assertions together) |
| Theorem 5.1 (i) | `leibnizDefect_twisted` |
| Theorem 5.1 (ii) | `leibnizDefect_add_comp` |
| Theorem 5.1 (iii) | `leibnizDefect_comp_tensor_of_eigenvector`, `leibnizDefect_comp_tensor_of_neg_eigenvector` |
| hypothesis of Theorems 3.4, 4.1, 5.1(iii) | `TwoTorsionFree`, satisfiable: `twoTorsionFree_moduleCat` |
| the symmetric case | `Symmetric.lean`: `symmetrizedProduct_eq_add`, `antisymmetrizedProduct_eq_sub`, `symmetrizedProduct_eq_add_self` (`μ_+ = μ + μ` for a commutative product), `antisymmetrizedProduct_eq_zero`, `comp_symmetrized_antisymmetrized` and `comp_antisymmetrized_symmetrized` (`(1 ± c)(1 ∓ c) = 0`), `twistedProduct_eq_add`, and `twistedBraiding_comp_self` (the twist of an involution is an involution) |

All theorems depend only on `propext`, `Classical.choice` and `Quot.sound`; the files contain no
`sorry`, no `axiom`, no `native_decide` and no heartbeat override. Proposition 3.2 is proved from
one general lemma, `comp_leibnizDefect`, rather than three times.

## What is not checked

1. **Remark 4.4** (the identification with Pareigis' `Der(A)`) and **Definition 4.5**
   (Barnes--Schenkel--Szabo), which the paper quotes for context: they are statements about
   Yetter--Drinfeld modules and quasi-Hopf algebras, not about an abstract symmetric closed category.
2. **The vector-space corollaries** in §4 and §5 (`A = A_+ ⊕ A_-`, the vanishing on `A_+ ⊗ A_-` for
   reduced commutative algebras, the Jordan derivation literature). These depend on the author's
   first paper [1] or on cited results, not on the paper's own computations.

## Where the Lean statements differ from the paper's

These are deliberate and are recorded here so that a reader comparing the two does not take them
for errors.

1. **Enrichment.** The paper assumes in §2 that composition and `⊗` are bilinear. The Lean code
   assumes `[Preadditive C]` for everything and `[MonoidalPreadditive C]` only where `⊗` is used
   additively: `neg_tensor_neg`, hence `leibnizDefect_comp_tensor_of_neg_eigenvector`,
   `familyDefect_symmetrized`, the kernel criterion `curryFamily_eq_zero_iff`, and the whole section
   `Object` (so the statement of Theorem 4.3 in Lean, `derivationObject`, assumes additivity of
   `⊗`). In particular all of §3 and §4 up to Lemma 4.2 needs no additivity of `⊗`.
2. **Closedness and kernels.** Theorem 4.3 assumes a symmetric closed category with kernels. In
   Lean that is `[MonoidalClosed C]` (the internal hom `X ⟶[C] Y` and `MonoidalClosed.curry`) and a
   `[Limits.HasKernel (derivationMorphism μ)]` instance for each of the two morphisms, rather than a
   global `HasKernels C`; the per-morphism form is what the proof uses, and `HasKernels C` would
   supply the instances.
3. **`DerivationObject` is an `abbrev`.** It is definitionally `Limits.kernel (derivationMorphism μ)`,
   so that the kernel's universal property applies to it without transport.
4. **The factorization `Φ₊ = (1+c)* ∘ Φ`.** The paper derives the containment `Der μ ⊆ Der μ(1+c)`
   from this factorization. The Lean proof establishes the consequence it needs, namely
   `kernel_ι_comp_derivationMorphism_symmetrized : kernel.ι Φ ≫ Φ₊ = 0`, directly from
   `familyDefect_symmetrized`, and does not state the factorization as an equation of internal-hom
   morphisms. The containment and its monomorphism are the same.
5. **Two-torsion freeness.** `TwoTorsionFree C` is a plain `def`, not a typeclass, so each theorem
   that needs it takes `(hC : TwoTorsionFree C)` explicitly.
6. **Theorem 5.1 is sharper in the paper too (v3).** `leibnizDefect_twisted` assumes only
   `D ≫ α = α ≫ D`, and `leibnizDefect_add_comp` assumes `c ≫ μ = μ` in addition; only the
   eigenvector statements assume `TwoTorsionFree C`.
7. **Coherence is not eliminated.** The paper omits associators and unitors by coherence; the Lean
   code cannot, so `familyLeft` and `familyRight` begin with `(α_ T A A).inv`. The factor
   `T ◁ (1 + c)` of `familyDefect_symmetrized` is the paper's `T ⊗ (1 + c)` (whiskering on the left
   is the tensor with `𝟙 T`), not a different morphism.
8. **`familyRight_braiding` keeps the symmetry hypothesis explicit.** It is proved for a braided
   category plus `(β_ T A).hom ≫ (β_ A T).hom = 𝟙 (T ⊗ A)`, and `familyDefect_symmetrized` is
   stated in a `[SymmetricCategory C]` section, where the hypothesis is discharged by
   `SymmetricCategory.symmetry`.
9. **Definitions are `@[expose]`d.** The files use Lean's module system, so a definition whose body
   a later file must unfold carries `@[expose]`; this is a compiling device, not a mathematical
   statement.
10. **The braided (non-symmetric) form of Theorem 4.3 is not formalized.** The sentence after the
    proof of Theorem 4.3 says that $\Phi$, and with it $\Der(\mu)$, is available already in a braided
    monoidal closed category. The Lean construction of $\Phi$ is carried out in sections with
    `[SymmetricCategory C]` (`DerivationObject.lean`, the currying convention uses the symmetry:
    `uncurryFamily`, `curryFamily`, `derivationMorphism`, `DerivationObject`), so the formalization
    covers the symmetric statement only.
11. **The general form of $\sigma^2$ is not formalized.** `twistedBraiding_comp_self` proves that
    the twist of an involution is an involution in a symmetric category; the identity
    $\sigma^2=(\alpha^2\otimes\alpha^2)\circ c^2$ of Section 5, from which the paper reads off the
    two hypotheses, is not a theorem of the Lean code.
