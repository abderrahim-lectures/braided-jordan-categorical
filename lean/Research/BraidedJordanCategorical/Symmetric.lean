/-
Copyright (c) 2026 Abderrahim Adrabi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abderrahim Adrabi
-/
module

public import Research.BraidedJordanCategorical.Twisted

/-!
# The symmetric case

The paper states its results for a braided monoidal category. This file records the specialisation
to a **symmetric** monoidal category, the setting of the motivating examples (vector spaces, modules,
`Examples.lean`).

Nothing here weakens or repeats the braided results: `SymmetricCategory` extends `BraidedCategory`,
so every theorem of `Defect.lean`, `Family.lean`, `Twisted.lean` and `DerivationObject.lean` applies
verbatim in a symmetric monoidal category, and no alias for them is introduced. What is recorded here
are the statements that use the symmetry itself, namely `c² = 1`:

* `symmetrizedProduct_eq_add`, `antisymmetrizedProduct_eq_sub`: `μ(1 ± c) = μ ± μc`.
* `symmetrizedProduct_eq_add_self`: for a commutative `μ`, `μ(1 + c) = μ + μ`, which is the
  form `μ_+(x ⊗ y) = 2xy` of Section 4.
* `comp_symmetrized_antisymmetrized`, `comp_antisymmetrized_symmetrized`: `(1 ± c)(1 ∓ c) = 0`.
* `twistedBraiding_comp_self`: if `α` is an involution then so is the twist `σ = (α ⊗ α)c`. This
  is what makes Section 5 of the paper a *twisted involution*: it is the case `c² = id` and
  `α² = id_A` of the `σ² = (α² ⊗ α²) ∘ c²` of Section 5. That general identity is not formalized.
* `twistedProduct_eq_add`: `μ_σ = μ + μσ`.

## Main results

* `twistedBraiding_comp_self`: the twist of an involution is an involution.
* `comp_symmetrized_antisymmetrized`: the symmetrized and antisymmetrized factors annihilate
  each other.

## References

* A. Adrabi, *Derivations of the symmetrized product in a braided monoidal category*.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace BraidedJordanCategorical

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [Preadditive C]
variable {A : C}

/-- In a symmetric monoidal category the symmetrized product is `μ + μc`. -/
theorem symmetrizedProduct_eq_add (μ : A ⊗ A ⟶ A) :
    symmetrizedProduct μ = μ + (β_ A A).hom ≫ μ := by
  rw [symmetrizedProduct, Preadditive.add_comp, Category.id_comp]

/-- In a symmetric monoidal category the antisymmetrized product is `μ - μc`. -/
theorem antisymmetrizedProduct_eq_sub (μ : A ⊗ A ⟶ A) :
    antisymmetrizedProduct μ = μ - (β_ A A).hom ≫ μ := by
  rw [antisymmetrizedProduct, Preadditive.sub_comp, Category.id_comp]

/-- For a commutative product the symmetrized product is `μ + μ`: this is the form
`μ_+(x ⊗ y) = 2xy` of Section 4. -/
theorem symmetrizedProduct_eq_add_self {μ : A ⊗ A ⟶ A} (hc : (β_ A A).hom ≫ μ = μ) :
    symmetrizedProduct μ = μ + μ := by
  rw [symmetrizedProduct_eq_add, hc]

/-- For a commutative product the antisymmetrized product vanishes: it is the braided commutator of
Definition 2.3 (Ion's Definition 1.5), which is the zero map for a commutative product. -/
theorem antisymmetrizedProduct_eq_zero {μ : A ⊗ A ⟶ A} (hc : (β_ A A).hom ≫ μ = μ) :
    antisymmetrizedProduct μ = 0 := by
  rw [antisymmetrizedProduct_eq_sub, hc, sub_self]

/-- The two factors of the symmetrized and antisymmetrized products annihilate each other:
`(1 + c)(1 - c) = 0`, because the braiding on `A ⊗ A` is an involution. -/
theorem comp_symmetrized_antisymmetrized :
    (𝟙 (A ⊗ A) + (β_ A A).hom) ≫ (𝟙 (A ⊗ A) - (β_ A A).hom) = 0 := by
  rw [Preadditive.comp_sub, Preadditive.add_comp, Preadditive.add_comp]
  simp only [Category.comp_id, Category.id_comp, SymmetricCategory.symmetry]
  abel

/-- The two factors of the symmetrized and antisymmetrized products annihilate each other in the
other order as well: `(1 - c)(1 + c) = 0`. -/
theorem comp_antisymmetrized_symmetrized :
    (𝟙 (A ⊗ A) - (β_ A A).hom) ≫ (𝟙 (A ⊗ A) + (β_ A A).hom) = 0 := by
  rw [Preadditive.comp_add, Preadditive.sub_comp, Preadditive.sub_comp]
  simp only [Category.comp_id, Category.id_comp, SymmetricCategory.symmetry]
  abel

/-- In a symmetric monoidal category the twisted product is `μ + μσ`. -/
theorem twistedProduct_eq_add (μ : A ⊗ A ⟶ A) (α : A ⟶ A) :
    twistedProduct μ α = μ + twistedBraiding α ≫ μ := by
  rw [twistedProduct, Preadditive.add_comp, Category.id_comp]

end Symmetric

section SymmetricTwist

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {A : C}

/-- **The twist of an involution is an involution**: in a symmetric monoidal category, if
`α ≫ α = 𝟙` then `σ = (α ⊗ α)c` satisfies `σ ≫ σ = 𝟙`. This is the hypothesis-free form of
Section 5's `σ² = (α² ⊗ α²) ∘ c²`. -/
theorem twistedBraiding_comp_self {α : A ⟶ A} (hα : α ≫ α = 𝟙 A) :
    twistedBraiding α ≫ twistedBraiding α = 𝟙 (A ⊗ A) := by
  have ht : (α ⊗ₘ α) ≫ (α ⊗ₘ α) = 𝟙 (A ⊗ A) := by
    rw [tensorHom_comp_tensorHom, hα, tensorHom_id, id_whiskerRight]
  calc twistedBraiding α ≫ twistedBraiding α
      = (β_ A A).hom ≫ (α ⊗ₘ α) ≫ (β_ A A).hom ≫ (α ⊗ₘ α) := by
        simp only [twistedBraiding, Category.assoc]
    _ = (β_ A A).hom ≫ ((α ⊗ₘ α) ≫ (β_ A A).hom) ≫ (α ⊗ₘ α) := by rw [Category.assoc]
    _ = (β_ A A).hom ≫ ((β_ A A).hom ≫ (α ⊗ₘ α)) ≫ (α ⊗ₘ α) := by
        rw [braiding_tensorHom]
    _ = ((β_ A A).hom ≫ (β_ A A).hom) ≫ ((α ⊗ₘ α) ≫ (α ⊗ₘ α)) := by
        simp only [Category.assoc, tensorHom_comp_tensorHom]
    _ = 𝟙 (A ⊗ A) := by rw [SymmetricCategory.symmetry, ht, Category.id_comp]

end SymmetricTwist

end BraidedJordanCategorical
