/-
Copyright (c) 2026 Abderrahim Adrabi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abderrahim Adrabi
-/
module

public import Research.BraidedJordanCategorical.Defect
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The twist of the braiding

Let `α : A ⟶ A` be an endomorphism and let `σ = (α ⊗ α) ∘ c`, written `(β_ A A).hom ≫ (α ⊗ₘ α)`
in this file, be the braiding twisted by `α`. It is not a braiding unless `α` is compatible with the
braided structure, which is not assumed; `Symmetric.lean` shows that it is an involution when `α`
is one and the braiding is symmetric.
For a product `μ` write `μ_σ = μ(1 + σ)`. The results of this file are Section 5 of the paper:
if `μ` is commutative, `D` derives `μ_σ` and `D` commutes with `α`, then the Leibniz defect `E_D`
satisfies `E_D + E_D ∘ (α ⊗ α) = 0`, and, when `C` is two-torsion free, vanishes on `p ⊗ p'` for
eigenvectors `p`, `p'`
of `α` with the same eigenvalue. No compatibility of `α` with `μ` is assumed.

## Main results

* `leibnizDefect_twisted`: `E_D` for `μ_σ` is `E_D` composed with `1 + σ` (Theorem 5.1 (i)).
* `leibnizDefect_add_comp`: `E_D + E_D ∘ (α ⊗ α) = 0` for a derivation of `μ_σ`
  (Theorem 5.1 (ii)).
* `leibnizDefect_comp_tensor_of_eigenvector`, `leibnizDefect_comp_tensor_of_neg_eigenvector`:
  `E_D` vanishes on `p ⊗ p'` for eigenvectors with the same eigenvalue, when `C` is two-torsion free
  (Theorem 5.1 (iii)).

## References

* A. Adrabi, *Derivations of the symmetrized product in a braided monoidal category*.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace BraidedJordanCategorical

section Braiding

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

variable {A : C}

/-- The braiding twisted by `α`: `twistedBraiding α = (β_ A A).hom ≫ (α ⊗ₘ α)`, that is,
`σ = (α ⊗ α) ∘ c`. -/
@[expose]
def twistedBraiding (α : A ⟶ A) : A ⊗ A ⟶ A ⊗ A :=
  (β_ A A).hom ≫ (α ⊗ₘ α)

/-- The braiding commutes with `α ⊗ α`. -/
theorem braiding_tensorHom (α : A ⟶ A) :
    (β_ A A).hom ≫ (α ⊗ₘ α) = (α ⊗ₘ α) ≫ (β_ A A).hom :=
  (braiding_naturality α α).symm

end Braiding

section Leibniz

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

variable {A : C}

/-- The tensor square `α ⊗ α` commutes with the Leibniz map of any `D` commuting with `α`. -/
theorem leibnizMap_tensorHom {α D : A ⟶ A} (hD : D ≫ α = α ≫ D) :
    leibnizMap D ≫ (α ⊗ₘ α) = (α ⊗ₘ α) ≫ leibnizMap D := by
  simp only [leibnizMap, Preadditive.add_comp, Preadditive.comp_add, whiskerRight_comp_tensorHom,
    tensorHom_comp_whiskerRight, whiskerLeft_comp_tensorHom, tensorHom_comp_whiskerLeft, hD]

end Leibniz

section TensorNeg

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

/-- Negating both factors does not change a tensor of morphisms. -/
theorem neg_tensor_neg {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    (-f) ⊗ₘ (-g) = f ⊗ₘ g := by
  have h1 : (-f) ⊗ₘ (-g) + f ⊗ₘ (-g) = 0 := by
    rw [← MonoidalPreadditive.add_tensor, neg_add_cancel, MonoidalPreadditive.zero_tensor]
  have h2 : f ⊗ₘ (-g) + f ⊗ₘ g = 0 := by
    rw [← MonoidalPreadditive.tensor_add, neg_add_cancel, MonoidalPreadditive.tensor_zero]
  rw [eq_neg_of_add_eq_zero_left h1, eq_neg_of_add_eq_zero_left h2, neg_neg]

end TensorNeg

section Twisted

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]

variable {A : C}

/-- The twisted symmetrized product `μ(1 + σ)`. -/
@[expose]
def twistedProduct (μ : A ⊗ A ⟶ A) (α : A ⟶ A) : A ⊗ A ⟶ A :=
  (𝟙 (A ⊗ A) + twistedBraiding α) ≫ μ

/-- The twist commutes with the Leibniz map of any `D` commuting with `α`. -/
theorem leibnizMap_comp_twistedBraiding {α D : A ⟶ A} (hD : D ≫ α = α ≫ D) :
    leibnizMap D ≫ twistedBraiding α = twistedBraiding α ≫ leibnizMap D := by
  rw [twistedBraiding, ← Category.assoc, ← braiding_leibnizMap, Category.assoc,
    leibnizMap_tensorHom hD, ← Category.assoc]

/-- The defect of the twisted product is the defect of `μ` composed with `1 + σ`. -/
theorem leibnizDefect_twisted (μ : A ⊗ A ⟶ A) {α D : A ⟶ A} (hD : D ≫ α = α ≫ D) :
    leibnizDefect (twistedProduct μ α) D
      = (𝟙 (A ⊗ A) + twistedBraiding α) ≫ leibnizDefect μ D := by
  refine (comp_leibnizDefect (D := D) (μ := μ) (f := 𝟙 (A ⊗ A) + twistedBraiding α) ?_).symm
  rw [Preadditive.comp_add, Preadditive.add_comp, Category.comp_id, Category.id_comp,
    leibnizMap_comp_twistedBraiding hD]

/-- For a commutative product the twist acts on the defect as `α ⊗ α`. -/
theorem twistedBraiding_comp_leibnizDefect {μ : A ⊗ A ⟶ A} (hc : (β_ A A).hom ≫ μ = μ)
    (α : A ⟶ A) :
    twistedBraiding α ≫ leibnizDefect μ D = (α ⊗ₘ α) ≫ leibnizDefect μ D := by
  calc twistedBraiding α ≫ leibnizDefect μ D
      = ((β_ A A).hom ≫ (α ⊗ₘ α)) ≫ leibnizDefect μ D := rfl
    _ = ((α ⊗ₘ α) ≫ (β_ A A).hom) ≫ leibnizDefect μ D := by rw [braiding_tensorHom]
    _ = (α ⊗ₘ α) ≫ ((β_ A A).hom ≫ leibnizDefect μ D) := Category.assoc _ _ _
    _ = (α ⊗ₘ α) ≫ leibnizDefect μ D := by rw [braiding_leibnizDefect hc]

/-- For a commutative product, a derivation of `μ_σ` commuting with `α` satisfies
`E_D + E_D ∘ (α ⊗ α) = 0`. -/
theorem leibnizDefect_add_comp {μ : A ⊗ A ⟶ A} (hc : (β_ A A).hom ≫ μ = μ)
    {α D : A ⟶ A} (hD : D ≫ α = α ≫ D) (h : IsDerivation (twistedProduct μ α) D) :
    leibnizDefect μ D + (α ⊗ₘ α) ≫ leibnizDefect μ D = 0 := by
  rw [isDerivation_iff, leibnizDefect_twisted μ hD, Preadditive.add_comp, Category.id_comp] at h
  rwa [twistedBraiding_comp_leibnizDefect hc] at h

/-- An eigenvector relation `p ⊗ p' ≫ (α ⊗ α) = p ⊗ p'` forces `E_D` to vanish on `p ⊗ p'`. -/
theorem leibnizDefect_comp_tensor_eq_zero (hC : TwoTorsionFree C) {μ : A ⊗ A ⟶ A}
    (hc : (β_ A A).hom ≫ μ = μ) {α D : A ⟶ A} (hD : D ≫ α = α ≫ D)
    (h : IsDerivation (twistedProduct μ α) D) {X : C} {p p' : X ⟶ A}
    (hpp' : (p ⊗ₘ p') ≫ (α ⊗ₘ α) = p ⊗ₘ p') :
    (p ⊗ₘ p') ≫ leibnizDefect μ D = 0 := by
  refine hC _ ?_
  calc (p ⊗ₘ p') ≫ leibnizDefect μ D + (p ⊗ₘ p') ≫ leibnizDefect μ D
      = (p ⊗ₘ p') ≫ (leibnizDefect μ D + (α ⊗ₘ α) ≫ leibnizDefect μ D) := by
        rw [Preadditive.comp_add, ← Category.assoc, hpp']
    _ = 0 := by rw [leibnizDefect_add_comp hc hD h]; simp

/-- The defect vanishes on `p ⊗ p'` for `+1` eigenvectors `p`, `p'` of `α`. -/
theorem leibnizDefect_comp_tensor_of_eigenvector (hC : TwoTorsionFree C) {μ : A ⊗ A ⟶ A}
    (hc : (β_ A A).hom ≫ μ = μ) {α D : A ⟶ A} (hD : D ≫ α = α ≫ D)
    (h : IsDerivation (twistedProduct μ α) D) {X : C} {p p' : X ⟶ A}
    (hp : p ≫ α = p) (hp' : p' ≫ α = p') :
    (p ⊗ₘ p') ≫ leibnizDefect μ D = 0 := by
  refine leibnizDefect_comp_tensor_eq_zero hC hc hD h ?_
  rw [tensorHom_comp_tensorHom, hp, hp']

/-- The defect vanishes on `p ⊗ p'` for `-1` eigenvectors `p`, `p'` of `α`. -/
theorem leibnizDefect_comp_tensor_of_neg_eigenvector [MonoidalPreadditive C]
    (hC : TwoTorsionFree C) {μ : A ⊗ A ⟶ A} (hc : (β_ A A).hom ≫ μ = μ)
    {α D : A ⟶ A} (hD : D ≫ α = α ≫ D) (h : IsDerivation (twistedProduct μ α) D)
    {X : C} {p p' : X ⟶ A} (hp : p ≫ α = -p) (hp' : p' ≫ α = -p') :
    (p ⊗ₘ p') ≫ leibnizDefect μ D = 0 := by
  refine leibnizDefect_comp_tensor_eq_zero hC hc hD h ?_
  rw [tensorHom_comp_tensorHom, hp, hp', neg_tensor_neg]

end Twisted

end BraidedJordanCategorical
