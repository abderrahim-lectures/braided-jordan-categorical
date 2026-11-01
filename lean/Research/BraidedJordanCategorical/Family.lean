/-
Copyright (c) 2026 Abderrahim Adrabi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abderrahim Adrabi
-/
module

public import Research.BraidedJordanCategorical.Defect
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Families of derivations

For an object `T`, a `T`-family is a morphism `f : T ⊗ A ⟶ A`; it is the family form of a
derivation, and the object of derivations of Pareigis is characterised by such families. The
Leibniz terms of `f` are `ℓ_f = f ⊗ 1` and `r_f = (1 ⊗ f) ≫ (c_{T,A} ⊗ 1)`, and the defect of
the family is

`E_f = (T ◁ μ) ≫ f - ℓ_f ≫ μ - r_f ≫ μ`.

This file contains Lemma 4.2 of the paper: in a symmetric category the defect of `f` for the
symmetrized product is the defect of `f` for `μ` composed with `T ◁ (1 + c)`.

## Main results

* `familyLeft_braiding`, `familyRight_braiding`: the Leibniz terms are exchanged by the braiding.
* `familyDefect_symmetrized`: `E⁺_f = E_f ∘ (T ⊗ (1 + c))`, that is,
  `T ◁ (1 + c) ≫ E_f` (Lemma 4.2).

## References

* A. Adrabi, *Derivations of the symmetrized product in a braided monoidal category*.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace BraidedJordanCategorical

section Family

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

variable {T A : C}

/-- The first Leibniz term `ℓ_f = f ⊗ 1` of a `T`-family `f : T ⊗ A ⟶ A`. -/
@[expose]
def familyLeft (f : T ⊗ A ⟶ A) : T ⊗ (A ⊗ A) ⟶ A ⊗ A :=
  (α_ T A A).inv ≫ f ▷ A

/-- The second Leibniz term `r_f = (1 ⊗ f) ≫ (c_{T,A} ⊗ 1)` of a `T`-family `f : T ⊗ A ⟶ A`:
`f` is applied to the second factor, after `T` has passed the first one. -/
@[expose]
def familyRight (f : T ⊗ A ⟶ A) : T ⊗ (A ⊗ A) ⟶ A ⊗ A :=
  (α_ T A A).inv ≫ (β_ T A).hom ▷ A ≫ (α_ A T A).hom ≫ A ◁ f

/-- The braiding sends the first Leibniz term of a family to the second one. -/
theorem familyLeft_braiding (f : T ⊗ A ⟶ A) :
    familyLeft f ≫ (β_ A A).hom = T ◁ (β_ A A).hom ≫ familyRight f := by
  have h := hexagon_reverse T A A
  have key : (α_ T A A).inv ≫ (β_ (T ⊗ A) A).hom
      = T ◁ (β_ A A).hom ≫ (α_ T A A).inv ≫ (β_ T A).hom ▷ A ≫ (α_ A T A).hom := by
    have h2 : (α_ T A A).inv ≫ (β_ (T ⊗ A) A).hom
        = (T ◁ (β_ A A).hom ≫ (α_ T A A).inv ≫ (β_ T A).hom ▷ A) ≫ (α_ A T A).hom :=
      (Iso.comp_inv_eq (α_ A T A)).1 (by simpa only [Category.assoc] using h)
    simpa only [Category.assoc] using h2
  unfold familyLeft familyRight
  rw [Category.assoc, braiding_naturality_left, ← Category.assoc (α_ T A A).inv, key]
  simp only [Category.assoc]

/-- If the double braiding of `T` and `A` is the identity, the braiding sends the second Leibniz
term of a family to the first one. -/
theorem familyRight_braiding (hsym : (β_ T A).hom ≫ (β_ A T).hom = 𝟙 (T ⊗ A))
    (f : T ⊗ A ⟶ A) : familyRight f ≫ (β_ A A).hom = T ◁ (β_ A A).hom ≫ familyLeft f := by
  have hex := hexagon_forward A T A
  have key : (α_ A T A).hom ≫ (β_ A (T ⊗ A)).hom
      = (β_ A T).hom ▷ A ≫ (α_ T A A).hom ≫ T ◁ (β_ A A).hom ≫ (α_ T A A).inv := by
    have h2 : (α_ A T A).hom ≫ (β_ A (T ⊗ A)).hom
        = ((β_ A T).hom ▷ A ≫ (α_ T A A).hom ≫ T ◁ (β_ A A).hom) ≫ (α_ T A A).inv :=
      (Iso.eq_comp_inv (α_ T A A)).2 (by simpa only [Category.assoc] using hex)
    simpa only [Category.assoc] using h2
  unfold familyRight familyLeft
  simp only [Category.assoc]
  rw [braiding_naturality_right, ← Category.assoc (α_ A T A).hom, key]
  simp only [Category.assoc]
  rw [← Category.assoc ((β_ T A).hom ▷ A), ← comp_whiskerRight, hsym, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id_assoc]

end Family

section FamilyDefect

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]

variable {T A : C}

/-- The defect of a `T`-family `f` for the product `μ`. -/
@[expose]
def familyDefect (μ : A ⊗ A ⟶ A) (f : T ⊗ A ⟶ A) : T ⊗ (A ⊗ A) ⟶ A :=
  T ◁ μ ≫ f - familyLeft f ≫ μ - familyRight f ≫ μ

end FamilyDefect

section SymmetricFamily

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [Preadditive C]
  [MonoidalPreadditive C]

variable {T A : C}

/-- In a symmetric category the defect of a `T`-family for the symmetrized product is the defect
for `μ` composed with `T ◁ (1 + c)`. -/
theorem familyDefect_symmetrized (μ : A ⊗ A ⟶ A) (f : T ⊗ A ⟶ A) :
    familyDefect (symmetrizedProduct μ) f
      = T ◁ (𝟙 (A ⊗ A) + (β_ A A).hom) ≫ familyDefect μ f := by
  have e2 : T ◁ (𝟙 (A ⊗ A) + (β_ A A).hom) = 𝟙 (T ⊗ (A ⊗ A)) + T ◁ (β_ A A).hom := by
    simp
  have e3 : familyLeft f ≫ (β_ A A).hom ≫ μ = T ◁ (β_ A A).hom ≫ familyRight f ≫ μ := by
    rw [← Category.assoc, familyLeft_braiding, Category.assoc]
  have e4 : familyRight f ≫ (β_ A A).hom ≫ μ = T ◁ (β_ A A).hom ≫ familyLeft f ≫ μ := by
    rw [← Category.assoc, familyRight_braiding (SymmetricCategory.symmetry T A), Category.assoc]
  unfold familyDefect symmetrizedProduct
  rw [whiskerLeft_comp, e2]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_sub, Category.id_comp,
    Category.assoc, e3, e4]
  abel

end SymmetricFamily

end BraidedJordanCategorical
