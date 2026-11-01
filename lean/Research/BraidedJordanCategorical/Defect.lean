/-
Copyright (c) 2026 Abderrahim Adrabi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abderrahim Adrabi
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Tactic.Abel

/-!
# The Leibniz defect of the symmetrized and antisymmetrized products

Let `C` be a braided monoidal category whose hom-sets are abelian groups, so that
composition is bilinear, and let `μ : A ⊗ A ⟶ A` be any morphism; no associativity of `μ`
is assumed. Write `c` for the braiding `β_ A A` and, for an endomorphism `D` of `A`, let
`Δ_D = D ▷ A + A ◁ D` be the Leibniz map. The *Leibniz defect*

`E_D = μ ≫ D - Δ_D ≫ μ`

measures the failure of `D` to satisfy the Leibniz rule for `μ`; `D` is a derivation of `μ`
when `E_D = 0`. The results collected here are those of Sections 3 and 4 of the paper.

## Main results

* `braiding_leibnizMap`: the braiding commutes with `Δ_D` (Lemma 3.1).
* `leibnizDefect_symmetrized`, `leibnizDefect_antisymmetrized`: the defect of `μ(1 ± c)` is
  `E_D` composed with `1 ± c` (Proposition 3.2).
* `isDerivation_symmetrized_of_isDerivation`, `isDerivation_antisymmetrized_of_isDerivation`: a
  derivation of `μ` derives both braided products (Corollary 3.3).
* `isDerivation_of_symmetrized_of_antisymmetrized`: in a two-torsion free category, a
  derivation of both braided products derives `μ` (Theorem 3.4).
* `isDerivation_symmetrized_iff_of_commutative`: for a commutative product the derivations of
  `μ(1 + c)` and of `μ` coincide (Theorem 4.1).

## References

* A. Adrabi, *Derivations of the symmetrized product in a braided monoidal category*.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace BraidedJordanCategorical

section MonoidalPreadditive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]

variable {A : C}

/-- The Leibniz map `Δ_D = D ⊗ 1 + 1 ⊗ D` of an endomorphism `D` of `A`. -/
@[expose]
def leibnizMap (D : A ⟶ A) : A ⊗ A ⟶ A ⊗ A :=
  D ▷ A + A ◁ D

/-- The Leibniz defect `E_D = μ ≫ D - Δ_D ≫ μ` of `D` with respect to `μ`. -/
@[expose]
def leibnizDefect (μ : A ⊗ A ⟶ A) (D : A ⟶ A) : A ⊗ A ⟶ A :=
  μ ≫ D - leibnizMap D ≫ μ

/-- `D` is a derivation of the product `μ` if its Leibniz defect vanishes. -/
@[expose]
def IsDerivation (μ : A ⊗ A ⟶ A) (D : A ⟶ A) : Prop :=
  leibnizDefect μ D = 0

@[simp]
theorem isDerivation_iff {μ : A ⊗ A ⟶ A} {D : A ⟶ A} :
    IsDerivation μ D ↔ leibnizDefect μ D = 0 :=
  Iff.rfl

/-- If `f` commutes with the Leibniz map, then composing the defect with `f` gives the defect of
the product `f ≫ μ`. This is the single computation behind Proposition 3.2. -/
theorem comp_leibnizDefect {μ : A ⊗ A ⟶ A} {D : A ⟶ A} {f : A ⊗ A ⟶ A ⊗ A}
    (h : leibnizMap D ≫ f = f ≫ leibnizMap D) :
    f ≫ leibnizDefect μ D = leibnizDefect (f ≫ μ) D := by
  have h' : leibnizMap D ≫ f ≫ μ = f ≫ leibnizMap D ≫ μ := by
    rw [← Category.assoc, h, Category.assoc]
  simp only [leibnizDefect, Preadditive.comp_sub, Category.assoc, h']

/-- A preadditive category is two-torsion free if doubling is injective on every hom-set. -/
@[expose]
def TwoTorsionFree (C : Type u) [Category.{v} C] [Preadditive C] : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), f + f = 0 → f = 0

end MonoidalPreadditive

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]

variable {A : C}

/-- The symmetrized product `μ(1 + c)` of `μ`, where `c = β_ A A` is the braiding. -/
@[expose]
def symmetrizedProduct (μ : A ⊗ A ⟶ A) : A ⊗ A ⟶ A :=
  (𝟙 (A ⊗ A) + (β_ A A).hom) ≫ μ

/-- The antisymmetrized product `μ(1 - c)` of `μ`, where `c = β_ A A` is the braiding. -/
@[expose]
def antisymmetrizedProduct (μ : A ⊗ A ⟶ A) : A ⊗ A ⟶ A :=
  (𝟙 (A ⊗ A) - (β_ A A).hom) ≫ μ

/-- The braiding commutes with the Leibniz map: `c ≫ Δ_D = Δ_D ≫ c`. -/
theorem braiding_leibnizMap (D : A ⟶ A) :
    (β_ A A).hom ≫ leibnizMap D = leibnizMap D ≫ (β_ A A).hom := by
  simp only [leibnizMap, Preadditive.comp_add, Preadditive.add_comp, braiding_naturality_left,
    braiding_naturality_right, add_comm]

theorem leibnizMap_comp_symmetrized (D : A ⟶ A) :
    leibnizMap D ≫ (𝟙 (A ⊗ A) + (β_ A A).hom) = (𝟙 (A ⊗ A) + (β_ A A).hom) ≫ leibnizMap D := by
  rw [Preadditive.comp_add, Preadditive.add_comp, Category.comp_id, Category.id_comp,
    braiding_leibnizMap]

theorem leibnizMap_comp_antisymmetrized (D : A ⟶ A) :
    leibnizMap D ≫ (𝟙 (A ⊗ A) - (β_ A A).hom) = (𝟙 (A ⊗ A) - (β_ A A).hom) ≫ leibnizMap D := by
  rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
    braiding_leibnizMap]

/-- The defect of the symmetrized product is the defect of `μ` composed with `1 + c`. -/
theorem leibnizDefect_symmetrized (μ : A ⊗ A ⟶ A) (D : A ⟶ A) :
    leibnizDefect (symmetrizedProduct μ) D
      = (𝟙 (A ⊗ A) + (β_ A A).hom) ≫ leibnizDefect μ D :=
  (comp_leibnizDefect (leibnizMap_comp_symmetrized D)).symm

/-- The defect of the antisymmetrized product is the defect of `μ` composed with `1 - c`. -/
theorem leibnizDefect_antisymmetrized (μ : A ⊗ A ⟶ A) (D : A ⟶ A) :
    leibnizDefect (antisymmetrizedProduct μ) D
      = (𝟙 (A ⊗ A) - (β_ A A).hom) ≫ leibnizDefect μ D :=
  (comp_leibnizDefect (leibnizMap_comp_antisymmetrized D)).symm

/-- A morphism is a derivation of `μ(1 + c)` if and only if `E_D ≫ (1 + c)` vanishes. -/
theorem isDerivation_symmetrized_iff (μ : A ⊗ A ⟶ A) (D : A ⟶ A) :
    IsDerivation (symmetrizedProduct μ) D
      ↔ (𝟙 (A ⊗ A) + (β_ A A).hom) ≫ leibnizDefect μ D = 0 := by
  rw [isDerivation_iff, leibnizDefect_symmetrized]

/-- A morphism is a derivation of `μ(1 - c)` if and only if `E_D ≫ (1 - c)` vanishes. -/
theorem isDerivation_antisymmetrized_iff (μ : A ⊗ A ⟶ A) (D : A ⟶ A) :
    IsDerivation (antisymmetrizedProduct μ) D
      ↔ (𝟙 (A ⊗ A) - (β_ A A).hom) ≫ leibnizDefect μ D = 0 := by
  rw [isDerivation_iff, leibnizDefect_antisymmetrized]

/-- A derivation of `μ` is a derivation of `μ(1 + c)`. -/
theorem isDerivation_symmetrized_of_isDerivation {μ : A ⊗ A ⟶ A} {D : A ⟶ A}
    (h : IsDerivation μ D) : IsDerivation (symmetrizedProduct μ) D := by
  rw [isDerivation_symmetrized_iff, h]
  simp

/-- A derivation of `μ` is a derivation of `μ(1 - c)`. -/
theorem isDerivation_antisymmetrized_of_isDerivation {μ : A ⊗ A ⟶ A} {D : A ⟶ A}
    (h : IsDerivation μ D) : IsDerivation (antisymmetrizedProduct μ) D := by
  rw [isDerivation_antisymmetrized_iff, h]
  simp

/-- In a two-torsion free category, a derivation of `μ(1 + c)` and of `μ(1 - c)` derives `μ`. -/
theorem isDerivation_of_symmetrized_of_antisymmetrized (hC : TwoTorsionFree C)
    {μ : A ⊗ A ⟶ A} {D : A ⟶ A} (hp : IsDerivation (symmetrizedProduct μ) D)
    (hm : IsDerivation (antisymmetrizedProduct μ) D) : IsDerivation μ D := by
  rw [isDerivation_symmetrized_iff] at hp
  rw [isDerivation_antisymmetrized_iff] at hm
  refine hC _ ?_
  have hsum : (𝟙 (A ⊗ A) + (β_ A A).hom) ≫ leibnizDefect μ D
      + (𝟙 (A ⊗ A) - (β_ A A).hom) ≫ leibnizDefect μ D = 0 := by
    rw [hp, hm, add_zero]
  rw [← Preadditive.add_comp,
    show (𝟙 (A ⊗ A) + (β_ A A).hom) + (𝟙 (A ⊗ A) - (β_ A A).hom)
      = 𝟙 (A ⊗ A) + 𝟙 (A ⊗ A) by abel,
    Preadditive.add_comp, Category.id_comp] at hsum
  exact hsum

/-- For a commutative product `c ≫ μ = μ`, the braiding fixes the Leibniz defect. -/
theorem braiding_leibnizDefect {μ : A ⊗ A ⟶ A} (hc : (β_ A A).hom ≫ μ = μ) (D : A ⟶ A) :
    (β_ A A).hom ≫ leibnizDefect μ D = leibnizDefect μ D := by
  rw [leibnizDefect, Preadditive.comp_sub, ← Category.assoc, hc, ← Category.assoc,
    braiding_leibnizMap, Category.assoc, hc]

/-- For a commutative product, the derivations of `μ(1 + c)` and of `μ` coincide. -/
theorem isDerivation_symmetrized_iff_of_commutative {μ : A ⊗ A ⟶ A}
    (hc : (β_ A A).hom ≫ μ = μ) (hC : TwoTorsionFree C) (D : A ⟶ A) :
    IsDerivation (symmetrizedProduct μ) D ↔ IsDerivation μ D := by
  rw [isDerivation_symmetrized_iff, Preadditive.add_comp, Category.id_comp,
    braiding_leibnizDefect hc]
  exact ⟨fun h => hC _ h, fun h => by rw [h, add_zero]⟩

end Braided

end BraidedJordanCategorical
