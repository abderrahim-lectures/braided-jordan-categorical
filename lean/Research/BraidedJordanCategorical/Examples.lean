/-
Copyright (c) 2026 Abderrahim Adrabi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abderrahim Adrabi
-/
module

public import Research.BraidedJordanCategorical.Defect
public import Research.BraidedJordanCategorical.Twisted
public import Research.BraidedJordanCategorical.Family
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# Non-vacuity of the two-torsion freeness hypothesis

Theorems 3.4, 4.1 and 5.1 of the paper assume that the ambient category is two-torsion free. This
file checks that the hypothesis holds for the motivating example, modules over a field in which
`2 ≠ 0`, and instantiates the main results there.

## Main results

* `twoTorsionFree_moduleCat`: `ModuleCat K` is two-torsion free when `2 ≠ 0` in `K`.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace BraidedJordanCategorical

/-- Over a field in which `2 ≠ 0`, modules form a two-torsion free category. -/
theorem twoTorsionFree_moduleCat (K : Type u) [Field K] [NeZero (2 : K)] :
    TwoTorsionFree (ModuleCat.{u} K) := by
  intro X Y f hf
  ext x
  have h : (2 : K) • f.hom x = 0 := by
    have h1 : (f + f).hom x = (0 : X ⟶ Y).hom x := congrArg (fun g : X ⟶ Y => g.hom x) hf
    simpa [two_smul] using h1
  have key : ((2 : K)⁻¹ * 2) • f.hom x = f.hom x := by
    rw [inv_mul_cancel₀ (NeZero.ne 2), one_smul]
  rw [mul_smul, h, smul_zero] at key
  exact key.symm

section ModuleCat

variable (K : Type u) [Field K] [NeZero (2 : K)]

example : TwoTorsionFree (ModuleCat.{u} K) :=
  twoTorsionFree_moduleCat K

variable {A : ModuleCat.{u} K}

/-- Theorem 3.4 for modules over a field of characteristic not two. -/
example (μ : A ⊗ A ⟶ A) (D : A ⟶ A) (hp : IsDerivation (symmetrizedProduct μ) D)
    (hm : IsDerivation (antisymmetrizedProduct μ) D) : IsDerivation μ D :=
  isDerivation_of_symmetrized_of_antisymmetrized (twoTorsionFree_moduleCat K) hp hm

/-- Theorem 4.1 for modules over a field of characteristic not two. -/
example (μ : A ⊗ A ⟶ A) (hc : (β_ A A).hom ≫ μ = μ) (D : A ⟶ A) :
    IsDerivation (symmetrizedProduct μ) D ↔ IsDerivation μ D :=
  isDerivation_symmetrized_iff_of_commutative hc (twoTorsionFree_moduleCat K) D

end ModuleCat

end BraidedJordanCategorical
