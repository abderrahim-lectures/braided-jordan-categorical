import Mathlib
import Research.BraidedJordanCategorical.Defect

/-! Result R6: derivations with a parameter object `T` (Pareigis, Definition 5.5).
A `T`-family is a map `f : T ⊗ A ⟶ A`. The proofs need `T` to braid symmetrically
with `A`, so the category is symmetric. -/

open CategoryTheory MonoidalCategory BraidedCategory

namespace BraidedJordanCategorical

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] {T A : C}

/-- First Leibniz term of a family: `(f ⊗ 1)` on `T ⊗ (A ⊗ A)`. -/
def famLeft (f : T ⊗ A ⟶ A) : T ⊗ (A ⊗ A) ⟶ A ⊗ A :=
  (α_ T A A).inv ≫ f ▷ A

/-- Second Leibniz term of a family: `f` is applied to the second factor, after `T`
has passed the first. -/
def famRight (f : T ⊗ A ⟶ A) : T ⊗ (A ⊗ A) ⟶ A ⊗ A :=
  (α_ T A A).inv ≫ (β_ T A).hom ▷ A ≫ (α_ A T A).hom ≫ A ◁ f

/-- The defect of a `T`-family `f` for the product `μ`. -/
def famDefect (μ : A ⊗ A ⟶ A) (f : T ⊗ A ⟶ A) : T ⊗ (A ⊗ A) ⟶ A :=
  T ◁ μ ≫ f - famLeft f ≫ μ - famRight f ≫ μ

omit [Preadditive C] in
theorem famLeft_c (f : T ⊗ A ⟶ A) : famLeft f ≫ c A = T ◁ c A ≫ famRight f := by
  have h := hexagon_reverse T A A
  have key : (α_ T A A).inv ≫ (β_ (T ⊗ A) A).hom =
      T ◁ (β_ A A).hom ≫ (α_ T A A).inv ≫ (β_ T A).hom ▷ A ≫ (α_ A T A).hom := by
    have h2 : (α_ T A A).inv ≫ (β_ (T ⊗ A) A).hom =
        (T ◁ (β_ A A).hom ≫ (α_ T A A).inv ≫ (β_ T A).hom ▷ A) ≫ (α_ A T A).hom :=
      (Iso.comp_inv_eq (α_ A T A)).1 (by simpa only [Category.assoc] using h)
    simpa only [Category.assoc] using h2
  unfold famLeft famRight c
  rw [Category.assoc, braiding_naturality_left, ← Category.assoc (α_ T A A).inv, key]
  simp only [Category.assoc]

omit [Preadditive C] in
/-- The second term goes back to the first when `T` braids symmetrically with `A`,
that is, when the double braiding of `T` and `A` is the identity. -/
theorem famRight_c (hsym : (β_ T A).hom ≫ (β_ A T).hom = 𝟙 _) (f : T ⊗ A ⟶ A) :
    famRight f ≫ c A = T ◁ c A ≫ famLeft f := by
  have hex := hexagon_forward A T A
  have key : (α_ A T A).hom ≫ (β_ A (T ⊗ A)).hom = (β_ A T).hom ▷ A ≫ (α_ T A A).hom ≫
      T ◁ (β_ A A).hom ≫ (α_ T A A).inv := by
    have h2 : (α_ A T A).hom ≫ (β_ A (T ⊗ A)).hom =
        ((β_ A T).hom ▷ A ≫ (α_ T A A).hom ≫ T ◁ (β_ A A).hom) ≫ (α_ T A A).inv :=
      (Iso.eq_comp_inv (α_ T A A)).2 (by simpa only [Category.assoc] using hex)
    simpa only [Category.assoc] using h2
  unfold famRight famLeft c
  simp only [Category.assoc]
  rw [braiding_naturality_right, ← Category.assoc (α_ A T A).hom, key]
  simp only [Category.assoc]
  rw [← Category.assoc ((β_ T A).hom ▷ A), ← comp_whiskerRight, hsym,
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc]

/-- R6: for a family `f : T ⊗ A ⟶ A`, the defect of `μ(1 + c)` is the defect of `μ`
composed with `T ◁ (1 + c)`. So `f` derives `μ(1 + c)` iff `T ◁ (1 + c) ≫ E_f = 0`.
This needs `T` to braid symmetrically with `A`. -/
theorem famDefect_plus [MonoidalPreadditive C] (hsym : (β_ T A).hom ≫ (β_ A T).hom = 𝟙 _)
    (μ : A ⊗ A ⟶ A) (f : T ⊗ A ⟶ A) :
    famDefect (mulPlus μ) f = T ◁ (𝟙 _ + c A) ≫ famDefect μ f := by
  have e2 : T ◁ (𝟙 (A ⊗ A) + c A) = 𝟙 _ + T ◁ c A := by
    rw [MonoidalPreadditive.whiskerLeft_add, whiskerLeft_id]
  have e3 : famLeft f ≫ c A ≫ μ = T ◁ c A ≫ famRight f ≫ μ := by
    rw [← Category.assoc, famLeft_c, Category.assoc]
  have e4 : famRight f ≫ c A ≫ μ = T ◁ c A ≫ famLeft f ≫ μ := by
    rw [← Category.assoc, famRight_c hsym, Category.assoc]
  unfold famDefect mulPlus
  rw [whiskerLeft_comp, e2]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_sub,
    Category.id_comp, Category.assoc, e3, e4]
  abel

end BraidedJordanCategorical
