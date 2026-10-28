import Mathlib

/-! Results R1 to R5 of the categorical paper: derivations of the symmetrized
product `μ(1 + c)` in a preadditive braided monoidal category. -/

open CategoryTheory MonoidalCategory BraidedCategory

namespace BraidedJordanCategorical

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C]

/-- The Leibniz map `D ⊗ 1 + 1 ⊗ D` on `A ⊗ A`. -/
def leib {A : C} (D : A ⟶ A) : A ⊗ A ⟶ A ⊗ A := D ▷ A + A ◁ D

/-- The braiding `c = c_{A,A}`. -/
def c (A : C) : A ⊗ A ⟶ A ⊗ A := (β_ A A).hom

/-- The symmetrized product `μ(1 + c)`. -/
def mulPlus {A : C} (μ : A ⊗ A ⟶ A) : A ⊗ A ⟶ A := (𝟙 _ + c A) ≫ μ

/-- The antisymmetrized product `μ(1 - c)`. -/
def mulMinus {A : C} (μ : A ⊗ A ⟶ A) : A ⊗ A ⟶ A := (𝟙 _ - c A) ≫ μ

/-- The defect of `D`: `D μ - μ (D ⊗ 1 + 1 ⊗ D)`. -/
def defect {A : C} (μ : A ⊗ A ⟶ A) (D : A ⟶ A) : A ⊗ A ⟶ A := μ ≫ D - leib D ≫ μ

/-- Naturality of the braiding for the Leibniz map. -/
theorem leib_comm_c {A : C} (D : A ⟶ A) : c A ≫ leib D = leib D ≫ c A := by
  unfold leib c
  rw [Preadditive.comp_add, Preadditive.add_comp, ← braiding_naturality_left,
    ← braiding_naturality_right, add_comm]

/-- R1: the defect of `μ(1 + c)` is the defect of `μ` composed with `1 + c`. -/
theorem defect_plus {A : C} (μ : A ⊗ A ⟶ A) (D : A ⟶ A) :
    (𝟙 _ + c A) ≫ defect μ D = defect (mulPlus μ) D := by
  have h : leib D ≫ (𝟙 _ + c A) = (𝟙 _ + c A) ≫ leib D := by
    rw [Preadditive.comp_add, Preadditive.add_comp, Category.comp_id, Category.id_comp,
      leib_comm_c]
  unfold defect mulPlus
  rw [Preadditive.comp_sub, ← Category.assoc (leib D), h, Category.assoc, Category.assoc]

/-- R3: the defect of `μ(1 - c)` is the defect of `μ` composed with `1 - c`. -/
theorem defect_minus {A : C} (μ : A ⊗ A ⟶ A) (D : A ⟶ A) :
    (𝟙 _ - c A) ≫ defect μ D = defect (mulMinus μ) D := by
  have h : leib D ≫ (𝟙 _ - c A) = (𝟙 _ - c A) ≫ leib D := by
    rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
      leib_comm_c]
  unfold defect mulMinus
  rw [Preadditive.comp_sub, ← Category.assoc (leib D), h, Category.assoc, Category.assoc]

/-- `D` is a derivation of `μ` when its defect vanishes. -/
def IsDeriv {A : C} (μ : A ⊗ A ⟶ A) (D : A ⟶ A) : Prop := defect μ D = 0

/-- R1, as a criterion: `D` derives `μ(1 + c)` iff `(1 + c) ≫ E_D = 0`. -/
theorem isDeriv_plus_iff {A : C} (μ : A ⊗ A ⟶ A) (D : A ⟶ A) :
    IsDeriv (mulPlus μ) D ↔ (𝟙 _ + c A) ≫ defect μ D = 0 := by
  unfold IsDeriv
  rw [defect_plus]

/-- R3, as a criterion: `D` derives `μ(1 - c)` iff `(1 - c) ≫ E_D = 0`. -/
theorem isDeriv_minus_iff {A : C} (μ : A ⊗ A ⟶ A) (D : A ⟶ A) :
    IsDeriv (mulMinus μ) D ↔ (𝟙 _ - c A) ≫ defect μ D = 0 := by
  unfold IsDeriv
  rw [defect_minus]

/-- R2: a derivation of `μ` derives `μ(1 + c)`. -/
theorem isDeriv_plus_of_isDeriv {A : C} {μ : A ⊗ A ⟶ A} {D : A ⟶ A}
    (h : IsDeriv μ D) : IsDeriv (mulPlus μ) D := by
  rw [isDeriv_plus_iff]
  unfold IsDeriv at h
  rw [h, Limits.comp_zero]

/-- R2: a derivation of `μ` derives `μ(1 - c)`. -/
theorem isDeriv_minus_of_isDeriv {A : C} {μ : A ⊗ A ⟶ A} {D : A ⟶ A}
    (h : IsDeriv μ D) : IsDeriv (mulMinus μ) D := by
  rw [isDeriv_minus_iff]
  unfold IsDeriv at h
  rw [h, Limits.comp_zero]

/-- R4: if no nonzero morphism is killed by `2`, a map deriving both `μ(1 + c)`
and `μ(1 - c)` derives `μ`. -/
theorem isDeriv_of_plus_minus {A : C} {μ : A ⊗ A ⟶ A} {D : A ⟶ A}
    (two : ∀ {X Y : C} (f : X ⟶ Y), f + f = 0 → f = 0)
    (hp : IsDeriv (mulPlus μ) D) (hm : IsDeriv (mulMinus μ) D) : IsDeriv μ D := by
  rw [isDeriv_plus_iff] at hp
  rw [isDeriv_minus_iff] at hm
  apply two
  have hsum : (𝟙 _ + c A) ≫ defect μ D + (𝟙 _ - c A) ≫ defect μ D
      = defect μ D + defect μ D := by
    rw [← Preadditive.add_comp, add_add_sub_cancel, Preadditive.add_comp, Category.id_comp]
  rw [← hsum, hp, hm, add_zero]

/-- R5: for a commutative product, the defect is symmetric. -/
theorem braid_defect {A : C} {μ : A ⊗ A ⟶ A} (hc : c A ≫ μ = μ) (D : A ⟶ A) :
    c A ≫ defect μ D = defect μ D := by
  unfold defect
  rw [Preadditive.comp_sub, ← Category.assoc (c A), hc, ← Category.assoc (c A),
    leib_comm_c, Category.assoc, hc]

/-- R5: for a commutative product, derivations of `μ(1 + c)` and of `μ` agree. -/
theorem isDeriv_plus_iff_commutative {A : C} {μ : A ⊗ A ⟶ A} (hc : c A ≫ μ = μ)
    (two : ∀ {X Y : C} (f : X ⟶ Y), f + f = 0 → f = 0) (D : A ⟶ A) :
    IsDeriv (mulPlus μ) D ↔ IsDeriv μ D := by
  rw [isDeriv_plus_iff, Preadditive.add_comp, braid_defect hc, Category.id_comp]
  exact ⟨two _, fun h => by rw [h, add_zero]⟩

/-- The twist `σ = c (α ⊗ α)`, `σ(x ⊗ y) = α y ⊗ α x`. -/
def sigma {A : C} (α : A ⟶ A) : A ⊗ A ⟶ A ⊗ A := c A ≫ (α ⊗ₘ α)

/-- The twisted symmetrized product `μ(1 + σ)`. -/
def mulTw {A : C} (μ : A ⊗ A ⟶ A) (α : A ⟶ A) : A ⊗ A ⟶ A := (𝟙 _ + sigma α) ≫ μ

omit [BraidedCategory C] in
/-- The Leibniz map commutes with `α ⊗ α` when `D` commutes with `α`. -/
theorem leib_comm_alpha {A : C} {α D : A ⟶ A} (hD : D ≫ α = α ≫ D) :
    leib D ≫ (α ⊗ₘ α) = (α ⊗ₘ α) ≫ leib D := by
  have h1 : D ▷ A ≫ (α ⊗ₘ α) = (α ⊗ₘ α) ≫ D ▷ A := by
    rw [MonoidalCategory.tensorHom_def, ← Category.assoc, ← comp_whiskerRight, hD, Category.assoc,
      whisker_exchange, ← Category.assoc, ← comp_whiskerRight]
  have h2 : A ◁ D ≫ (α ⊗ₘ α) = (α ⊗ₘ α) ≫ A ◁ D := by
    rw [MonoidalCategory.tensorHom_def, ← Category.assoc, whisker_exchange, Category.assoc,
      ← whiskerLeft_comp, hD, Category.assoc, ← whiskerLeft_comp]
  unfold leib
  rw [Preadditive.add_comp, Preadditive.comp_add, h1, h2]

/-- R7, first step: the defect of `μ(1 + σ)` is `(1 + σ) ≫ E_D`. -/
theorem defect_tw {A : C} {α D : A ⟶ A} (μ : A ⊗ A ⟶ A) (hD : D ≫ α = α ≫ D) :
    (𝟙 _ + sigma α) ≫ defect μ D = defect (mulTw μ α) D := by
  have hs : leib D ≫ sigma α = sigma α ≫ leib D := by
    unfold sigma
    rw [← Category.assoc, ← leib_comm_c, Category.assoc, leib_comm_alpha hD, ← Category.assoc]
  have h : leib D ≫ (𝟙 _ + sigma α) = (𝟙 _ + sigma α) ≫ leib D := by
    rw [Preadditive.comp_add, Preadditive.add_comp, Category.comp_id, Category.id_comp, hs]
  unfold defect mulTw
  rw [Preadditive.comp_sub, ← Category.assoc (leib D), h, Category.assoc, Category.assoc]

omit [Preadditive C] in
/-- The braiding commutes with `α ⊗ α`. -/
theorem c_comm_alpha {A : C} (α : A ⟶ A) : c A ≫ (α ⊗ₘ α) = (α ⊗ₘ α) ≫ c A := by
  unfold c
  rw [← BraidedCategory.braiding_naturality]

/-- For a commutative product and an `α`-equivariant `D`, a derivation of `μ(1 + σ)`
has `E + (α ⊗ α) ≫ E = 0`. -/
theorem twisted_defect_eq {A : C} {μ : A ⊗ A ⟶ A} {α D : A ⟶ A} (hc : c A ≫ μ = μ)
    (hD : D ≫ α = α ≫ D) (h : IsDeriv (mulTw μ α) D) :
    defect μ D + (α ⊗ₘ α) ≫ defect μ D = 0 := by
  unfold IsDeriv at h
  rw [← defect_tw μ hD] at h
  have h2 : sigma α ≫ defect μ D = (α ⊗ₘ α) ≫ defect μ D := by
    unfold sigma
    rw [c_comm_alpha, Category.assoc, braid_defect hc]
  rw [Preadditive.add_comp, Category.id_comp, h2] at h
  exact h

/-- R7: let `p, p'` be `+1` eigenvectors of `α` (`p ≫ α = p`). Then a derivation of
the twisted product has zero defect on the component `p ⊗ p'`. -/
theorem twisted_parity_plus {A X : C} {μ : A ⊗ A ⟶ A} {α D : A ⟶ A} (hc : c A ≫ μ = μ)
    (two : ∀ {X Y : C} (f : X ⟶ Y), f + f = 0 → f = 0) (hD : D ≫ α = α ≫ D)
    (h : IsDeriv (mulTw μ α) D) {p p' : X ⟶ A} (hp : p ≫ α = p) (hp' : p' ≫ α = p') :
    (p ⊗ₘ p') ≫ defect μ D = 0 := by
  apply two
  have h1 : (p ⊗ₘ p') ≫ (α ⊗ₘ α) = p ⊗ₘ p' := by
    rw [tensorHom_comp_tensorHom, hp, hp']
  have h2 := twisted_defect_eq hc hD h
  have h3 : (p ⊗ₘ p') ≫ (defect μ D + (α ⊗ₘ α) ≫ defect μ D) = 0 := by
    rw [h2, Limits.comp_zero]
  rw [Preadditive.comp_add, ← Category.assoc (p ⊗ₘ p'), h1] at h3
  exact h3

omit [BraidedCategory C] in
/-- Negating both factors does not change a tensor of morphisms. -/
theorem neg_tensor_neg [MonoidalPreadditive C] {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    (-f) ⊗ₘ (-g) = f ⊗ₘ g := by
  have h1 : (-f) ⊗ₘ (-g) + f ⊗ₘ (-g) = 0 := by
    rw [← MonoidalPreadditive.add_tensor, neg_add_cancel, MonoidalPreadditive.zero_tensor]
  have h2 : f ⊗ₘ (-g) + f ⊗ₘ g = 0 := by
    rw [← MonoidalPreadditive.tensor_add, neg_add_cancel, MonoidalPreadditive.tensor_zero]
  rw [eq_neg_of_add_eq_zero_left h1, eq_neg_of_add_eq_zero_left h2, neg_neg]

/-- R7: let `p, p'` be `-1` eigenvectors of `α` (`p ≫ α = -p`). Then a derivation of
the twisted product has zero defect on the component `p ⊗ p'`. -/
theorem twisted_parity_minus [MonoidalPreadditive C] {A X : C} {μ : A ⊗ A ⟶ A}
    {α D : A ⟶ A} (hc : c A ≫ μ = μ)
    (two : ∀ {X Y : C} (f : X ⟶ Y), f + f = 0 → f = 0) (hD : D ≫ α = α ≫ D)
    (h : IsDeriv (mulTw μ α) D) {p p' : X ⟶ A} (hp : p ≫ α = -p) (hp' : p' ≫ α = -p') :
    (p ⊗ₘ p') ≫ defect μ D = 0 := by
  apply two
  have h1 : (p ⊗ₘ p') ≫ (α ⊗ₘ α) = p ⊗ₘ p' := by
    rw [tensorHom_comp_tensorHom, hp, hp', neg_tensor_neg]
  have h2 := twisted_defect_eq hc hD h
  have h3 : (p ⊗ₘ p') ≫ (defect μ D + (α ⊗ₘ α) ≫ defect μ D) = 0 := by
    rw [h2, Limits.comp_zero]
  rw [Preadditive.comp_add, ← Category.assoc (p ⊗ₘ p'), h1] at h3
  exact h3

end BraidedJordanCategorical
