/-
Copyright (c) 2026 Abderrahim Adrabi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abderrahim Adrabi
-/
module

public import Research.BraidedJordanCategorical.Family
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The derivation object

This file is Theorem 4.3 of the paper: in a symmetric closed category with kernels, the derivations
of `μ` and of the symmetrized product `μ(1 + c)` are represented by objects `Der μ` and
`Der (μ(1+c))`, and `Der μ` is a subobject of `Der (μ(1+c))`.

The construction is the paper's. The assignment `f ↦ E_f` from `T`-families to families of
two-variable maps is natural in the parameter `T` (`familyDefect_comp_tensor`); currying it through
the internal hom `X ⟶[C] A` exhibits it as composition with a single morphism
`derivationMorphism μ : (A ⟶[C] A) ⟶ ((A ⊗ A) ⟶[C] A)`, the morphism `Φ` of the paper. Then
`Der μ` is the kernel of `Φ`, and the universal property of the kernel gives the identification
`(T ⟶ Der μ) ≃ {f : T ⊗ A ⟶ A // E_f = 0}`, natural in `T`. The containment is the factorization
`Der μ ⟶ Der (μ(1+c))` through the kernel of `Φ₊`, which is a monomorphism.

## Main results

* `familyDefect_comp_tensor`: `E_f` is natural in the parameter: `E_{(k ⊗ 1) ≫ f} = (k ⊗ 1) ≫ E_f`.
* `derivationMorphism`: the morphism `Φ : [A,A] ⟶ [A⊗A,A]` inducing `f ↦ E_f`.
* `familyDefect_eq_zero_iff`: `E_f = 0` if and only if the curried family annihilates `Φ`.
* `DerivationObject` and `derivationObjectEquiv`: the object `Der μ` and the identification
  `(T ⟶ Der μ) ≃ {f : T ⊗ A ⟶ A // E_f = 0}`.
* `derivationObjectEquiv_natural`: that identification is natural in `T`.
* `derivationInclusion` and its `Mono` instance: `Der μ` is a subobject of `Der (μ(1+c))`.

## References

* A. Adrabi, *Derivations of the symmetrized product in a braided monoidal category*.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory MonoidalClosed

universe v u

namespace BraidedJordanCategorical

section Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A : C}

/-- The first Leibniz term of a family is natural in the parameter: `k` only acts on `T`. -/
theorem familyLeft_comp_tensor {T T' : C} (k : T' ⟶ T) (f : T ⊗ A ⟶ A) :
    familyLeft ((k ⊗ₘ 𝟙 A) ≫ f) = (k ⊗ₘ 𝟙 (A ⊗ A)) ≫ familyLeft f := by
  unfold familyLeft
  rw [comp_whiskerRight, tensorHom_id, tensorHom_id, ← Category.assoc,
    (associator_inv_naturality_left k A A).symm, Category.assoc]

end Monoidal

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
variable {A : C}

/-- The second Leibniz term of a family is natural in the parameter. -/
theorem familyRight_comp_tensor {T T' : C} (k : T' ⟶ T) (f : T ⊗ A ⟶ A) :
    familyRight ((k ⊗ₘ 𝟙 A) ≫ f) = (k ⊗ₘ 𝟙 (A ⊗ A)) ≫ familyRight f := by
  unfold familyRight
  rw [whiskerLeft_comp, tensorHom_id, tensorHom_id]
  have hB : (β_ T' A).hom ▷ A ≫ (A ◁ k) ▷ A = ((k ▷ A) ▷ A) ≫ ((β_ T A).hom ▷ A) := by
    calc (β_ T' A).hom ▷ A ≫ (A ◁ k) ▷ A
        = (((β_ T' A).hom ≫ (A ◁ k)) ▷ A) := (comp_whiskerRight _ _ A).symm
      _ = ((k ▷ A) ≫ (β_ T A).hom) ▷ A := by rw [← braiding_naturality_left k A]
      _ = ((k ▷ A) ▷ A) ≫ ((β_ T A).hom ▷ A) := comp_whiskerRight _ _ A
  rw [← Category.assoc (α_ A T' A).hom, (associator_naturality_middle A k A).symm,
    Category.assoc, ← Category.assoc ((β_ T' A).hom ▷ A), hB, Category.assoc,
    ← Category.assoc (α_ T' A A).inv, (associator_inv_naturality_left k A A).symm, Category.assoc]

end Braided

section Preadditive

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
variable {A : C}

/-- **Naturality of the family defect in the parameter**: `E_f` is natural in `T`. This is the
computation that the Yoneda step of Theorem 4.3 rests on. -/
theorem familyDefect_comp_tensor {μ : A ⊗ A ⟶ A} {T T' : C} (k : T' ⟶ T) (f : T ⊗ A ⟶ A) :
    familyDefect μ ((k ⊗ₘ 𝟙 A) ≫ f) = (k ⊗ₘ 𝟙 (A ⊗ A)) ≫ familyDefect μ f := by
  have h1 : (T' ◁ μ) ≫ ((k ⊗ₘ 𝟙 A) ≫ f) = (k ⊗ₘ 𝟙 (A ⊗ A)) ≫ ((T ◁ μ) ≫ f) := by
    rw [← id_tensorHom T' μ, ← id_tensorHom T μ, ← Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, ← Category.assoc, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp]
  unfold familyDefect
  rw [h1, familyLeft_comp_tensor, familyRight_comp_tensor, Preadditive.comp_sub,
    Preadditive.comp_sub]
  simp only [Category.assoc]

end Preadditive

section Currying

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
variable {A : C}

/-- Uncurrying a family indexed by `T`: the morphism `T ⊗ X ⟶ A` attached to `g : T ⟶ X ⟶[C] A`. -/
def uncurryFamily {X : C} {T : C} (g : T ⟶ X ⟶[C] A) : T ⊗ X ⟶ A :=
  (β_ T X).hom ≫ MonoidalClosed.uncurry g

/-- Currying a family `T ⊗ X ⟶ A` to a morphism `T ⟶ X ⟶[C] A`. -/
def curryFamily {X : C} {T : C} (f : T ⊗ X ⟶ A) : T ⟶ X ⟶[C] A :=
  MonoidalClosed.curry ((β_ X T).hom ≫ f)

/-- The two currying maps are inverse to each other. -/
theorem uncurryFamily_curryFamily {X : C} {T : C} (f : T ⊗ X ⟶ A) :
    uncurryFamily (curryFamily f) = f := by
  unfold uncurryFamily curryFamily
  rw [MonoidalClosed.uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- The two currying maps are inverse to each other. -/
theorem curryFamily_uncurryFamily {X : C} {T : C} (g : T ⟶ X ⟶[C] A) :
    curryFamily (uncurryFamily g) = g := by
  unfold uncurryFamily curryFamily
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, MonoidalClosed.curry_uncurry]

/-- Currying a family that starts with a morphism of the parameter. -/
theorem curryFamily_comp_tensor {X : C} {T T' : C} (k : T' ⟶ T) (f : T ⊗ X ⟶ A) :
    curryFamily ((k ⊗ₘ 𝟙 X) ≫ f) = k ≫ curryFamily f := by
  unfold curryFamily
  rw [tensorHom_id, ← Category.assoc, ← braiding_naturality_right, Category.assoc,
    MonoidalClosed.curry_natural_left]

/-- Currying a morphism `X ⊗ T ⟶ A` and then uncurrying it only introduces the symmetry. -/
theorem uncurryFamily_curry {X : C} {T : C} (f : X ⊗ T ⟶ A) :
    uncurryFamily (X := X) (MonoidalClosed.curry f) = (β_ T X).hom ≫ f := by
  rw [uncurryFamily, MonoidalClosed.uncurry_curry]

/-- The universal family: the evaluation `(A ⟶[C] A) ⊗ A ⟶ A`. -/
def evFamily : (A ⟶[C] A) ⊗ A ⟶ A := uncurryFamily (X := A) (𝟙 (A ⟶[C] A))

/-- A family is the composite of its currying with the universal family. -/
theorem uncurryFamily_eq_comp {T : C} (g : T ⟶ A ⟶[C] A) :
    uncurryFamily g = (g ⊗ₘ 𝟙 A) ≫ evFamily := by
  rw [evFamily, uncurryFamily, uncurryFamily, MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq,
    tensorHom_id, ← Category.assoc, ← braiding_naturality_left g A, whiskerLeft_id, Category.id_comp,
    Category.assoc]

end Currying

section Defect

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [Preadditive C]
  [MonoidalClosed C]
variable {A : C}

/-- The defect of a family is natural in the parameter: the case of the universal family. -/
theorem familyDefect_uncurryFamily {T : C} (μ : A ⊗ A ⟶ A) (g : T ⟶ A ⟶[C] A) :
    familyDefect μ (uncurryFamily g) = (g ⊗ₘ 𝟙 (A ⊗ A)) ≫ familyDefect μ evFamily := by
  rw [uncurryFamily_eq_comp g, familyDefect_comp_tensor]

/-- **The morphism `Φ` of Theorem 4.3**: the defect map `f ↦ E_f`, curried, as a morphism
`(A ⟶[C] A) ⟶ ((A ⊗ A) ⟶[C] A)`. -/
def derivationMorphism (μ : A ⊗ A ⟶ A) : (A ⟶[C] A) ⟶ ((A ⊗ A) ⟶[C] A) :=
  curryFamily (familyDefect μ evFamily)

/-- `Φ` induces the defect map: currying `E_f` is composing the curried `f` with `Φ`. -/
theorem curryFamily_familyDefect {T : C} (μ : A ⊗ A ⟶ A) (f : T ⊗ A ⟶ A) :
    curryFamily (familyDefect μ f) = curryFamily f ≫ derivationMorphism μ := by
  simp only [curryFamily, derivationMorphism]
  rw [MonoidalClosed.curry_eq_iff, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry, ← Category.assoc, braiding_naturality_right, ← tensorHom_id,
    Category.assoc, ← familyDefect_uncurryFamily, uncurryFamily_curry, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp]

/-- The inclusion of a kernel in its source is a monomorphism. -/
theorem kernel_ι_mono (μ : A ⊗ A ⟶ A) [Limits.HasKernel (derivationMorphism μ)] :
    Mono (Limits.kernel.ι (derivationMorphism μ)) := by
  rw [← Limits.equalizer_as_kernel (derivationMorphism μ)]
  infer_instance

end Defect

section Object

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [Preadditive C]
  [MonoidalPreadditive C] [MonoidalClosed C]
variable {A : C}

/-- Currying preserves zero. -/
theorem curryFamily_zero {X : C} {T : C} : curryFamily (0 : T ⊗ X ⟶ A) = 0 := by
  rw [curryFamily, Limits.comp_zero, MonoidalClosed.curry_eq_iff, MonoidalClosed.uncurry_eq,
    MonoidalPreadditive.whiskerLeft_zero, Limits.zero_comp]

/-- A curried family vanishes if and only if the family does. -/
theorem curryFamily_eq_zero_iff {X : C} {T : C} (f : T ⊗ X ⟶ A) :
    curryFamily f = 0 ↔ f = 0 := by
  constructor
  · intro h
    rw [← uncurryFamily_curryFamily f, h, uncurryFamily, MonoidalClosed.uncurry_eq,
      MonoidalPreadditive.whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
  · intro h
    rw [h]
    exact curryFamily_zero

/-- `E_f` vanishes if and only if the curried family annihilates `Φ`. -/
theorem familyDefect_eq_zero_iff {T : C} (μ : A ⊗ A ⟶ A) (f : T ⊗ A ⟶ A) :
    familyDefect μ f = 0 ↔ curryFamily f ≫ derivationMorphism μ = 0 := by
  rw [← curryFamily_familyDefect, curryFamily_eq_zero_iff]

/-- **The derivation object of `μ`**: the kernel of `Φ`, i.e. the object `Der(μ)` of Theorem 4.3. -/
noncomputable abbrev DerivationObject (μ : A ⊗ A ⟶ A) [Limits.HasKernel (derivationMorphism μ)] : C :=
  Limits.kernel (derivationMorphism μ)

/-- **The universal property of the derivation object**: a `T`-family is a morphism into `Der(μ)`
if and only if its defect vanishes. -/
noncomputable def derivationObjectEquiv (μ : A ⊗ A ⟶ A) [Limits.HasKernel (derivationMorphism μ)]
    (T : C) : { f : T ⊗ A ⟶ A // familyDefect μ f = 0 } ≃ (T ⟶ DerivationObject μ) where
  toFun f := Limits.kernel.lift (derivationMorphism μ) (curryFamily f.1)
    ((familyDefect_eq_zero_iff μ f.1).1 f.2)
  invFun g := ⟨uncurryFamily (g ≫ Limits.kernel.ι (derivationMorphism μ)), by
    rw [familyDefect_eq_zero_iff, curryFamily_uncurryFamily]
    have hcond : Limits.kernel.ι (derivationMorphism μ) ≫ derivationMorphism μ = 0 :=
      Limits.kernel.condition (derivationMorphism μ)
    calc (g ≫ Limits.kernel.ι (derivationMorphism μ)) ≫ derivationMorphism μ
        = g ≫ (Limits.kernel.ι (derivationMorphism μ) ≫ derivationMorphism μ) :=
          Category.assoc _ _ _
      _ = g ≫ 0 := congrArg (fun t => g ≫ t) hcond
      _ = 0 := Limits.comp_zero⟩
  left_inv f := by
    refine Subtype.ext ?_
    show uncurryFamily (Limits.kernel.lift (derivationMorphism μ) (curryFamily f.1) _ ≫
      Limits.kernel.ι (derivationMorphism μ)) = f.1
    rw [Limits.kernel.lift_ι, uncurryFamily_curryFamily]
  right_inv g := by
    have := kernel_ι_mono μ
    apply (cancel_mono (Limits.kernel.ι (derivationMorphism μ))).1
    simp only [Limits.kernel.lift_ι, curryFamily_uncurryFamily]

/-- **Naturality of the universal property**: the identification of `derivationObjectEquiv` commutes
with a change of the parameter `T`. -/
theorem derivationObjectEquiv_natural {μ : A ⊗ A ⟶ A} [Limits.HasKernel (derivationMorphism μ)]
    {T T' : C} (k : T' ⟶ T) (f : T ⊗ A ⟶ A) (hf : familyDefect μ f = 0) :
    ((derivationObjectEquiv μ T' ⟨(k ⊗ₘ 𝟙 A) ≫ f, by
      rw [familyDefect_comp_tensor, hf, Limits.comp_zero]⟩ : T' ⟶ DerivationObject μ)) =
      k ≫ derivationObjectEquiv μ T ⟨f, hf⟩ := by
  have := kernel_ι_mono μ
  apply (cancel_mono (Limits.kernel.ι (derivationMorphism μ))).1
  show Limits.kernel.lift (derivationMorphism μ) (curryFamily ((k ⊗ₘ 𝟙 A) ≫ f)) _ ≫
      Limits.kernel.ι (derivationMorphism μ)
    = (k ≫ Limits.kernel.lift (derivationMorphism μ) (curryFamily f) _) ≫
      Limits.kernel.ι (derivationMorphism μ)
  rw [Limits.kernel.lift_ι, Category.assoc, Limits.kernel.lift_ι, curryFamily_comp_tensor]

/-- The image of `Der(μ)` in `Der(μ(1+c))` vanishes: `Φ₊` kills the kernel of `Φ`. This is the
factorization `Φ₊ = (1+c)* ∘ Φ` of the paper, in the form needed for the inclusion. -/
theorem kernel_ι_comp_derivationMorphism_symmetrized (μ : A ⊗ A ⟶ A)
    [Limits.HasKernel (derivationMorphism μ)] :
    Limits.kernel.ι (derivationMorphism μ) ≫ derivationMorphism (symmetrizedProduct μ) = 0 := by
  have h : curryFamily (uncurryFamily (X := A) (Limits.kernel.ι (derivationMorphism μ))) ≫
      derivationMorphism (symmetrizedProduct μ) = 0 := by
    rw [← familyDefect_eq_zero_iff (symmetrizedProduct μ), familyDefect_symmetrized]
    have h0 : familyDefect μ (uncurryFamily (X := A) (Limits.kernel.ι (derivationMorphism μ))) = 0 := by
      rw [← curryFamily_eq_zero_iff, curryFamily_familyDefect, curryFamily_uncurryFamily]
      exact Limits.kernel.condition (derivationMorphism μ)
    rw [h0, Limits.comp_zero]
  rwa [curryFamily_uncurryFamily] at h

/-- **`Der(μ)` is a subobject of `Der(μ(1+c))`**: the induced morphism of kernels. -/
noncomputable def derivationInclusion (μ : A ⊗ A ⟶ A) [Limits.HasKernel (derivationMorphism μ)]
    [Limits.HasKernel (derivationMorphism (symmetrizedProduct μ))] :
    DerivationObject μ ⟶ DerivationObject (symmetrizedProduct μ) :=
  Limits.kernel.lift (derivationMorphism (symmetrizedProduct μ))
    (Limits.kernel.ι (derivationMorphism μ)) (kernel_ι_comp_derivationMorphism_symmetrized μ)

/-- The inclusion of derivation objects is compatible with the two kernel inclusions. -/
theorem derivationInclusion_comp_ι (μ : A ⊗ A ⟶ A) [Limits.HasKernel (derivationMorphism μ)]
    [Limits.HasKernel (derivationMorphism (symmetrizedProduct μ))] :
    derivationInclusion μ ≫ Limits.kernel.ι (derivationMorphism (symmetrizedProduct μ)) =
      Limits.kernel.ι (derivationMorphism μ) :=
  Limits.kernel.lift_ι _ _ _

/-- The inclusion of derivation objects is a monomorphism. -/
instance derivationInclusion_mono (μ : A ⊗ A ⟶ A) [Limits.HasKernel (derivationMorphism μ)]
    [Limits.HasKernel (derivationMorphism (symmetrizedProduct μ))] : Mono (derivationInclusion μ) :=
  mono_of_mono_fac (derivationInclusion_comp_ι μ)

/-- **Theorem 4.3** (the derivation object of the paper). In a symmetric closed preadditive category
with kernels, the derivations of `μ` and of the symmetrized product `μ(1 + c)` are represented by
the objects `Der μ` and `Der (μ(1+c))`, and `Der μ` is a subobject of `Der (μ(1+c))`. -/
theorem derivationObject (μ : A ⊗ A ⟶ A) [Limits.HasKernel (derivationMorphism μ)]
    [Limits.HasKernel (derivationMorphism (symmetrizedProduct μ))] :
    (Nonempty (∀ T, { f : T ⊗ A ⟶ A // familyDefect μ f = 0 } ≃ (T ⟶ DerivationObject μ))) ∧
    (Nonempty (∀ T, { f : T ⊗ A ⟶ A // familyDefect (symmetrizedProduct μ) f = 0 } ≃
      (T ⟶ DerivationObject (symmetrizedProduct μ)))) ∧
    Mono (derivationInclusion μ) :=
  ⟨⟨derivationObjectEquiv μ⟩, ⟨derivationObjectEquiv (symmetrizedProduct μ)⟩, inferInstance⟩

end Object

end BraidedJordanCategorical
