module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.Homotopy

/-!
# Acyclicity of the extended Čech complex

Let `f : U ⥤ X` be a covering of `X` over a base category `C` and let `F` be an abelian
presheaf on `X`. The pullback map `Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F)` lies in the kernel of `d⁰`, so it
defines a canonical morphism of complexes `Γ(X, F)[0] ⟶ Č(U → X, F)` from the complex with
`Γ(X, F)` in degree `0`. The extended Čech complex, which has `Γ(X, F)` in degree `-1`, is
acyclic if and only if this canonical morphism is a quasi-isomorphism.

## Main definitions

* `Stacks.Cech.fromGlobalSections`: the canonical morphism `Γ(X, F)[0] ⟶ Č(U → X, F)`.

## Main results

* `Stacks.Cech.acyclic_extendedComplexNat_iff_quasiIso`: the `ℕ`-indexed extended Čech complex
  is acyclic if and only if `Γ(X, F)[0] ⟶ Č(U → X, F)` is a quasi-isomorphism.
* `Stacks.Cech.acyclic_extendedComplex_iff_quasiIso`: the same for the extended Čech complex
  indexed by `ℤ`, with `Γ(X, F)` in degree `-1`, as in the source.

## Implementation notes

The coefficient category is any abelian category with the limits computing the global sections
that occur; abelian presheaves are the case `A = AddCommGrpCat`. "Acyclic" is
`HomologicalComplex.Acyclic`, exactness in every degree.

## References

* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Stacks.RelativeCech (Tuple)

namespace Stacks.Cech

universe vA vC vU vX uA uC uU uX

variable {A : Type uA} [Category.{vA} A]
  {C : Type uC} [Category.{vC} C]
  {U : Type uU} [Category.{vU} U]
  {X : Type uX} [Category.{vX} X]
  (p : X ⥤ C) (f : U ⥤ X) (F : Xᵒᵖ ⥤ A)
  [HasLimitsOfShape Xᵒᵖ A] [∀ n : ℕ, HasLimitsOfShape (Tuple p f n)ᵒᵖ A]

section Preadditive

variable [Preadditive A] [HasZeroObject A]

/-- The canonical morphism `Γ(X, F)[0] ⟶ Č(U → X, F)` from the complex with `Γ(X, F)` in degree
`0`: in degree `0` it is the pullback map `Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F)` along `f_0`, which lies in
the kernel of `d⁰`. -/
public def fromGlobalSections : (CochainComplex.single₀ A).obj (limit F) ⟶ complex p f F :=
  (CochainComplex.fromSingle₀Equiv (complex p f F) (limit F)).symm
    ⟨augmentation p f F 0, augmentation_comp_d p f F⟩

/-- In degree `0` the canonical morphism `Γ(X, F)[0] ⟶ Č(U → X, F)` is the pullback map
`Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F)`. -/
public theorem fromGlobalSections_f_zero :
    (fromGlobalSections p f F).f 0 = augmentation p f F 0 :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end Preadditive

section Abelian

variable [Abelian A]

/-- Exactness of the `ℕ`-indexed extended Čech complex at `Γ(X, F)` is injectivity of the
pullback map `Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F)`. -/
private lemma extendedComplexNat_exactAt_zero_iff :
    (extendedComplexNat p f F).ExactAt 0 ↔ Mono (augmentation p f F 0) := by
  rw [exactAt_iff' _ 0 0 1 (by simp) (by simp)]
  exact ShortComplex.exact_iff_mono _ ((extendedComplexNat p f F).shape 0 0 (by simp))

/-- Exactness of the `ℕ`-indexed extended Čech complex at `Γ(U_0, f_0⁻¹F)`. -/
private lemma extendedComplexNat_exactAt_one_iff :
    (extendedComplexNat p f F).ExactAt 1 ↔
      (ShortComplex.mk _ _ (augmentation_comp_d p f F)).Exact := by
  rw [exactAt_iff' _ 0 1 2 (by simp) (by simp)]
  rfl

/-- Exactness of the `ℕ`-indexed extended Čech complex at `Γ(U_{n + 1}, f_{n + 1}⁻¹F)` is
exactness of the Čech complex there. -/
private lemma extendedComplexNat_exactAt_add_two_iff (n : ℕ) :
    (extendedComplexNat p f F).ExactAt (n + 2) ↔ (complex p f F).ExactAt (n + 1) := by
  rw [exactAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp),
    exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  rfl

/-- The canonical morphism `Γ(X, F)[0] ⟶ Č(U → X, F)` induces an isomorphism on `H⁰` exactly
when `0 ⟶ Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F) ⟶ Γ(U_1, f_1⁻¹F)` is exact. -/
private lemma quasiIsoAt_zero_fromGlobalSections_iff :
    QuasiIsoAt (fromGlobalSections p f F) 0 ↔
      (ShortComplex.mk _ _ (augmentation_comp_d p f F)).Exact ∧
        Mono (augmentation p f F 0) := by
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · have key : ∀ (g : limit F ⟶ (complex p f F).X 0) (_ : g = augmentation p f F 0)
        (w : g ≫ (complex p f F).d 0 1 = 0),
        (ShortComplex.mk g _ w).Exact ∧ Mono g ↔
          (ShortComplex.mk _ _ (augmentation_comp_d p f F)).Exact ∧
            Mono (augmentation p f F 0) := by
      rintro _ rfl _
      exact Iff.rfl
    exact key _ (fromGlobalSections_f_zero p f F) _
  · simp; rfl
  · simp; rfl
  · exact (complex p f F).shape 0 0 (by simp)

/-- The `ℕ`-indexed extended Čech complex, with `Γ(X, F)` in degree `0`, is acyclic if and only
if the canonical morphism `Γ(X, F)[0] ⟶ Č(U → X, F)` is a quasi-isomorphism. -/
public theorem acyclic_extendedComplexNat_iff_quasiIso :
    (extendedComplexNat p f F).Acyclic ↔ QuasiIso (fromGlobalSections p f F) := by
  have hsucc (n : ℕ) :
      QuasiIsoAt (fromGlobalSections p f F) (n + 1) ↔ (complex p f F).ExactAt (n + 1) :=
    quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)
  rw [acyclic_iff, quasiIso_iff]
  constructor
  · intro h i
    cases i with
    | zero =>
      exact (quasiIsoAt_zero_fromGlobalSections_iff p f F).2
        ⟨(extendedComplexNat_exactAt_one_iff p f F).1 (h 1),
          (extendedComplexNat_exactAt_zero_iff p f F).1 (h 0)⟩
    | succ n => exact (hsucc n).2 ((extendedComplexNat_exactAt_add_two_iff p f F n).1 (h _))
  · intro h i
    have h₀ := (quasiIsoAt_zero_fromGlobalSections_iff p f F).1 (h 0)
    match i with
    | 0 => exact (extendedComplexNat_exactAt_zero_iff p f F).2 h₀.2
    | 1 => exact (extendedComplexNat_exactAt_one_iff p f F).2 h₀.1
    | n + 2 => exact (extendedComplexNat_exactAt_add_two_iff p f F n).2 ((hsucc n).1 (h _))

/-- The extended Čech complex `… ⟶ 0 ⟶ Γ(X, F) ⟶ Γ(U_0, f_0⁻¹F) ⟶ Γ(U_1, f_1⁻¹F) ⟶ …`, with
`Γ(X, F)` in degree `-1`, is acyclic if and only if the canonical morphism
`Γ(X, F)[0] ⟶ Č(U → X, F)` is a quasi-isomorphism. -/
@[stacks 06X3 "the extended Čech complex is acyclic iff Γ(X, F)[0] → Č is a quasi-isomorphism"]
public theorem acyclic_extendedComplex_iff_quasiIso :
    (extendedComplex p f F).Acyclic ↔ QuasiIso (fromGlobalSections p f F) := by
  rw [← acyclic_extendedComplexNat_iff_quasiIso]
  constructor
  · intro h n
    exact ((extendedComplexNat p f F).extend_exactAt_iff (ComplexShape.embeddingUpIntGE (-1))
      (j := n) (j' := -1 + n) (by simp)).1 (h _)
  · intro h i
    by_cases hi : i < -1
    · exact (extendedComplexNat p f F).extend_exactAt _ i
        ((ComplexShape.notMem_range_embeddingUpIntGE_iff (-1) i).2 hi)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -1 + n := ⟨(i + 1).toNat, by lia⟩
      exact ((extendedComplexNat p f F).extend_exactAt_iff (ComplexShape.embeddingUpIntGE (-1))
        (j := n) (j' := -1 + n) (by simp)).2 (h n)

end Abelian

end Stacks.Cech

end
