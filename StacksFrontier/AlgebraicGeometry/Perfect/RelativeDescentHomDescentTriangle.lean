module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentHomDescentIso
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentMayerVietoris
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# The conclusion of Stacks 0DI7 is closed under distinguished triangles in its first argument

For a relative descent situation of Stacks 0DI6 and objects `K₀`, `L₀` of `D(𝒪_{X₀})`,
`AlgebraicGeometry.RelativeDescentSituation.HomDescent K₀ L₀` asserts that
`colim_i Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀) ⟶ Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)` is bijective.
This file proves that, for a fixed second argument `L₀`, the class of first arguments for which
this holds is closed under isomorphisms, finite biproducts and distinguished triangles.

Every map in the contravariant long exact sequence attached to a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` of `D(𝒪_{X₀})` and read through the derived pullback to a stage or to
the limit is precomposition with the derived pullback of a fixed morphism of `D(𝒪_{X₀})`. Such a
precomposition commutes with the transition and comparison maps of the system, and the derived
pullback is a triangulated functor, so the five lemma applies in the colimit.

## Main results

* `AlgebraicGeometry.RelativeDescentSituation.homTransition_map_comp` and
  `homComparison_map_comp`: the transition and comparison maps are natural in the first argument.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_of_iso_fst`: invariance under an
  isomorphism of the first argument.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_biprod`: closure under binary
  biproducts.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_obj₃`: **the five lemma.** For a
  distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, the conclusion for `X₁`, `X₂`, `X₁⟦1⟧` and
  `X₂⟦1⟧` gives the conclusion for `X₃`.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_shift_obj₃`: the same for the conclusion
  at every shift.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedPullback

variable {X Y Z : Scheme.{u}}

/-- **The map on derived morphism sets attached to a factorisation is natural in its source.**
For `f ≫ g = k` and `a : K ⟶ K'`, precomposing by `Lg^*a` before applying `schemeFactorHom` is the
same as applying `schemeFactorHom` and then precomposing by `Lk^*a`. -/
theorem schemeFactorHom_map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K K' L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (a : K ⟶ K')
    (φ : (derivedPullback g.toLRSHom.toShHom).obj K' ⟶
      (derivedPullback g.toLRSHom.toShHom).obj L) :
    schemeFactorHom f g k h K L ((derivedPullback g.toLRSHom.toShHom).map a ≫ φ) =
      (derivedPullback k.toLRSHom.toShHom).map a ≫ schemeFactorHom f g k h K' L φ := by
  have nat := (schemeFactorIso f g k h).inv.naturality a
  simp only [Functor.comp_map] at nat
  simp only [schemeFactorHom, Iso.homCongr_apply, Functor.map_comp, Category.assoc, Iso.app_hom,
    Iso.app_inv]
  rw [reassoc_of% nat]

end Stacks.DerivedPullback

namespace CategoryTheory.Functor

/-- Precomposition with `F(e⁻¹)` followed by `F(e)` is the identity. -/
theorem map_inv_map_hom_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X Y : C}
    (e : X ≅ Y) {W : D} (x : F.obj Y ⟶ W) : F.map e.inv ≫ F.map e.hom ≫ x = x :=
  (F.mapIso e).inv_hom_id_assoc x

/-- A morphism out of the image of a binary biproduct under an additive functor is the sum of
its two components. -/
theorem eq_map_fst_comp_add_map_snd_comp {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] {A B : C} [HasBinaryBiproduct A B]
    {W : D} (x : F.obj (A ⊞ B) ⟶ W) :
    x = F.map biprod.fst ≫ F.map biprod.inl ≫ x + F.map biprod.snd ≫ F.map biprod.inr ≫ x := by
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← Preadditive.add_comp, ← F.map_add,
    biprod.total, F.map_id, Category.id_comp]

/-- The image of a composite which vanishes, followed by any morphism, vanishes. -/
theorem map_comp_map_comp_eq_zero {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {A B E : C} {a : A ⟶ B} {b : B ⟶ E} (hab : a ≫ b = 0) {W : D} (x : F.obj E ⟶ W) :
    F.map a ≫ F.map b ≫ x = 0 := by
  rw [← F.map_comp_assoc, hab, F.map_zero, zero_comp]

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
  (hT : Triangle.mk f g h ∈ distTriang C) {W : D}

include hT

/-- Exactness of `Hom(F(-), W)` at `F(X₂)` for a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`. -/
theorem exists_eq_map_comp_of_distTriang₂ (φ : F.obj X₂ ⟶ W) (hφ : F.map f ≫ φ = 0) :
    ∃ ψ : F.obj X₃ ⟶ W, φ = F.map g ≫ ψ :=
  Triangle.yoneda_exact₂ _ (F.map_distinguished _ hT) φ hφ

/-- Exactness of `Hom(F(-), W)` at `F(X₃)` for a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`. -/
theorem exists_eq_map_comp_of_distTriang₃ (φ : F.obj X₃ ⟶ W) (hφ : F.map g ≫ φ = 0) :
    ∃ ψ : F.obj (X₁⟦(1 : ℤ)⟧) ⟶ W, φ = F.map h ≫ ψ := by
  obtain ⟨ψ, hψ⟩ := Triangle.yoneda_exact₃ _ (F.map_distinguished _ hT) φ hφ
  exact ⟨((F.commShiftIso (1 : ℤ)).hom.app X₁) ≫ ψ, hψ.trans (Category.assoc _ _ _)⟩

/-- Exactness of `Hom(F(-), W)` at `F(X₁⟦1⟧)` for a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`. -/
theorem exists_eq_map_comp_of_distTriang₁ (φ : F.obj (X₁⟦(1 : ℤ)⟧) ⟶ W)
    (hφ : F.map h ≫ φ = 0) :
    ∃ ψ : F.obj (X₂⟦(1 : ℤ)⟧) ⟶ W, φ = F.map (f⟦(1 : ℤ)⟧') ≫ ψ := by
  obtain ⟨ψ, hψ⟩ := F.exists_eq_map_comp_of_distTriang₃ g h (-f⟦(1 : ℤ)⟧')
    (rot_of_distTriang _ hT) φ hφ
  refine ⟨-ψ, hψ.trans ?_⟩
  have e : F.map (-f⟦(1 : ℤ)⟧') = -F.map (f⟦(1 : ℤ)⟧') := F.map_neg
  rw [e]
  exact (Preadditive.neg_comp _ _).trans (Preadditive.comp_neg _ _).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

/-- The derived pullback `Lf_{i0}^*` from `X₀` to a stage. -/
abbrev stagePullback (i : D.LaterIndex) :=
  derivedPullback (D.toFixedStage i).toLRSHom.toShHom

/-- The derived pullback `Lf₀^*` from `X₀` to the limit. -/
abbrev limitPullback := derivedPullback D.limitToFixedStage.toLRSHom.toShHom

section Naturality

variable {K₀ K₀' :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace))}
  (L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- **The transition maps of the system of derived morphism sets are natural in the first
argument.** -/
theorem homTransition_map_comp (a : K₀ ⟶ K₀') {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ : (D.stagePullback i).obj K₀' ⟶ (D.stagePullback i).obj L₀) :
    D.homTransition K₀ L₀ h ((D.stagePullback i).map a ≫ φ) =
      (D.stagePullback j).map a ≫ D.homTransition K₀' L₀ h φ :=
  Stacks.DerivedPullback.schemeFactorHom_map_comp (D.transition h) (D.toFixedStage i)
    (D.toFixedStage j) (D.transition_comp_toFixedStage h) K₀ K₀' L₀ a φ

/-- **The comparison maps of the system of derived morphism sets are natural in the first
argument.** -/
theorem homComparison_map_comp (a : K₀ ⟶ K₀') (i : D.LaterIndex)
    (φ : (D.stagePullback i).obj K₀' ⟶ (D.stagePullback i).obj L₀) :
    D.homComparison K₀ L₀ i ((D.stagePullback i).map a ≫ φ) =
      (D.limitPullback).map a ≫ D.homComparison K₀' L₀ i φ :=
  Stacks.DerivedPullback.schemeFactorHom_map_comp (D.projection i) (D.toFixedStage i)
    D.limitToFixedStage (D.projection_comp_toFixedStage i) K₀ K₀' L₀ a φ

end Naturality

section Additivity

variable (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- The transition maps of the system of derived morphism sets are additive. -/
theorem homTransition_add {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ ψ : (D.stagePullback i).obj K₀ ⟶ (D.stagePullback i).obj L₀) :
    D.homTransition K₀ L₀ h (φ + ψ) = D.homTransition K₀ L₀ h φ + D.homTransition K₀ L₀ h ψ :=
  Stacks.DerivedPullback.schemeFactorHom_add (D.transition h) (D.toFixedStage i)
    (D.toFixedStage j) (D.transition_comp_toFixedStage h) K₀ L₀ φ ψ

/-- The comparison maps of the system of derived morphism sets are additive. -/
theorem homComparison_add (i : D.LaterIndex)
    (φ ψ : (D.stagePullback i).obj K₀ ⟶ (D.stagePullback i).obj L₀) :
    D.homComparison K₀ L₀ i (φ + ψ) = D.homComparison K₀ L₀ i φ + D.homComparison K₀ L₀ i ψ :=
  Stacks.DerivedPullback.schemeFactorHom_add (D.projection i) (D.toFixedStage i)
    D.limitToFixedStage (D.projection_comp_toFixedStage i) K₀ L₀ φ ψ

/-- The transition map of the system of derived morphism sets as a group homomorphism. -/
def homTransitionAddHom {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    ((D.stagePullback i).obj K₀ ⟶ (D.stagePullback i).obj L₀) →+
      ((D.stagePullback j).obj K₀ ⟶ (D.stagePullback j).obj L₀) :=
  AddMonoidHom.mk' (D.homTransition K₀ L₀ h) (D.homTransition_add K₀ L₀ h)

/-- The comparison map of the system of derived morphism sets as a group homomorphism. -/
def homComparisonAddHom (i : D.LaterIndex) :
    ((D.stagePullback i).obj K₀ ⟶ (D.stagePullback i).obj L₀) →+
      ((D.limitPullback).obj K₀ ⟶ (D.limitPullback).obj L₀) :=
  AddMonoidHom.mk' (D.homComparison K₀ L₀ i) (D.homComparison_add K₀ L₀ i)

/-- The transition maps preserve differences. -/
theorem homTransition_sub {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ ψ : (D.stagePullback i).obj K₀ ⟶ (D.stagePullback i).obj L₀) :
    D.homTransition K₀ L₀ h (φ - ψ) = D.homTransition K₀ L₀ h φ - D.homTransition K₀ L₀ h ψ :=
  (D.homTransitionAddHom K₀ L₀ h).map_sub φ ψ

/-- The comparison maps preserve differences. -/
theorem homComparison_sub (i : D.LaterIndex)
    (φ ψ : (D.stagePullback i).obj K₀ ⟶ (D.stagePullback i).obj L₀) :
    D.homComparison K₀ L₀ i (φ - ψ) = D.homComparison K₀ L₀ i φ - D.homComparison K₀ L₀ i ψ :=
  (D.homComparisonAddHom K₀ L₀ i).map_sub φ ψ

/-- The transition maps preserve zero. -/
theorem homTransition_zero {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.homTransition K₀ L₀ h 0 = 0 :=
  (D.homTransitionAddHom K₀ L₀ h).map_zero

/-- The comparison maps preserve zero. -/
theorem homComparison_zero (i : D.LaterIndex) : D.homComparison K₀ L₀ i 0 = 0 :=
  (D.homComparisonAddHom K₀ L₀ i).map_zero

end Additivity

/-- Two stages have a common later stage. -/
theorem exists_laterIndex_ge_ge (i j : D.LaterIndex) :
    ∃ k : D.LaterIndex, i.1 ≤ k.1 ∧ j.1 ≤ k.1 := by
  have := D.isDirected_laterIndex
  exact directed_of (· ≤ ·) i j

section Closure

variable (L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

section Helpers

variable {X Y : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace))}

/-- `homComparison_map_comp` with the comparison of `φ` already computed. -/
theorem homComparison_map_comp_of_eq (a : X ⟶ Y) {i : D.LaterIndex}
    {φ : (D.stagePullback i).obj Y ⟶ (D.stagePullback i).obj L₀}
    {ψ : (D.limitPullback).obj Y ⟶ (D.limitPullback).obj L₀}
    (hφ : D.homComparison Y L₀ i φ = ψ) :
    D.homComparison X L₀ i ((D.stagePullback i).map a ≫ φ) = (D.limitPullback).map a ≫ ψ :=
  (D.homComparison_map_comp L₀ a i φ).trans (congrArg (fun x => (D.limitPullback).map a ≫ x) hφ)

/-- The comparison of a transition image is the comparison of the original morphism. -/
theorem homComparison_homTransition_of_eq {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    {φ : (D.stagePullback i).obj X ⟶ (D.stagePullback i).obj L₀}
    {ψ : (D.limitPullback).obj X ⟶ (D.limitPullback).obj L₀}
    (hφ : D.homComparison X L₀ i φ = ψ) :
    D.homComparison X L₀ j (D.homTransition X L₀ h φ) = ψ :=
  (D.homComparison_homTransition X L₀ h φ).trans hφ

/-- Equal transition images at a stage stay equal at every later stage. -/
theorem homTransition_eq_of_le {i j k : D.LaterIndex} (hij : i.1 ≤ j.1) (hjk : j.1 ≤ k.1)
    {φ φ' : (D.stagePullback i).obj X ⟶ (D.stagePullback i).obj L₀}
    (e : D.homTransition X L₀ hij φ = D.homTransition X L₀ hij φ') :
    D.homTransition X L₀ (hij.trans hjk) φ = D.homTransition X L₀ (hij.trans hjk) φ' :=
  (D.homTransition_homTransition X L₀ hij hjk φ).symm.trans
    ((congrArg (D.homTransition X L₀ hjk) e).trans (D.homTransition_homTransition X L₀ hij hjk φ'))

/-- Equal transition images of two precomposites are precomposites of equal transition
images. -/
theorem homTransition_map_comp_of_eq (a : X ⟶ Y) {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    {φ φ' : (D.stagePullback i).obj Y ⟶ (D.stagePullback i).obj L₀}
    (e : D.homTransition X L₀ h ((D.stagePullback i).map a ≫ φ) =
      D.homTransition X L₀ h ((D.stagePullback i).map a ≫ φ')) :
    (D.stagePullback j).map a ≫ D.homTransition Y L₀ h φ =
      (D.stagePullback j).map a ≫ D.homTransition Y L₀ h φ' :=
  (D.homTransition_map_comp L₀ a h φ).symm.trans (e.trans (D.homTransition_map_comp L₀ a h φ'))

/-- Precomposition preserves equality of comparisons. -/
theorem homComparison_map_comp_congr (a : X ⟶ Y) {i : D.LaterIndex}
    {φ φ' : (D.stagePullback i).obj Y ⟶ (D.stagePullback i).obj L₀}
    (e : D.homComparison Y L₀ i φ = D.homComparison Y L₀ i φ') :
    D.homComparison X L₀ i ((D.stagePullback i).map a ≫ φ) =
      D.homComparison X L₀ i ((D.stagePullback i).map a ≫ φ') :=
  (D.homComparison_map_comp L₀ a i φ).trans
    ((congrArg (fun x => (D.limitPullback).map a ≫ x) e).trans
      (D.homComparison_map_comp L₀ a i φ').symm)

/-- If `a` kills a limit morphism which is the comparison of `φ`, then `a` kills a later
transition image of `φ`, when the conclusion holds for the source of `a`. -/
private theorem exists_map_comp_homTransition_eq_zero (hX : D.HomDescent X L₀) (a : X ⟶ Y)
    {i : D.LaterIndex} {φ : (D.stagePullback i).obj Y ⟶ (D.stagePullback i).obj L₀}
    {ψ : (D.limitPullback).obj Y ⟶ (D.limitPullback).obj L₀}
    (hφ : D.homComparison Y L₀ i φ = ψ) (hψ : (D.limitPullback).map a ≫ ψ = 0) :
    ∃ (j : D.LaterIndex) (hij : i.1 ≤ j.1),
      (D.stagePullback j).map a ≫ D.homTransition Y L₀ hij φ = 0 := by
  obtain ⟨j, hij, hj⟩ := hX.2 i _ _ ((D.homComparison_map_comp_of_eq L₀ a hφ).trans
    (hψ.trans (D.homComparison_zero X L₀ i).symm))
  exact ⟨j, hij, (D.homTransition_map_comp L₀ a hij φ).symm.trans
    (hj.trans (D.homTransition_zero X L₀ hij))⟩

end Helpers

/-- **The conclusion of Stacks 0DI7 is invariant under an isomorphism of its first argument.**
Precomposition with the derived pullback of `e⁻¹` is a bijection on derived morphism sets at
every stage and at the limit, compatible with the transition and comparison maps. -/
theorem homDescent_of_iso_fst {K₀ K₀' : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace))} (e : K₀ ≅ K₀') (hd : D.HomDescent K₀ L₀) :
    D.HomDescent K₀' L₀ := by
  refine ⟨fun ψ => ?_, fun i φ φ' hφ => ?_⟩
  · obtain ⟨i, φ, hφ⟩ := hd.1 ((D.limitPullback).map e.hom ≫ ψ)
    exact ⟨i, (D.stagePullback i).map e.inv ≫ φ, (D.homComparison_map_comp_of_eq L₀ e.inv hφ).trans
      ((D.limitPullback).map_inv_map_hom_comp e ψ)⟩
  · obtain ⟨j, hij, hj⟩ := hd.2 i ((D.stagePullback i).map e.hom ≫ φ)
      ((D.stagePullback i).map e.hom ≫ φ') (D.homComparison_map_comp_congr L₀ e.hom hφ)
    exact ⟨j, hij, (cancel_epi _).1 (D.homTransition_map_comp_of_eq L₀ e.hom hij hj)⟩

/-- **The conclusion of Stacks 0DI7 is closed under binary biproducts in its first argument.**
The derived pullbacks are additive, so a morphism out of the derived pullback of `K₁ ⊞ K₂` is
the sum of its two components. -/
theorem homDescent_biprod (K₁ K₂ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace)))
    (h₁ : D.HomDescent K₁ L₀) (h₂ : D.HomDescent K₂ L₀) : D.HomDescent (K₁ ⊞ K₂) L₀ := by
  constructor
  · intro ψ
    have t₁ := h₁.1 ((D.limitPullback).map (biprod.inl : K₁ ⟶ K₁ ⊞ K₂) ≫ ψ)
    have t₂ := h₂.1 ((D.limitPullback).map (biprod.inr : K₂ ⟶ K₁ ⊞ K₂) ≫ ψ)
    obtain ⟨i₁, φ₁, hφ₁⟩ := t₁
    obtain ⟨i₂, φ₂, hφ₂⟩ := t₂
    have t₃ := D.exists_laterIndex_ge_ge i₁ i₂
    obtain ⟨k, h₁k, h₂k⟩ := t₃
    exact ⟨k, (D.stagePullback k).map (biprod.fst : K₁ ⊞ K₂ ⟶ K₁) ≫
        D.homTransition K₁ L₀ h₁k φ₁ +
      (D.stagePullback k).map (biprod.snd : K₁ ⊞ K₂ ⟶ K₂) ≫ D.homTransition K₂ L₀ h₂k φ₂,
      (D.homComparison_add _ L₀ k _ _).trans ((congrArg₂ (· + ·)
        (D.homComparison_map_comp_of_eq L₀ _ (D.homComparison_homTransition_of_eq L₀ h₁k hφ₁))
        (D.homComparison_map_comp_of_eq L₀ _
          (D.homComparison_homTransition_of_eq L₀ h₂k hφ₂))).trans
        ((D.limitPullback).eq_map_fst_comp_add_map_snd_comp ψ).symm)⟩
  · intro i φ φ' hφ
    have t₁ := h₁.2 i ((D.stagePullback i).map (biprod.inl : K₁ ⟶ K₁ ⊞ K₂) ≫ φ)
      ((D.stagePullback i).map (biprod.inl : K₁ ⟶ K₁ ⊞ K₂) ≫ φ')
      (D.homComparison_map_comp_congr L₀ _ hφ)
    have t₂ := h₂.2 i ((D.stagePullback i).map (biprod.inr : K₂ ⟶ K₁ ⊞ K₂) ≫ φ)
      ((D.stagePullback i).map (biprod.inr : K₂ ⟶ K₁ ⊞ K₂) ≫ φ')
      (D.homComparison_map_comp_congr L₀ _ hφ)
    obtain ⟨j₁, hij₁, hj₁⟩ := t₁
    obtain ⟨j₂, hij₂, hj₂⟩ := t₂
    have t₃ := D.exists_laterIndex_ge_ge j₁ j₂
    obtain ⟨k, h₁k, h₂k⟩ := t₃
    have e₁ := D.homTransition_map_comp_of_eq L₀ _ (hij₁.trans h₁k)
      (D.homTransition_eq_of_le L₀ hij₁ h₁k hj₁)
    have e₂ := D.homTransition_map_comp_of_eq L₀ _ (hij₂.trans h₂k)
      (D.homTransition_eq_of_le L₀ hij₂ h₂k hj₂)
    exact ⟨k, hij₁.trans h₁k,
      ((D.stagePullback k).eq_map_fst_comp_add_map_snd_comp _).trans
        ((congrArg₂ (fun x y => (D.stagePullback k).map (biprod.fst : K₁ ⊞ K₂ ⟶ K₁) ≫ x +
          (D.stagePullback k).map (biprod.snd : K₁ ⊞ K₂ ⟶ K₂) ≫ y) e₁ e₂).trans
          ((D.stagePullback k).eq_map_fst_comp_add_map_snd_comp _).symm)⟩

section Triangle

variable {X₁ X₂ X₃ : DerivedCategory (SheafOfModules.{u}
    (structureSheafRing D.X₀.left.toRingedSpace))}
  (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
  (hT : Triangle.mk f g h ∈ distTriang (DerivedCategory (SheafOfModules.{u}
    (structureSheafRing D.X₀.left.toRingedSpace))))

include hT in
/-- The surjectivity half of the five lemma for `homDescent_obj₃`. -/
theorem exists_homComparison_eq_of_distTriang (h₂ : D.HomDescent X₂ L₀)
    (h₁ : D.HomDescent X₁ L₀) (h₁' : D.HomDescent (X₁⟦(1 : ℤ)⟧) L₀)
    (ψ : (D.limitPullback).obj X₃ ⟶ (D.limitPullback).obj L₀) :
    ∃ (i : D.LaterIndex) (φ : (D.stagePullback i).obj X₃ ⟶ (D.stagePullback i).obj L₀),
      D.homComparison X₃ L₀ i φ = ψ := by
  have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  obtain ⟨i, φ₂, hφ₂⟩ := h₂.1 ((D.limitPullback).map g ≫ ψ)
  obtain ⟨j, hij, hj'⟩ := D.exists_map_comp_homTransition_eq_zero L₀ h₁ f hφ₂
    ((D.limitPullback).map_comp_map_comp_eq_zero hfg ψ)
  obtain ⟨φ₃, hφ₃⟩ := (D.stagePullback j).exists_eq_map_comp_of_distTriang₂ f g h hT _ hj'
  have hψ' : (D.limitPullback).map g ≫ (ψ - D.homComparison X₃ L₀ j φ₃) = 0 :=
    (Preadditive.comp_sub _ _ _).trans (sub_eq_zero.2 (hφ₂.symm.trans
      ((D.homComparison_homTransition X₂ L₀ hij φ₂).symm.trans
        ((congrArg (D.homComparison X₂ L₀ j) hφ₃).trans (D.homComparison_map_comp L₀ g j φ₃)))))
  obtain ⟨χ, hχ⟩ := (D.limitPullback).exists_eq_map_comp_of_distTriang₃ f g h hT _ hψ'
  obtain ⟨k, χk, hχk⟩ := h₁'.1 χ
  obtain ⟨m, hjm, hkm⟩ := D.exists_laterIndex_ge_ge j k
  exact ⟨m, D.homTransition _ _ hjm φ₃ + (D.stagePullback m).map h ≫ D.homTransition _ _ hkm χk,
    (D.homComparison_add _ L₀ m _ _).trans ((congrArg₂ (· + ·)
      (D.homComparison_homTransition X₃ L₀ hjm φ₃)
      ((D.homComparison_map_comp_of_eq L₀ h (D.homComparison_homTransition_of_eq L₀ hkm hχk)).trans
        hχ.symm)).trans (add_sub_cancel _ _))⟩

include hT in
/-- The injectivity half of the five lemma for `homDescent_obj₃`. -/
theorem exists_homTransition_eq_of_distTriang (h₂ : D.HomDescent X₂ L₀)
    (h₂' : D.HomDescent (X₂⟦(1 : ℤ)⟧) L₀) (h₁' : D.HomDescent (X₁⟦(1 : ℤ)⟧) L₀)
    (i : D.LaterIndex) (φ φ' : (D.stagePullback i).obj X₃ ⟶ (D.stagePullback i).obj L₀)
    (hφ : D.homComparison X₃ L₀ i φ = D.homComparison X₃ L₀ i φ') :
    ∃ (j : D.LaterIndex) (hj : i.1 ≤ j.1),
      D.homTransition X₃ L₀ hj φ = D.homTransition X₃ L₀ hj φ' := by
  have hhf : h ≫ f⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have hδ : D.homComparison X₃ L₀ i (φ - φ') = 0 :=
    (D.homComparison_sub X₃ L₀ i φ φ').trans (sub_eq_zero.2 hφ)
  obtain ⟨j, hij, hj'⟩ := D.exists_map_comp_homTransition_eq_zero L₀ h₂ g hδ comp_zero
  obtain ⟨χ, hχ⟩ := (D.stagePullback j).exists_eq_map_comp_of_distTriang₃ f g h hT _ hj'
  have hχ0 : (D.limitPullback).map h ≫ D.homComparison _ L₀ j χ = 0 :=
    (D.homComparison_map_comp L₀ h j χ).symm.trans
      ((congrArg (D.homComparison X₃ L₀ j) hχ).symm.trans
        ((D.homComparison_homTransition X₃ L₀ hij _).trans hδ))
  obtain ⟨ω, hω⟩ := (D.limitPullback).exists_eq_map_comp_of_distTriang₁ f g h hT _ hχ0
  obtain ⟨k, ωk, hωk⟩ := h₂'.1 ω
  obtain ⟨m, hjm, hkm⟩ := D.exists_laterIndex_ge_ge j k
  have hz' : D.homComparison _ L₀ m (D.homTransition _ L₀ hjm χ) =
      D.homComparison _ L₀ m ((D.stagePullback m).map (f⟦(1 : ℤ)⟧') ≫
        D.homTransition _ L₀ hkm ωk) :=
    (D.homComparison_homTransition _ L₀ hjm χ).trans (hω.trans
      (D.homComparison_map_comp_of_eq L₀ _ (D.homComparison_homTransition_of_eq L₀ hkm hωk)).symm)
  obtain ⟨l, hml, hl⟩ := h₁'.2 m _ _ hz'
  have hl' : D.homTransition _ L₀ (hjm.trans hml) χ =
      (D.stagePullback l).map (f⟦(1 : ℤ)⟧') ≫
        D.homTransition _ L₀ hml (D.homTransition _ L₀ hkm ωk) :=
    (D.homTransition_homTransition _ L₀ hjm hml χ).symm.trans
      (hl.trans (D.homTransition_map_comp L₀ _ hml _))
  have hzero : D.homTransition X₃ L₀ ((hij.trans hjm).trans hml) (φ - φ') = 0 :=
    (D.homTransition_homTransition X₃ L₀ hij (hjm.trans hml) _).symm.trans
      ((congrArg (D.homTransition X₃ L₀ (hjm.trans hml)) hχ).trans
        ((D.homTransition_map_comp L₀ h (hjm.trans hml) χ).trans
          ((congrArg (fun x => (D.stagePullback l).map h ≫ x) hl').trans
            ((D.stagePullback l).map_comp_map_comp_eq_zero hhf _))))
  exact ⟨l, (hij.trans hjm).trans hml,
    sub_eq_zero.1 ((D.homTransition_sub X₃ L₀ _ φ φ').symm.trans hzero)⟩

include hT in
/-- **The five lemma for the conclusion of Stacks 0DI7 in its first argument**, for a
distinguished triangle presented by its three morphisms. -/
theorem homDescent_of_distTriang (h₁ : D.HomDescent X₁ L₀) (h₂ : D.HomDescent X₂ L₀)
    (h₁' : D.HomDescent (X₁⟦(1 : ℤ)⟧) L₀) (h₂' : D.HomDescent (X₂⟦(1 : ℤ)⟧) L₀) :
    D.HomDescent X₃ L₀ :=
  ⟨D.exists_homComparison_eq_of_distTriang L₀ f g h hT h₂ h₁ h₁',
    D.exists_homTransition_eq_of_distTriang L₀ f g h hT h₂ h₂' h₁'⟩

end Triangle

/-- **The five lemma for the conclusion of Stacks 0DI7 in its first argument.** For a
distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` of `D(𝒪_{X₀})`, if the conclusion holds for
`X₁`, `X₂`, `X₁⟦1⟧` and `X₂⟦1⟧` against `L₀`, then it holds for `X₃`. -/
theorem homDescent_obj₃ (T : Triangle (DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace))))
    (hT : T ∈ distTriang (DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace))))
    (h₁ : D.HomDescent T.obj₁ L₀) (h₂ : D.HomDescent T.obj₂ L₀)
    (h₁' : D.HomDescent (T.obj₁⟦(1 : ℤ)⟧) L₀) (h₂' : D.HomDescent (T.obj₂⟦(1 : ℤ)⟧) L₀) :
    D.HomDescent T.obj₃ L₀ :=
  D.homDescent_of_distTriang L₀ T.mor₁ T.mor₂ T.mor₃ hT h₁ h₂ h₁' h₂'

/-- **The conclusion of Stacks 0DI7 at every shift is closed under distinguished triangles in
its first argument.** If it holds for every shift of `X₁` and of `X₂`, it holds for every shift
of `X₃`. -/
theorem homDescent_shift_obj₃ (T : Triangle (DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace))))
    (hT : T ∈ distTriang (DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace))))
    (h₁ : ∀ n : ℤ, D.HomDescent (T.obj₁⟦n⟧) L₀)
    (h₂ : ∀ n : ℤ, D.HomDescent (T.obj₂⟦n⟧) L₀) (n : ℤ) : D.HomDescent (T.obj₃⟦n⟧) L₀ :=
  D.homDescent_obj₃ L₀ ((CategoryTheory.shiftFunctor (Triangle _) n).obj T)
    (Triangle.shift_distinguished T hT n) (h₁ n) (h₂ n)
    (D.homDescent_of_iso_fst L₀ ((shiftFunctorAdd' _ n 1 (n + 1) rfl).app T.obj₁) (h₁ (n + 1)))
    (D.homDescent_of_iso_fst L₀ ((shiftFunctorAdd' _ n 1 (n + 1) rfl).app T.obj₂) (h₂ (n + 1)))

end Closure

end AlgebraicGeometry.RelativeDescentSituation

end
