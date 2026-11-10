module

public import StacksFrontier.Deformation.RingedSpaceThickening.FlatLiftExistence
import StacksCore.Tactic.StacksAttribute

/-!
# The flat lifts of a module form a torsor under `Ext¹` (Stacks 08LM)

Let `(f, f')` be a strict morphism of first order thickenings of ringed spaces (**Stacks 08KZ**,
**Stacks 08L1**), with `i : X ⟶ X'` the upper thickening and `ℐ` its ideal sheaf, and let `ℱ`
be an `𝒪_X`-module flat over `S`. **Stacks 08LM** says that the isomorphism classes of flat lifts
of `ℱ` — pairs `(ℱ', α)` of an `𝒪_{X'}`-module `ℱ'` flat over `S'` and an isomorphism
`α : i^* ℱ' ≅ ℱ` — form, when there is one, a principal homogeneous space under
`Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)`.

The difference of two flat lifts is
`AlgebraicGeometry.RingedSpaceThickening.flatLiftDifference`, the class whose direct image is the
difference of the classes of their kernel extensions. The difference is additive,
`d(A, B) + d(B, C) = d(A, C)`, and every class is a difference: given a flat lift `B` and a class
`ξ`, there is a flat lift `A` with `d(A, B) = ξ`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.flatLiftDifference_mapExactFunctor`: the direct image
  of the difference is the difference of the classes of the kernel extensions.
* `AlgebraicGeometry.RingedSpaceThickening.flatLiftDifference_add`: the difference is additive.
* `AlgebraicGeometry.RingedSpaceThickening.exists_flatLiftDifference_eq`: every class is the
  difference of a flat lift and a given one.
* `AlgebraicGeometry.RingedSpaceThickening.flatLiftClassDifference_isPrincipalHomogeneous`:
  **Stacks 08LM**.

## References

* [Stacks Project, Tag 08LM](https://stacks.math.columbia.edu/tag/08LM)
* [Stacks Project, Tag 08L7](https://stacks.math.columbia.edu/tag/08L7)
* [Stacks Project, Tag 08LN](https://stacks.math.columbia.edu/tag/08LN)
* [Stacks Project, Tag 08LI](https://stacks.math.columbia.edu/tag/08LI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u w

namespace AlgebraicGeometry.RingedSpaceThickening

variable {D : MorphismOfThickenings.{u}}
  [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X))]
  [CategoryTheory.HasExt.{w} (SheafOfModules.{u} (structureSheafRing D.X'))]

/-- **The direct image of the difference of two flat lifts** is the difference of the classes of
their kernel extensions in `Ext¹_{𝒪_{X'}}(i_* ℱ, i_*(ℐ ⊗_{𝒪_X} ℱ))`. -/
theorem flatLiftDifference_mapExactFunctor
    [Limits.PreservesFiniteLimits (modulePushforward D.i)]
    [Limits.PreservesFiniteColimits (modulePushforward D.i)]
    (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A B : FlatLift D F) :
    (flatLiftDifference hi hs A B).mapExactFunctor (modulePushforward D.i) =
      (CategoryTheory.Abelian.YonedaExtension.shortExact (A.kernelExtension hi hs)).extClass -
        (CategoryTheory.Abelian.YonedaExtension.shortExact (B.kernelExtension hi hs)).extClass := by
  obtain ⟨P⟩ := exists_differencePresentation.{u, w} hi hs A B
  rw [flatLiftDifference_eq hi hs P, P.mapExactFunctor_differenceClass,
    A.extClass_eq_of_isKernelExtension hi P.isKernelExtension_extA
      (A.isKernelExtension_kernelExtension hi hs),
    B.extClass_eq_of_isKernelExtension hi P.isKernelExtension_extB
      (B.isKernelExtension_kernelExtension hi hs)]

/-- The pushforward along the upper thickening is fully faithful and preserves finite limits and
colimits. -/
private theorem modulePushforward_instances (D : MorphismOfThickenings.{u}) :
    (modulePushforward D.i).Full ∧ (modulePushforward D.i).Faithful ∧
      Limits.PreservesFiniteLimits (modulePushforward D.i) ∧
      Limits.PreservesFiniteColimits (modulePushforward D.i) :=
  ⟨(closedQuotientOfIsThickening D.i D.i_isThickening).full_modulePushforward,
    (closedQuotientOfIsThickening D.i D.i_isThickening).faithful_modulePushforward,
    preservesFiniteLimits_modulePushforward D.i,
    preservesFiniteColimits_modulePushforward D.i D.i_isThickening⟩

/-- **The difference of flat lifts is additive**: `d(A, B) + d(B, C) = d(A, C)`. -/
theorem flatLiftDifference_add (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (A B C : FlatLift D F) :
    flatLiftDifference hi hs A B + flatLiftDifference hi hs B C =
      flatLiftDifference hi hs A C := by
  obtain ⟨_, _, _, _⟩ := modulePushforward_instances D
  refine CategoryTheory.Abelian.mapExactFunctor_injective_one (modulePushforward D.i) _ _ ?_
  change (flatLiftDifference hi hs A B + flatLiftDifference hi hs B C).mapExactFunctor
      (modulePushforward D.i) = (flatLiftDifference hi hs A C).mapExactFunctor
      (modulePushforward D.i)
  rw [CategoryTheory.Abelian.Ext.mapExactFunctor_add, flatLiftDifference_mapExactFunctor,
    flatLiftDifference_mapExactFunctor, flatLiftDifference_mapExactFunctor]
  abel

/-- **Every class is a difference of flat lifts.** Given a flat lift `B` of a module `ℱ` flat
over `S` and a class `ξ` in `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)`, there is a flat lift `A` with
`d(A, B) = ξ`. -/
theorem exists_flatLiftDifference_eq (hi : IsFirstOrderThickening D.i)
    (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (hF : AlgebraicGeometry.IsFlatOver D.f F)
    (B : FlatLift D F) (ξ : CategoryTheory.Abelian.Ext.{w} F (idealTensor D F) 1) :
    ∃ A : FlatLift D F, flatLiftDifference hi hs A B = ξ := by
  obtain ⟨_, _, _, _⟩ := modulePushforward_instances D
  obtain ⟨Dξ, hDcl, hDess⟩ :=
    exists_yonedaExtension_essImage_extClass_eq_mapExactFunctor D.i F (idealTensor D F) ξ
  obtain ⟨E, hEcl, hEact⟩ := exists_extClass_add_of_essImage D.i F (idealTensor D F) hi
    (B.kernelExtension hi hs) Dξ hDess
  have hact : (firstOrderExtensionAction D.i F (idealTensor D F) hi E).val =
      𝟙 (idealTensor D F) :=
    hEact.trans (B.kernelExtension_action hi hs)
  have hrestr : AlgebraicGeometry.IsFlatOver D.f ((modulePullback D.i).obj B.module') :=
    (AlgebraicGeometry.isFlatOver_iff_of_moduleIso D.f B.identification).2 hF
  have hcomp : IsIso (baseIdealTensorComparison D F) :=
    isIso_baseIdealTensorComparison_of_iso D B.identification
      (baseToSourceIdealTensor_isIso D hi ht hs B.module' hrestr B.flat)
  let A := FlatLift.ofExtension D hi ht hs hF hcomp E (isIso_of_eq hact.symm (IsIso.id _))
  refine ⟨A, CategoryTheory.Abelian.mapExactFunctor_injective_one
    (modulePushforward D.i) _ _ ?_⟩
  change (flatLiftDifference hi hs A B).mapExactFunctor (modulePushforward D.i) =
    ξ.mapExactFunctor (modulePushforward D.i)
  rw [flatLiftDifference_mapExactFunctor,
    A.extClass_eq_of_isKernelExtension hi (A.isKernelExtension_kernelExtension hi hs)
      (FlatLift.isKernelExtension_ofExtension D hi ht hs hF hcomp E hact),
    hEcl, hDcl]
  abel

/-- The difference of isomorphism classes of flat lifts is additive. -/
theorem flatLiftClassDifference_add (hi : IsFirstOrderThickening D.i) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (a b c : FlatLiftClass D F) :
    flatLiftClassDifference hi hs F a b + flatLiftClassDifference hi hs F b c =
      flatLiftClassDifference hi hs F a c := by
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B =>
      induction c using Quotient.inductionOn with
      | h C => exact flatLiftDifference_add hi hs A B C

/-- Let `(f, f')` be a strict morphism of first order thickenings of ringed spaces and let `ℱ` be
an `𝒪_X`-module flat over `S`. The isomorphism classes of pairs `(ℱ', α)` of an `𝒪_{X'}`-module
`ℱ'` flat over `S'` and an isomorphism `α : i^* ℱ' ≅ ℱ` form a principal homogeneous space under
`Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)`: the difference
`AlgebraicGeometry.RingedSpaceThickening.flatLiftClassDifference` is additive, and for every class
`b` the map `a ↦ d(a, b)` is a bijection onto `Ext¹_{𝒪_X}(ℱ, ℐ ⊗_{𝒪_X} ℱ)`. When there is no flat
lift both conditions hold vacuously. -/
@[stacks 08LM]
theorem flatLiftClassDifference_isPrincipalHomogeneous (hi : IsFirstOrderThickening D.i)
    (ht : IsFirstOrderThickening D.t) (hs : D.IsStrict)
    {F : SheafOfModules.{u} (structureSheafRing D.X)} (hF : AlgebraicGeometry.IsFlatOver D.f F) :
    (∀ a b c : FlatLiftClass D F,
      flatLiftClassDifference hi hs F a b + flatLiftClassDifference hi hs F b c =
        flatLiftClassDifference hi hs F a c) ∧
      ∀ b : FlatLiftClass D F,
        Function.Bijective fun a : FlatLiftClass D F => flatLiftClassDifference hi hs F a b := by
  refine ⟨flatLiftClassDifference_add hi hs, fun b => ⟨fun a a' h => ?_, fun ξ => ?_⟩⟩
  · refine (flatLiftClassDifference_eq_zero_iff hi hs a a').1 ?_
    have h1 := flatLiftClassDifference_add hi hs a a' b
    rw [show flatLiftClassDifference hi hs F a b = flatLiftClassDifference hi hs F a' b from h]
      at h1
    exact add_eq_right.1 h1
  · induction b using Quotient.inductionOn with
    | h B =>
      obtain ⟨A, hA⟩ := exists_flatLiftDifference_eq hi ht hs hF B ξ
      exact ⟨Quotient.mk (flatLiftSetoid D F) A, hA⟩

end AlgebraicGeometry.RingedSpaceThickening

end
