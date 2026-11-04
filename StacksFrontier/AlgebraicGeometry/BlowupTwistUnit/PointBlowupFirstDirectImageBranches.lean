module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalTwistNegativeOne
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupDerivedSingleCollapse
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularPointBlowupCohomology

/-!
# `R¹b_*` vanishes on both branches of the twist dichotomy

Let `W` be a scheme, let `w ∈ W` be a closed point whose local ring is regular of dimension two
and let `b : W' ⟶ W` be the blowing up of `W` in the reduced point `{w}`. The dichotomy of
[Stacks, Tag 0B3T], in the form
`nonempty_tensorIso_or_nonempty_iso_pullbackHullForms_vanishingIdeal_singleton` (in the namespace
`Stacks.BlowupTwistUnit`), presents the top forms upstairs as

`𝒪_{W'}(E) ⊗ b^*L`  or  `b^*L`,   `L = (Ω^r_{W/S₀})^{**}` invertible.

This file proves that `R¹b_*` vanishes on both. That is the hypothesis
`Stacks.BlowupTwistUnit.IsZeroFirstDirectImageBlowUp` of
`Stacks.BlowupTwistUnit.quasiCoherentDerivedPushforwardSingleIso`, which therefore identifies,
on both branches, the derived direct image in the field
`Stacks.BlowupTwistUnit.NormalizedTopFormData.pushforwardIso` with the ordinary direct image
`b_*`.

The whole content is the projection formula for an invertible module in degree one,
`Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso`,

`R¹b_*(ℱ ⊗ b^*L) ≅ (R¹b_*ℱ) ⊗ L`,

which reduces each branch to a vanishing already proved: `R¹b_*𝒪_{W'}(E) = 0` and
`R¹b_*𝒪_{W'} = 0`, part (2) of [Stacks, Tag 0AGS] relativized at `n = -1` and at `n = 0`.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `isZero_rightDerived_one_pushforward_tensorPullback`: **`R¹b_*ℱ = 0` implies
  `R¹b_*(ℱ ⊗ b^*L) = 0`** for `L` invertible on the base.
* `isZero_rightDerived_one_pushforward_exceptionalInvertibleSheaf` and
  `isZero_rightDerived_one_pushforward_unit`: `R¹b_*𝒪_{W'}(E) = 0` and `R¹b_*𝒪_{W'} = 0`, in the
  spellings the dichotomy produces.
* `isZeroFirstDirectImageBlowUp_exceptionalTwistPullback`: **`R¹b_*(𝒪_{W'}(E) ⊗ b^*L) = 0`**, the
  twisted branch.
* `isZeroFirstDirectImageBlowUp_pullback`: **`R¹b_*(b^*L) = 0`**, the untwisted branch.

## Implementation notes

*Two models, bridged through the `ℕ`-indexed higher direct images.* The vanishing statements
`AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_blowUp_pointIdeal` and
`AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_exceptionalTwist_pointIdeal` are
written at `CategoryTheory.HasDerivedCategory.standard`, while the projection formula
`Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso` is read at the locally small
model, its `attribute [local instance] HasDerivedCategory.standard` being outranked by the
global locally small instances of its import closure. `CategoryTheory.Functor.rightDerivedPlus`
depends on the model, so the two cannot be composed directly.

Mathlib's `CategoryTheory.Functor.rightDerived`, computed by injective resolutions, mentions no
derived category at all, and `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` identifies
its vanishing with that of `rightDerivedPlus` at whichever model is in force. Everything below is
therefore stated with `rightDerived`, each statement proved in a section where the model matching
its input is installed, and only the last two results are converted back to
`Stacks.BlowupTwistUnit.IsZeroFirstDirectImageBlowUp`, which is pinned at the standard model
because its consumer is.

*The untwisted branch is not the structure sheaf.* `R¹b_*𝒪_{W'} = 0` is about
`SheafOfModules.unit` and the branch of the dichotomy is about `b^*L`; the two are related by the
left unitor `𝒪_{W'} ⊗ b^*L ≅ b^*L` of [Stacks, Tag 01CA]
(`Stacks.RingedSpace.tensorSheafUnitLeftIso`), the projection formula carrying the tensor factor
on the left.

*The dimension of the local ring at `w` stays a hypothesis*, as it must — a closed point of a
two-dimensional scheme may have a local ring of dimension `0`, `1` or `2`, and part (2) of
[Stacks, Tag 0AGS] is about a regular local ring of dimension two.

**No `@[stacks]` attribute is placed.** The projection formula is [Stacks, Tag 0FZE] and
[Stacks, Tag 01E8] and the two vanishings are part (2) of [Stacks, Tag 0AGS], each registered
where it is proved; what is below is their combination at one morphism, an input of the induction
of [Stacks, Tag 0B4T].

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.BlowupTwistUnit

variable {W : Scheme.{u}}

/-! ### The two inputs, at the `ℕ`-indexed higher direct images -/

section Inputs

attribute [-instance] ModuleCat.hasDerivedCategory SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [local instance] HasDerivedCategory.standard

/-- **`R¹b_*𝒪_{W'}(E) = 0`** for the blowing up of a scheme in a closed point whose local ring is
regular of dimension two, with `𝒪_{W'}(E)` spelled as `Stacks.Divisors.invertibleSheaf'` of the
exceptional ideal — the spelling the dichotomy of [Stacks, Tag 0B3T] produces — and the vanishing
read at Mathlib's `ℕ`-indexed higher direct image, which mentions no model of the derived
category.

This is `AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_exceptionalTwist_pointIdeal`,
part (2) of [Stacks, Tag 0AGS] at `n = -1`, read through
`AlgebraicGeometry.exceptionalInvertibleSheafIsoBlowUpTwistNegOne`. -/
theorem isZero_rightDerived_one_pushforward_exceptionalInvertibleSheaf [IsLocallyNoetherian W]
    (w : W) (hw : IsClosed ({w} : Set W)) [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) :
    IsZero (((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).rightDerived 1).obj
      (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))))) :=
  (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ (by norm_num) _).mp
    ((AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_exceptionalTwist_pointIdeal
        w hw hstalkdim).of_iso
      (((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨{w}, hw⟩ : Closeds W)))).rightDerivedPlus 1).mapIso
            (AlgebraicGeometry.exceptionalInvertibleSheafIsoBlowUpTwistNegOne _)))

/-- **`R¹b_*𝒪_{W'} = 0`** for the blowing up of a scheme in a closed point whose local ring is
regular of dimension two, read at the `ℕ`-indexed higher direct image:
`AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_blowUp_pointIdeal`, part (2) of
[Stacks, Tag 0AGS] at `n = 0`. -/
theorem isZero_rightDerived_one_pushforward_unit [IsLocallyNoetherian W]
    (w : W) (hw : IsClosed ({w} : Set W)) [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) :
    IsZero (((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).rightDerived 1).obj
      (SheafOfModules.unit (AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).ringCatSheaf)) :=
  (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ (by norm_num) _).mp
    (AlgebraicGeometry.isZero_rightDerivedPlus_one_pushforward_blowUp_pointIdeal w hw hstalkdim)

end Inputs

/-! ### The projection formula -/

/-- **The projection formula kills `R¹b_*` on a twist by a pullback**: if `R¹b_*ℱ = 0` then
`R¹b_*(ℱ ⊗ b^*L) = 0`, for `L` an invertible module on the base.

`R¹b_*(ℱ ⊗ b^*L) ≅ (R¹b_*ℱ) ⊗ L` by
`Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso`, and tensoring by an invertible
module is an equivalence ([Stacks, Tag 01CS]), hence additive, hence carries the zero object to
the zero object. -/
theorem isZero_rightDerived_one_pushforward_tensorPullback (w : W)
    (hw : IsClosed ({w} : Set W)) (L : W.Modules)
    [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L]
    (F : (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).Modules)
    (h1 : IsZero (((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).rightDerived 1).obj F)) :
    IsZero (((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).rightDerived 1).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible
          (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal
            (⟨{w}, hw⟩ : Closeds W)))
          ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase
            (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj L)).obj F)) :=
  (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).mpr
    (((Stacks.ProjectionFormula.tensorRightInvertible W L).map_isZero
        ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 F).mp h1)).of_iso
      (Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso
        (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) L F ((1 : ℕ) : ℤ)))

/-! ### The two branches -/

section Branches

attribute [-instance] ModuleCat.hasDerivedCategory SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [local instance] HasDerivedCategory.standard

variable [AlgebraicGeometry.IsIntegral W] [IsNoetherian W]

omit [AlgebraicGeometry.IsIntegral W] in
/-- **`R¹b_*(𝒪_{W'}(E) ⊗ b^*L) = 0`**, the twisted branch of the dichotomy of
[Stacks, Tag 0B3T]: the projection formula
`Stacks.BlowupTwistUnit.isZero_rightDerived_one_pushforward_tensorPullback` applied to
`Stacks.BlowupTwistUnit.isZero_rightDerived_one_pushforward_exceptionalInvertibleSheaf`. -/
theorem isZeroFirstDirectImageBlowUp_exceptionalTwistPullback (w : W)
    (hw : IsClosed ({w} : Set W)) [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2)
    (L : W.Modules) [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L] :
    IsZeroFirstDirectImageBlowUp w hw
      ((Stacks.ProjectionFormula.tensorRightInvertible
          (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal
            (⟨{w}, hw⟩ : Closeds W)))
          ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase
            (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj L)).obj
        (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))))) :=
  (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ (by norm_num) _).mpr
    (isZero_rightDerived_one_pushforward_tensorPullback w hw L _
      (isZero_rightDerived_one_pushforward_exceptionalInvertibleSheaf w hw hstalkdim))

omit [AlgebraicGeometry.IsIntegral W] in
/-- **`R¹b_*(b^*L) = 0`**, the untwisted branch of the dichotomy of [Stacks, Tag 0B3T], for `L`
invertible on the base.

The projection formula
`Stacks.BlowupTwistUnit.isZero_rightDerived_one_pushforward_tensorPullback` applied to
`Stacks.BlowupTwistUnit.isZero_rightDerived_one_pushforward_unit` gives the vanishing for
`𝒪_{W'} ⊗ b^*L`, and the left unitor of [Stacks, Tag 01CA] identifies that with `b^*L`. -/
theorem isZeroFirstDirectImageBlowUp_pullback (w : W) (hw : IsClosed ({w} : Set W))
    [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2)
    (L : W.Modules) [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L] :
    IsZeroFirstDirectImageBlowUp w hw
      ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj L) :=
  isZeroFirstDirectImageBlowUp_of_iso w hw
    ((Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ (by norm_num) _).mpr
      (isZero_rightDerived_one_pushforward_tensorPullback w hw L _
        (isZero_rightDerived_one_pushforward_unit w hw hstalkdim)))
    (Stacks.RingedSpace.tensorSheafUnitLeftIso
      (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : Closeds W))).toRingedSpace
      ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj L)).symm

end Branches

end Stacks.BlowupTwistUnit

end
