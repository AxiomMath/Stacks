module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptional
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ComapBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeFunctionField
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
import all StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.InverseImageComponents
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The exceptional fibre of a blowup at a closed point of a scheme

Let `Y` be a regular Noetherian scheme of dimension two and let `w` be a closed point of `Y` whose
local ring there has dimension two. For the blowup of `Y` at the reduced point `{w}`, the fibre
over `w` is irreducible and the exceptional divisor is a regular scheme; consequently an
exceptional fibre component, with its reduced structure, is regular.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_image_supportSet_exceptionalIdeal_comap_fromSpecStalk`: the
  fibre over `w` is the image, under the comparison morphism of [Stacks, Tag 0805], of the
  exceptional fibre of the blowup of `Spec 𝒪_{Y,w}` at its closed point.
* `isIrreducible_preimage_singleton_blowUpToBase_vanishingIdeal_singleton`, in the namespace
  `Stacks.ResolutionOfSurfaces`: that fibre is irreducible.
* `Stacks.ResolutionOfSurfaces.isRegular_exceptionalDivisor_vanishingIdeal_singleton`: the
  exceptional divisor is a regular scheme.
* `Stacks.ResolutionOfSurfaces.isRegular_subscheme_vanishingIdeal_of_isExceptionalFibreComponent`:
  an exceptional fibre component, with its reduced structure, is regular.

## References

* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

/-- The support of the pullback of the vanishing ideal of a closed point `w` is the fibre over
`w`. -/
private theorem coe_support_comap_vanishingIdeal_singleton {X Y : Scheme.{u}} (f : X ⟶ Y) (w : Y)
    (hw : IsClosed ({w} : Set Y)) :
    (((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y)).comap f).support : Set X) =
      f.base ⁻¹' {w} := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The comparison of [Stacks, Tag 0805] along `Spec 𝒪_{Y,w} ⟶ Y` carries the exceptional fibre
of the blowup of `Spec 𝒪_{Y,w}` at its closed point *onto* the fibre over `w` of the blowup of
`Y` at the reduced point `{w}`. -/
public theorem exists_image_supportSet_exceptionalIdeal_comap_fromSpecStalk {Y : Scheme.{u}}
    (w : Y) (hw : IsClosed ({w} : Set Y)) :
    ∃ h : blowUp ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y)).comap
        (Y.fromSpecStalk w)) ⟶
      blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y)),
      h.base '' (exceptionalIdeal ((Scheme.IdealSheafData.vanishingIdeal
            (⟨{w}, hw⟩ : Closeds Y)).comap (Y.fromSpecStalk w))).supportSet =
        (blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y))).base ⁻¹' {w} := by
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y) with hM
  have hflat : Flat (Y.fromSpecStalk w) := flat_fromSpecStalk Y w
  obtain ⟨h, hpb⟩ := exists_isPullback_blowUpToBase_comap (Y.fromSpecStalk w) M
  have hsupp : ((M.comap (Y.fromSpecStalk w)).support : Set (Spec (Y.presheaf.stalk w))) =
      (Y.fromSpecStalk w).base ⁻¹' {w} := coe_support_comap_vanishingIdeal_singleton _ w hw
  have hexc : (exceptionalIdeal (M.comap (Y.fromSpecStalk w))).supportSet =
      (blowUpToBase (M.comap (Y.fromSpecStalk w))).base ⁻¹'
        ((M.comap (Y.fromSpecStalk w)).support : Set (Spec (Y.presheaf.stalk w))) :=
    Stacks.StrictTransform.supportSet_exceptionalIdeal (M.comap (Y.fromSpecStalk w))
  refine ⟨h, Set.eq_of_subset_of_subset (fun z hz => ?_) (fun z hz => ?_)⟩
  · obtain ⟨w', hw', rfl⟩ := hz
    rw [hexc, Set.mem_preimage, hsupp, Set.mem_preimage, Set.mem_singleton_iff] at hw'
    have hcomm : (blowUpToBase (M.comap (Y.fromSpecStalk w)) ≫ Y.fromSpecStalk w).base w' =
        (h ≫ blowUpToBase M).base w' := congrArg (fun k => k.base w') hpb.w
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    simpa [hw'] using hcomm.symm
  · rw [Set.mem_preimage, Set.mem_singleton_iff] at hz
    obtain ⟨w', hfst, hsnd⟩ := Scheme.exists_preimage_of_isPullback hpb
      (IsLocalRing.closedPoint (Y.presheaf.stalk w)) z
      (Scheme.fromSpecStalk_closedPoint.trans hz.symm)
    refine ⟨w', ?_, hsnd⟩
    rw [hexc, Set.mem_preimage, hsupp, Set.mem_preimage, Set.mem_singleton_iff, hfst]
    exact Scheme.fromSpecStalk_closedPoint

/-- Let `w` be a closed point of a scheme `Y` whose local ring there is regular of dimension two.
Then the fibre over `w` of the blowup of `Y` at the reduced point `{w}` is irreducible. -/
@[sga "7 X 2.2" "partial"]
public theorem isIrreducible_preimage_singleton_blowUpToBase_vanishingIdeal_singleton
    {Y : Scheme.{u}} (w : Y) (hw : IsClosed ({w} : Set Y))
    (hreg : IsRegularLocalRing (Y.presheaf.stalk w))
    (hdim : ringKrullDim (Y.presheaf.stalk w) = 2) :
    IsIrreducible ((blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y))).base ⁻¹' {w}) := by
  have := hreg
  obtain ⟨h, himg⟩ := exists_image_supportSet_exceptionalIdeal_comap_fromSpecStalk w hw
  rw [← himg]
  have hlocal : IsIrreducible ((exceptionalIdeal
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y)).comap
        (Y.fromSpecStalk w))).supportSet) := by
    rw [vanishingIdeal_singleton_comap_fromSpecStalk_eq w hw]
    exact isIrreducible_supportSet_exceptionalIdeal_maximalIdeal _ hdim
  exact hlocal.image h.base h.continuous.continuousOn

/-- Let `Y` be a regular Noetherian scheme of dimension two and let `w` be a closed point whose
local ring has dimension two. Then the exceptional divisor of the blowup of `Y` at the reduced
point `{w}` is a regular scheme. -/
@[sga "6 VII 3.7" "special case"]
public theorem isRegular_exceptionalDivisor_vanishingIdeal_singleton {Y : Scheme.{u}}
    [IsNoetherian Y] (hY : AlgebraicGeometry.IsRegular Y) (hdimY : topologicalKrullDim Y = 2)
    (w : Y) (hw : IsClosed ({w} : Set Y)) (hdim : ringKrullDim (Y.presheaf.stalk w) = 2) :
    AlgebraicGeometry.IsRegular
      (exceptionalDivisor (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y))) := by
  have : IsRegularLocalRing (Y.presheaf.stalk w) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hY w
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y) with hM
  have hregBl : AlgebraicGeometry.IsRegular (blowUp M) :=
    (isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton Y hY hdimY w hw).1
  have : IsLocallyNoetherian (blowUp M) := ((isRegular_iff_regular_stalks _).mp hregBl).1
  have hflat : Flat (Y.fromSpecStalk w) := flat_fromSpecStalk Y w
  obtain ⟨h, hpb⟩ := exists_isPullback_blowUpToBase_comap (Y.fromSpecStalk w) M
  have : Flat h := MorphismProperty.of_isPullback (P := @Flat) hpb hflat
  have : IsPreimmersion h :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hpb inferInstance
  have hExc : exceptionalIdeal (M.comap (Y.fromSpecStalk w)) = (exceptionalIdeal M).comap h := by
    show (M.comap (Y.fromSpecStalk w)).comap
        (blowUpToBase (M.comap (Y.fromSpecStalk w))) =
      (M.comap (blowUpToBase M)).comap h
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hpb.w]
  have hregA : AlgebraicGeometry.IsRegular (((exceptionalIdeal M).comap h).subscheme) := by
    rw [← hExc, vanishingIdeal_singleton_comap_fromSpecStalk_eq w hw]
    exact isRegular_exceptionalDivisor_maximalIdeal _ hdim
  have : IsPreimmersion (Stacks.Chow.comapSubschemeMap (exceptionalIdeal M) h) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion)
      (Stacks.Chow.isPullback_comapSubschemeMap (exceptionalIdeal M) h) inferInstance
  have hsupp : ((exceptionalIdeal M).support : Set (blowUp M)) =
      (blowUpToBase M).base ⁻¹' {w} := coe_support_comap_vanishingIdeal_singleton _ w hw
  rw [isRegular_iff_regular_stalks]
  refine ⟨(exceptionalIdeal M).isLocallyNoetherian_subscheme, fun ξ => ?_⟩
  have hz : (blowUpToBase M) ((exceptionalIdeal M).subschemeι ξ) = w := by
    have hmem : (exceptionalIdeal M).subschemeι ξ ∈
        ((exceptionalIdeal M).support : Set (blowUp M)) := by
      rw [← (exceptionalIdeal M).range_subschemeι]; exact ⟨ξ, rfl⟩
    rw [hsupp] at hmem
    simpa using hmem
  obtain ⟨w', -, hw'⟩ := Scheme.exists_preimage_of_isPullback hpb
    (IsLocalRing.closedPoint (Y.presheaf.stalk w)) ((exceptionalIdeal M).subschemeι ξ)
    (Scheme.fromSpecStalk_closedPoint.trans hz.symm)
  obtain ⟨ξ', -, hξ'⟩ := Scheme.exists_preimage_of_isPullback
    (Stacks.Chow.isPullback_comapSubschemeMap (exceptionalIdeal M) h) w' ξ hw'
  have : IsIso ((Stacks.Chow.comapSubschemeMap (exceptionalIdeal M) h).stalkMap ξ') :=
    isIso_stalkMap_of_flat_preimmersion _ ξ'
  have := AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hregA ξ'
  have hst : IsRegularLocalRing ((exceptionalIdeal M).subscheme.presheaf.stalk
      ((Stacks.Chow.comapSubschemeMap (exceptionalIdeal M) h) ξ')) :=
    IsRegularLocalRing.of_ringEquiv
      (asIso ((Stacks.Chow.comapSubschemeMap (exceptionalIdeal M) h).stalkMap
        ξ')).commRingCatIsoToRingEquiv.symm
  exact hξ' ▸ hst

section FibreComponent

variable {Y : Scheme.{u}} [IsNoetherian Y] (w : Y) (hw : IsClosed ({w} : Set Y))

/-- The centre of the blowup: the vanishing ideal of the reduced point `{w}`. -/
local notation3 "centre" => Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y)

/-- Let `Y` be a regular Noetherian scheme of dimension two and let `w` be a closed point whose
local ring has dimension two. Then an exceptional fibre component of the blowup of `Y` at the
reduced point `{w}`, with its reduced structure, is a regular scheme. -/
public theorem isRegular_subscheme_vanishingIdeal_of_isExceptionalFibreComponent
    (hY : AlgebraicGeometry.IsRegular Y) (hdimY : topologicalKrullDim Y = 2)
    (hdim : ringKrullDim (Y.presheaf.stalk w) = 2) (T : Closeds (blowUp centre))
    (hT : IsExceptionalFibreComponent w hw T) :
    AlgebraicGeometry.IsRegular (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
  have : IsRegularLocalRing (Y.presheaf.stalk w) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hY w
  have hregE : AlgebraicGeometry.IsRegular (exceptionalDivisor centre) :=
    isRegular_exceptionalDivisor_vanishingIdeal_singleton hY hdimY w hw hdim
  have : IsReduced (exceptionalDivisor centre) := AlgebraicGeometry.isReduced_of_isRegular hregE
  have hsupp : ((exceptionalIdeal centre).support : Set (blowUp centre)) =
      (blowUpToBase centre).base ⁻¹' {w} := coe_support_comap_vanishingIdeal_singleton _ w hw
  have hfib : IsIrreducible ((blowUpToBase centre).base ⁻¹' {w}) :=
    isIrreducible_preimage_singleton_blowUpToBase_vanishingIdeal_singleton w hw ‹_› hdim
  have hTeq : (T : Set (blowUp centre)) = (blowUpToBase centre).base ⁻¹' {w} :=
    Set.Subset.antisymm hT.1.2 (hT.2 ⟨hfib, subset_rfl⟩ hT.1.2)
  have hTsupp : (exceptionalIdeal centre).support = T := Closeds.ext (hsupp.trans hTeq.symm)
  rwa [← Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
    (exceptionalIdeal centre) T hTsupp]

end FibreComponent

end Stacks.ResolutionOfSurfaces

end
