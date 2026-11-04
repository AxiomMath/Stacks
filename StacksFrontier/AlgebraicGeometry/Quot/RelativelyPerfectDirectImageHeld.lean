module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectDirectImageReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBasePerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso

/-!
# Perfectness of relatively perfect direct images

Let `f : X ⟶ Y` be a flat, proper morphism of finite presentation of algebraic spaces over a
scheme `S`, and let `E` be `Y`-perfect. Then `Rf_*E` is perfect and its formation commutes with
arbitrary base change (Stacks 0DKX). This file proves this from the comparisons along the change
of base `S ⟶ Spec ℤ` of Stacks 04SG:

* `smallerBaseDerivedPushforwardComparison`: the change of base commutes with `Rf_*`;
* `smallerBasePerfectComparison`: it preserves and reflects perfectness;
* `smallerBaseRelativelyPerfectComparison`: it preserves and reflects relative perfectness.

## Main results

* `perfectnessReducesToNoetherianDescent_of_held_properInSite`: the reduction of Stacks 0DKX to
  Noetherian stages, with Stacks 08K1 discharged.
* `properSupportPerfectDirectImage`: `ProperSupportPerfectDirectImage` holds over `S`
  (Stacks 08IS).
* `flatDerivedBaseChange`: flat base change for the derived pushforward of quasi-coherent
  complexes (Stacks 0A1K at `𝒢^• = 𝒪_X`).
* `isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_relativelyPerfectColimit`:
  **Stacks 0DKX**, assuming that relative perfectness passes to colimits (Stacks 0DKW).
* `relativelyPerfectPushforwardBaseChange_of_relativelyPerfectColimit`: the same statement in the
  form `RelativelyPerfectPushforwardBaseChange`, the 0DKX input of the proof of Stacks 0DKY.

## References

* [Stacks Project, Tag 0DKX](https://stacks.math.columbia.edu/tag/0DKX)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If properness descends to some stage of a directed limit of morphisms (Stacks 08K1), then
perfectness of relatively perfect direct images reduces to Noetherian stages over `S`. -/
theorem perfectnessReducesToNoetherianDescent_of_held
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi)) :
    PerfectnessReducesToNoetherianDescent B S hS :=
  perfectnessReducesToNoetherianDescent_of_changeOfBase B S hS h08K1
    (smallerBaseDerivedPushforwardComparison B (toTerminalSite B B.contains_terminal hS))
    (smallerBasePerfectComparison B (toTerminalSite B B.contains_terminal hS))
    (smallerBaseRelativelyPerfectComparison B (toTerminalSite B B.contains_terminal hS))

/-- Perfectness of relatively perfect direct images over `S` reduces to Noetherian stages: the
hypothesis of `perfectnessReducesToNoetherianDescent_of_held` is Stacks 08K1 under the
convention 07SD. -/
theorem perfectnessReducesToNoetherianDescent_of_held_properInSite :
    PerfectnessReducesToNoetherianDescent B S hS :=
  perfectnessReducesToNoetherianDescent_of_held B S hS
    (@fun _ _ _ _ _ _ D hconv hf hf₀ =>
      D.exists_isProper_mapAt_of_siteContainsBaseChangeLimits hconv hf hf₀)

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0DKX**, assuming Stacks 0A1K, 08IS and 0DKW at every base scheme and Stacks 08K1:
assume flat derived base change, perfectness of direct images with proper support, and passage
of relative perfectness to colimits over every base scheme, and that properness descends to a
stage of a directed limit. Let `f : X ⟶ Y` be flat, proper and of finite presentation, and let
`E` be `Y`-perfect. Then `Rf_*E` is perfect and its formation commutes with arbitrary base
change. -/
theorem isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_held
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        (hpb : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w E) :=
  isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_changeOfBase B S hS h0A1K h08IS h0DKW
    h08K1 (smallerBaseDerivedPushforwardComparison B (toTerminalSite B B.contains_terminal hS))
    (smallerBasePerfectComparison B (toTerminalSite B B.contains_terminal hS))
    (smallerBaseRelativelyPerfectComparison B (toTerminalSite B B.contains_terminal hS))
    f hproper hflat hfp E hE

/-- Under the hypotheses of `isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_held`,
`RelativelyPerfectPushforwardBaseChange` (the 0DKX input of the proof of Stacks 0DKY) holds
over `S`. -/
theorem relativelyPerfectPushforwardBaseChange_of_held
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi)) :
    RelativelyPerfectPushforwardBaseChange B S hS :=
  relativelyPerfectPushforwardBaseChange_of_changeOfBase B S hS h0A1K h08IS h0DKW h08K1
    (smallerBaseDerivedPushforwardComparison B (toTerminalSite B B.contains_terminal hS))
    (smallerBasePerfectComparison B (toTerminalSite B B.contains_terminal hS))
    (smallerBaseRelativelyPerfectComparison B (toTerminalSite B B.contains_terminal hS))

/-- `ProperSupportPerfectDirectImage` holds over `S`: it is Stacks 08IS,
`isPerfect_derivedModulePushforward_of_hasProperSupport`. -/
theorem properSupportPerfectDirectImage : ProperSupportPerfectDirectImage B S hS :=
  fun hTop _ _ f hf hfqs hY E hE hsupp T hTor =>
    isPerfect_derivedModulePushforward_of_hasProperSupport B S hS hTop f hf hfqs hY E hE hsupp T
      hTor

/-- **Stacks 0DKX**, assuming Stacks 0A1K, 0DKW and 08K1: assume flat derived base change and
passage of relative perfectness to colimits over every base scheme, and that properness descends
to a stage of a directed limit. Let `f : X ⟶ Y` be flat, proper and of finite presentation, and
let `E` be `Y`-perfect. Then `Rf_*E` is perfect and its formation commutes with arbitrary base
change. -/
theorem isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_flatDerivedBaseChange
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        (hpb : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w E) :=
  isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_held B S hS h0A1K
    (fun hT => properSupportPerfectDirectImage B _ hT) h0DKW h08K1 f hproper hflat hfp E hE

/-- The 0DKX input of the proof of Stacks 0DKY, assuming Stacks 0A1K, 0DKW and 08K1: assume flat
derived base change and passage of relative perfectness to colimits over every base scheme, and
that properness descends to a stage of a directed limit. Then
`RelativelyPerfectPushforwardBaseChange` holds over `S`. -/
theorem relativelyPerfectPushforwardBaseChange_of_flatDerivedBaseChange
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi)) :
    RelativelyPerfectPushforwardBaseChange B S hS :=
  relativelyPerfectPushforwardBaseChange_of_held B S hS h0A1K
    (fun hT => properSupportPerfectDirectImage B _ hT) h0DKW h08K1

/-- **Stacks 0DKX**, assuming Stacks 0A1K and 0DKW, with Stacks 08K1 discharged under the
convention 07SD: assume flat derived base change and passage of relative perfectness to colimits
over every base scheme. Let `f : X ⟶ Y` be flat, proper and of finite presentation, and let `E`
be `Y`-perfect. Then `Rf_*E` is perfect and its formation commutes with arbitrary base change. -/
theorem isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_flatDerivedBaseChange_properInSite
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        (hpb : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w E) :=
  isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_flatDerivedBaseChange B S hS h0A1K h0DKW
    (@fun _ _ _ _ _ _ D hconv hf hf₀ =>
      D.exists_isProper_mapAt_of_siteContainsBaseChangeLimits hconv hf hf₀)
    f hproper hflat hfp E hE

/-- The 0DKX input of the proof of Stacks 0DKY, assuming Stacks 0A1K and 0DKW: assume flat
derived base change and passage of relative perfectness to colimits over every base scheme. Then
`RelativelyPerfectPushforwardBaseChange` holds over `S`. -/
theorem relativelyPerfectPushforwardBaseChange_of_flatDerivedBaseChange_properInSite
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT) :
    RelativelyPerfectPushforwardBaseChange B S hS :=
  relativelyPerfectPushforwardBaseChange_of_flatDerivedBaseChange B S hS h0A1K h0DKW
    (@fun _ _ _ _ _ _ D hconv hf hf₀ =>
      D.exists_isProper_mapAt_of_siteContainsBaseChangeLimits hconv hf hf₀)

/-- `FlatDerivedBaseChange` holds over `S`: for a cartesian square of algebraic spaces with `f`
quasi-compact, quasi-separated and flat, and `E ∈ D_QCoh(𝒪_X)`, the base change map
`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of Stacks 07A7 is an isomorphism. This is the case `𝒢^• = 𝒪_X` of
Stacks 0A1K. -/
theorem flatDerivedBaseChange : FlatDerivedBaseChange B S hS :=
  fun sq hfqc hfqs hflat E hE =>
    isIso_smallEtaleDerivedBaseChangeMap_of_isFlat sq hfqc hfqs hflat E hE

/-- **Stacks 0DKX**, assuming only Stacks 0DKW: assume that relative perfectness passes to
colimits over every base scheme. Let `f : X ⟶ Y` be flat, proper and of finite presentation, and
let `E` be `Y`-perfect. Then `Rf_*E` is perfect and its formation commutes with arbitrary base
change. -/
theorem isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_relativelyPerfectColimit
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        (hpb : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w E) :=
  isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_flatDerivedBaseChange_properInSite
    B S hS (fun hT => flatDerivedBaseChange B _ hT) h0DKW f hproper hflat hfp E hE

/-- The 0DKX input of the proof of Stacks 0DKY, assuming only Stacks 0DKW: assume that relative
perfectness passes to colimits over every base scheme. Then
`RelativelyPerfectPushforwardBaseChange` holds over `S`. -/
theorem relativelyPerfectPushforwardBaseChange_of_relativelyPerfectColimit
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT) :
    RelativelyPerfectPushforwardBaseChange B S hS :=
  relativelyPerfectPushforwardBaseChange_of_flatDerivedBaseChange_properInSite B S hS
    (fun hT => flatDerivedBaseChange B _ hT) h0DKW

end AlgebraicGeometry.Space

end
