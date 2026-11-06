module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineOpenImmersionAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward

/-!
# Closed immersions and finite presentation of spaces affine over a base, read on chart sections

Let `X` be a quasi-compact algebraic space and let `Y`, `Z` be algebraic spaces affine over `X`.

* A morphism `g : Y ⟶ Z` over `X` whose map of direct-image algebras `Z_* 𝒪_Z ⟶ Y_* 𝒪_Y` is
  surjective on the sections over every affine étale chart of `X` is a closed immersion.
* `Z ⟶ X` is of finite presentation as soon as its direct-image algebra `Z_* 𝒪_Z` is of finite
  presentation over `𝒪_X` on every affine étale chart.

Both are checked on one affine surjective étale chart `U` of `X` (Stacks 03H6), where the base
changes are morphisms of affine schemes and the maps on global functions are the chart values of
the direct-image algebras, by `AlgebraicGeometry.Space.pushforwardRingMap_app_eq` and
`AlgebraicGeometry.Space.fSharp_app_comp_pushforwardAlgebraSectionsIso`.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_of_surjective_pushforwardRingMap_app`.
* `AlgebraicGeometry.Space.isFinitePresentation_of_isFinitePresentation_pushforwardAlgebra`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An affine surjective étale chart of a quasi-compact algebraic space, as an object of its small
étale site. -/
theorem exists_smallEtale_isAffine_surjective {X : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) :
    ∃ U : SmallEtale B S hS X.1, IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf U.1.hom := by
  obtain ⟨U₀, u, hUaff, husurj, huet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).mp hXqc
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 U₀)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 U₀)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have huet' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u := by
    have h := huet U₀ (yoneda.map (𝟙 U₀)) hid
    rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact ⟨⟨CostructuredArrow.mk u, huet'⟩, hUaff, husurj⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_AffineOverChartSectionCriteria :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S`, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_AffineOverChartSectionCriteria
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A morphism of spaces affine over a quasi-compact base which is surjective on direct-image
sections over the affine étale charts is a closed immersion.** -/
theorem isClosedImmersion_of_surjective_pushforwardRingMap_app {X : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (Y Z : AffineOver B S hS X) (g : Y.obj ⟶ Z.obj)
    (hsurj : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
        Function.Surjective ((pushforwardRingMap B S hS g).hom.app (op U))) :
    IsClosedImmersion B S hS g.left.hom := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, hUaff, husurj⟩ := exists_smallEtale_isAffine_surjective B S hS hXqc
  have hfac : g.left.hom ≫ Z.obj.hom.hom = Y.obj.hom.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
    exact congrArg (fun m : Y.obj.left ⟶ X => m.hom) (Over.w g)
  have hYaff := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS Y.obj.hom.hom
    Y.obj.left.2 X.2).out 2 1).mp Y.property
  have hZaff := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS Z.obj.hom.hom
    Z.obj.left.2 X.2).out 2 1).mp Z.property
  have hY : yoneda.relativelyRepresentable Y.obj.hom.hom := hYaff.2.rep
  have hZ : yoneda.relativelyRepresentable Z.obj.hom.hom := hZaff.2.rep
  have hq₀ := hZ.isPullback U.1.hom
  let σY := pushforwardAlgebraSectionsIso B S hS Y.obj hY U
  let σZ := pushforwardAlgebraSectionsIso B S hS Z.obj hZ U
  let m := smallBaseChangeOverMap B S hS g hY hZ U
  have : IsAffine (T.obj (hY.pullback U.1.hom)) :=
    @isAffine_of_isAffineHom _ _ (T.map (hY.snd U.1.hom))
      (hYaff.2.property U.1.hom (hY.fst U.1.hom) (hY.snd U.1.hom) (hY.isPullback U.1.hom)) hUaff
  have : IsAffine (T.obj (hZ.pullback U.1.hom)) :=
    @isAffine_of_isAffineHom _ _ (T.map (hZ.snd U.1.hom))
      (hZaff.2.property U.1.hom (hZ.fst U.1.hom) (hZ.snd U.1.hom) (hZ.isPullback U.1.hom)) hUaff
  let ρ := (pushforwardRingMap B S hS g).hom.app (op U)
  have hsurj' : Function.Surjective (T.map m).appTop := by
    intro t
    obtain ⟨a, ha⟩ := hsurj U hUaff (σY.inv t)
    refine ⟨σZ.hom a, ?_⟩
    rw [← pushforwardRingMap_app_eq B S hS g hY hZ U]
    show σY.hom (ρ (σZ.inv (σZ.hom a))) = t
    rw [Iso.hom_inv_id_apply, ha]
    exact Iso.inv_hom_id_apply σY t
  have hsq : IsPullback (hY.fst U.1.hom) (yoneda.map m) g.left.hom (hZ.fst U.1.hom) := by
    refine IsPullback.of_bot ?_ (yoneda_map_smallBaseChangeOverMap_fst B S hS g hY hZ U).symm hq₀
    rw [← Functor.map_comp, smallBaseChangeOverMap_snd, hfac]
    exact hY.isPullback U.1.hom
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  apply ((isClosedImmersion_tfae B S hS Y.obj.left.2 Z.obj.left.2 g.left.hom).out 4 1).mp
  refine ⟨hZ.pullback U.1.hom, hZ.fst U.1.hom,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hq₀.flip husurj,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hq₀.flip U.2, ?_⟩
  have : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have hcl : IsClosedImmersion B S hS (yoneda.map m) :=
    MorphismProperty.relative_map (IsClosedImmersion.of_surjective_of_isAffine _ hsurj')
  rw [← hsq.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp _ hsq.isoPullback.inv _ hcl

/-- **A space affine over a quasi-compact base whose direct-image algebra is of finite
presentation on the affine étale charts is of finite presentation over the base.** -/
theorem isFinitePresentation_of_isFinitePresentation_pushforwardAlgebra
    {X : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1) (Z : AffineOver B S hS X)
    (hfp : (pushforwardAlgebra B S hS Z.obj).IsFinitePresentation) :
    IsFinitePresentation B S hS Z.obj.hom.hom := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, hUaff, husurj⟩ := exists_smallEtale_isAffine_surjective B S hS hXqc
  have hZaff := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS Z.obj.hom.hom
    Z.obj.left.2 X.2).out 2 1).mp Z.property
  have hZ : yoneda.relativelyRepresentable Z.obj.hom.hom := hZaff.2.rep
  have : IsAffine (T.obj (hZ.pullback U.1.hom)) :=
    @isAffine_of_isAffineHom _ _ (T.map (hZ.snd U.1.hom))
      (hZaff.2.property U.1.hom (hZ.fst U.1.hom) (hZ.snd U.1.hom) (hZ.isPullback U.1.hom)) hUaff
  have hq₀ := hZ.isPullback U.1.hom
  refine ⟨?_, isQuasiCompact_of_isAffineHom' B S hS Z.obj.hom.hom Z.obj.left.2 X.2 Z.property,
    isQuasiSeparated_of_isAffineHom B S hS Z.obj.hom.hom Z.obj.left.2 X.2 Z.property⟩
  have happ : RingHom.FinitePresentation (T.map (hZ.snd U.1.hom)).appTop.hom := by
    rw [← fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Z.obj hZ U]
    have h1 : RingHom.FinitePresentation
        ((smallEtaleRingedToposHom B S hS Z.obj.hom).fSharp.hom.app (op U)).hom := hfp U hUaff
    have hbij : Function.Bijective
        (CommRingCat.Hom.hom (pushforwardAlgebraSectionsIso B S hS Z.obj hZ U).hom) :=
      ConcreteCategory.bijective_of_isIso _
    have h2 : RingHom.FinitePresentation
        (CommRingCat.Hom.hom (pushforwardAlgebraSectionsIso B S hS Z.obj hZ U).hom) := by
      refine RingHom.FinitePresentation.of_surjective _ hbij.2 ?_
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hbij.1]
      exact Submodule.fg_bot
    exact h2.comp h1
  have hlfp : LocallyOfFinitePresentation (T.map (hZ.snd U.1.hom)) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mpr happ
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget Z.obj.left.2 X.2
    Z.obj.hom.hom).2
    ⟨hZ.pullback U.1.hom, U.1.left, hZ.fst U.1.hom, U.1.hom, hZ.snd U.1.hom,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hq₀.flip U.2, U.2,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hq₀.flip husurj, hq₀.w.symm, hlfp⟩

end AlgebraicGeometry.Space

end
