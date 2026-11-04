module

public import StacksFrontier.AlgebraicGeometry.Morphisms.HenselianLocalFinitePiece
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ImpurityPullbackAlongSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.StrictHenselizationConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.StrictHenselizationConditionsTwo
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.AtPrime

/-!
# Stacks 0CVB, (4) ⟹ (1): an impurity over the strict henselization

In Situation 0CV6 let `ȳ` be a geometric point of `Y` lying over `y`, and let `Y^{sh}` be the
strict henselization built in
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/StrictHenselizationConditions.lean`. This file proves
the implication (4) ⟹ (1) of Stacks 0CVB: an impurity `(T ⟶ Y, t' ⤳ t, ξ)` of `ℱ` above `y` with
`T ⟶ Y` quasi-finite at `t` gives an impurity `(Y^{sh} ⟶ Y, y' ⤳ ȳ, θ)`.

## Main results

* `AlgebraicGeometry.Space.isFlatAt_strictHenselizationToSpace`: `Y^{sh} ⟶ Y` is flat at the
  closed point.
* `AlgebraicGeometry.Space.hasImpurityOverStrictHenselization_of_hasImpurityQuasiFiniteAtPoint`:
  **Stacks 0CVB, (4) ⟹ (1).**

## Implementation notes

The proof is the source's. Stacks 0CVA along the flat morphism `Y^{sh} ⟶ Y`
(`AlgebraicGeometry.Space.exists_flatImpurityAscentData_of_isFlatAt`) gives an impurity
`(T₁ ⟶ Y^{sh}, t₁' ⤳ t₁, ξ₁)` with `T₁` étale over `T ×_Y Y^{sh}`, so that `T₁ ⟶ Y^{sh}` is
quasi-finite at `t₁` (Stacks 03XL and 03XK). The test scheme is then shrunk twice, each time
pulling the impurity back along an open immersion
(`AlgebraicGeometry.Space.ImpurityDiagram.exists_isImpurity_pullbackAlong`): first to an open on
which `T₁ ⟶ Y^{sh}` is locally quasi-finite, then — `Y^{sh}` being the spectrum of a henselian
local ring — to an open neighbourhood of `t₁` finite over `Y^{sh}` in which `t₁` is the only point
over the closed point (`AlgebraicGeometry.exists_isFinite_forall_eq_of_locallyQuasiFinite`, the
form Stacks 02LK takes over a henselian base). The source asks for an open and closed piece; an
open one with a single point over the closed point is what the closing step uses. That step,
`AlgebraicGeometry.Space.exists_isImpurity_of_isImpurity_ofTestScheme`, pushes the impurity down
to `Y^{sh}` through Stacks 0CV2, part (1), and the closedness of `X_{T₁} ⟶ X^{sh}`.

The flatness of `Y^{sh} ⟶ Y` at the closed point is read on the pointed chart `Y^{sh} ⟶ V` over
the chosen étale chart `V ⟶ Y`, where `Y^{sh} ⟶ V` is flat because the strict henselization of a
local ring is ind-étale over it.

## References

* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
* [Stacks Project, Tag 0CVA](https://stacks.math.columbia.edu/tag/0CVA)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (ybar : GeometricPoint B S hS Y)

attribute [local instance] pointTopology

/-! ### `Y^{sh} ⟶ Y` is flat at the closed point -/

/-- The canonical morphism `Y^{sh} ⟶ V` to the chosen chart is flat: it is the spectrum of the
ind-étale, hence flat, map from the local ring of `V` to its strict henselization, followed by
the flat morphism from the spectrum of that local ring. -/
theorem flat_strictHenselizationSchemeToChart :
    Flat (strictHenselizationSchemeToChart hY ybar) := by
  have hflat : Flat (Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing
      (strictHenselizationSite hY ybar) (strictHenselizationChart hY ybar)
      (contains_strictHenselizationSite hY ybar) (strictHenselizationChartPoint hY ybar)))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, ← algebraMap_etaleLocalRing,
      RingHom.flat_algebraMap_iff]
    exact StacksDraft.flat_of_indEtale (indEtale_etaleLocalRing _ _ _ _)
  have := flat_fromSpecStalk (strictHenselizationChart hY ybar)
    ((strictHenselizationChartPoint hY ybar).hom
      (IsLocalRing.closedPoint (strictHenselizationChartPoint hY ybar).residueField))
  change Flat (Spec.map _ ≫ _)
  infer_instance

/-- **`Y^{sh} ⟶ Y` is flat at the closed point.** The pointed chart `(Y^{sh} ⟶ V)` over the
étale chart `V ⟶ Y` computes flatness at the closed point, and `Y^{sh} ⟶ V` is flat. -/
theorem isFlatAt_strictHenselizationToSpace :
    IsFlatAt B S hS (strictHenselizationToSpace hY ybar)
      (strictHenselizationClosedPoint hY ybar) := by
  obtain ⟨p, hp⟩ := Quot.exists_rep (strictHenselizationClosedPoint hY ybar)
  let c : EtaleChartAtPoint B S hS (strictHenselizationToSpace hY ybar)
      (strictHenselizationClosedPoint hY ybar) :=
    { U := strictHenselizationObj hY ybar
      V := (strictHenselizationNbhd hY ybar).chart.obj.left
      a := 𝟙 _
      b := (strictHenselizationNbhd hY ybar).chart.obj.hom
      h := strictHenselizationToChart hY ybar
      a_etale := presheaf_etale_of_iso B S hS (Iso.refl _)
      b_etale := (strictHenselizationNbhd hY ybar).chart.property
      comm := by
        rw [Category.id_comp]
        rfl
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := by rwa [pointsMap_id] }
  refine (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@MorphismOfGerms.IsFlat.{u})
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat _ _ c).mpr ?_
  have : Flat ((BigFppfOver.toScheme B S hS).map c.h) :=
    flat_strictHenselizationSchemeToChart hY ybar
  exact MorphismOfGerms.isFlat_ofSchemeHom _ _

/-! ### The closed point of `Y^{sh}` lies over the point under `ȳ` -/

/-- The lift of `ȳ` to `Y^{sh}`, as a morphism of the site from the spectrum of the field of
`ȳ`: the canonical point of the strict henselization of the chart. -/
def strictHenselizationLift : ybar.val.siteObject ⟶ strictHenselizationObj hY ybar :=
  siteHomMk B S hS (geometricPointToStrictHenselization (strictHenselizationSite hY ybar)
      (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
      (strictHenselizationChartPoint hY ybar)) (by
    change _ ≫ strictHenselizationSchemeToChart hY ybar ≫
      B.inclusion.map (strictHenselizationNbhd hY ybar).chart.obj.left.hom = _
    rw [← Category.assoc, geometricPointToStrictHenselization_comp]
    change B.inclusion.map (strictHenselizationNbhd hY ybar).point.left ≫ _ = _
    rw [← B.inclusion.map_comp]
    exact congrArg B.inclusion.map (Over.w (strictHenselizationNbhd hY ybar).point))

/-- The lift of `ȳ` to `Y^{sh}` followed by `Y^{sh} ⟶ V` is the lift of `ȳ` to `V`. -/
theorem strictHenselizationLift_comp_toChart :
    strictHenselizationLift hY ybar ≫ strictHenselizationToChart hY ybar =
      (strictHenselizationNbhd hY ybar).point := by
  apply hom_ext_toScheme
  rw [Functor.map_comp]
  exact geometricPointToStrictHenselization_comp _ _ _ _

/-- The lift of `ȳ` to `Y^{sh}`, as a field-valued point. -/
def strictHenselizationLiftPoint :
    FieldValuedPoint B S hS (yoneda.obj (strictHenselizationObj hY ybar)) where
  carrier := ybar.val.carrier
  contained := ybar.val.contained
  toBase := ybar.val.toBase
  value := strictHenselizationLift hY ybar

/-- The lift of `ȳ` represents the closed point of `Y^{sh}`. -/
theorem class_strictHenselizationLiftPoint :
    (strictHenselizationLiftPoint hY ybar).class B S hS _ =
      strictHenselizationClosedPoint hY ybar := by
  refine injective_pointsToScheme B S hS _ ?_
  rw [pointsToScheme_class, strictHenselizationClosedPoint]
  refine Eq.trans ?_ (pointsToScheme_presheafPoint B S hS _ _ _).symm
  change geometricPointToStrictHenselization _ _ _ _ (IsLocalRing.closedPoint _) =
    (IsLocalRing.closedPoint _ : strictHenselizationScheme hY ybar)
  rw [← geometricPointToStrictHenselization_base_default]
  exact congrArg _ (Subsingleton.elim _ _)

/-! ### Stacks 0CVB, (4) ⟹ (1) -/

/-- Over `Y^{sh}`, an impurity whose structure morphism is locally quasi-finite can be shrunk to
one whose structure morphism is universally closed, with `t` its only point over the closed
point (Stacks 02LK over a henselian base). -/
private theorem exists_isImpurity_universallyClosed_of_isLocallyQuasiFinite
    {P : PrePureSituation.{u, u} B S hS} (ybar : GeometricPoint B S hS P.Y)
    {g₀ : yoneda.obj (strictHenselizationObj P.hY ybar) ⟶ P.Y}
    {hy₀ : pointsMap B S hS _ g₀ (strictHenselizationClosedPoint P.hY ybar) = P.y}
    (E : ImpurityDiagram (PointedOver.ofTestScheme _ g₀ _ hy₀).baseChange)
    (hE : E.IsImpurity) (hlqf : IsLocallyQuasiFinite B S hS E.g) :
    ∃ E' : ImpurityDiagram (PointedOver.ofTestScheme _ g₀ _ hy₀).baseChange,
      E'.IsImpurity ∧ UniversallyClosed B S hS E'.g ∧
      ∀ w : points B S hS (yoneda.obj E'.T), pointsMap B S hS (yoneda.obj E'.T) E'.g w =
        strictHenselizationClosedPoint P.hY ybar → w = E'.t := by
  set T₀ := strictHenselizationObj P.hY ybar
  set y₀ := strictHenselizationClosedPoint P.hY ybar
  obtain ⟨k, hk⟩ : ∃ k : E.T ⟶ T₀, yoneda.map k = E.g := ⟨_, Functor.map_preimage _ _⟩
  have hsch := (isLocallyQuasiFinite_yoneda_map_iff B S hS k).mp (hk ▸ hlqf)
  let a : (BigFppfOver.toScheme B S hS).obj E.T ⟶ strictHenselizationScheme P.hY ybar :=
    (BigFppfOver.toScheme B S hS).map k
  have : LocallyOfFiniteType a := hsch.1
  have : LocallyQuasiFinite a := hsch.2
  have hy₀pt : pointsToScheme B S hS T₀ y₀ =
      (IsLocalRing.closedPoint _ : strictHenselizationScheme P.hY ybar) :=
    pointsToScheme_presheafPoint B S hS _ _ _
  have hapt : ∀ w, pointsToScheme B S hS T₀ (pointsMap B S hS (yoneda.obj E.T) E.g w) =
      a (pointsToScheme B S hS E.T w) := by
    rw [← hk]
    exact pointsToScheme_pointsMap_yoneda B S hS k
  set x := pointsToScheme B S hS E.T E.t
  have hx : a x = IsLocalRing.closedPoint _ :=
    (hapt _).symm.trans ((congrArg (pointsToScheme B S hS T₀) E.mapsToChosenPoint).trans hy₀pt)
  obtain ⟨U, hxU, hfin, huniqU⟩ := exists_isFinite_forall_eq_of_locallyQuasiFinite a x hx
  have hU : B.Contains (U : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion U.ι E.T.left.property
  set T₃ : BigFppfOver B S hS := BigFppfOver.mk B S hS hU (U.ι ≫ B.inclusion.map E.T.hom)
  set j : T₃ ⟶ E.T := siteHomMk B S hS U.ι rfl
  set t₃ := (pointsEquivScheme B S hS T₃).symm (⟨x, hxU⟩ : U)
  have ht₃pt : pointsToScheme B S hS T₃ t₃ = (⟨x, hxU⟩ : U) :=
    (pointsEquivScheme B S hS T₃).apply_symm_apply _
  have ht₃ : pointsMap B S hS (yoneda.obj T₃) (yoneda.map j) t₃ = E.t := by
    refine injective_pointsToScheme B S hS _ ?_
    rw [pointsToScheme_pointsMap_yoneda, ht₃pt]
    rfl
  obtain ⟨t₃', hs₃, ht₃'⟩ := exists_specializes_of_isOpenImmersion j
    (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion U.ι)) t₃ E.t' (ht₃ ▸ E.specializes)
  obtain ⟨xi₃, hxi₃, himp₃⟩ := E.exists_isImpurity_pullbackAlong hE (yoneda.map j) hs₃ ht₃ ht₃'
  have hg₃ : yoneda.map j ≫ E.g = yoneda.map (j ≫ k) := by rw [Functor.map_comp, hk]
  refine ⟨E.pullbackAlong (yoneda.map j) hs₃ ht₃ xi₃ hxi₃, himp₃, ?_, fun w hw => ?_⟩
  · change UniversallyClosed B S hS (yoneda.map j ≫ E.g)
    rw [hg₃]
    refine universallyClosed_yoneda_map B S hS (j ≫ k) ?_
    have : _root_.AlgebraicGeometry.IsFinite (U.ι ≫ a) := hfin
    change _root_.AlgebraicGeometry.UniversallyClosed (U.ι ≫ a)
    infer_instance
  · have hw' : pointsToScheme B S hS T₀
        (pointsMap B S hS (yoneda.obj T₃) (yoneda.map j ≫ E.g) w) =
        pointsToScheme B S hS T₀ y₀ := congrArg (pointsToScheme B S hS T₀) hw
    rw [hg₃, pointsToScheme_pointsMap_yoneda, hy₀pt] at hw'
    refine injective_pointsToScheme B S hS _ ?_
    change pointsToScheme B S hS T₃ w = pointsToScheme B S hS T₃ t₃
    rw [ht₃pt]
    exact Subtype.ext (huniqU (pointsToScheme B S hS T₃ w).1 (pointsToScheme B S hS T₃ w).2 hw')

/-- **Stacks 0CVB, (4) ⟹ (1).** In Situation 0CV6, let `ȳ` be a geometric point of `Y` over `y`.
If there is an impurity `(T ⟶ Y, t' ⤳ t, ξ)` of `ℱ` above `y` with `T ⟶ Y` quasi-finite at `t`,
then there is an impurity of `ℱ` above `y` over the strict henselization `Y^{sh}`, with
specialized point the closed point. -/
theorem hasImpurityOverStrictHenselization_of_hasImpurityQuasiFiniteAtPoint
    (P : PrePureSituation.{u, u} B S hS) (ybar : GeometricPoint B S hS P.Y)
    (hybar : ybar.LiesOver P.y) (h : HasImpurityQuasiFiniteAtPoint P) :
    HasImpurityOverStrictHenselization P ybar := by
  obtain ⟨D, hqf, hD⟩ := h
  set T₀ := strictHenselizationObj P.hY ybar
  set g₀ := strictHenselizationToSpace P.hY ybar
  set y₀ := strictHenselizationClosedPoint P.hY ybar
  set c := PointedOver.ofTestScheme T₀ g₀ y₀
    (pointsMap_strictHenselizationToSpace_closedPoint P.hY ybar hybar)
  -- Stacks 0CVA along the flat morphism `Y^{sh} ⟶ Y`.
  obtain ⟨d, hxi, hass⟩ := exists_flatImpurityAscentData_of_isFlatAt P c
    (isFlatAt_strictHenselizationToSpace P.hY ybar) D hD
  -- Shrink to a locally quasi-finite structure morphism.
  obtain ⟨E₂, hE₂, hlqf⟩ := exists_isImpurity_isLocallyQuasiFinite_of_isQuasiFiniteAt d.diagram
    (d.isImpurity_diagram hxi hass hD) (d.isQuasiFiniteAt_structureMap hqf)
  -- Stacks 02LK over the strictly henselian base: a finite piece around `t`.
  obtain ⟨E₃, hE₃, huc, huniq⟩ :=
    exists_isImpurity_universallyClosed_of_isLocallyQuasiFinite ybar E₂ hE₂ hlqf
  -- The impurity over `Y^{sh}`.
  obtain ⟨t', hs, xi, hxi', himp⟩ := exists_isImpurity_of_isImpurity_ofTestScheme E₃ hE₃ huc huniq
  refine ⟨_, Iso.refl _, himp, ?_, ?_⟩
  · change g₀ = yoneda.map (𝟙 T₀) ≫ g₀
    rw [yoneda.map_id, Category.id_comp]
  · change pointsMap B S hS (yoneda.obj T₀) (yoneda.map (𝟙 T₀)) y₀ = y₀
    rw [yoneda.map_id, pointsMap_id]
    rfl

end AlgebraicGeometry.Space

end
