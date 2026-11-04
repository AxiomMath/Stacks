module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.StrictHenselizationConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsFibreProductResidueIso

/-!
# Conditions (1) and (2) of Stacks 0CVB are equivalent

In Situation 0CV6 let `ȳ` be a geometric point of `Y` lying over `y`. This file proves that
condition (1) of Stacks 0CVB, an impurity of `ℱ` above `y` over the strict henselization
`Y^{sh}` with specialized point the closed point, is equivalent to condition (2), a relative
associated point of `ℱ^{sh}` on `X^{sh} = Y^{sh} ×_Y X` which does not specialize into the closed
fibre. Stacks calls this immediate from the definition of an impurity.

## Main results

* `AlgebraicGeometry.Space.pointsMap_strictHenselizationToSpace_closedPoint`: the closed point of
  `Y^{sh}` lies over `y`.
* `AlgebraicGeometry.Space.ImpurityDiagram.exists_isRelativeWeaklyAssociatedPoint_of_iso`: an
  impurity transported along an isomorphism of test schemes.
* `AlgebraicGeometry.Space.hasImpurityOverStrictHenselization_iff_`
  `hasRelativeAssociatedPointAvoidingClosedFibre`: (1) ⟺ (2).

## References

* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-! ### The closed point of the strict henselization -/

section ClosedPoint

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (ybar : GeometricPoint B S hS Y)

/-- The scheme point underlying the closed point of `Y^{sh}` is the closed point of the spectrum
of the étale local ring. -/
theorem pointsToScheme_strictHenselizationClosedPoint :
    pointsToScheme B S hS (strictHenselizationObj hY ybar)
        (strictHenselizationClosedPoint hY ybar) =
      (show strictHenselizationScheme hY ybar from IsLocalRing.closedPoint _) :=
  pointsToScheme_presheafPoint B S hS _ _ _

/-- The closed point of `Y^{sh}` maps to the point of the chosen chart presented by the lift
of `ȳ`: it is the image of the canonical lift of the chart's geometric point. -/
theorem pointsMap_strictHenselizationToChart_closedPoint :
    pointsMap B S hS (yoneda.obj (strictHenselizationObj hY ybar))
        (yoneda.map (strictHenselizationToChart hY ybar))
        (strictHenselizationClosedPoint hY ybar) =
      (chartFieldValuedPoint (strictHenselizationNbhd hY ybar)).class B S hS
        (yoneda.obj (strictHenselizationNbhd hY ybar).chart.obj.left) := by
  refine injective_pointsToScheme B S hS _ ?_
  have key : strictHenselizationSchemeToChart hY ybar
      (IsLocalRing.closedPoint (AlgebraicGeometry.etaleLocalRing (strictHenselizationSite hY ybar)
        (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
        (strictHenselizationChartPoint hY ybar))) =
      (strictHenselizationChartPoint hY ybar).hom default := by
    rw [← geometricPointToStrictHenselization_base_default, ← Scheme.Hom.comp_apply,
      geometricPointToStrictHenselization_comp]
  rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_strictHenselizationClosedPoint]
  exact key.trans (pointsToScheme_class_eq B S hS (strictHenselizationNbhd hY ybar).chart.obj.left
    (chartFieldValuedPoint (strictHenselizationNbhd hY ybar))
    (default : (strictHenselizationChartPoint hY ybar).source)).symm

/-- **The closed point of `Y^{sh}` lies over `y`** when `ȳ` lies over `y`. -/
theorem pointsMap_strictHenselizationToSpace_closedPoint {y : points B S hS Y}
    (hybar : ybar.LiesOver y) :
    pointsMap B S hS (yoneda.obj (strictHenselizationObj hY ybar))
        (strictHenselizationToSpace hY ybar) (strictHenselizationClosedPoint hY ybar) = y := by
  rw [strictHenselizationToSpace, pointsMap_comp_apply,
    pointsMap_strictHenselizationToChart_closedPoint, chartFieldValuedPoint_pointsMap]
  exact hybar

/-- Every point of `Y^{sh}` specializes to its closed point, `Y^{sh}` being the spectrum of a
local ring. -/
theorem specializes_strictHenselizationClosedPoint
    (t : points B S hS (yoneda.obj (strictHenselizationObj hY ybar))) :
    pointsToScheme B S hS (strictHenselizationObj hY ybar) t ⤳
      pointsToScheme B S hS (strictHenselizationObj hY ybar)
        (strictHenselizationClosedPoint hY ybar) := by
  rw [pointsToScheme_strictHenselizationClosedPoint]
  exact IsLocalRing.specializes_closedPoint _

end ClosedPoint

/-! ### Transport of an impurity along an isomorphism of test schemes -/

/-- **An impurity transported along an isomorphism `e : T ≅ T'` of test schemes.** If
`D.g = e ≫ g'`, then the image of `ξ` in `T' ×_Y X` lies in the relative weak assassin of
`ℱ_{T'}`, and the image of `t` in `T'` is not in the image of its closure: the comparison
`T ×_Y X ≅ T' ×_Y X` is an isomorphism over `e`, so the square it makes is cartesian, and
Stacks 0CV2 part (1) applies to it. -/
theorem ImpurityDiagram.exists_isRelativeWeaklyAssociatedPoint_of_iso
    {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P) (hD : D.IsImpurity)
    {T' : BigFppfOver B S hS} (e : D.T ≅ T') (g' : yoneda.obj T' ⟶ P.Y)
    (hg : D.g = yoneda.map e.hom ≫ g') :
    ∃ ξ : points B S hS (pullback g' P.f),
      IsRelativeWeaklyAssociatedPoint B S hS (P.baseChangeToBase T' g')
          (P.baseChangeModule T' g') ξ ∧
        pointsMap B S hS (yoneda.obj D.T) (yoneda.map e.hom) D.t ∉
          pointsMap B S hS (pullback g' P.f) (pullback.fst g' P.f) '' closure {ξ} := by
  rw [ImpurityDiagram.isImpurity_iff] at hD
  let φ : pullback D.g P.f ⟶ pullback g' P.f :=
    pullback.map D.g P.f g' P.f (yoneda.map e.hom) (𝟙 P.X) (𝟙 P.Y)
      (by rw [Category.comp_id, hg]) (by rw [Category.comp_id, Category.id_comp])
  have hφfst : φ ≫ pullback.fst g' P.f = pullback.fst D.g P.f ≫ yoneda.map e.hom :=
    pullback.lift_fst _ _ _
  have hφsnd : φ ≫ pullback.snd g' P.f = pullback.snd D.g P.f := by
    simp [φ]
  let φS : P.baseChangeSpace D.T D.g ⟶ P.baseChangeSpace T' g' := ObjectProperty.homMk φ
  let eS : (⟨yoneda.obj D.T, isAlgebraicSpace_yoneda B S hS D.T⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ :=
    ObjectProperty.homMk (yoneda.map e.hom)
  have sq : IsPullback φS.hom (P.baseChangeToBase D.T D.g).hom
      (P.baseChangeToBase T' g').hom eS.hom :=
    IsPullback.of_horiz_isIso (fst := φ) (g := yoneda.map e.hom) ⟨hφfst⟩
  have hcomp : φS ≫ P.baseChangeToSource T' g' = P.baseChangeToSource D.T D.g :=
    ObjectProperty.hom_ext _ hφsnd
  let modIso : (modulePullback B S hS φS).obj (P.baseChangeModule T' g') ≅
      P.baseChangeModule D.T D.g :=
    (modulePullbackCompIso B S hS φS (P.baseChangeToSource T' g')).app P.F ≪≫
      eqToIso (by rw [hcomp])
  have hx' := (isRelativeWeaklyAssociatedPoint_congr _ modIso D.xi).2
    ((D.isRelativeWeakAssassinPoint_iff D.xi).1 hD.1)
  refine ⟨pointsMap B S hS _ φ D.xi,
    isRelativeWeaklyAssociatedPoint_of_baseChange B S hS sq (P.baseChangeModule T' g') hx', ?_⟩
  have hinj : Function.Injective (pointsMap B S hS (yoneda.obj D.T) (yoneda.map e.hom)) := by
    intro a b hab
    have h := congrArg (pointsMap B S hS (yoneda.obj T') (yoneda.map e.inv)) hab
    rwa [← pointsMap_comp_apply, ← pointsMap_comp_apply, ← CategoryTheory.Functor.map_comp,
      e.hom_inv_id, CategoryTheory.Functor.map_id, pointsMap_id] at h
  rintro ⟨z, hz, hzt⟩
  refine hD.2 (pointsMap B S hS _ (inv φ) z) ?_ (hinj ?_)
  · have h := (specializes_iff_mem_closure.2 hz).map (continuous_pointsMap B S hS (inv φ))
    rwa [← pointsMap_comp_apply, IsIso.hom_inv_id, pointsMap_id] at h
  · rw [← pointsMap_comp_apply, ← hφfst, pointsMap_comp_apply,
      ← pointsMap_comp_apply B S hS (inv φ), IsIso.inv_hom_id, pointsMap_id]
    exact hzt

/-! ### Stacks 0CVB, (1) ⟺ (2) -/

variable (P : PrePureSituation.{u, u} B S hS) (ybar : GeometricPoint B S hS P.Y)

/-- **Stacks 0CVB, (1) ⟹ (2).** -/
theorem hasRelativeAssociatedPointAvoidingClosedFibre_of_hasImpurityOverStrictHenselization
    (h : HasImpurityOverStrictHenselization P ybar) :
    HasRelativeAssociatedPointAvoidingClosedFibre P ybar := by
  obtain ⟨D, e, hD, hg, ht⟩ := h
  obtain ⟨ξ, hass, hnot⟩ := D.exists_isRelativeWeaklyAssociatedPoint_of_iso hD e _ hg
  exact ⟨ξ, hass, ht ▸ hnot⟩

/-- **Stacks 0CVB, (2) ⟹ (1)**, for `ȳ` lying over `y`: the base change `X^{sh}` along
`Y^{sh} ⟶ Y`, with the closed point of `Y^{sh}` and the image of `ξ` there, is an impurity
diagram, and condition (2) says exactly that it is an impurity. -/
theorem hasImpurityOverStrictHenselization_of_hasRelativeAssociatedPointAvoidingClosedFibre
    (hybar : ybar.LiesOver P.y) (h : HasRelativeAssociatedPointAvoidingClosedFibre P ybar) :
    HasImpurityOverStrictHenselization P ybar := by
  obtain ⟨ξ, hass, hnot⟩ := h
  let D : ImpurityDiagram P :=
    { T := strictHenselizationObj P.hY ybar
      g := strictHenselizationToSpace P.hY ybar
      t' := pointsMap B S hS _ (pullback.fst (strictHenselizationToSpace P.hY ybar) P.f) ξ
      t := strictHenselizationClosedPoint P.hY ybar
      specializes := specializes_strictHenselizationClosedPoint P.hY ybar _
      mapsToChosenPoint := pointsMap_strictHenselizationToSpace_closedPoint P.hY ybar hybar
      xi := ξ
      xi_liesOver := rfl }
  refine ⟨D, Iso.refl _, ⟨(D.isRelativeWeakAssassinPoint_iff ξ).2 hass, hnot⟩, ?_, ?_⟩
  · rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [Iso.refl_hom, CategoryTheory.Functor.map_id, pointsMap_id]
    rfl

/-- **Stacks 0CVB, (1) ⟺ (2).** For a geometric point `ȳ` of `Y` lying over `y`, there is an
impurity of `ℱ` above `y` over the strict henselization `Y^{sh}` exactly when some point of the
relative assassin of `ℱ^{sh}` does not specialize to a point of the closed fibre. -/
@[stacks 0CVB "(1) ⟺ (2), with (2) corrected as in
`AlgebraicGeometry.Space.HasRelativeAssociatedPointAvoidingClosedFibre`"]
theorem hasImpurityOverStrictHenselization_iff_hasRelativeAssociatedPointAvoidingClosedFibre
    (hybar : ybar.LiesOver P.y) :
    HasImpurityOverStrictHenselization P ybar ↔
      HasRelativeAssociatedPointAvoidingClosedFibre P ybar :=
  ⟨hasRelativeAssociatedPointAvoidingClosedFibre_of_hasImpurityOverStrictHenselization P ybar,
    hasImpurityOverStrictHenselization_of_hasRelativeAssociatedPointAvoidingClosedFibre P ybar
      hybar⟩

end AlgebraicGeometry.Space

end
