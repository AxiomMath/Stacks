module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageCartesianChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RingSheafChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientCharts

/-!
# Sections of direct images along `X ⟶ X'` over the thickened charts

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
(the data of Stacks 05ZT), `X = U/R` an étale presentation whose chart thickenings lie in the
site, `i : X ⟶ X' = U'/R'` the thickened quotient, and `W` a chart of `X` over `U`. The chart
`W' ⟶ X'` satisfies `W = X ×_{X'} W'` (`isPullback_thickenedChartHom`), so the inclusion
`W ⟶ W'` is a cartesian chart diagram over `i` and, for every sheaf of commutative rings `𝒜`
on the small étale site of `X`, projecting the sections of `i_*𝒜` over `W'` to `W` is a ring
isomorphism `(i_*𝒜)(W') ≅ 𝒜(W)`.

This is the identification `(i_*𝒜)(W') = 𝒜(W) = Γ(W') = 𝒪_{X'}(W')` on the dense family of charts
by which the proof of Stacks 05ZT compares the structure sheaf of `X'` with the extension.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.thickenedChartDiagram`: `W ⟶ W'` over `i`.
* `AlgebraicGeometry.Space.SquareZeroExtension.thickenedChartRingEquiv`: `(i_*𝒜)(W') ≃+* 𝒜(W)`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeΓIso`: `𝒜(W) ≅ Γ(W', ⊤)`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.bijective_ringChartProjection_thickenedChartDiagram`

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable (P : Presentation B S hS X.obj X.property)
  (hU : B.Contains (E.chartRealizedScheme (presentationChart P)))
  (hR : B.Contains (E.chartRealizedScheme (presentationRelationChart P)))

/-- **The chart diagram `W ⟶ W'` over `X ⟶ X'`** of a chart `W` of `X` over `U`. -/
noncomputable def thickenedChartDiagram (W : OverPresentation P) :
    ChartDiagram B S hS X.1 (E.thickeningQuotient hS P hU hR).1
      (E.thickeningImmersion P hU hR).hom where
  U := W.obj
  V := (E.thickenedChartFunctor P hU hR).obj W
  g := E.chartInclusionOver W.obj
    (E.contains_chartRealizedScheme_of_hom (Classical.choice W.property) hU)
  comm := (E.isPullback_thickenedChartHom P hU hR (Classical.choice W.property)).w

/-- The chart diagram `W ⟶ W'` over `X ⟶ X'` is cartesian: `W = X ×_{X'} W'`. -/
theorem isPullback_thickenedChartDiagram (W : OverPresentation P) :
    IsPullback (E.thickenedChartDiagram P hU hR W).U.1.hom
      (yoneda.map (E.thickenedChartDiagram P hU hR W).g) (E.thickeningImmersion P hU hR).hom
      (E.thickenedChartDiagram P hU hR W).V.1.hom :=
  E.isPullback_thickenedChartHom P hU hR (Classical.choice W.property)

/-- **Projecting the sections of `i_*𝒜` over `W'` to `W` is bijective**, for every sheaf of
commutative rings `𝒜` on the small étale site of `X`: the chart `W` is an initial index of the
limit computing those sections, `W` being `X ×_{X'} W'`. -/
theorem bijective_ringChartProjection_thickenedChartDiagram
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) (W : OverPresentation P) :
    Function.Bijective (ringDirectImageRanChartProjection B S hS (E.thickeningImmersion P hU hR) A
      (E.thickenedChartDiagram P hU hR W).V
      (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W))) := by
  let Q := (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).obj
    (ringSheafOf B S hS A)
  have e : ⇑(ringDirectImageRanChartProjection B S hS (E.thickeningImmersion P hU hR) A
      (E.thickenedChartDiagram P hU hR W).V
      (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W))) =
      (ranChartCone B S hS X Q.obj (chartBaseChange B S hS (E.thickeningImmersion P hU hR)
        (E.thickenedChartDiagram P hU hR W).V)).π.app
          (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W)) :=
    funext fun x ↦ chartProjection_app B S hS _ Q _ _ x
  rw [e]
  exact (isIso_iff_bijective _).mp ((ranChartIsLimit B S hS X _ _).isIso_π_app_of_isInitial _
    (isInitialIndexOfChartDiagram B S hS _ _ (E.isPullback_thickenedChartDiagram P hU hR W)))

/-- **`(i_*𝒜)(W') ≃+* 𝒜(W)`** for a chart `W` of `X` over `U`, by projection. -/
noncomputable def thickenedChartRingEquiv
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) (W : OverPresentation P) :
    (ringDirectImageRan B S hS (E.thickeningImmersion P hU hR) A).obj.obj
        (op ((E.thickenedChartFunctor P hU hR).obj W)) ≃+*
      A.obj.obj (op W.obj) :=
  RingEquiv.ofBijective _ (E.bijective_ringChartProjection_thickenedChartDiagram P hU hR A W)

/-- `thickenedChartRingEquiv` sends a section of `i_*𝒜` over `W'` to its projection to `𝒜(W)`. -/
theorem thickenedChartRingEquiv_apply
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) (W : OverPresentation P)
    (x : (ringDirectImageRan B S hS (E.thickeningImmersion P hU hR) A).obj.obj
        (op ((E.thickenedChartFunctor P hU hR).obj W))) :
    E.thickenedChartRingEquiv P hU hR A W x =
      ringDirectImageRanChartProjection B S hS (E.thickeningImmersion P hU hR) A
        (E.thickenedChartDiagram P hU hR W).V
        (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W)) x :=
  rfl

/-- **`𝒜(W) ≅ Γ(W', ⊤)`**: the regular functions on the chart thickening `W'` are the sections of
`𝒜` over the chart cut out by the whole of `W`, which is `W` itself (`chartOpensTopHom`). -/
noncomputable def chartRealizedSchemeΓIso (W : SmallEtale B S hS X.1) :
    E.A.obj.obj (op W) ≅ (E.chartRealizedScheme W).presheaf.obj (op ⊤) :=
  E.A.obj.mapIso (asIso (chartOpensTopHom B S hS X W)).op

/-- The forward map of `chartRealizedSchemeΓIso` is restriction of `𝒜` along `chartOpensTopHom`. -/
theorem chartRealizedSchemeΓIso_hom (W : SmallEtale B S hS X.1) :
    (E.chartRealizedSchemeΓIso W).hom = E.A.obj.map (chartOpensTopHom B S hS X W).op :=
  rfl

end AlgebraicGeometry.Space.SquareZeroExtension

end
