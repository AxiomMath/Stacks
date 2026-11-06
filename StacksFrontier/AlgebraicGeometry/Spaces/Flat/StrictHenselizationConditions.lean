module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.StrictHenselizationImpurity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# The four conditions of Stacks 0CVB

In Situation 0CV6 let `ȳ` be a geometric point of `Y`. This file builds the strict henselization
`Y^{sh} = Spec 𝒪_{Y, ȳ}` as a test scheme of the site, together with its canonical morphism to
`Y` and its closed point, and states the four conditions of Stacks 0CVB in terms of it.

## Main definitions

* `AlgebraicGeometry.Space.strictHenselizationObj`: `Y^{sh}`, the spectrum of the étale local ring
  of a chosen étale chart of `Y` at the geometric point the chart carries. By Stacks 04KF this
  ring is the étale local ring `𝒪_{Y, ȳ}`
  (`AlgebraicGeometry.Space.strictHenselizationEquivEtaleLocalRing`).
* `AlgebraicGeometry.Space.strictHenselizationToSpace`: the canonical morphism `Y^{sh} ⟶ Y`.
* `AlgebraicGeometry.Space.strictHenselizationClosedPoint`: the closed point of `Y^{sh}`, the
  image of the canonical lift of `ȳ`.
* `AlgebraicGeometry.Space.HasImpurityOverStrictHenselization`,
  `AlgebraicGeometry.Space.HasRelativeAssociatedPointAvoidingClosedFibre`,
  `AlgebraicGeometry.Space.HasImpurityOverEtaleNeighborhood` and
  `AlgebraicGeometry.Space.HasImpurityQuasiFiniteAtPoint`: conditions (1) to (4).

## Main results

* `AlgebraicGeometry.Space.hasImpurityOverEtaleNeighborhood_of_hasImpurityOverStrictHenselization`:
  (1) ⟹ (3).
* `AlgebraicGeometry.Space.hasImpurityQuasiFiniteAtPoint_of_hasImpurityOverEtaleNeighborhood`:
  (3) ⟹ (4).

## Implementation notes

The étale local ring of Stacks 04KG is a colimit over a category one universe above the schemes
of the site, so its spectrum is not a test scheme. Stacks 04KF identifies it with the strict
henselization of any étale chart at the geometric point the chart carries, which does live in the
site's universe; `Y^{sh}` is that spectrum, for a chart chosen once for all and an auxiliary big
étale site containing it. It lies in the big fppf site by
`AlgebraicGeometry.Space.contains_strictHenselization`, because the field of a geometric point of
an algebraic space is small for the site.

Condition (2) is stated as the existence of a relative associated point of `ℱ^{sh}` which does
**not** specialize into the closed fibre: the source's printed condition (2) is the negation of
(1), (3) and (4), and is corrected as in the note of the statement of record for Stacks 0CVB. Its
relative assassin is the relative weak assassin of Stacks 0CV0, as in Stacks 0CV8.

## References

* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (ybar : GeometricPoint B S hS Y)

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_StrictHenselizationConditions
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The strict henselization as a test scheme -/

/-- The étale chart of `Y` through which `Y^{sh}` is computed, with its lift of `ȳ`. -/
def strictHenselizationNbhd : SmallEtaleNeighborhood ybar :=
  Classical.choice (nonempty_smallEtaleNeighborhood hY ybar)

/-- The scheme of the chosen chart. -/
abbrev strictHenselizationChart : Scheme.{u} :=
  neighborhoodChartScheme (strictHenselizationNbhd hY ybar)

/-- The geometric point of the chosen chart induced by `ȳ`. -/
abbrev strictHenselizationChartPoint :
    _root_.AlgebraicGeometry.GeometricPoint (strictHenselizationChart hY ybar) :=
  chartGeometricPoint (strictHenselizationNbhd hY ybar)

/-- An auxiliary big étale site containing the chosen chart. -/
def strictHenselizationSite : BigEtaleSite.{u} :=
  haveI := small_single.{u} (strictHenselizationChart hY ybar)
  BigEtaleSite.ofSet {strictHenselizationChart hY ybar}

/-- The auxiliary big étale site contains the chosen chart. -/
theorem contains_strictHenselizationSite :
    (strictHenselizationSite hY ybar).Contains (strictHenselizationChart hY ybar) :=
  have := small_single.{u} (strictHenselizationChart hY ybar)
  BigEtaleSite.contains_ofSet _ (Set.mem_singleton _)

/-- The scheme `Y^{sh}`: the strict henselization of the chosen chart at the induced geometric
point, in the sense of Stacks 03PS. -/
abbrev strictHenselizationScheme : Scheme.{u} :=
  _root_.AlgebraicGeometry.strictHenselization (strictHenselizationSite hY ybar)
    (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
    (strictHenselizationChartPoint hY ybar)

/-- `Y^{sh}` lies in the big fppf site: the field of the geometric point does. -/
theorem contains_strictHenselizationScheme : B.Contains (strictHenselizationScheme hY ybar) :=
  contains_strictHenselization (strictHenselizationNbhd hY ybar).chart.obj.left _
    (contains_strictHenselizationSite hY ybar) (strictHenselizationChartPoint hY ybar)
    ybar.val.contained

/-- The canonical morphism of schemes `Y^{sh} ⟶ V` to the chosen chart. -/
abbrev strictHenselizationSchemeToChart :
    strictHenselizationScheme hY ybar ⟶ strictHenselizationChart hY ybar :=
  _root_.AlgebraicGeometry.strictHenselizationToBase (strictHenselizationSite hY ybar)
    (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
    (strictHenselizationChartPoint hY ybar)

/-- **`Y^{sh} = Spec 𝒪_{Y, ȳ}`, as a test scheme.** -/
def strictHenselizationObj : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_strictHenselizationScheme hY ybar)
    (strictHenselizationSchemeToChart hY ybar ≫
      B.inclusion.map (strictHenselizationNbhd hY ybar).chart.obj.left.hom)

/-- The scheme underlying `Y^{sh}` is the strict henselization of the chart. -/
theorem toScheme_obj_strictHenselizationObj :
    (BigFppfOver.toScheme B S hS).obj (strictHenselizationObj hY ybar) =
      strictHenselizationScheme hY ybar := rfl

/-- The canonical morphism `Y^{sh} ⟶ V` of the site. -/
def strictHenselizationToChart :
    strictHenselizationObj hY ybar ⟶ (strictHenselizationNbhd hY ybar).chart.obj.left :=
  siteHomMk B S hS (strictHenselizationSchemeToChart hY ybar) rfl

/-- The morphism of schemes underlying `Y^{sh} ⟶ V` is the canonical morphism to the chart. -/
theorem toScheme_map_strictHenselizationToChart :
    (BigFppfOver.toScheme B S hS).map (strictHenselizationToChart hY ybar) =
      strictHenselizationSchemeToChart hY ybar := rfl

/-- **The canonical morphism `Y^{sh} ⟶ Y`.** -/
def strictHenselizationToSpace : yoneda.obj (strictHenselizationObj hY ybar) ⟶ Y :=
  yoneda.map (strictHenselizationToChart hY ybar) ≫
    (strictHenselizationNbhd hY ybar).chart.obj.hom

/-- **The closed point `ȳ` of `Y^{sh}`**, as a point of the presheaf it represents. -/
def strictHenselizationClosedPoint : points B S hS (yoneda.obj (strictHenselizationObj hY ybar)) :=
  presheafPoint B S hS (strictHenselizationObj hY ybar)
    (show strictHenselizationScheme hY ybar from IsLocalRing.closedPoint _)
    (B.residueField_spec_contains (contains_strictHenselizationScheme hY ybar) _)

/-- The chosen chart is étale over `Y`. -/
theorem isEtale_strictHenselizationNbhd_hom :
    IsEtale B S hS (strictHenselizationNbhd hY ybar).chart.obj.hom :=
  isEtale_of_presheaf_etale B S hS (strictHenselizationNbhd hY ybar).chart.property

/-! ### The four conditions -/

variable (P : PrePureSituation.{u, u} B S hS) (ybar : GeometricPoint B S hS P.Y)

/-- **Stacks 0CVB, condition (1).** There is an impurity `(Y^{sh} ⟶ Y, y' ⤳ ȳ, ξ)` of `ℱ`
above `y`: an impurity diagram whose test scheme is `Y^{sh}` over `Y`, with specialized point the
closed point. -/
def HasImpurityOverStrictHenselization : Prop :=
  ∃ (D : ImpurityDiagram P) (e : D.T ≅ strictHenselizationObj P.hY ybar),
    D.IsImpurity ∧ D.g = yoneda.map e.hom ≫ strictHenselizationToSpace P.hY ybar ∧
      pointsMap B S hS (yoneda.obj D.T) (yoneda.map e.hom) D.t =
        strictHenselizationClosedPoint P.hY ybar

/-- **Stacks 0CVB, condition (2)**, corrected as recorded in the module docstring: some point of
`Ass_{X^{sh}/Y^{sh}}(ℱ^{sh})` does not specialize to a point of the closed fibre `X_ȳ`. -/
def HasRelativeAssociatedPointAvoidingClosedFibre : Prop :=
  ∃ ξ : points B S hS (pullback (strictHenselizationToSpace P.hY ybar) P.f),
    IsRelativeWeaklyAssociatedPoint B S hS
        (P.baseChangeToBase (strictHenselizationObj P.hY ybar)
          (strictHenselizationToSpace P.hY ybar))
        (P.baseChangeModule (strictHenselizationObj P.hY ybar)
          (strictHenselizationToSpace P.hY ybar)) ξ ∧
      strictHenselizationClosedPoint P.hY ybar ∉
        pointsMap B S hS (pullback (strictHenselizationToSpace P.hY ybar) P.f)
          (pullback.fst (strictHenselizationToSpace P.hY ybar) P.f) '' closure {ξ}

/-- **Stacks 0CVB, condition (3).** There is an impurity `(T ⟶ Y, t' ⤳ t, ξ)` of `ℱ` above `y`
such that `(T, t) ⟶ (Y, y)` is an étale neighbourhood. -/
def HasImpurityOverEtaleNeighborhood : Prop :=
  ∃ D : ImpurityDiagram P, IsEtale B S hS D.g ∧ D.IsImpurity

/-- **Stacks 0CVB, condition (4).** There is an impurity `(T ⟶ Y, t' ⤳ t, ξ)` of `ℱ` above `y`
such that `T ⟶ Y` is quasi-finite at `t`. -/
def HasImpurityQuasiFiniteAtPoint : Prop :=
  ∃ D : ImpurityDiagram P, IsQuasiFiniteAt B S hS D.g D.t ∧ D.IsImpurity

/-! ### (1) ⟹ (3) ⟹ (4) -/

/-- **Stacks 0CVB, (1) ⟹ (3).** -/
theorem hasImpurityOverEtaleNeighborhood_of_hasImpurityOverStrictHenselization
    (h : HasImpurityOverStrictHenselization P ybar) : HasImpurityOverEtaleNeighborhood P := by
  obtain ⟨D, e, hD, hg, -⟩ := h
  refine exists_isImpurity_isEtale_of_isImpurity_strictHenselization D
    (strictHenselizationNbhd P.hY ybar).chart.obj.left
    (strictHenselizationNbhd P.hY ybar).chart.obj.hom
    (isEtale_strictHenselizationNbhd_hom P.hY ybar) (strictHenselizationSite P.hY ybar)
    (contains_strictHenselizationSite P.hY ybar) (strictHenselizationChartPoint P.hY ybar)
    ybar.val.contained (e.hom ≫ strictHenselizationToChart P.hY ybar)
    ((BigFppfOver.toScheme B S hS).mapIso e) ?_ ?_ hD
  · exact (BigFppfOver.toScheme B S hS).map_comp _ _
  · rw [hg, Functor.map_comp, Category.assoc]
    rfl

/-- **Stacks 0CVB, (3) ⟹ (4).** -/
theorem hasImpurityQuasiFiniteAtPoint_of_hasImpurityOverEtaleNeighborhood
    (h : HasImpurityOverEtaleNeighborhood P) : HasImpurityQuasiFiniteAtPoint P :=
  exists_isImpurity_isQuasiFiniteAt_of_exists_isImpurity_isEtale P h

end AlgebraicGeometry.Space

end
