module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationStepsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StagesReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal

/-!
# The relation `R₀ = U₀ ×_{X₀} U₀` at a separated stage, and its system over the stages

In the second step of the proof of Stacks 07SI one chooses an affine chart `U₀ ⟶ X₀` of the
chosen stage and forms the relation `R₀ = U₀ ×_{X₀} U₀` and the two systems
`Uᵢ = Xᵢ ×_{X₀} U₀` and `Rᵢ = R₀ ×_{X₀} Xᵢ`.  The chart system machinery of Stacks 03WF and
Stacks 07SF produces such a system, with a limit, from *any* affine scheme-valued point of the
stage — it asks nothing else of the point, neither étaleness nor surjectivity.  So the only
obstruction to using it for the relation system as well is whether `R₀` is affine, and that is
exactly what a separated stage supplies.

`R₀` is the base change of `U₀ ⟶ X₀` along itself, so it is affine as soon as `U₀ ⟶ X₀` is an
affine morphism; and a morphism from an affine object of the site to a separated algebraic space
is affine, which is Stacks 08GB part (4), already available as
`AlgebraicGeometry.Space.isAffineHom_of_affine_source_of_isAbsolutelySeparated`.  Concretely, the
diagonal `X₀ ⟶ X₀ × X₀` being a closed immersion makes `R₀ ⟶ U₀ × U₀` a closed immersion into an
affine scheme.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.chartSystem` is the system
  `j ↦ Xⱼ ×_{X₀} V` of affine charts of the stages at or beyond the chosen one, for an arbitrary
  affine scheme-valued point `V ⟶ X₀`, and
  `AlgebraicGeometry.Space.LimitSituation.chartLimitBridge` is its limit.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.exists_affine_relationChart_of_isAbsolutelySeparated`,
  and its form for a bare presheaf
  `AlgebraicGeometry.Space.exists_affine_selfPullback_of_isAbsolutelySeparated`:
  **at a separated stage the relation `R₀ = U₀ ×_{X₀} U₀` of an affine chart is affine**, that
  is, it is represented by an affine object of the site, with the two projections.

Applied to `R₀`, `AlgebraicGeometry.Space.LimitSituation.chartSystem` and
`.chartLimitBridge` give the relation system and its limit; composed with
`AlgebraicGeometry.Space.LimitSituation.stagesSchemeDiagram`,
`.isAffine_stagesSchemeDiagram_obj`, `.stagesSchemeCone` and `.isLimit_stagesSchemeCone` they
give `ER` together with `∀ a, IsAffine (ER.obj a)` and a limiting cone, in the shape
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation_of_isAffine`
consumes — and the same declarations applied to `U₀` give `EU`.

## Implementation notes

*Why not `AlgebraicGeometry.Space.exists_quotient_presentation_of_affine_transition`.*  That is
Stacks 07SG and builds both systems, but its exported conclusion
(`AlgebraicGeometry.Space.exists_limit_chart_relation` in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/QuotientPresentation.lean`) keeps only the Cartesian
squares and the étale equivalence relation and does not mention the limiting cones, and both its
appeals to the affineness of the base changes bind that affineness to `_`.  Widening those
conclusions would change existing statements.  The route here needs none of it: the chart system
of Stacks 03WF already produces the system and Stacks 07SF its limit, for the affine point `R₀`
directly.

*What the chart system asks of the point.*  Only that it be a morphism from an affine object of
the site to the chosen stage.  In particular the two systems `Uᵢ` and `Rᵢ` are produced by the
same construction, applied to `U₀` and to `R₀`; nothing here uses that the chart `U₀ ⟶ X₀` is
étale or surjective, which is what the *equalizer presentation* — not the systems — needs.

*The size hypotheses.*  `AlgebraicGeometry.Space.AffineChartSystem.limitBridge` carries the two
size bounds of Stacks 07SF, on the objects and on the morphisms of the index category.  For the
index category `A.Iᵒᵖ` of a limit situation the second is automatic, a preorder being thin, so
only the bound on the index set itself appears below, in the same form as on
`AlgebraicGeometry.Space.LimitSituation.isAffineHom_π`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The self fibre product of an affine chart of a separated algebraic space is affine.**  Let
`Y` be a presheaf on the big fppf site of `S` whose absolute diagonal is a closed immersion — a
separated algebraic space in the sense of Stacks 03BS, part (1) — and let
`f : V ⟶ Y` be a morphism from an affine object of the site.  Then `V ×_Y V` is represented by an
affine object of the site, with its two projections.

In the proof of Stacks 07SI this is the relation `R₀ = U₀ ×_{X₀} U₀` of an affine chart of a
separated stage: separatedness makes `R₀ ⟶ U₀ × U₀` a closed immersion into an affine scheme.
Formally it is Stacks 08GB, part (4)
(`AlgebraicGeometry.Space.isAffineHom_of_affine_source_of_isAbsolutelySeparated`), which makes
`f` an affine morphism, read at the base change of `f` along `f` itself. -/
theorem exists_affine_selfPullback_of_isAbsolutelySeparated
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hsep : IsAbsolutelySeparated B S hS hZ Y)
    (V : BigAffineFppf B S hS)
    (f : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ Y) :
    ∃ (R : BigAffineFppf B S hS)
      (t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R) ⟶
        yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V))
      (s : (BigAffineFppf.inclusion B S hS).obj R ⟶
        (BigAffineFppf.inclusion B S hS).obj V),
      IsPullback t (yoneda.map s) f f :=
  isAffineHom_of_affine_source_of_isAbsolutelySeparated B S hS hZ V f hsep V f

namespace LimitSituation

variable {B S hS hZ} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : LimitSituation B S hS hZ X)

/-- **The relation `R₀ = U₀ ×_{X₀} U₀` of an affine chart of a separated stage is affine.**  This
is `AlgebraicGeometry.Space.exists_affine_selfPullback_of_isAbsolutelySeparated` at the chosen
stage of a limit situation: an affine object `R₀` of the site representing `U₀ ×_{X₀} U₀`,
together with the two projections `t` and `s` to `U₀`.

It is the hypothesis under which the relation system `Rᵢ = R₀ ×_{X₀} Xᵢ` of Stacks 07SI is a
system of *affine* schemes, so that the affine case of Stacks 01Z0 suffices for it; Situation
084R itself gives only that `R₀` is quasi-compact and separated.  In the regime of Stacks 07SQ
the separated stage is supplied by `exists_isAbsolutelySeparated_system_obj_of_isAffineSpace` of
`AlgebraicGeometry.Space.DescentSituation`. -/
theorem exists_affine_relationChart_of_isAbsolutelySeparated
    (hsep : IsAbsolutelySeparated B S hS hZ (A.system.obj (op A.base)))
    (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)) :
    ∃ (R₀ : BigAffineFppf B S hS)
      (t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
        yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀))
      (s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶
        (BigAffineFppf.inclusion B S hS).obj U₀),
      IsPullback t (yoneda.map s) f₀ f₀ :=
  exists_affine_selfPullback_of_isAbsolutelySeparated B S hS hZ hsep U₀ f₀

variable (V : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ A.system.obj (op A.base))

/-- **The system of affine charts of a limit situation at its chosen stage.**  For an affine
scheme-valued point `V ⟶ X₀` of the chosen stage, the stages at or beyond it base change to
`Xⱼ ×_{X₀} V`, and affineness of the transition morphisms of the situation makes each of those
an affine object of the site.

This is `AlgebraicGeometry.Space.affineChartSystem` (Stacks 03WF) with the situation's own
`transition_affine`.  Applied to an affine chart `U₀ ⟶ X₀` it is the system `Uᵢ` of the proof of
Stacks 07SI; applied to the relation `R₀` of
`AlgebraicGeometry.Space.LimitSituation.exists_affine_relationChart_of_isAbsolutelySeparated` it
is the system `Rᵢ`. -/
noncomputable def chartSystem :
    AffineChartSystem B S hS (op A.base) A.system V g :=
  affineChartSystem B S hS (op A.base) A.system V g fun f => A.transition_affine f

/-- **A limit situation indexed below the cofinality of the cutoff has bounded base changes**
at its chosen stage (`AlgebraicGeometry.Space.hasBoundedBaseChanges_of_lt_cof`): the index
category of a limit situation is a preorder, hence thin
(`AlgebraicGeometry.Space.LimitSituation.mk_hom_lt_aleph0`), and `ℵ₀` is below the cofinality of
the site's cutoff. -/
theorem hasBoundedBaseChanges_of_lt_cof (hI : #A.I < B.cutoff.ord.cof) :
    HasBoundedBaseChanges B S hS (op A.base) A.system :=
  Space.hasBoundedBaseChanges_of_lt_cof B S hS _ _ (fun f => A.transition_affine f)
    (A.mk_op ▸ hI) fun i j => (A.mk_hom_lt_aleph0 i j).trans B.aleph0_lt_cutoff_cof

/-- **The limit of the system of affine charts of a limit situation at its chosen stage**, as a
limit bridge, when the base changes of the stages along the affine points of the chosen stage
are bounded below the cutoff.

This is `AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBounded` (Stacks 07SF). -/
noncomputable def chartLimitBridgeOfBounded
    (hb : HasBoundedBaseChanges B S hS (op A.base) A.system) :
    AffineChartSystem.LimitBridge (A.chartSystem V g) :=
  AffineChartSystem.limitBridgeOfBounded (A.chartSystem V g)
    ((A.chartSystem V g).diagramBoundedBelow hb)

/-- **The limit of the system of affine charts of a limit situation at its chosen stage**, as a
limit bridge: a limit cone in the site whose underlying schemes form a limit cone too.

This is `AlgebraicGeometry.Space.AffineChartSystem.limitBridge` (Stacks 07SF).  Of that tag's two
size hypotheses only the bound on the index set appears: the bound on the morphisms is automatic,
the index category of a limit situation being a preorder and hence thin
(`AlgebraicGeometry.Space.LimitSituation.mk_hom_lt_aleph0`), and `ℵ₀` is below the cofinality of
the site's cutoff. -/
noncomputable def chartLimitBridge (hI : #A.I < B.cutoff.ord.cof) :
    AffineChartSystem.LimitBridge (A.chartSystem V g) :=
  AffineChartSystem.limitBridgeOfIsSiteSmall (A.chartSystem V g) (.of_lt_cof (A.mk_op ▸ hI)
    fun i j => (A.mk_hom_lt_aleph0 i j).trans B.aleph0_lt_cutoff_cof)

end LimitSituation

end AlgebraicGeometry.Space

end
