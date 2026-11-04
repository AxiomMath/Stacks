module

public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeGroupoidEvaluation

/-!
# The arrows of the evaluated groupoid of a base change

Let `H = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `X` and let
`g : X' ⟶ X` be a morphism of algebraic spaces. The base change of Stacks 0DTA has
`U' = X' ×_X U` and `R' = X' ×_X R`, so a `V`-point of `R'` is a `V`-point of `R` together with a
`V`-point of `X'` lying under it. This file turns that into the statement needed by the fullness
half of Stacks 0DTG: **the evaluated functor of the projection `(U', R') ⟶ (U, R)` is surjective
on arrows between two `V`-points of `U'` with the same `X'`-component.**

The restriction on the `X'`-components cannot be dropped: an arrow of the evaluated groupoid of
the base change has its source and its target over one and the same `V`-point of `X'`, because
both the source and the target of a `V`-point of `R'` have for `X'`-component the `X'`-component
of that point.

## Main results

* `AlgebraicGeometry.Space.exists_baseChangeArrowSection`: a `V`-point of `R` and a `V`-point of
  `X'` with the same image in `X` are the two projections of a `V`-point of `R' = X' ×_X R`.
* `AlgebraicGeometry.Space.arrowsToBase_eq_objectsToBase_source` and
  `AlgebraicGeometry.Space.arrowsToBase_eq_objectsToBase_target`: the groupoid axioms
  `source_over` and `target_over`, read on a `V`-point of the arrow space.
* `AlgebraicGeometry.Space.objectsToBase_mapObjects`: the cartesian square on object spaces, read
  on a `V`-point.
* `AlgebraicGeometry.Space.exists_baseChangeEvaluationArrow`: **an arrow of the evaluated
  groupoid of the base change out of an arrow of the evaluated groupoid downstairs**, between two
  `V`-points of `U'` with the same `X'`-component.

## Implementation notes

The two projections of the wanted `V`-point of `R'` are the `V`-point of `R` underlying the given
arrow and the `X'`-component of the source; their compatibility over `X` is the groupoid axiom
`source_over` followed by the cartesian square on object spaces. That the source and the target
of the `V`-point produced are the two prescribed `V`-points of `U'` is then joint injectivity of
the two projections of the cartesian square on object spaces
(`AlgebraicGeometry.Space.section_eq_of_isPullback`, Stacks 02X2 on sections).

Every step is written in term mode. The cartesian squares of `AlgebraicGeometry.Space.BaseChange`
present their first leg as an `ObjectProperty.homMk` of the projection, which `simp` does not see
through, so a `simpa` that normalises the composites of a square leaves the two spellings of that
leg side by side and fails; `exact` checks the two against each other at the default transparency
and succeeds.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 0DTA](https://stacks.math.columbia.edu/tag/0DTA)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **A `V`-point of `R` and a `V`-point of `X'` with the same image in `X` are the two
projections of a `V`-point of `R' = X' ×_X R`.** This is Stacks 02X2 on sections
(`AlgebraicGeometry.Space.exists_section_of_isPullback`) for the cartesian square on arrow spaces
recorded by `AlgebraicGeometry.Space.BaseChange`. -/
theorem exists_baseChangeArrowSection {X X' : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS X) (g : X' ⟶ X) (V : BigFppfOver C S hS)
    (r : H.arrows.obj.obj (op V)) (x' : X'.obj.obj (op V))
    (h : H.arrowsToBase.hom.app (op V) r = g.hom.app (op V) x') :
    ∃ r' : (Space.baseChange H g).groupoid.arrows.obj.obj (op V),
      (Space.baseChange H g).projection.mapArrows.app (op V) r' = r ∧
        (Space.baseChange H g).groupoid.arrowsToBase.hom.app (op V) r' = x' :=
  Space.exists_section_of_isPullback C S hS (Space.baseChange H g).arrows_isPullback r x' h

/-- **The structure morphism to the base of a `V`-point of the arrow space is that of its
source**: the groupoid axiom `source_over`, read on a point. -/
theorem arrowsToBase_eq_objectsToBase_source {Y : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS Y) (V : BigFppfOver C S hS)
    (r : H.arrows.obj.obj (op V)) :
    H.arrowsToBase.hom.app (op V) r =
      H.objectsToBase.hom.app (op V) (H.source.hom.app (op V) r) := by
  have h := congrArg (fun k : H.arrows ⟶ Y => k.hom.app (op V) r) H.source_over
  simpa using h.symm

/-- **The structure morphism to the base of a `V`-point of the arrow space is that of its
target**: the groupoid axiom `target_over`, read on a point. -/
theorem arrowsToBase_eq_objectsToBase_target {Y : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS Y) (V : BigFppfOver C S hS)
    (r : H.arrows.obj.obj (op V)) :
    H.arrowsToBase.hom.app (op V) r =
      H.objectsToBase.hom.app (op V) (H.target.hom.app (op V) r) := by
  have h := congrArg (fun k : H.arrows ⟶ Y => k.hom.app (op V) r) H.target_over
  simpa using h.symm

/-- **The cartesian square on object spaces of a base change, read on a `V`-point of `U'`**: the
image in `X` of its image in `U` is the image in `X` of its `X'`-component. -/
theorem objectsToBase_mapObjects {X X' : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS X) (g : X' ⟶ X) (V : BigFppfOver C S hS)
    (u : (Space.baseChange H g).groupoid.objects.obj.obj (op V)) :
    H.objectsToBase.hom.app (op V)
        ((Space.baseChange H g).projection.mapObjects.app (op V) u) =
      g.hom.app (op V) ((Space.baseChange H g).groupoid.objectsToBase.hom.app (op V) u) := by
  have h0 : (Space.baseChange H g).projection.mapObjects ≫ H.objectsToBase.hom =
      (Space.baseChange H g).groupoid.objectsToBase.hom ≫ g.hom :=
    congrArg (fun k : (Space.baseChange H g).groupoid.objects ⟶ X => k.hom)
      (Space.baseChange H g).objects_isPullback.w
  exact congrArg (fun k : (Space.baseChange H g).groupoid.objects.obj ⟶ X.obj =>
    k.app (op V) u) h0

/-- **An arrow of the evaluated groupoid of a base change out of an arrow of the evaluated
groupoid downstairs.** Let `u₁` and `u₂` be two `V`-points of `U' = X' ×_X U` with the same
`X'`-component. Then every arrow of `H(V)` from the image of `u₁` to the image of `u₂` is the
image of an arrow of the evaluated groupoid of the base change from `u₁` to `u₂`.

The `V`-point of `R' = X' ×_X R` is produced by
`AlgebraicGeometry.Space.exists_baseChangeArrowSection` from the `V`-point of `R` underlying the
arrow and the common `X'`-component; the hypothesis on the `X'`-components is what identifies its
target with `u₂`. -/
theorem exists_baseChangeEvaluationArrow {X X' : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS X) (g : X' ⟶ X) (V : BigFppfOver C S hS)
    (u₁ u₂ : (Space.baseChange H g).groupoid.objects.obj.obj (op V))
    (hx : (Space.baseChange H g).groupoid.objectsToBase.hom.app (op V) u₁ =
      (Space.baseChange H g).groupoid.objectsToBase.hom.app (op V) u₂)
    (arr : (show H.toGroupoidInFunctors.Evaluation (op V) from
        (Space.baseChange H g).projection.mapObjects.app (op V) u₁) ⟶
      (Space.baseChange H g).projection.mapObjects.app (op V) u₂) :
    ∃ arr' : (show (Space.baseChange H g).groupoid.toGroupoidInFunctors.Evaluation (op V)
        from u₁) ⟶ u₂,
      ((Space.baseChange H g).projection.evaluation (op V)).map arr' = arr := by
  obtain ⟨hs, ht⟩ := (H.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _ arr).2
  have hcompat : H.arrowsToBase.hom.app (op V)
        (H.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _ arr).1 =
      g.hom.app (op V)
        ((Space.baseChange H g).groupoid.objectsToBase.hom.app (op V) u₁) :=
    (arrowsToBase_eq_objectsToBase_source H V _).trans
      ((congrArg (fun k : H.objects.obj.obj (op V) => H.objectsToBase.hom.app (op V) k) hs).trans
        (objectsToBase_mapObjects H g V u₁))
  obtain ⟨r', hr'₁, hr'₂⟩ := exists_baseChangeArrowSection H g V _ _ hcompat
  have hsrc : (Space.baseChange H g).groupoid.source.hom.app (op V) r' = u₁ := by
    refine Space.section_eq_of_isPullback C S hS (Space.baseChange H g).objects_isPullback _ _ ?_ ?_
    · exact ((Space.baseChange H g).projection.map_source (op V) r').symm.trans
        ((congrArg (fun k : H.arrows.obj.obj (op V) => H.source.hom.app (op V) k) hr'₁).trans hs)
    · exact (arrowsToBase_eq_objectsToBase_source (Space.baseChange H g).groupoid V r').symm.trans
        hr'₂
  have htgt : (Space.baseChange H g).groupoid.target.hom.app (op V) r' = u₂ := by
    refine Space.section_eq_of_isPullback C S hS (Space.baseChange H g).objects_isPullback _ _ ?_ ?_
    · exact ((Space.baseChange H g).projection.map_target (op V) r').symm.trans
        ((congrArg (fun k : H.arrows.obj.obj (op V) => H.target.hom.app (op V) k) hr'₁).trans ht)
    · exact (arrowsToBase_eq_objectsToBase_target (Space.baseChange H g).groupoid V r').symm.trans
        (hr'₂.trans hx)
  refine ⟨((Space.baseChange H g).groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op V)
    u₁ u₂).symm ⟨r', hsrc, htgt⟩, ?_⟩
  refine (H.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ _).injective (Subtype.ext ?_)
  refine (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
    (Space.baseChange H g).projection (op V) _).trans ?_
  refine Eq.trans (congrArg
    (fun k : (Space.baseChange H g).groupoid.arrows.obj.obj (op V) =>
      (Space.baseChange H g).projection.mapArrows.app (op V) k)
    (congrArg Subtype.val (Equiv.apply_symm_apply
      ((Space.baseChange H g).groupoid.toGroupoidInFunctors.evaluationArrowEquiv (op V) u₁ u₂)
      ⟨r', hsrc, htgt⟩))) hr'₁

end AlgebraicGeometry.Space

end
