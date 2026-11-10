module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibreFieldRepresentative

/-!
# Closing the equivalence of Stacks 03JU

Stacks 03JU is a four-way equivalence at a point `x` of an algebraic space `F` over a scheme
`S`:

1. some étale chart of `F` has two points above `x` with finite relation fibre;
2. every pair of points above `x` in every étale chart of `F` has finite relation fibre;
3. some field-valued representative of `x` has étale quasi-compact self-intersection
   projections;
4. some field-valued representative of `x` presents it by a monomorphism out of the spectrum
   of a field.

This file proves that condition (4) implies condition (2), which closes the cycle of
implications.

## Main results

* **Stacks 03JU, part (4) implies part (2)**:
`AlgebraicGeometry.Space.HasMonomorphicFieldRepresentative.hasFiniteRelationFiberAtEveryEtaleChart`

The other links of the cycle of equivalences of Stacks 03JU are, in the namespace
`AlgebraicGeometry`: `(1) ↔ (2)` is `Space.hasFiniteRelationFiberAt_iff_everyEtaleChart` and
`(2) ↔ (3)` is
`Space.hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative`, both
in `StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers`, and `(3) ↔ (4)` is
`Space.hasEtaleQuasiCompactFieldRepresentative_iff` in
`StacksFrontier.AlgebraicGeometry.Spaces.RelationFibreMonomorphism`.

## Implementation notes

The set whose finiteness condition (2) asks for is the set of Tag 0AC2 attached to the cartesian
square presenting the relation `R = h_U ×_F h_U`: the points of `R` whose two projections are
the two given points of `|U|`. Tag 0AC7
(`AlgebraicGeometry.Space.finite_fibrePoints_of_mono_of_isQuasiFiniteAt`) makes such a set finite
when the common image point has a monomorphic field-valued representative and the lower
horizontal morphism is quasi-finite at the lower point. The first is condition (4); the second
holds because the chart is étale. Decency of `F` is not assumed, so the equivalence holds at
every point of every algebraic space.

## References

* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 0AC1](https://stacks.math.columbia.edu/tag/0AC1)
* [Stacks Project, Tag 0AC2](https://stacks.math.columbia.edu/tag/0AC2)
* [Stacks Project, Tag 0AC7](https://stacks.math.columbia.edu/tag/0AC7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 03JU, part (4) implies part (2) -/

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the pullback `h_U ×_F h_U` of presheaves on the big fppf site exceeds
-- the default budget
/-- **Stacks 03JU, condition (4) implies condition (2).** If a point `x` of an algebraic space
`F` over `S` has a field-valued representative presenting it by a monomorphism out of the
spectrum of a field, then for every étale chart `φ : h_U ⟶ F` and every pair of points of `|U|`
above `x` the fibre of `|h_U ×_F h_U| → |U| × |U|` over that pair is finite. -/
@[stacks 03JU "part (4) implies part (2)"]
theorem HasMonomorphicFieldRepresentative.hasFiniteRelationFiberAtEveryEtaleChart
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (h : HasMonomorphicFieldRepresentative B S hS F x) :
    HasFiniteRelationFiberAtEveryEtaleChart B S hS F x := by
  intro U φ a b hφ ha hb
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let D : PointsFibresDiagram B S hS :=
    { W := Limits.pullback φ φ
      Z := yoneda.obj U
      X := yoneda.obj U
      Y := F
      W_isAlgebraicSpace := isAlgebraicSpace_pullback B S hS φ φ hUalg hUalg hF
      Z_isAlgebraicSpace := hUalg
      X_isAlgebraicSpace := hUalg
      Y_isAlgebraicSpace := hF
      q := pullback.snd φ φ
      p := pullback.fst φ φ
      f := φ
      g := φ
      isPullback := IsPullback.of_hasPullback φ φ }
  have hqf : IsQuasiFiniteAt B S hS φ b :=
    isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hUalg
      (isLocallyQuasiFinite_of_isEtale' B S hS hφ) b
  have hcomm : pointsMap B S hS D.X D.f a = pointsMap B S hS D.Z D.g b := by
    change pointsMap B S hS (yoneda.obj U) φ a = pointsMap B S hS (yoneda.obj U) φ b
    rw [ha, hb]
  have hy : HasMonomorphicFieldRepresentative B S hS D.Y
      (pointsMap B S hS D.X D.f a) := by
    change HasMonomorphicFieldRepresentative B S hS F (pointsMap B S hS (yoneda.obj U) φ a)
    rw [ha]
    exact h
  exact finite_fibrePoints_of_mono_of_isQuasiFiniteAt D a b hcomm hy hqf

end AlgebraicGeometry.Space

end
