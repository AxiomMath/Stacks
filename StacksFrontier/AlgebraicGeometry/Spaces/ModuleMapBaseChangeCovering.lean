module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Base-change spaces of a map of modules form a cartesian family over the test schemes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, with a
map `u : F ⟶ G` of quasi-coherent `𝒪_X`-modules.  For a morphism `g : T' ⟶ T` of schemes over
`Y` the two base-change spaces are related by `X ×_Y T' ⟶ X ×_Y T`, and that comparison square
is cartesian: it identifies `X ×_Y T'` with `(X ×_Y T) ×_T T'`.  Consequently the comparison
inherits from `g` every property stable under base change, and a jointly surjective family of
test schemes over `T` base changes to a jointly surjective family over `X ×_Y T`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isPullback_baseChangeMap`: the comparison square
  of base-change spaces over `g : T' ⟶ T` is cartesian.
* `AlgebraicGeometry.Space.ModuleMapSituation.isFlat_baseChangeMap`: the comparison is flat as
  soon as `g` is.
* `AlgebraicGeometry.Space.ModuleMapSituation.isJointlySurjective_baseChangeMap`: a jointly
  surjective family of test schemes over `T` stays jointly surjective after base change
  to `X ×_Y T`.

## Implementation notes

The cartesian square is the pasting of the two squares exhibiting `X ×_Y T'` and `X ×_Y T` as
fibre products over `Y`, so it is obtained from
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` by
`CategoryTheory.IsPullback.of_right'`; the induced morphism that lemma produces is the lift
defining `AlgebraicGeometry.Space.ModuleMapSituation.baseChangeMap` on the nose.  Joint
surjectivity transfers along it by Stacks 03H4, surjectivity of the map from the points of a
cartesian square to the fibre product of the point sets.

## References

* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ModuleMapSituation

variable (D : ModuleMapSituation.{u, m} B S hS)

/-- **The comparison of base-change spaces over a morphism of test schemes is cartesian**: for
`g : T' ⟶ T` the projection `X ×_Y T' ⟶ T'` and the comparison `X ×_Y T' ⟶ X ×_Y T` exhibit
`X ×_Y T'` as the fibre product of `T' ⟶ T` and the projection `X ×_Y T ⟶ T`, that is,
`X ×_Y T' = (X ×_Y T) ×_T T'`.

This is the pasting of the two cartesian squares defining `X ×_Y T'` and `X ×_Y T` over `Y`. -/
theorem isPullback_baseChangeMap {T T' : D.SchemesOver} (g : T' ⟶ T) :
    IsPullback (D.baseChangeInclusion T') (D.baseChangeMap g)
      ((schemeSpaceFunctor B S hS).map g.left) (D.baseChangeInclusion T) := by
  have hbig : IsPullback (D.baseChangeProjection T') (D.baseChangeInclusion T') D.f
      ((schemeSpaceFunctor B S hS).map g.left ≫ T.hom) := by
    rw [CostructuredArrow.w g]
    exact AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T'.hom
  exact (IsPullback.of_right' hbig
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom)).flip

/-- The comparison of base-change spaces is flat whenever the morphism of test schemes it comes
from is, flatness of morphisms of algebraic spaces being stable under base change. -/
theorem isFlat_baseChangeMap {T T' : D.SchemesOver} (g : T' ⟶ T)
    (hg : IsFlat B S hS ((schemeSpaceFunctor B S hS).map g.left).hom) :
    IsFlat B S hS (D.baseChangeMap g).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback (D.isPullback_baseChangeMap g) hg

/-- **Joint surjectivity of a family of test schemes transfers to the base-change spaces.**  If
the morphisms `T' i ⟶ T` are jointly surjective on points, then so are the comparisons
`X ×_Y T' i ⟶ X ×_Y T`.

A point of `X ×_Y T` maps to a point of `T`, which is the image of a point of some `T' i`; the
cartesian square of `AlgebraicGeometry.Space.ModuleMapSituation.isPullback_baseChangeMap` then
produces a point of `X ×_Y T' i` above both. -/
theorem isJointlySurjective_baseChangeMap {I : Type v} {T : D.SchemesOver}
    (T' : I → D.SchemesOver) (g : ∀ i, T' i ⟶ T)
    (h : IsJointlySurjective B S hS (fun i ↦ ((schemeSpaceFunctor B S hS).obj (T' i).left).1)
      fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) :
    IsJointlySurjective B S hS (fun i ↦ (D.baseChangeSpace (T' i)).1)
      fun i ↦ (D.baseChangeMap (g i)).hom := by
  refine (isJointlySurjective_iff B S hS _ _).2 fun x ↦ ?_
  obtain ⟨i, t, ht⟩ := (isJointlySurjective_iff B S hS _ _).1 h
    (pointsMap B S hS _ (D.baseChangeInclusion T).hom x)
  obtain ⟨w, -, hw⟩ :=
    exists_point_of_isPullback B S hS (D.isPullback_baseChangeMap (g i)) t x ht
  exact ⟨i, w, hw⟩

end ModuleMapSituation

end AlgebraicGeometry.Space

end
