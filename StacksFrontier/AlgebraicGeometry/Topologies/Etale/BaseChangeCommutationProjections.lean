module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation

/-!
# The base change comparisons of slice categories on first projections

`CategoryTheory.overPullbackBaseChangeIso` identifies, for a cartesian square, base change after
pushforward of slice categories with pushforward after base change, and
`AlgebraicGeometry.smallEtaleCartesianIndexIso` is its restriction to a small étale site. This
file records what both do to the first projections of the fibre products involved.

## Main results

* `CategoryTheory.overPullbackBaseChangeIso_hom_app_left_fst` — the comparison of slice
  categories, followed by the first projection of the target fibre product, is the first
  projection of the source one.
* `AlgebraicGeometry.smallEtaleCartesianIndexIso_hom_app_left_fst` — the same for
  `AlgebraicGeometry.smallEtaleCartesianIndexIso`.

## Implementation notes

These are lemmas about
`StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutation`, placed in their own file
so that the base file is unchanged. The definition of
`AlgebraicGeometry.smallEtaleCartesianIndexIso` is kept as it is there, and the proof of the
second lemma unfolds it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- The base-change comparison of the slice categories, on underlying objects, followed by the
first projection of the target fibre product, is the first projection of the source one. -/
public theorem CategoryTheory.overPullbackBaseChangeIso_hom_app_left_fst
    {C : Type*} [Category C] [HasPullbacks C]
    {T' T S' S : C} (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) (X : Over S') :
    ((overPullbackBaseChangeIso g' f' f g h).hom.app X).left ≫ pullback.fst X.hom f' =
      pullback.fst (X.hom ≫ g) f := by
  simp [overPullbackBaseChangeIso]

namespace AlgebraicGeometry

/-- On underlying objects, `AlgebraicGeometry.smallEtaleCartesianIndexIso` followed by the first
projection of the target fibre product is the first projection of the source one. -/
public theorem smallEtaleCartesianIndexIso_hom_app_left_fst
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {T' T S' S : B.Scheme}
    (g' : T' ⟶ T) (f' : T' ⟶ S') (f : T ⟶ S) (g : S' ⟶ S)
    (h : IsPullback g' f' f g) (U : SmallEtale B S'.obj S'.property) :
    ((smallEtaleCartesianIndexIso B g' f' f g h).hom.app U).left ≫ pullback.fst U.obj.hom f' =
      pullback.fst (U.obj.hom ≫ g) f :=
  calc ((smallEtaleCartesianIndexIso B g' f' f g h).hom.app U).left ≫ pullback.fst U.obj.hom f'
      _ = (𝟙 _ ≫ (overPullbackBaseChangeIso g' f' f g h).hom.app U.obj ≫ 𝟙 _).left ≫
          pullback.fst U.obj.hom f' := rfl
      _ = ((overPullbackBaseChangeIso g' f' f g h).hom.app U.obj).left ≫
          pullback.fst U.obj.hom f' := by simp
      _ = pullback.fst (U.obj.hom ≫ g) f :=
        CategoryTheory.overPullbackBaseChangeIso_hom_app_left_fst g' f' f g h _

end AlgebraicGeometry

end
