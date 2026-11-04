module

public import StacksFrontier.Deformation.Groupoid.Basic

/-!
# Morphisms of groupoids in functors preserve inverses

A morphism `F` of groupoids in functors on a category `C` evaluates, at every object `T` of `C`,
to a functor `Deformation.GroupoidInFunctors.Hom.evaluation F T` between the evaluated groupoids.
A functor between groupoids preserves inverses, so the arrow that `F` assigns to the inverse of an
arrow `a` is the inverse of the arrow it assigns to `a`. This file records that identity directly
on the arrow functors, where the inverse of an arrow is `Deformation.inverseArrow`.

## Main results

* `Deformation.inverseArrow_eq_of_endpoints` computes `Deformation.inverseArrow` from any
  identification of the source and the target of an arrow with objects of the evaluation.
* `Deformation.GroupoidInFunctors.Hom.mapArrows_inverseArrow` states that a morphism of groupoids
  in functors intertwines the pointwise inverses.

## Implementation notes

The conclusion is an equality of two elements of the arrow functor rather than of two morphisms
of the evaluated groupoids, because the endpoints of the image of `inverseArrow G T a` agree with
the endpoints of `inverseArrow H T (F.mapArrows.app T a)` only propositionally, through
`Deformation.GroupoidInFunctors.Hom.map_source` and `map_target`; phrasing the statement with
`Quiver.Hom` would therefore need transports along those two identifications. They are instead
absorbed by `inverseArrow_eq_of_endpoints`, which restates `inverseArrow` with the endpoints
supplied by the caller. What remains is the comparison of the image of a categorical inverse with
the categorical inverse of an image, which is `CategoryTheory.Functor.map_inv` applied to the
evaluated functor.

## References

* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory
universe u v w

/-- The inverse of an arrow `a`, read through an identification of the source and the target of
`a` with objects `x` and `y` of the evaluated groupoid: it is the arrow underlying the categorical
inverse of `a` viewed as a morphism from `x` to `y`. -/
theorem inverseArrow_eq_of_endpoints {C : Type u} [Category.{v} C]
    (G : GroupoidInFunctors.{u, v, w} C) (T : C) (a : G.arrows.obj T)
    {x y : G.Evaluation T} (hs : G.source.app T a = x) (ht : G.target.app T a = y) :
    inverseArrow G T a =
      (G.evaluationArrowEquiv T y x
        (Groupoid.inv ((G.evaluationArrowEquiv T x y).symm ⟨a, hs, ht⟩))).1 := by
  subst x
  subst y
  rfl

namespace GroupoidInFunctors

/-- A morphism of groupoids in functors intertwines the pointwise inverses: the arrow it assigns
to the inverse of `a` is the inverse of the arrow it assigns to `a`. -/
theorem Hom.mapArrows_inverseArrow {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H) (T : C) (a : G.arrows.obj T) :
    F.mapArrows.app T (inverseArrow G T a) =
      inverseArrow H T (F.mapArrows.app T a) := by
  let b := (G.evaluationArrowEquiv T _ _).symm ⟨a, rfl, rfl⟩
  rw [inverseArrow_eq_of_endpoints H T _ (F.map_source T a) (F.map_target T a)]
  have hb : (H.evaluationArrowEquiv T _ _).symm
      ⟨F.mapArrows.app T a, F.map_source T a, F.map_target T a⟩ =
      (F.evaluation T).map b := by
    apply (H.evaluationArrowEquiv T _ _).injective
    apply Subtype.ext
    simpa only [F.evaluation_obj, b, Equiv.apply_symm_apply] using
      (F.evaluation_map_arrow T b).symm
  rw [hb]
  show F.mapArrows.app T (G.evaluationArrowEquiv T _ _ (Groupoid.inv b)).val = _
  rw [← F.evaluation_map_arrow]
  simp only [Groupoid.inv_eq_inv, Functor.map_inv, F.evaluation_obj]

end GroupoidInFunctors

end

end Deformation
