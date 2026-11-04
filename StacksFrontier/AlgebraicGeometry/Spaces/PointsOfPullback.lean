module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Points of a cartesian square

A cartesian square of presheaves on the big fppf site of `S` is surjective on points over the
fibre product of the point sets: a pair of points of the two middle terms with the same image
in the lower right corner is the image of a point of the upper left corner.

For a cartesian square of algebraic spaces this is the surjectivity of
`|Z ×_Y X| → |Z| ×_{|Y|} |X|`, the fibre product of algebraic spaces being computed as the
fibre product of the underlying sheaves.

## Main results

* `AlgebraicGeometry.Space.exists_point_of_isPullback_presheaf`: a compatible pair of points of a
  cartesian square comes from a point of the upper left corner. The square is one of presheaves;
  the statement for a cartesian square of algebraic spaces is
  `AlgebraicGeometry.Space.exists_point_of_isPullback` in
  `StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback`, which is a square in the category
  `AlgebraicGeometry.Space.AlgebraicSpaces` rather than in the presheaf category and so is
  neither this statement nor an instance of it.

## Implementation notes

Surjectivity is stated elementwise, so no set-theoretic fibre product of the point sets has to
be named. The square is an arbitrary cartesian square of presheaves and the algebraic-space
axioms are never used: the argument only lifts a common field-valued extension of the two given
points through the universal property of the square.

Concretely, the two points agree in the lower right corner, so their field-valued
representatives admit a common extension there, over the spectrum of a single field `A` in the
site. Restricting each representative along the two morphisms to `A` provides two sections over
`A`, that is two morphisms out of `yoneda.obj A`, which agree over the lower right corner; the
square's universal property turns them into a morphism `yoneda.obj A ⟶ W`, and its value at the
identity is a field-valued point of `W` restricting to the two given ones.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03H4.** Compatible points of the two middle terms of a cartesian square of
presheaves on the big fppf site of `S` lift to a point of its upper left corner.

This is surjectivity of `|Z ×_Y X| → |Z| ×_{|Y|} |X|`, stated elementwise for an arbitrary
cartesian square of presheaves. The companion statement for a cartesian square in the category
of algebraic spaces is `AlgebraicGeometry.Space.exists_point_of_isPullback`. -/
@[stacks 03H4]
theorem exists_point_of_isPullback_presheaf
    {W Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (z : points B S hS Z) (x : points B S hS X)
    (h : pointsMap B S hS Z g z = pointsMap B S hS X f x) :
    ∃ w : points B S hS W,
      pointsMap B S hS W p w = z ∧ pointsMap B S hS W q w = x := by
  classical
  obtain ⟨z₀, rfl⟩ := Quot.exists_rep z
  obtain ⟨x₀, rfl⟩ := Quot.exists_rep x
  rw [pointsMap_class, pointsMap_class] at h
  obtain ⟨r, ⟨i, hi⟩, ⟨j, hj⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS Y
      (FieldValuedPoint.map B S hS Z g z₀) (FieldValuedPoint.map B S hS X f x₀)).mp h
  let A := r.siteObject B S hS Y
  let z' := Z.map i.op z₀.value
  let x' := X.map j.op x₀.value
  let yZ : yoneda.obj A ⟶ Z := yonedaEquiv.symm z'
  let yX : yoneda.obj A ⟶ X := yonedaEquiv.symm x'
  have hcompat : yZ ≫ g = yX ≫ f := by
    apply (yonedaEquiv (X := A) (F := Y)).injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, yZ, yX] using calc
      g.app (Opposite.op A) z' = Y.map i.op (g.app
          (Opposite.op (z₀.siteObject B S hS Z)) z₀.value) :=
        g.naturality_apply i.op z₀.value
      _ = r.value := hi
      _ = Y.map j.op (f.app (Opposite.op (x₀.siteObject B S hS X)) x₀.value) := hj.symm
      _ = f.app (Opposite.op A) x' := (f.naturality_apply j.op x₀.value).symm
  have hp : p.app (Opposite.op A) (yonedaEquiv (sq.lift yZ yX hcompat)) = z' :=
    (congrArg yonedaEquiv (sq.lift_fst yZ yX hcompat)).trans (Equiv.apply_symm_apply _ _)
  have hq : q.app (Opposite.op A) (yonedaEquiv (sq.lift yZ yX hcompat)) = x' :=
    (congrArg yonedaEquiv (sq.lift_snd yZ yX hcompat)).trans (Equiv.apply_symm_apply _ _)
  refine ⟨FieldValuedPoint.class B S hS W
    ⟨r.carrier, r.contained, r.toBase, yonedaEquiv (sq.lift yZ yX hcompat)⟩, ?_, ?_⟩
  all_goals
    rw [pointsMap_class]
    apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
    refine ⟨_, FieldValuedPoint.dominates_refl B S hS _ _, ?_⟩
    first
      | exact ⟨i, hp.symm⟩
      | exact ⟨j, hq.symm⟩

end AlgebraicGeometry.Space

end
