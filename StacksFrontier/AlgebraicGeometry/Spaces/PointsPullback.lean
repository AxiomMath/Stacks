module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Points of a cartesian square of algebraic spaces

For a cartesian square of algebraic spaces over a scheme, every pair of points of the two
intermediate spaces with the same image in the base comes from a point of the top-left
corner: the map from the points of a fibre product to the fibre product of the point sets
is surjective.

## Main results

* `AlgebraicGeometry.Space.exists_point_of_isPullback`: in a cartesian square, a point of `Z`
  and a point of `X` with the same image in `Y` are the two images of a point of `W`.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- In a cartesian square of algebraic spaces over `S`, a point of `Z` and a
point of `X` with the same image in `Y` are the two images of a point of `W`. -/
@[stacks 03H4]
theorem exists_point_of_isPullback (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W Z X Y : AlgebraicSpaces B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (z : points B S hS Z.1) (x : points B S hS X.1)
    (h : pointsMap B S hS Z.1 g.hom z = pointsMap B S hS X.1 f.hom x) :
    ∃ w : points B S hS W.1,
      pointsMap B S hS W.1 p.hom w = z ∧ pointsMap B S hS W.1 q.hom w = x := by
  classical
  obtain ⟨z₀, rfl⟩ := Quot.exists_rep z
  obtain ⟨x₀, rfl⟩ := Quot.exists_rep x
  rw [pointsMap_class, pointsMap_class] at h
  obtain ⟨r, ⟨i, hi⟩, ⟨j, hj⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS Y.1
      (FieldValuedPoint.map B S hS Z.1 g.hom z₀)
      (FieldValuedPoint.map B S hS X.1 f.hom x₀)).mp h
  let A := r.siteObject B S hS Y.1
  let zY := FieldValuedPoint.map B S hS Z.1 g.hom z₀
  let xY := FieldValuedPoint.map B S hS X.1 f.hom x₀
  let z' := Z.1.map i.op z₀.value
  let x' := X.1.map j.op x₀.value
  let yZ : yoneda.obj A ⟶ Z.1 := yonedaEquiv.symm z'
  let yX : yoneda.obj A ⟶ X.1 := yonedaEquiv.symm x'
  have hcompat : yZ ≫ g.hom = yX ≫ f.hom := by
    apply (yonedaEquiv (X := A) (F := Y.1)).injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, yZ, yX] using calc
      g.hom.app (Opposite.op A) z'
          = Y.1.map i.op (g.hom.app (Opposite.op zY.siteObject) z₀.value) :=
            g.hom.naturality_apply i.op z₀.value
      _ = r.value := hi
      _ = Y.1.map j.op (f.hom.app (Opposite.op xY.siteObject) x₀.value) := hj.symm
      _ = f.hom.app (Opposite.op A) x' := (f.hom.naturality_apply j.op x₀.value).symm
  let R : AlgebraicSpaces B S hS := ⟨yoneda.obj A, isAlgebraicSpace_yoneda B S hS A⟩
  let yZ' : R ⟶ Z := ObjectProperty.homMk (P := algebraicSpaceProperty B S hS) yZ
  let yX' : R ⟶ X := ObjectProperty.homMk (P := algebraicSpaceProperty B S hS) yX
  have hcompat' : yZ' ≫ g = yX' ≫ f := ObjectProperty.hom_ext _ hcompat
  let c : PullbackCone g f := PullbackCone.mk yZ' yX' hcompat'
  let ℓ : R ⟶ W := sq.isLimit.lift c
  let β : yoneda.obj A ⟶ W.1 := ℓ.hom
  let w₀ : FieldValuedPoint B S hS W.1 :=
    ⟨r.carrier, r.contained, r.toBase, β.app (Opposite.op A) (𝟙 A)⟩
  have hp : p.hom.app (Opposite.op A) w₀.value = z' := by
    have hl : ℓ ≫ p = yZ' := sq.isLimit.fac c WalkingCospan.left
    have heval := congrArg (fun k : R ⟶ Z ↦ k.hom.app (Opposite.op A) (𝟙 A)) hl
    simp only [ObjectProperty.FullSubcategory.comp_hom] at heval
    simpa [β, ℓ, c, yZ', yZ] using heval
  have hq : q.hom.app (Opposite.op A) w₀.value = x' := by
    have hl : ℓ ≫ q = yX' := sq.isLimit.fac c WalkingCospan.right
    have heval := congrArg (fun k : R ⟶ X ↦ k.hom.app (Opposite.op A) (𝟙 A)) hl
    simp only [ObjectProperty.FullSubcategory.comp_hom] at heval
    simpa [β, ℓ, c, yX', yX] using heval
  refine ⟨w₀.class B S hS W.1, ?_, ?_⟩
  all_goals
    rw [pointsMap_class]
    apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
    refine ⟨_, FieldValuedPoint.dominates_refl B S hS _ _, ?_⟩
    first | exact ⟨i, hp.symm⟩ | exact ⟨j, hq.symm⟩

end AlgebraicGeometry.Space

end
