module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularDescent
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularSmooth

/-!
# Flat descent of smoothness over a field

Let `X` and `Y` be schemes locally of finite type over a field `k`. If a morphism `f : X ⟶ Y`
is flat at a point of `X` and the structure morphism of `X` is smooth there, then the structure
morphism of `Y` is smooth at the image point. Globally, smoothness over `k` descends along a
flat surjective morphism.

## Main results

* `AlgebraicGeometry.smoothAt_of_flatAt`: the pointwise descent of smoothness along a morphism
  which is flat at the point.
* `AlgebraicGeometry.smooth_of_flat_of_surjective`: its global consequence, that a flat
  surjective image of a scheme smooth over `k` is smooth over `k`.

## Implementation notes

A scheme over `k` is represented by an explicit structure morphism to `Spec k`, so the structure
morphism of the source is the composite `f ≫ p` and the assertion that `f` is a morphism over
`k` is built into the formulation rather than carried as a separate commutativity hypothesis.

## References

* [Stacks Project, Tag 05AX](https://stacks.math.columbia.edu/tag/05AX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Smoothness over a field descends at a point through a morphism which is flat there, provided
both schemes are locally of finite type over the field. -/
@[stacks 05AX "pointwise statement"]
public theorem smoothAt_of_flatAt
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ p)] [LocallyOfFiniteType p]
    (x : X) (hX : InfinitesimalLifting.SmoothAt (f ≫ p) x)
    (hf : AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x) :
    InfinitesimalLifting.SmoothAt p (f x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  apply (isGeometricallyRegularAt_iff_smoothAt p (f x)).mp
  exact isGeometricallyRegularAt_of_flatAt f p x
    ((isGeometricallyRegularAt_iff_smoothAt (f ≫ p) x).mpr hX) hf

/-- A flat surjective image of a scheme smooth over a field is smooth, when both schemes are
locally of finite type over that field. -/
@[stacks 05AX "global consequence"]
public theorem smooth_of_flat_of_surjective
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] [Smooth (f ≫ p)]
    [Flat f] [Surjective f] : Smooth p := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  let _ := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth) (Q := RingHom.Smooth)
  let _ := (inferInstance : MorphismProperty.Respects (@Smooth) (@IsOpenImmersion)).toRespectsRight
  apply (IsZariskiLocalAtSource.iff_exists_resLE (P := @Smooth) (f := p)).mpr
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  obtain ⟨U, hxU, hU⟩ := smoothAt_of_flatAt f p x
    ⟨⊤, trivial, IsZariskiLocalAtSource.resLE le_top (inferInstance : Smooth (f ≫ p))⟩
    (Flat.stalkMap f x)
  exact ⟨⊤, U, hxU, le_top, hU⟩

end AlgebraicGeometry

end
