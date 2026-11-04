module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smooth.Reduced

/-!
# Smooth morphisms have geometrically reduced fibres

A morphism of schemes `f : X ⟶ Y` is geometrically reduced when `X ×_Y Spec K` is a reduced
scheme for every field `K` and every morphism `Spec K ⟶ Y`. This file proves that a smooth
morphism has that property.

## Main results

* `AlgebraicGeometry.isReduced_of_smooth_of_isAffine`: the source of a smooth morphism to a
  reduced affine scheme is reduced.
* `AlgebraicGeometry.geometricallyReduced_of_smooth`: a smooth morphism is geometrically
  reduced. This is the geometric-reducedness conclusion of Stacks 056T.

## Implementation notes

The source states Lemma 056T for a scheme smooth over a field, where "geometrically reduced over
`k`" means that the base change to every field extension of `k` is reduced. Mathlib's
`AlgebraicGeometry.GeometricallyReduced` is the relative form of that notion — reducedness of
`X ×_Y Spec K` for every field-valued point of the base — and for `Y = Spec k` the two agree,
since a morphism `Spec K ⟶ Spec k` is the same thing as a field extension `k ⊆ K`. No base field
therefore has to be fixed and the statement is proved for an arbitrary base.

Because the test schemes `Spec K` are affine, the only geometry needed is reducedness of the
source of a smooth morphism whose *target* is affine and reduced; the base change is handled by
stability of smoothness under base change. That affine statement is in turn affine-local on the
source: the sections over an affine open of the source form a smooth algebra over the global
sections of the target, so Stacks 033B — `Algebra.isReduced_of_smooth`, which carries no
Noetherian hypothesis — makes them reduced.

Only the geometric-reducedness conclusion of Lemma 056T is proved here. The source draws two
further conclusions, geometric regularity and geometric normality, from the equivalences of
Lemmas 038V and 038O, neither of which is available yet.

## References

* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **A scheme smooth over a reduced affine scheme is reduced.** On an affine open of the source
the sections form a smooth algebra over the global sections of the target, which are reduced, so
Stacks 033B applies; reducedness is local on the source. -/
public theorem isReduced_of_smooth_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [IsAffine Y] [IsReduced Y] : IsReduced X := by
  have h : ∀ i, IsReduced (X.affineCover.X i) := fun i => by
    have hsmooth : Smooth (X.affineCover.f i ≫ f) :=
      HasRingHomProperty.comp_of_isOpenImmersion @Smooth (X.affineCover.f i) f ‹Smooth f›
    let φ := ((X.affineCover.f i ≫ f).appTop).hom
    let : Algebra Γ(Y, ⊤) Γ(X.affineCover.X i, ⊤) := φ.toAlgebra
    let : Algebra.Smooth Γ(Y, ⊤) Γ(X.affineCover.X i, ⊤) :=
      (HasRingHomProperty.appTop @Smooth (X.affineCover.f i ≫ f) hsmooth).toAlgebra
    let : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
      Algebra.isReduced_of_smooth Γ(Y, ⊤) Γ(X.affineCover.X i, ⊤)
    exact isReduced_of_isAffine_isReduced (X.affineCover.X i)
  exact IsReduced.of_openCover X X.affineCover

/-- **Stacks Project, Tag 056T**, the geometric-reducedness conclusion: a smooth morphism of
schemes is geometrically reduced, that is, its base change to every field-valued point of the
target is a reduced scheme.

The source fixes a field `k` as the base; no base field is needed, a morphism `Spec K ⟶ Spec k`
being the same thing as a field extension of `k`. -/
@[stacks 056T "geometrically reduced",
  ega "IV 17.15.2" "smooth ⇒ reduced",
  sga "1 II 3.1" "base a field, reduced", ega "IV 7.3.9" "special case"]
public theorem geometricallyReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  have : Smooth (pullback.snd f y) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback f y) ‹Smooth f›
  exact isReduced_of_smooth_of_isAffine (pullback.snd f y)

end AlgebraicGeometry

end
