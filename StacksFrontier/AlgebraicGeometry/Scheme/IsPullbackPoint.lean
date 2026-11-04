module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Points of a scheme presented as a fibre product

Mathlib's `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` produces a point of the
chosen fibre product `X ×_Z Y` out of a point of `X` and a point of `Y` with the same image in
`Z`. This file transports that statement to an arbitrary cartesian square, where the fibre
product is presented by some other scheme — which is how fibre products of affine schemes arise,
namely as the spectrum of a tensor product.

## Main results

* `AlgebraicGeometry.exists_point_of_isPullback`: **a cartesian square of schemes has a point over
  any pair of points with the same image in the base.**

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)

## Tags

scheme, fibre product, cartesian square, point
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A cartesian square of schemes has a point over any pair of points with the same image in
the base.** The statement is `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` for the
chosen fibre product, carried along the canonical isomorphism of the cartesian square with it. -/
theorem exists_point_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y)
    (hxy : f.base x = g.base y) :
    ∃ z : P, fst.base z = x ∧ snd.base z = y := by
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hxy
  refine ⟨h.isoPullback.inv.base w, ?_, ?_⟩
  · rw [← hw₁]
    exact congrArg (fun k : pullback f g ⟶ X => k.base w) h.isoPullback_inv_fst
  · rw [← hw₂]
    exact congrArg (fun k : pullback f g ⟶ Y => k.base w) h.isoPullback_inv_snd

end AlgebraicGeometry

end
