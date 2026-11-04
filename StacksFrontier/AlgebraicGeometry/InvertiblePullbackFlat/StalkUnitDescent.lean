module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.StalkGenerator
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.Stalks

/-!
# A unit relation upstairs descends to the local ring of the base

The uniqueness sentence of the penultimate paragraph of [Stacks, Tag 0BD7] — that the multiplier
`g` is "well defined up to multiplication by an element of `𝒪_{Y, y}^*`" — rests on the fact that
a relation `φ^*(p) = u φ^*(q)` with `u` a unit of `𝒪_{X, x}` forces `p` and `q` to differ by a
unit of `𝒪_{Y, y}`. This file states that for a flat morphism of integral schemes, the local
instance of `Module.FaithfullyFlat.associated_of_algebraMap_eq_isUnit_mul` which until now was
available only for abstract rings.

## Main results

* `AlgebraicGeometry.exists_isUnit_mul_eq_of_isUnit_stalkMap`: the descent of the unit, at a point
  of `X` and its image.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 05UU](https://stacks.math.columbia.edu/tag/05UU)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **The uniqueness clause of [Stacks, Tag 0BD7], on the local rings.** For `φ` flat between
integral schemes, two germs on the base whose pullbacks differ by a unit of `𝒪_{X, x}` already
differ by a unit of `𝒪_{Y, φ(x)}`: extension of ideals along `𝒪_{Y, φ(x)} → 𝒪_{X, x}` is
injective because that map is faithfully flat. -/
theorem exists_isUnit_mul_eq_of_isUnit_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsIntegral X] [IsIntegral Y] (x : X) (p q : Y.presheaf.stalk (f.base x))
    {u : X.presheaf.stalk x} (hu : IsUnit u)
    (h : (f.stalkMap x).hom p = u * (f.stalkMap x).hom q) :
    ∃ v : Y.presheaf.stalk (f.base x), IsUnit v ∧ p = v * q := by
  let : Algebra ↑(Y.presheaf.stalk (f.base x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : IsDomain ↑(Y.presheaf.stalk (f.base x)) := inferInstance
  have : IsDomain ↑(X.presheaf.stalk x) := inferInstance
  have : Module.FaithfullyFlat ↑(Y.presheaf.stalk (f.base x)) ↑(X.presheaf.stalk x) :=
    Flat.faithfullyFlat_stalkMap f x
  obtain ⟨c, hc⟩ := Module.FaithfullyFlat.associated_of_algebraMap_eq_isUnit_mul hu h
  refine ⟨(c⁻¹ : _), (c⁻¹).isUnit, ?_⟩
  rw [← hc, mul_comm, mul_assoc, Units.mul_inv, mul_one]

end AlgebraicGeometry

end
