module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Varieties.BoundedDegree.Rank

/-!
# Bounding fibre degrees by field-valued base changes

For a morphism of schemes and a nonnegative integer, bounding the degrees of its fibres is
equivalent to requiring every base change to the spectrum of a field to be finite locally free
of degree at most that integer.

## Main results

* `AlgebraicGeometry.boundsFiberDegrees_iff_field_baseChange_of_nonneg` is the field-valued
  base-change characterization of a bound on fibre degrees, in the shape the source states it:
  for a nonnegative integer.
* `AlgebraicGeometry.boundsFiberDegrees_iff_pullback_snd` phrases that bound with the pullback
  projection instead of the canonical map from the scheme-theoretic fibre.

## Implementation notes

The degree of a field-valued base change is expressed by the rank of its structure morphism to
the field spectrum. The base change is the categorical pullback, whose first projection is this
structure morphism.

`AlgebraicGeometry.BoundsFiberDegrees` is phrased through
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`, whereas a cartesian square produces the
pullback projection directly; `boundsFiberDegrees_iff_pullback_snd` records that these are the
same condition and mediates between the two phrasings.

The nonnegativity hypothesis is not used by either direction; it is recorded because the source
records it, and the same equivalence without it is
`AlgebraicGeometry.boundsFiberDegrees_iff_field_baseChange`.

A field-valued point `Spec k ⟶ Y` factors, up to the isomorphism identifying `k` with the
residue field of `Spec k` at its closed point, through the residue field of `Y` at the image
point. So the base change of `f` along it is a base change of the fibre of `f` at that point,
and `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback` transports the rank. No
comparison of direct images around the square is needed.

## References

* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A bound on the degrees of the fibres of `f`, phrased with the second projection of the
pullback along the inclusion of a residue field rather than with
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`. -/
theorem boundsFiberDegrees_iff_pullback_snd {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℤ) :
    BoundsFiberDegrees f n ↔
      ∀ y : Y, ∃ r : ℕ, (r : ℤ) ≤ n ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank
          (pullback.snd f (Y.fromSpecResidueField y)) r :=
  Iff.rfl

/-- **Stacks Project, Tag 03J5.** A nonnegative integer bounds the degrees of the fibres of a
scheme morphism exactly when every field-valued base change is finite locally free of rank at
most that integer.

The nonnegativity hypothesis is the source's and is not used, so it is named `_hn`; the form
without it is `AlgebraicGeometry.boundsFiberDegrees_iff_field_baseChange`, in
`StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange`. -/
@[stacks 03J5 "bounded_degree_iff_field_base_changes"]
theorem boundsFiberDegrees_iff_field_baseChange_of_nonneg
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℤ) (_hn : 0 ≤ n) :
    BoundsFiberDegrees f n ↔
      ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
        ∃ r : ℕ, (r : ℤ) ≤ n ∧
          Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r :=
  boundsFiberDegrees_iff_field_baseChange f n

end AlgebraicGeometry

end
