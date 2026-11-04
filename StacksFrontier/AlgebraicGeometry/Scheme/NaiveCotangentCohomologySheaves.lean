module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex

/-!
# The cohomology sheaves of the naive cotangent complex of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y` the naive cotangent complex `NL_{X/Y}` is a two-term
complex of sheaves of `𝒪_X`-modules concentrated in degrees `-1` and `0`. This file records the
consequence for its cohomology sheaves: `H^i(NL_{X/Y})` vanishes for every `i` other than `-1`
and `0`.

## Main results

* `AlgebraicGeometry.Scheme.isZero_homology_naiveCotangentComplex`: the cohomology sheaves of
  `NL_{X/Y}` are zero outside degrees `-1` and `0`.

## Implementation notes

Only the vanishing clause of [Stacks Project, Tag 0D0J] is proved here, and the attribute below
is scoped accordingly. The tag's other two clauses are elsewhere: `H^0(NL_{X/Y})` is the sheaf
of relative differentials `Ω_{X/Y}` by
`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`, and the cohomology sheaves are
quasi-coherent in every degree by
`AlgebraicGeometry.Scheme.isQuasicoherent_homology_naiveCotangentComplex`, which consumes the
vanishing proved here for the degrees other than `-1` and `0`.

## References

* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J)
* [Stacks Project, Tag 0D0H](https://stacks.math.columbia.edu/tag/0D0H), the naive cotangent
  complex of a morphism of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks 0D0J, vanishing clause.** The cohomology sheaves of the naive cotangent complex
`NL_{X/Y}` of a morphism of schemes vanish outside degrees `-1` and `0`: the complex has no
terms in those degrees, so it is exact there. -/
@[stacks 0D0J "the vanishing outside degrees -1 and 0 only; quasi-coherence and H^0 = Omega are
proved separately"]
theorem isZero_homology_naiveCotangentComplex (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((naiveCotangentComplex f).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (naiveCotangentComplex_isZero_X f i hneg hzero)).isZero_homology

end AlgebraicGeometry.Scheme

end
