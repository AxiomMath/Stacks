module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs

/-!
# The two spellings of perfectness on a ringed space agree

Perfectness of a complex of `𝒪_X`-modules on a ringed space (Stacks 08CM) has two spellings,
`AlgebraicGeometry.RingedSpace.IsPerfect` and `Stacks.Cohomology.PerfectComplexes.IsPerfect`. Both
ask for a representative which, on the members of an open covering, receives a quasi-isomorphism
from a strictly perfect complex, along the same restriction functors, so the two predicates are
definitionally equal.

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfectComplex_iff_perfectComplexes_isPerfectComplex`: the two
  predicates on cochain complexes of `𝒪_X`-modules agree.
* `AlgebraicGeometry.RingedSpace.isPerfect_iff_perfectComplexes_isPerfect`: the two predicates on
  objects of `D(𝒪_X)` agree.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public section

open CategoryTheory

universe u d

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-- The two spellings of a perfect complex of `𝒪_X`-modules agree. -/
theorem isPerfectComplex_iff_perfectComplexes_isPerfectComplex
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) :
    IsPerfectComplex E ↔ Stacks.Cohomology.PerfectComplexes.IsPerfectComplex E :=
  Iff.rfl

/-- The two spellings of a perfect object of `D(𝒪_X)` agree. -/
theorem isPerfect_iff_perfectComplexes_isPerfect
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) :
    IsPerfect K ↔ Stacks.Cohomology.PerfectComplexes.IsPerfect K :=
  Iff.rfl

end AlgebraicGeometry.RingedSpace
