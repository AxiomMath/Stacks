module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Fppf, smooth, étale and Zariski coverings are fpqc

Every fppf covering family is an fpqc covering family, so the same holds for the smooth,
étale and Zariski covering families, which are fppf.

## Main results

* `AlgebraicGeometry.Scheme.smoothPrecoverage_le_fpqcPrecoverage`: every smooth covering
  family is an fpqc covering family.
* `AlgebraicGeometry.Scheme.etalePrecoverage_le_fpqcPrecoverage`: every étale covering
  family is an fpqc covering family.

## Implementation notes

Each comparison is obtained by composing the corresponding inclusion into the fppf
precoverage with `AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`.  The fppf
and Zariski inclusions are already available and are recorded here for the census.

Mathlib's `AlgebraicGeometry.Scheme.fpqcPrecoverage` is declared together with its
`Precoverage.HasIsos`, `Precoverage.IsStableUnderBaseChange` and
`Precoverage.IsStableUnderComposition` instances.  Those three properties are the axioms of a
site for a collection of coverings, so that declaration carries [Stacks, Tag 03NZ].

## References

* [Stacks Project, Tag 022C](https://stacks.math.columbia.edu/tag/022C)
* [Stacks Project, Tag 03NZ](https://stacks.math.columbia.edu/tag/03NZ)
* [Stacks Project, Tag 03PH](https://stacks.math.columbia.edu/tag/03PH)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

add_to_stacks 03NZ "the collection of fpqc coverings, whose site axioms are its \
Precoverage.HasIsos, Precoverage.IsStableUnderBaseChange and \
Precoverage.IsStableUnderComposition instances" Scheme.fpqcPrecoverage

add_to_stacks 022C "fppf coverings" Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-- **Stacks 022C.** Every smooth covering family is an fpqc covering family. -/
@[stacks 022C "smooth coverings"]
public theorem smoothPrecoverage_le_fpqcPrecoverage :
    Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) ≤
      Scheme.fpqcPrecoverage :=
  Scheme.smoothPrecoverage_le_fppfPrecoverage.trans Scheme.fppfPrecoverage_le_fpqcPrecoverage

/-- **Stacks 022C, 03PH.** Every étale covering family is an fpqc covering family. -/
@[stacks 022C "étale coverings"]
public theorem etalePrecoverage_le_fpqcPrecoverage :
    Scheme.etalePrecoverage ≤ Scheme.fpqcPrecoverage :=
  Scheme.etalePrecoverage_le_fppfPrecoverage.trans Scheme.fppfPrecoverage_le_fpqcPrecoverage

attribute [stacks 03PH] etalePrecoverage_le_fpqcPrecoverage

add_to_stacks 022C "Zariski coverings" Scheme.zariskiPrecoverage_le_fpqcPrecoverage

end AlgebraicGeometry.Scheme
