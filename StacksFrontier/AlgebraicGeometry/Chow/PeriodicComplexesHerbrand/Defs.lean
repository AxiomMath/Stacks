module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Length
public import StacksCore.Tactic.StacksAttribute

/-!
# Multiplicity of a two-periodic complex

The multiplicity of a two-periodic complex whose cohomology modules have finite length is the
length of its degree-zero cohomology minus the length of its degree-one cohomology. For a
two-periodic complex having the same module in both degrees, this is also called the additive
Herbrand quotient.

## Main definitions

* `AlgebraicGeometry.periodicLength` is the multiplicity of a two-periodic complex of modules.

## Implementation notes

A two-periodic complex is represented by a `CochainComplex` indexed by `ZMod 2`. Module length
takes values in `ℕ∞`; applying `ENat.toNat` gives its ordinary natural-number value whenever the
cohomology module has finite length. This totalized definition lets finiteness remain a hypothesis
of results about the multiplicity rather than an argument to the multiplicity itself.

## References

* [Stacks Project, Tag 02PH](https://stacks.math.columbia.edu/tag/02PH)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- The multiplicity (or periodic length) of a two-periodic complex of modules. For a complex
whose two objects agree, this is also known as its additive Herbrand quotient. -/
@[stacks 02PH] public noncomputable abbrev periodicLength {R : Type u} [Ring R]
    (C : CochainComplex (ModuleCat.{v} R) (ZMod 2)) : ℤ :=
  ((Module.length R (C.homology (0 : ZMod 2))).toNat : ℤ) -
    ((Module.length R (C.homology (1 : ZMod 2))).toNat : ℤ)

end AlgebraicGeometry
