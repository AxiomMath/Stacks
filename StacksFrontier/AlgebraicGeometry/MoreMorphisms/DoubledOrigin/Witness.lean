module

public import Mathlib.Algebra.Field.ULift
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcCounterexample.NotFpqc
public import StacksFrontier.Deformation.ToposThickening.ObstructionIX.DoubledOriginDatum

/-!
# The doubled-origin source of the fpqc counterexample is inhabited

`AlgebraicGeometry.DoubledOriginSource` packages a ground field with a doubled-origin gluing
datum over it, and the fpqc counterexample is stated for an arbitrary such package. This file
exhibits one, over any field, from the canonical gluing datum
`AlgebraicGeometry.doubledOriginDatum`, and deduces that the type is nonempty. The statements of
the counterexample are therefore not vacuous: they assert something about the scheme obtained by
glueing two copies of `Spec k[t₀, t₁, …]` along the complement of the origin.

## Main definitions

* `AlgebraicGeometry.doubledOriginSource`: the doubled-origin source over a given field, built
  from the canonical gluing datum.

## Main results

* `AlgebraicGeometry.instNonemptyDoubledOriginSource`: `DoubledOriginSource` is nonempty.

## Implementation notes

The ground field of a `DoubledOriginSource` lives in `Type u`, so the field witnessing
nonemptiness is `ULift ℚ` rather than `ℚ`.

## References

* [Stacks Project, Tag 01KL](https://stacks.math.columbia.edu/tag/01KL)
* [Stacks Project, Tag 0H7E](https://stacks.math.columbia.edu/tag/0H7E)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

universe u

/-- Countably infinite-dimensional affine space over `k` with its origin doubled, as a
`DoubledOriginSource`: the ground field `k` together with the canonical doubled-origin gluing
datum over it. -/
public def doubledOriginSource (k : Type u) [Field k] : DoubledOriginSource.{u} where
  k := k
  gluing := doubledOriginDatum k

/-- The ground field of `doubledOriginSource k` is `k`. -/
@[simp]
public lemma doubledOriginSource_k (k : Type u) [Field k] : (doubledOriginSource k).k = k := rfl

/-- The gluing datum of `doubledOriginSource k` is the canonical one, `doubledOriginDatum k`. -/
@[simp]
public lemma doubledOriginSource_gluing (k : Type u) [Field k] :
    (doubledOriginSource k).gluing = doubledOriginDatum k := rfl

/-- There is a doubled-origin source: the one over `ULift ℚ`. -/
public instance instNonemptyDoubledOriginSource : Nonempty DoubledOriginSource.{u} :=
  ⟨doubledOriginSource (ULift.{u} ℚ)⟩

end AlgebraicGeometry

end
