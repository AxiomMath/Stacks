module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange

/-!
# Closed immersions of algebraic spaces are fppf local on the base

Being a closed immersion of Stacks 02YU, part (3) — a representable morphism of algebraic spaces
over `S` every represented base change of which is a closed immersion of schemes — is local on
the base for the fppf topology of Stacks 03YH.

This is **Stacks 0420** read at the fppf precoverage. The source states that tag for the coarser
fpqc topology, and the library proves it there as
`AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fpqc`; every fppf covering family of
algebraic spaces is an fpqc covering family, **Stacks 0DFQ**, so the fpqc statement restricts to
the fppf one.

The fppf precoverage is the one at which the relative properties of Stacks 03YK are introduced,
so this is the form in which `AlgebraicGeometry.Stack.IsClosedImmersion` — and through it the
thickenings of Stacks 0BPP — ask for target locality of closed immersions of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fppf`: **Stacks 0420** at the fppf
  precoverage.

## Implementation notes

Unlike its siblings `AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf` (Stacks 0429) and
`AlgebraicGeometry.Space.surjective_isLocalAtTarget_fppf` (Stacks 041Q), the restriction cannot
be written as a bare `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`: the fpqc form is a
plain theorem rather than an instance, because the universe of the index type of a covering
family is a free parameter of its statement. It is therefore introduced as a local instance
first, at the packaged spelling `AlgebraicGeometry.Space.closedImmersionProperty` and at the
same index universe as the conclusion.

The result itself is an instance, as the fppf forms for smoothness, surjectivity, finite type
and open immersions are, so that the consumers of the relative properties of Stacks 03YK need
not carry it as a hypothesis.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0420** at the fppf precoverage: being a closed immersion is local on the base for
the fppf topology for morphisms of algebraic spaces over `S`, so such a morphism is a closed
immersion exactly when its base change to every member of some fppf covering of its target is
one.

The fpqc form is `AlgebraicGeometry.Space.isClosedImmersion_isLocalAtTarget_fpqc`, and the two
are compared by `AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` (Stacks 0DFQ). This
is the form in which the relative properties of Stacks 03YK ask for it. -/
@[stacks 0420 "the fppf precoverage"]
instance isClosedImmersion_isLocalAtTarget_fppf :
    (closedImmersionProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  have _hfpqc : (closedImmersionProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
    isClosedImmersion_isLocalAtTarget_fpqc B S hS
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
