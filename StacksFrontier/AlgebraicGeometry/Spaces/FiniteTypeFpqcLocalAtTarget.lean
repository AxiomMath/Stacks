module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness

/-!
# Finite typeness of morphisms of algebraic spaces is fpqc local on the base (Stacks 041U)

Let `S` be a scheme contained in a big fppf site `B`. A morphism of algebraic spaces over `S` is
of finite type when it is locally of finite type and quasi-compact (**Stacks 03XF**, part (3)),
and each of those two conditions is local on the target for the fpqc topology of **Stacks 03YH**
— the first is **Stacks 041S** and the second is **Stacks 041L**. Their conjunction is therefore
local on the target too, which is **Stacks 041U**, and the fppf form that the relative properties
of Stacks 03YK ask for follows from it by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` over
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isFiniteType_isLocalAtTarget_fpqc`: **Stacks 041U**.
* `AlgebraicGeometry.Space.isFiniteType_isLocalAtTarget_fppf`: the same at the fppf precoverage.

## Implementation notes

Both declarations are one application each, and the whole content of the module is that the two
inputs Stacks 041U asks for are now available at the same precoverage. The combination step
itself is available, property-agnostically, as
`AlgebraicGeometry.Space.finiteTypeProperty_isLocalAtTarget`
(`StacksFrontier/AlgebraicGeometry/Spaces/SeparationMorphismProperties.lean`), which takes the two
atomic localities as hypotheses and so proves no tag on its own. Its quasi-compact input is the tagged `@[stacks 041L]`
`AlgebraicGeometry.Space.isQuasiCompact_isLocalAtTarget_fpqc`, and its locally-of-finite-type
input is the content of **Stacks 041S**, proved untagged as
`AlgebraicGeometry.Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothLocalityFiniteness.lean`, where it was proved for the
locally-of-finite-type case of Stacks 06FC. So nothing here is new mathematics; what is new is
that the two halves are put together, and the conjunction is the hypothesis that
descent of the finite-type condition along an fppf covering needs.

The fppf form is obtained from the fpqc form rather than by combining two fppf halves, exactly as
the fppf forms of Stacks 041L and Stacks 041T are, and it is left **untagged** for the same
reason: it is the same tag read at a coarser precoverage.

Tag 041U is in Descent on Spaces, **Chapter 74**, alongside
`AlgebraicGeometry.Space.isQuasiCompact_isLocalAtTarget_fpqc` (Tag 041L),
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtTarget_fpqc` (Tag 041T),
`AlgebraicGeometry.Space.isQuasiSeparated_isLocalAtTarget_fpqc` (Tag 041N) and
`AlgebraicGeometry.Space.isUnramified_isLocalAtTarget_fpqc` (Tag 042A), all in this directory.
It introduces no new notion: both conjuncts, the packaging abbreviation
`AlgebraicGeometry.Space.finiteTypeProperty` and the precoverage are defined elsewhere.

## References

* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
* [Stacks Project, Tag 041S](https://stacks.math.columbia.edu/tag/041S)
* [Stacks Project, Tag 041U](https://stacks.math.columbia.edu/tag/041U)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 041U.** Being of finite type, as a property of morphisms of algebraic spaces over
`S`, is local on the target for the fpqc topology.

Being of finite type is being locally of finite type and quasi-compact (**Stacks 03XF**, part
(3)); the first conjunct is local on the target for the fpqc topology by **Stacks 041S** and the
second by **Stacks 041L**, so their conjunction is. -/
@[stacks 041U]
instance isFiniteType_isLocalAtTarget_fpqc :
    (finiteTypeProperty B S hS).IsLocalAtTarget
      (Topology.fpqc.precoverage.{u, v} B S hS) :=
  finiteTypeProperty_isLocalAtTarget B S hS
    (isLocallyOfFiniteType_isLocalAtTarget_fpqc B S hS)
    (isQuasiCompact_isLocalAtTarget_fpqc B S hS)

/-- **Stacks 041U** at the fppf precoverage: being of finite type for morphisms of algebraic
spaces over `S` is local at the target for the fppf topology. This is the form in which Stacks
03YK's relative properties ask for it, and it follows from the fpqc form because every fppf
covering family of algebraic spaces is an fpqc covering family. -/
instance isFiniteType_isLocalAtTarget_fppf :
    (finiteTypeProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
