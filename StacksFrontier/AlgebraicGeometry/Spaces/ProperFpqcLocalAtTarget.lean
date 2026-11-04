module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget

/-!
# Properness of morphisms of algebraic spaces is fpqc local on the base

A morphism of algebraic spaces over `S` is *proper* when it is separated, of finite type and
universally closed (Stacks 03ZM). This file proves that properness is local on the base for the
fpqc topology of Stacks 03YH, which is **Stacks 0422**, and transports it to the fppf topology.

Properness is the conjunction of its three conjuncts by definition, and each conjunct is local
on the base for the fpqc topology: separatedness by **Stacks 0421**, being of finite type by
**Stacks 041U** and universal closedness by **Stacks 041O**. A conjunction of properties local
at the target is local at the target, so those three statements assemble into this one.

## Main results

* `AlgebraicGeometry.Space.proper_isLocalAtTarget_fpqc`: **Stacks 0422**, properness of
  morphisms of algebraic spaces over `S` is local on the base for the fpqc topology.
* `AlgebraicGeometry.Space.proper_isLocalAtTarget_fppf`: the same statement at the fppf
  precoverage.

## Implementation notes

The conjunction is discharged by `AlgebraicGeometry.Space.properProperty_isLocalAtTarget`, which
reads properness as an infimum of morphism properties and appeals to
`CategoryTheory.MorphismProperty.IsLocalAtTarget.inf`; it takes the locality of the three
conjuncts as hypotheses, and this file supplies them.

Universal closedness has one packaged spelling,
`AlgebraicGeometry.Space.universallyClosedProperty`, at which both the locality instance and the
conjunctive decomposition of properness are stated.

## References

* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 041O](https://stacks.math.columbia.edu/tag/041O)
* [Stacks Project, Tag 041U](https://stacks.math.columbia.edu/tag/041U)
* [Stacks Project, Tag 0421](https://stacks.math.columbia.edu/tag/0421)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0422.** Properness of morphisms of algebraic spaces over `S` is local on the base
for the fpqc topology: a morphism is proper exactly when its base change to every member of some
fpqc covering family of its target is proper.

Being proper is being separated, of finite type and universally closed (**Stacks 03ZM**); the
three conjuncts are local on the base for the fpqc topology by **Stacks 0421**, **Stacks 041U**
and **Stacks 041O**, so their conjunction is. -/
@[stacks 0422, sga "1 VIII 4.8" "more general", sga "4 IV 8.5.5" "more general"]
instance proper_isLocalAtTarget_fpqc :
    (properProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  properProperty_isLocalAtTarget B S hS
    (separated_isLocalAtTarget_fpqc B S hS)
    (isFiniteType_isLocalAtTarget_fpqc B S hS)
    (universallyClosed_isLocalAtTarget_fpqc B S hS)

/-- **Stacks 0422** at the fppf precoverage: properness of morphisms of algebraic spaces over
`S` is local on the base for the fppf topology. This is the form in which Stacks 03YK's relative
properties ask for it, and it follows from the fpqc form because every fppf covering family of
algebraic spaces is an fpqc covering family. -/
@[sga "1 VIII 4.8" "partial", sga "4 IV 8.5.5" "special case"]
instance proper_isLocalAtTarget_fppf :
    (properProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
