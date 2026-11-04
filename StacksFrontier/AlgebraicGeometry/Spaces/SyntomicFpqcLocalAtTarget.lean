module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SyntomicLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcTargetLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic

/-!
# Syntomicity of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`.  Syntomicity of a morphism of algebraic
spaces over `S` (**Stacks 03Z7**, part (1)) is local on the base for the fpqc topology of
**Stacks 03YH**: it may be checked after an fpqc covering of the target.  This is
**Stacks 0428**.

Syntomicity of a morphism of algebraic spaces is the chart condition of **Stacks 03MJ** at
syntomicity of morphisms of schemes, so it is an instance of the transfer
`AlgebraicGeometry.Space.isLocalAtTarget_fpqc_of_schemes`: syntomicity of morphisms of schemes
is étale local on the source and target (**Stacks 04R3**), stable under composition
(**Stacks 01UI**) and under base change (**Stacks 01UK**), implied by étaleness, and fpqc local
on the base (**Stacks 02VK**).

## Main results

* `AlgebraicGeometry.Space.syntomic_isLocalAtTarget_fpqc`: **Stacks 0428**.

## References

* [Stacks Project, Tag 0428](https://stacks.math.columbia.edu/tag/0428)
* [Stacks Project, Tag 03Z7](https://stacks.math.columbia.edu/tag/03Z7)
* [Stacks Project, Tag 02VK](https://stacks.math.columbia.edu/tag/02VK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0428.**  Syntomicity of a morphism of algebraic spaces over `S` is local on the
base for the fpqc topology of Stacks 03YH. -/
@[stacks 0428]
instance syntomic_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsSyntomic B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  isLocalAtTarget_fpqc_of_schemes B S hS (@Syntomic.{u} : MorphismProperty Scheme.{u})
    syntomic_isEtaleLocalOnSourceAndTarget
    fun g hg => have := hg; syntomic_of_etale g

end AlgebraicGeometry.Space

end
