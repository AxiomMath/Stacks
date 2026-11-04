module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcTargetLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Finite type of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`. Being locally of finite type and being of
finite type are, for morphisms of algebraic spaces over `S`, local on the base for the fpqc
topology: each may be checked after base change to the members of an fpqc covering of the
target.

## Main results

* `AlgebraicGeometry.Space.locallyOfFiniteType_isLocalAtTarget_fpqc`: being locally of finite
  type is fpqc local on the base.
* `AlgebraicGeometry.Space.finiteType_isLocalAtTarget_fpqc`: being of finite type is fpqc local
  on the base.

## References

* [Stacks Project, Tag 02KX](https://stacks.math.columbia.edu/tag/02KX)
* [Stacks Project, Tag 02KY](https://stacks.math.columbia.edu/tag/02KY)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
* [Stacks Project, Tag 041S](https://stacks.math.columbia.edu/tag/041S)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041U](https://stacks.math.columbia.edu/tag/041U)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being locally of finite type is, for morphisms of algebraic spaces over `S`, local on the
base for the fpqc topology. -/
@[stacks 041S]
instance locallyOfFiniteType_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsLocallyOfFiniteType B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  isLocalAtTarget_fpqc_of_schemes B S hS
    (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    fun _ hg => have := hg; inferInstance

/-- Being of finite type is, for morphisms of algebraic spaces over `S`, local on the base for
the fpqc topology. -/
@[stacks 041U]
instance finiteType_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsFiniteType B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  MorphismProperty.IsLocalAtTarget.inf
    (P := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsLocallyOfFiniteType B S hS f.hom)
    (Q := quasiCompactProperty B S hS)

end AlgebraicGeometry.Space

end
