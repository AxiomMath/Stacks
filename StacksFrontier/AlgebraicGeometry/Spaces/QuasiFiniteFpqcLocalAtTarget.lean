module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcTargetLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Quasi-finiteness of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`.  Local quasi-finiteness and
quasi-finiteness of a morphism of algebraic spaces over `S` (**Stacks 03XJ**, parts (1) and (3))
are local on the base for the fpqc topology of **Stacks 03YH**: either may be checked after an
fpqc covering of the target.  This is **Stacks 0427**.

Local quasi-finiteness of a morphism of algebraic spaces is the chart condition of
**Stacks 03MJ** at the property `LocallyOfFiniteType ⊓ LocallyQuasiFinite` of morphisms of
schemes, so it is an instance of the transfer
`AlgebraicGeometry.Space.isLocalAtTarget_fpqc_of_schemes`: that property is étale local on the
source and target (**Stacks 04R3**), stable under composition and under base change, implied by
étaleness (**Stacks 03II**), and fpqc local on the base for schemes (**Stacks 02VM**).
Quasi-finiteness is local quasi-finiteness together with quasi-compactness, which is fpqc local
on the base by **Stacks 041L**, so the second half is the infimum of two properties local on
the base.

## Main results

* `AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtTarget_fpqc`: **Stacks 0427**, the
  locally quasi-finite case.
* `AlgebraicGeometry.Space.isQuasiFinite_isLocalAtTarget_fpqc`: **Stacks 0427**, the quasi-finite
  case.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtTarget_fppf` and
  `AlgebraicGeometry.Space.isQuasiFinite_isLocalAtTarget_fppf`: the same two at the fppf
  precoverage, which is the form the relative properties of Stacks 03YK consume.

## References

* [Stacks Project, Tag 0427](https://stacks.math.columbia.edu/tag/0427)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0427**, the locally quasi-finite case.  Local quasi-finiteness of a morphism of
algebraic spaces over `S` is local on the base for the fpqc topology of Stacks 03YH. -/
@[stacks 0427 "locally quasi-finite case"]
instance isLocallyQuasiFinite_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsLocallyQuasiFinite B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have := MorphismProperty.IsStableUnderComposition.inf
    (P := (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}))
    (Q := (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
  have := MorphismProperty.IsStableUnderBaseChange.inf
    (P := (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}))
    (Q := (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
  exact isLocalAtTarget_fpqc_of_schemes B S hS _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    fun g hg => have := hg; locallyQuasiFinite_of_etale g

/-- **Stacks 0427**, the quasi-finite case.  Quasi-finiteness of a morphism of algebraic spaces
over `S` is local on the base for the fpqc topology of Stacks 03YH.

Quasi-finiteness is local quasi-finiteness together with quasi-compactness, and quasi-compactness
is fpqc local on the base by Stacks 041L. -/
@[stacks 0427 "quasi-finite case", sga "4 IV 8.5.5" "more general"]
instance isQuasiFinite_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsQuasiFinite B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- **Stacks 0427**, the locally quasi-finite case, at the fppf precoverage: being locally
quasi-finite is local on the target for the fppf topology of algebraic spaces.  This is the form
in which the relative properties of Stacks 03YK ask for it, and it follows from the fpqc form
because every fppf covering family of algebraic spaces is an fpqc covering family. -/
instance isLocallyQuasiFinite_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsLocallyQuasiFinite B S hS f.hom)
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

/-- **Stacks 0427**, the quasi-finite case, at the fppf precoverage: being quasi-finite is local
on the target for the fppf topology of algebraic spaces. -/
instance isQuasiFinite_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsQuasiFinite B S hS f.hom)
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
