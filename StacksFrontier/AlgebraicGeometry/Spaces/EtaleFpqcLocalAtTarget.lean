module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Unramified
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcTargetLocalityTransfer

/-!
# Étaleness of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`.  Étaleness of a morphism of algebraic
spaces over `S` (**Stacks 03FR**) is local on the base for the fpqc topology of **Stacks 03YH**:
it may be checked after an fpqc covering of the target.  This is **Stacks 042B**.

## Main results

* `AlgebraicGeometry.Space.isEtale_isLocalAtTarget_fpqc`: **Stacks 042B**.

## Implementation notes

Étaleness of a morphism of algebraic spaces is not defined as the chart condition of
**Stacks 03MJ** but as the stability condition of Stacks 03FR, so the transfer
`AlgebraicGeometry.Space.isLocalAtTarget_fpqc_of_schemes` does not apply to it on the nose.  The
two conditions agree by **Stacks 03XT**, condition (7), which is
`AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`, and rewriting with that comparison
turns the statement into the chart condition at étaleness of morphisms of schemes.  The transfer
then applies: étaleness of morphisms of schemes is étale local on the source and target
(**Stacks 04R3**), stable under composition (**Stacks 02GN**) and under base change
(**Stacks 02GO**), trivially implied by étaleness, and fpqc local on the base (**Stacks 02VN**).

## References

* [Stacks Project, Tag 042B](https://stacks.math.columbia.edu/tag/042B)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
* [Stacks Project, Tag 02VN](https://stacks.math.columbia.edu/tag/02VN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 042B.**  Étaleness of a morphism of algebraic spaces over `S` is local on the base
for the fpqc topology of Stacks 03YH. -/
@[stacks 042B]
instance isEtale_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsEtale B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have hchart :
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsEtale B S hS f.hom) =
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        HoldsOnEveryEtaleChart B S hS (@Etale.{u} : MorphismProperty Scheme.{u}) f.hom) := by
    funext X Y f
    exact propext (isEtale_iff_holdsOnEveryEtaleChart B S hS X.property Y.property f.hom)
  rw [hchart]
  have : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact isLocalAtTarget_fpqc_of_schemes B S hS (@Etale.{u} : MorphismProperty Scheme.{u})
    etale_isEtaleLocalOnSourceAndTarget fun _ hg => hg

end AlgebraicGeometry.Space

end
