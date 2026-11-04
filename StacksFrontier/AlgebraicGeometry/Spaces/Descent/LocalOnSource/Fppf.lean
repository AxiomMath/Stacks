module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.TopologyTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSourceLocalityFiniteType

/-!
# The finiteness properties of morphisms of algebraic spaces are fppf local on the source

Let `S` be a scheme contained in a big fppf site `B`. Being locally of finite presentation
(**Stacks 03XP**, part (1)) and being locally of finite type (**Stacks 03XF**, part (1)) are
local on the source for the fppf topology of **Stacks 03YH** on the algebraic spaces over `S`.

Local finite presentation is proved here, as an instance of the transfer
`AlgebraicGeometry.Space.Topology.isLocalAtSource_of_schemes`: the property of morphisms
of schemes is étale local on the source and target (**Stacks 04R3**) and local on the source
for the fppf topology of schemes (**Stacks 036N**), and the fppf covering families of algebraic
spaces compose and are stable under base change (**Stacks 03Y9**). Local finite type is the same
transfer applied to **Stacks 036O**, and is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/FppfSourceLocalityFiniteType.lean`, which this module
imports and re-exports.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtSource_fppf`:
  **Stacks 06EV**.

## Implementation notes

Both are registered as instances, as `AlgebraicGeometry.Space.isFlat_isLocalAtSource_fpqc` is;
this is the form in which `CategoryTheory.MorphismProperty.IsLocalAtSource`'s API — in
particular the precomposition statement `AlgebraicGeometry.Space.comp_of_isMember` of
**Stacks 06EQ** — consumes them.

The counterpart on schemes of the fppf topology of algebraic spaces is
`AlgebraicGeometry.Scheme.fppfPrecoverage`, which is how
`AlgebraicGeometry.Space.Topology.schemePrecoverage` evaluates at `Topology.fppf`; the
scheme-side locality instance is therefore supplied through a `letI` at that spelling rather
than found by instance synthesis.

## References

* [Stacks Project, Tag 06EV](https://stacks.math.columbia.edu/tag/06EV)
* [Stacks Project, Tag 06EW](https://stacks.math.columbia.edu/tag/06EW)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06EV.** Being locally of finite presentation, for a morphism of algebraic spaces
over `S`, is local on the source for the fppf topology. -/
@[stacks 06EV]
instance isLocallyOfFinitePresentation_isLocalAtSource_fppf :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyOfFinitePresentation B S hS f.hom)
      (Topology.fppf.precoverage.{u, v} B S hS) := by
  let : MorphismProperty.IsLocalAtSource
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (Topology.schemePrecoverage .fppf) := locallyOfFinitePresentation_isLocalAtSource
  exact Topology.isLocalAtSource_of_schemes B S hS .fppf
    (Topology.hasCoveringStability_fppf B S hS) _
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget

end AlgebraicGeometry.Space

end
