module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.TopologyTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType

/-!
# Étaleness and local quasi-finiteness are étale local on the source

Let `S` be a scheme contained in a big fppf site `B`. Étaleness of a morphism of algebraic
spaces over `S` (**Stacks 03FR**) and local quasi-finiteness (**Stacks 03XJ**, part (1)) are
local on the source for the étale topology of **Stacks 03YH**: each may be checked after an
étale covering of the source.

Both are instances of the transfer
`AlgebraicGeometry.Space.Topology.isLocalAtSource_of_schemes`: étaleness and the conjunction of
local finite type and local quasi-finiteness are étale local on the source and target
(**Stacks 04R3**) and local on the source for the étale topology of schemes (**Stacks 036W**
and **Stacks 03X4**), and the étale covering families of algebraic spaces compose and are
stable under base change (**Stacks 041F**).

## Main results

* `AlgebraicGeometry.Space.isEtale_isLocalAtSource_etale`: **Stacks 06F4**.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtSource_etale`: **Stacks 06F5**.

## Implementation notes

Unlike the other four properties for which Stacks 06ER is used, étaleness of a morphism of
algebraic spaces is *not* defined as the chart condition of Stacks 03MJ but as the stability
condition of Stacks 03FR, so the transfer does not apply to it directly. The two conditions
agree, by **Stacks 03FS**, condition (4), and **Stacks 03MJ**, the equivalence of conditions
(1) and (2): both say that the morphism fits into one commuting square of étale charts, with
the chart of the source surjective, whose morphism of schemes is étale. That comparison is
`AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`, Stacks 03XT, condition (7), which
is stated for a morphism of presheaves carrying the hypothesis that its source and its target
are algebraic spaces; here it is applied to the underlying morphism of an arrow of the category
of algebraic spaces over `S`, whose objects carry that hypothesis.

Local quasi-finiteness is the chart condition at the conjunction of local finite type and local
quasi-finiteness of morphisms of schemes, matching Stacks 03XJ, so the transfer applies to it
as stated.

The counterpart on schemes of the étale topology of algebraic spaces is
`AlgebraicGeometry.Scheme.etalePrecoverage`, which is how
`AlgebraicGeometry.Space.Topology.schemePrecoverage` evaluates at `Topology.etale`; the
scheme-side locality instances are therefore supplied through a `letI` at that spelling rather
than found by instance synthesis.

## References

* [Stacks Project, Tag 06F4](https://stacks.math.columbia.edu/tag/06F4)
* [Stacks Project, Tag 06F5](https://stacks.math.columbia.edu/tag/06F5)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06F4.** Étaleness of a morphism of algebraic spaces over `S` is local on the
source for the étale topology. -/
@[stacks 06F4]
instance isEtale_isLocalAtSource_etale :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsEtale B S hS f.hom)
      (Topology.etale.precoverage.{u, v} B S hS) := by
  let : MorphismProperty.IsLocalAtSource (@Etale.{u} : MorphismProperty Scheme.{u})
      (Topology.schemePrecoverage .etale) := etale_isLocalAtSource
  have hchart :
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsEtale B S hS f.hom) =
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS (@Etale.{u} : MorphismProperty Scheme.{u}) f.hom) := by
    funext F G f
    exact propext (isEtale_iff_holdsOnEveryEtaleChart B S hS F.property G.property f.hom)
  rw [hchart]
  exact Topology.isLocalAtSource_of_schemes B S hS .etale
    (Topology.hasCoveringStability_etale B S hS) _ etale_isEtaleLocalOnSourceAndTarget

/-- **Stacks 06F5.** Local quasi-finiteness of a morphism of algebraic spaces over `S` is local
on the source for the étale topology. -/
@[stacks 06F5]
instance isLocallyQuasiFinite_isLocalAtSource_etale :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsLocallyQuasiFinite B S hS f.hom)
      (Topology.etale.precoverage.{u, v} B S hS) := by
  let : MorphismProperty.IsLocalAtSource
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (Topology.schemePrecoverage .etale) := locallyQuasiFinite_isLocalAtSource_etale
  exact Topology.isLocalAtSource_of_schemes B S hS .etale
    (Topology.hasCoveringStability_etale B S hS) _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget

end AlgebraicGeometry.Space

end
