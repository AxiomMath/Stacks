module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.InternalHomQuasicoherentChartLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal Hom of two coherent modules on an algebraic space is quasi-coherent

Let `F` be an algebraic space over a scheme `S` and let `M`, `N` be coherent `𝒪_F`-modules.  Then
`𝓗om_{𝒪_F}(M, N)` is a quasi-coherent `𝒪_F`-module.

This is Stacks 03M1(6) with its hypotheses supplied from coherence alone.  That clause,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom`, asks for quasi-coherence
of both modules and finite presentation of the source; coherence delivers all three, and on any
ringed site, with no Noetherian hypothesis anywhere:

* quasi-coherence is a parent of `AlgebraicGeometry.Space.IsCoherent`, which is declared as a
  class extending `CategoryTheory.SheafOfModules.IsQuasicoherentOnSite` and
  `CategoryTheory.SheafOfModules.IsCoherentOnSite`, so it is a projection; and
* finite presentation is
  `CategoryTheory.SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite`, which
  constrains neither the universe of the objects of the site nor that of the sections.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_isCoherent` — the
  internal Hom of two coherent `𝒪_F`-modules is quasi-coherent.

## Implementation notes

The module universes are those of Stacks 03M1(6): `M` and `N` are `Modules.{u, u}`, while the
conclusion is about `AlgebraicGeometry.Space.smallEtaleInternalHom B S hS F hF M N`, which is a
`Modules.{u, u + 1}` — a section of the internal Hom over an étale chart `U` is a morphism of
modules on the slice of the small étale site at `U`, and those objects form a `Type (u + 1)`.
So the statement already crosses the module universes that the two arguments live in, and needs
no `ULift` to do it.

That is worth recording because the neighbouring route does need one.
`CategoryTheory.SheafOfModules.isFinitePresentation_of_isCoherentOnSite` concludes the
Mathlib predicate `IsFinitePresentation` rather than `IsFinitePresentationOnSite` and carries a
`UnivLE` hypothesis between the universe of the objects of the site and that of the sections;
for the small étale ringed site, which is a `RingedSite.{u + 1, u, u}`, that instantiates to
`UnivLE.{u + 1, u}` and is false.  The lemma used here is the one with no such hypothesis.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The internal Hom of two coherent `𝒪_F`-modules is quasi-coherent.**  Stacks 03M1(6) asks
for quasi-coherence of the two modules and finite presentation of the source; coherence supplies
all three, so no hypothesis beyond coherence is needed, and in particular neither Noetherianity
of `F` nor coherence of the internal Hom itself.

The clause is `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom`.  Its first
two hypotheses are parent projections of `AlgebraicGeometry.Space.IsCoherent` and the third is
`CategoryTheory.SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite`, which is not an
instance — two routes from coherence to quasi-coherence would otherwise exist — and so is
applied by name. -/
@[sga "3 III 0.6" "special case"]
theorem isQuasicoherentOnSite_smallEtaleInternalHom_of_isCoherent
    (M N : Modules.{u, u} B S hS F hF)
    (hM : IsCoherent B S hS F hF M) (hN : IsCoherent B S hS F hF N) :
    (smallEtaleInternalHom B S hS F hF M N).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_smallEtaleInternalHom B S hS F hF M N
    hM.toIsQuasicoherentOnSite hN.toIsQuasicoherentOnSite
    (SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite M hM.toIsCoherentOnSite)

end AlgebraicGeometry.Space

end
