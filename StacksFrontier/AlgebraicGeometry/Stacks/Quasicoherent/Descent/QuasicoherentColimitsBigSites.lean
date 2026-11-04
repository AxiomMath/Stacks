module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEquivalencePresentationReduction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseMemberLocalStep
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullOnFree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.MemberLocalStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSmallEtaleBigSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.BaseAssociatedModuleColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTransfer

/-!
# Stacks 0GNC (1), (2), (3) on the big `τ`-site of a scheme, at every `τ`

Clauses (1), (2) and (3) of Descent, Lemma 0GNC say that the quasi-coherent `𝒪`-modules on the
big site `(Sch/S)_τ` of a scheme `S` are closed under direct sums, under colimits and under
cokernels, for each `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.  The source proves all
three by one transfer: write each module as an `𝓕^a`, form the colimit in `QCoh(𝒪_S)`, and
carry it back with Lemma 06VE.

This file performs that transfer at **every** `τ`, with no hypothesis.  Its one topology-dependent
input used to be carried as the predicate
`AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule τ` — the essential
surjectivity half of Descent, Proposition 03DX (1) at `(Sch/S)_τ` — and is now the theorem
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`, which obtains it
at a coarser `τ` from the fact that a quasi-coherent module on `(Sch/S)_τ` is a sheaf for the
localized *fppf* topology, global presentations being fppf sheaves.  Every other input of the
transfer is already proved `τ`-parametrically and is supplied here with no hypothesis:

* `AlgebraicGeometry.BigFppfOver.full_baseAssociatedModuleQcoh` and
  `…faithful_baseAssociatedModuleQcoh` — Stacks 0GN7, i.e. clause (1) of Stacks 06VE, at every
  `τ`;
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_baseAssociatedModuleQcoh` — clause (3)
  of Stacks 06VE at every `τ`, `𝓕 ↦ 𝓕^a` being a left adjoint there;
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`
  — Stacks 03DV (1) at every `τ`;
* `AlgebraicGeometry.BigFppfOver.hasColimitsOfShape_isQuasicoherent` — the colimits in
  `QCoh(𝒪_S)`, which is Schemes, Section 01LA and sees no site.

So clauses (1), (2) and (3) hold at all five topologies, and that is what the three statements
below assert.  One neighbouring file restates them at a narrower shape and keeps its own
registration:
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsFppfSite` at
`τ = fppf` for the fppf structure sheaf `structureSheaf B S hS` itself rather than for
`FibredSite.baseRingStructureSheaf _ .fppf`; a tag registered on several declarations is
expected.  The index universe of the site needs no separate registration: clause (2) below is
stated for an index category `K : Type uK` at an arbitrary universe `uK`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_baseIsQuasicoherentOnSite`:
  **Stacks 0GNC (2)** at every `τ` — quasi-coherence of `𝒪`-modules on `(Sch/S)_τ` is closed
  under colimits of shape `K`.
* `AlgebraicGeometry.BigFppfOver`
  `.isClosedUnderColimitsOfShape_discrete_baseIsQuasicoherentOnSite`: **Stacks 0GNC (1)** at
  every `τ` — a direct sum of quasi-coherent modules is quasi-coherent.
* `AlgebraicGeometry.BigFppfOver`
  `.isClosedUnderColimitsOfShape_walkingParallelPair_baseIsQuasicoherentOnSite`:
  **Stacks 0GNC (3)** at every `τ` — the cokernel of a morphism of quasi-coherent modules is
  quasi-coherent.

## Implementation notes

The index shapes are `K : Type u` with `Category.{u} K`, `u` being the universe of the
morphisms of the site and of its structure sheaf; this is the convention of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTransfer`, whose
implementation notes explain why a bare `HasColimits` would say something else.  The two
colimit-existence instances the transfer consumes — colimits of shape `K` in `ModuleCat.{u} R`
and in the `𝒪_S`-modules of the small Zariski site — are carried as instance arguments on
clause (2), which is stated at an arbitrary index universe `uK`; clauses (1) and (3) instantiate
`K` at shapes where instance search finds them.

## What is not proved here

Clause (4) of Stacks 0GNC — the middle term of a short exact sequence — is not here.  It is
proved at every `τ` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExactAll.lean`, on
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all`, by the route the source
takes: part (10) of Stacks 06VE, whose essential-image form on the big sites is
`AlgebraicGeometry.BigFppfOver.essImage_X₂_of_shortExact_big`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseExtensionEssImage.lean`).  Clauses
(5) and (6) are in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteProperties.lean`.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uK u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GNC (2) on the big `τ`-site of `S`, at every `τ` and with no hypothesis**:
quasi-coherence of `𝒪`-modules on `(Sch/S)_τ` is closed under colimits of shape `K`, for `K` at
an arbitrary universe.

This is the transfer the source performs with Lemma 06VE, carried out at every `τ`: the
quasi-coherent modules of `(Sch/S)_τ` are the essential image of `𝓕 ↦ 𝓕^a`, which is fully
faithful (Stacks 0GN7) and preserves colimits (Stacks 06VE (3)) out of `QCoh(𝒪_S)`, where the
colimits exist and are quasi-coherent; so they are closed under those colimits.  That the
essential image is *all* the quasi-coherent modules is the essential-surjectivity half of
Descent, Proposition 03DX (1) at `(Sch/S)_τ`, and is
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`. -/
@[stacks 0GNC "part (2), big site at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, \
unconditionally, for an index category K at an arbitrary universe"]
public theorem isClosedUnderColimitsOfShape_baseIsQuasicoherentOnSite (τ : SiteKind)
    (K : Type uK) [Category.{uK} K]
    [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
    [HasColimitsOfShape K (SheafOfModules.{u} S.ringCatSheaf)] :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.baseRingStructureSheaf B S hS τ)).IsClosedUnderColimitsOfShape K := by
  have := full_baseAssociatedModuleQcoh B S hS τ
  have := faithful_baseAssociatedModuleQcoh B S hS τ
  have := hasColimitsOfShape_isQuasicoherent S K
  have := preservesColimitsOfShape_baseAssociatedModuleQcoh B S hS τ K
  exact SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite
    (baseAssociatedModuleQcoh B S hS τ) K
    (fun M => isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B S hS τ
      M.obj M.property)
    (baseQuasicoherentIsEssImageAssociatedModule B S hS τ)

/-- **Stacks 0GNC (1) on the big `τ`-site of `S`, at every `τ` and with no hypothesis**: a
direct sum of quasi-coherent `𝒪`-modules on `(Sch/S)_τ` is quasi-coherent.  A direct sum is a
colimit over a discrete index category, which is how the source argues it. -/
@[stacks 0GNC "part (1), big site at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, \
unconditionally"]
public theorem isClosedUnderColimitsOfShape_discrete_baseIsQuasicoherentOnSite (τ : SiteKind)
    (I : Type u) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.baseRingStructureSheaf B S hS τ)).IsClosedUnderColimitsOfShape
      (Discrete I) :=
  isClosedUnderColimitsOfShape_baseIsQuasicoherentOnSite B S hS τ (Discrete I)

/-- **Stacks 0GNC (3) on the big `τ`-site of `S`, at every `τ` and with no hypothesis**: the
cokernel of a morphism of quasi-coherent `𝒪`-modules on `(Sch/S)_τ` is quasi-coherent.  A
cokernel is a colimit over `CategoryTheory.Limits.WalkingParallelPair`, and the source obtains
clause (3) from clause (2) in exactly this way. -/
@[stacks 0GNC "part (3), big site at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, \
unconditionally"]
public theorem isClosedUnderColimitsOfShape_walkingParallelPair_baseIsQuasicoherentOnSite
    (τ : SiteKind) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.baseRingStructureSheaf B S hS τ)).IsClosedUnderColimitsOfShape
      WalkingParallelPair :=
  isClosedUnderColimitsOfShape_baseIsQuasicoherentOnSite B S hS τ WalkingParallelPair

end BigFppfOver

end AlgebraicGeometry

end
