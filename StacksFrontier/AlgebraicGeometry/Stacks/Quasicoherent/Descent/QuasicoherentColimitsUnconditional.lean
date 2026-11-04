module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithfulUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence

/-!
# Colimits of quasi-coherent modules on the big fppf site, over essential surjectivity alone

`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize` proves
Stacks 0GNC (1), (2), (3) and the existence half of Stacks 0GNE (1) for `τ = fppf` over four
inputs: fullness and faithfulness of `𝓕 ↦ 𝓕^a`, the fact that `𝓕^a` is quasi-coherent on the
site (Stacks 03DV), and essential surjectivity of `𝓕 ↦ 𝓕^a` onto the quasi-coherent modules of
the site (the surjectivity half of Stacks 03DX (1)).  Three of the four are now theorems:

* fullness and faithfulness are
  `AlgebraicGeometry.BigFppfOver.full_associatedModuleQcoh'` and
  `AlgebraicGeometry.BigFppfOver.faithful_associatedModuleQcoh'`, instances of
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithfulUnconditional`;
* `AlgebraicGeometry.BigFppfOver.AssociatedModuleIsQuasicoherent` is
  `AlgebraicGeometry.BigFppfOver.associatedModuleIsQuasicoherent`, proved in
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence` by pushing a
  Zariski presentation of `𝓕` forward along the image of the same covering.

This file restates each result of that file with those three discharged, leaving
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` as the single remaining
hypothesis.

## Main results

Each is the correspondingly named result of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize` over
`hsurj` alone:

* `AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_isQuasicoherentOnSite'`:
  **Stacks 0GNC (2)** for `τ = fppf`.
* `AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_discrete_isQuasicoherentOnSite'`
  and
  `AlgebraicGeometry.BigFppfOver`
  `.isClosedUnderColimitsOfShape_walkingParallelPair_isQuasicoherentOnSite'`:
  **Stacks 0GNC (1)** and **(3)** for `τ = fppf`.
* `AlgebraicGeometry.BigFppfOver.closedUnderColimitsOfSize_isQuasicoherentOnSite'`: the same
  over every shape `K : Type u`.
* `AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite'`: the existence half of
  **Stacks 0GNE (1)**.
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_quasicoherentOnSite_ι'`: the half of
  **Stacks 0GNE (1)** that compares those colimits with the ones taken in
  `Mod((Sch/S)_fppf, 𝒪)`.

## Implementation notes

Nothing here carries a `stacks` attribute.  There are two separate reasons, and they are worth
keeping apart.

*For Stacks 0GNC* every clause below is still an implication, over
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`: the source's proof
writes each quasi-coherent module on the site as a `𝓖^a`, which is the surjectivity half of
Stacks 03DX (1) and goes through the effectivity of fpqc descent, Stacks 023T.  A hypothesis is
part of a citation, so the clauses may not be tagged *here*.  That hypothesis is now a theorem,
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementRestrFun.lean`
`:702`), and the clauses below are restated with it discharged, and tagged, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsFppfSite`.
Over and above that, Stacks 0GNC quantifies over
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}` while these are the big fppf site alone, and
clauses (4), (5), (6) of the source — the two-out-of-three property for a short exact sequence,
tensor products, and internal hom out of a finite locally free module — are not here at all;
(5) and (6) are proved at every `τ` in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteProperties`, and (4)
is not in the library.

*For Stacks 0GNE (1)* there is in addition a second reason, and it is not the `τ`-quantifier.
The clause is **not** `τ`-quantified: it is a statement about `QCoh((Sch/S)_fppf, 𝒪)` which
asserts that its colimits agree with the colimits computed in *three* ambient categories,
`Mod((Sch/S)_Zar, 𝒪)`, `Mod((Sch/S)_étale, 𝒪)` and `Mod((Sch/S)_fppf, 𝒪)`.  Only the third is
below.  The first two are colimits in categories of sheaves for a coarser topology, where
sheafification is a different functor, so their agreement is not a formal consequence of
anything here; it needs the comparison of the big-site module categories across topologies.
**That comparison is now in the library and all three halves of the clause are proved**, for an
arbitrary diagram and with no hypothesis, in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteColimitAgreement.lean`,
which is where the 0GNE (1) attributes sit:
`AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite_fppf`,
`…preservesColimitsOfSize_quasicoherentOnSite_ι_fppf` and
`…preservesColimitsOfSize_quasicoherentOnSite_ι_comp_restrictTopology`.  The two declarations
below are those statements over `hsurj`, and remain untagged for that reason alone.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uK u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GNC (2)** for `τ = fppf`, over essential surjectivity of `𝓕 ↦ 𝓕^a` alone:
quasi-coherence of modules on the big fppf site of `S` is closed under colimits of shape `K`.

`AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_isQuasicoherentOnSite` with its
full-faithfulness instances and its Stacks 03DV hypothesis discharged. -/
public theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite'
    (K : Type uK) [Category.{uK} K]
    [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
    [HasColimitsOfShape K (SheafOfModules.{u} S.ringCatSheaf)]
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape K :=
  isClosedUnderColimitsOfShape_isQuasicoherentOnSite B S hS K
    (associatedModuleIsQuasicoherent B S hS) hsurj

/-- **Stacks 0GNC (1)** for `τ = fppf`, over essential surjectivity alone: a direct sum of
quasi-coherent modules on the big fppf site of `S` is quasi-coherent. -/
public theorem isClosedUnderColimitsOfShape_discrete_isQuasicoherentOnSite' (I : Type u)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape (Discrete I) :=
  isClosedUnderColimitsOfShape_isQuasicoherentOnSite' B S hS (Discrete I) hsurj

/-- **Stacks 0GNC (3)** for `τ = fppf`, over essential surjectivity alone: the cokernel of a
morphism of quasi-coherent modules on the big fppf site of `S` is quasi-coherent, a cokernel
being a colimit over `CategoryTheory.Limits.WalkingParallelPair`. -/
public theorem isClosedUnderColimitsOfShape_walkingParallelPair_isQuasicoherentOnSite'
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape WalkingParallelPair :=
  isClosedUnderColimitsOfShape_isQuasicoherentOnSite' B S hS WalkingParallelPair hsurj

/-- Closure of quasi-coherence on the big fppf site of `S` under colimits of every shape
`K : Type u`, over essential surjectivity alone. -/
public theorem closedUnderColimitsOfSize_isQuasicoherentOnSite'
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u} (structureSheaf B S hS) :=
  fun K _ ↦ isClosedUnderColimitsOfShape_isQuasicoherentOnSite' B S hS K hsurj

/-- **Stacks 0GNE (1), the existence half**, over essential surjectivity alone: the category of
quasi-coherent modules on the big fppf site of `S` has all colimits indexed at the size of the
site. -/
public theorem hasColimitsOfSize_quasicoherentOnSite'
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    HasColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  hasColimitsOfSize_quasicoherentOnSite B S hS
    (closedUnderColimitsOfSize_isQuasicoherentOnSite' B S hS hsurj)

/-- **Stacks 0GNE (1), the comparison with the modules of the big fppf site**, over essential
surjectivity alone: colimits of quasi-coherent modules on `(Sch/S)_fppf` are the colimits of the
same diagram taken in all modules on `(Sch/S)_fppf`.

The source's clause (1) compares with three ambient categories and this is one of them; see the
implementation notes of this file. -/
public theorem preservesColimitsOfSize_quasicoherentOnSite_ι'
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).ι :=
  preservesColimitsOfSize_quasicoherentOnSite_ι B S hS
    (closedUnderColimitsOfSize_isQuasicoherentOnSite' B S hS hsurj)

end BigFppfOver

end AlgebraicGeometry

end
