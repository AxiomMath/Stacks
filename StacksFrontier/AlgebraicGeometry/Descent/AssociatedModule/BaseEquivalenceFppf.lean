module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementRestrFun
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSmallEtaleBigSite

/-!
# The `τ`-indexed reduction of Stacks 03DX (1), discharged at `τ = fppf`

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSmallEtaleBigSite` carries
clause (1) of Stacks 03DX at every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` down to a
single predicate, `AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule τ`:
the functor `𝓕 ↦ 𝓕^a : QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)` exists and is fully faithful at every
`τ` with no hypothesis (Stacks 03DV (1) and Stacks 0GN7, both proved `τ`-parametrically), and
only essential surjectivity is carried.  **This file discharges that predicate at `τ = fppf`.**

Both instantiations are equalities of definitions rather than comparisons:

    FibredSite.baseRingStructureSheaf B S hS .fppf = structureSheaf B S hS
    baseAssociatedModuleQcoh B S hS .fppf = associatedModuleQcoh B S hS

hold by `rfl`.  So the predicate at `τ = fppf` *is*
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`, which
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'` proves, and the
`τ`-indexed functor at `τ = fppf` is
`AlgebraicGeometry.BigFppfOver.associatedModuleQcohOnSite'`.

What this records is the exact size of the remaining gap in clause (1): the four coarser
topologies are short of it by four instances of one predicate and nothing else — no further
plumbing stands between them and the assembly, which is already written and already fully
faithful at every `τ`.

## Main results

* `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule_fppf`: the
  outstanding predicate of the `τ`-indexed reduction, discharged at `τ = fppf`.
* `AlgebraicGeometry.BigFppfOver.isEquivalence_baseAssociatedModuleQcohOnSite_fppf` and
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleEquivalenceOnSite_fppf`: Stacks 03DX (1)
  at `τ = fppf` read through the `τ`-indexed assembly, with no hypothesis.

## Implementation notes

No `stacks` attribute is placed.  Clause (1) at `τ = fppf` is already registered, on
`AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite_fppf` and
`AlgebraicGeometry.BigFppfOver.associatedModuleEquivalence_fppf`
(`EffectiveGlueAgreementRestrFun.lean:721` and `:730`), and the declarations below are that same
statement reached through the `τ`-indexed spelling: they add no scope, so tagging them would
duplicate the registration rather than extend it.  Clause (1) at
`τ ∈ {Zariski, étale, smooth, syntomic}` is not proved here, and nothing below should be read as
covering it; it is proved, for every `τ` at once, in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity`
(`AlgebraicGeometry.BigFppfOver.isEquivalence_baseAssociatedModuleQcohOnSite'` and
`…baseAssociatedModuleEquivalenceOnSite'`, where the tag is registered).

A consequence outside Stacks 03DX, not claimed here: the `hbig` hypothesis of
`AlgebraicGeometry.smallEtaleBigFppfQuasicoherentEquivalence` — clause (5) of Stacks 0DEW — is
this predicate at `τ = fppf`, and its `hsmall` hypothesis is
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`
(`SmallEtaleCounit.lean:327`), which is unconditional.  So that clause can now be stated with
no hypothesis; its clause string still says "over essential surjectivity of 𝓕 ↦ 𝓕^a on S_étale
and (Sch/S)_fppf" and discharging it belongs to Stacks 0DEW, not here.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The outstanding predicate of the `τ`-indexed reduction of Stacks 03DX (1), discharged at
`τ = fppf`.**  At `τ = fppf` the predicate is
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` by definition, and that
is `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`. -/
public theorem baseQuasicoherentIsEssImageAssociatedModule_fppf :
    BaseQuasicoherentIsEssImageAssociatedModule B S hS .fppf :=
  quasicoherentIsEssImageAssociatedModule' B S hS

/-- **Stacks 03DX (1) at `τ = fppf`, read through the `τ`-indexed assembly**: `𝓕 ↦ 𝓕^a` is an
equivalence `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)`, with no hypothesis.  The registered form of
this statement is
`AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite_fppf`. -/
public theorem isEquivalence_baseAssociatedModuleQcohOnSite_fppf :
    (baseAssociatedModuleQcohOnSite B S hS .fppf).IsEquivalence :=
  isEquivalence_baseAssociatedModuleQcohOnSite B S hS .fppf
    (baseQuasicoherentIsEssImageAssociatedModule_fppf B S hS)

/-- **The equivalence of Stacks 03DX (1) at `τ = fppf`, read through the `τ`-indexed
assembly**, with no hypothesis.  The registered form is
`AlgebraicGeometry.BigFppfOver.associatedModuleEquivalence_fppf`. -/
public noncomputable def baseAssociatedModuleEquivalenceOnSite_fppf :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf B S hS .fppf)).FullSubcategory :=
  baseAssociatedModuleEquivalenceOnSite B S hS .fppf
    (baseQuasicoherentIsEssImageAssociatedModule_fppf B S hS)

end AlgebraicGeometry.BigFppfOver

end
