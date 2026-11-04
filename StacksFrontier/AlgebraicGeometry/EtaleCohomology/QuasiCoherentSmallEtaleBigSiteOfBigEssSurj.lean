module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSmallEtaleBigSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit

/-!
# The small-étale/big-site equivalences of quasi-coherent modules over one hypothesis

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/QuasiCoherentSmallEtaleBigSite.lean` builds the
equivalence `QCoh(S_étale, 𝒪) ≌ QCoh((Sch/S)_τ, 𝒪)` of clauses (4) and (5) of Stacks 0DEW by
composing the two equivalences of Descent, Proposition 03DX, and carries the essential
surjectivity of `𝓕 ↦ 𝓕^a` onto both the small étale and the big-site quasi-coherent modules.

The small étale one of those two hypotheses is a theorem of this development,
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleCounit.lean`), proved for an
arbitrary scheme by a counit argument. This file records the three equivalences with it
discharged, so that only the big-site hypothesis is left.

## Main definitions

* `AlgebraicGeometry.smallEtaleBigSiteQuasicoherentEquivalenceOfBigEssSurj`: the equivalence
  `QCoh(S_étale, 𝒪) ≌ QCoh((Sch/S)_τ, 𝒪)` at an arbitrary `τ`, over the big-site essential
  surjectivity alone.
* `AlgebraicGeometry.smallEtaleBigEtaleQuasicoherentEquivalenceOfBigEssSurj` and
  `AlgebraicGeometry.smallEtaleBigFppfQuasicoherentEquivalenceOfBigEssSurj`: its instances at
  `τ = étale` and `τ = fppf`.

## Implementation notes

These declarations are **not registered** against Stacks 0DEW. The hypothesis they still carry,
`AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule`, is the big-site
half of Descent, Proposition 03DX (1). On the big site it is the effectivity of fpqc descent,
Stacks 023T, which is still open, so a registration here would be conditional. The small étale
half does not go through 023T: the counit route derives it from Stacks 0GN7 at the Zariski site
together with the cartesianness of quasi-coherent modules between affine objects.

## References

* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The equivalence between the quasi-coherent modules on the small étale site of `S` and those
on the big site `(Sch/S)_τ`, at an arbitrary `τ`, **over the big-site essential surjectivity
alone**.

This is `AlgebraicGeometry.smallEtaleBigSiteQuasicoherentEquivalence` with its small étale
hypothesis discharged by `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`. -/
public noncomputable def smallEtaleBigSiteQuasicoherentEquivalenceOfBigEssSurj
    (BE : BigEtaleSite.{u}) (BF : BigFppfSite.{u}) (S : Scheme.{u})
    (hE : BE.Contains S) (hF : BF.Contains S) (τ : SiteKind)
    (hbig : BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule BF S hF τ) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf BE S hE)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf BF S hF τ)).FullSubcategory :=
  (SmallEtale.associatedModuleEquivalence' BE S hE).symm.trans
    (BigFppfOver.baseAssociatedModuleEquivalenceOnSite BF S hF τ hbig)

/-- `AlgebraicGeometry.smallEtaleBigSiteQuasicoherentEquivalenceOfBigEssSurj` at `τ = étale`:
`QCoh(S_étale, 𝒪) ≌ QCoh((Sch/S)_étale, 𝒪)`, over the big étale essential surjectivity alone. -/
public noncomputable def smallEtaleBigEtaleQuasicoherentEquivalenceOfBigEssSurj
    (BE : BigEtaleSite.{u}) (BF : BigFppfSite.{u}) (S : Scheme.{u})
    (hE : BE.Contains S) (hF : BF.Contains S)
    (hbig : BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule BF S hF .etale) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf BE S hE)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf BF S hF .etale)).FullSubcategory :=
  smallEtaleBigSiteQuasicoherentEquivalenceOfBigEssSurj BE BF S hE hF .etale hbig

/-- `AlgebraicGeometry.smallEtaleBigSiteQuasicoherentEquivalenceOfBigEssSurj` at `τ = fppf`:
`QCoh(S_étale, 𝒪) ≌ QCoh((Sch/S)_fppf, 𝒪)`, over the big fppf essential surjectivity alone. -/
public noncomputable def smallEtaleBigFppfQuasicoherentEquivalenceOfBigEssSurj
    (BE : BigEtaleSite.{u}) (BF : BigFppfSite.{u}) (S : Scheme.{u})
    (hE : BE.Contains S) (hF : BF.Contains S)
    (hbig : BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule BF S hF .fppf) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf BE S hE)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf BF S hF .fppf)).FullSubcategory :=
  smallEtaleBigSiteQuasicoherentEquivalenceOfBigEssSurj BE BF S hE hF .fppf hbig

end AlgebraicGeometry

end
