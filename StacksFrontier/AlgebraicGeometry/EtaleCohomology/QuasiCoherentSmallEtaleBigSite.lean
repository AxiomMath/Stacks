module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssentialImage
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules on the small étale site and on a big site of a scheme

Let `S` be a scheme.  For a quasi-coherent `𝒪_S`-module `𝓕` on the *small étale* site `S_étale`
the rule `𝓕 ↦ 𝓕^a`, `(f : T → S) ↦ Γ(T, f_small^*𝓕)`, is an equivalence onto the quasi-coherent
modules on the big étale site `((Sch/S)_étale, 𝒪)`, and also onto the quasi-coherent modules on
the big fppf site `((Sch/S)_fppf, 𝒪)`.  These are clauses (4) and (5) of Stacks 0DEW, and the
source proves them exactly as they are proved here: by composing the two equivalences of
Descent, Proposition 03DX — the small-site one for `S_étale` and the big-site one for
`(Sch/S)_τ` — both of which have the quasi-coherent `𝒪_S`-modules of the *scheme* `S` as their
common source.  The consistency of the notation `𝓕^a` across the three sites is the first
paragraph of the source's proof and is Remark 03FH; it is what makes the composite the rule
`𝓕 ↦ 𝓕^a` rather than merely *an* equivalence.

The big étale and big fppf sites of `S` have the same underlying category and differ only in
their topology, which is how the source arranges Sections 021A and 021R through the compatible
cutoff choices of Remark 03FF.  That is also how this library arranges them: the five
topologies of `AlgebraicGeometry.SiteKind` all live on `AlgebraicGeometry.BigFppfOver B S hS`
through `AlgebraicGeometry.BigFppfOver.baseOverTopology`, and `(Sch/S)_étale` is the value of
that family at `AlgebraicGeometry.SiteKind.etale`.  So one statement, quantified over `τ`,
gives both clauses, and the two clauses are recorded as its two instances.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule`: essential
  surjectivity of `𝓕 ↦ 𝓕^a` onto the quasi-coherent modules of `(Sch/S)_τ`, as a hypothesis;
  it is now a theorem, so each declaration below that takes it has an unprimed form carrying it
  and a primed form with the hypothesis discharged.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleQcohOnSite`: the functor of Stacks
  03DX (1) at an arbitrary `τ`, `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)`.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleEquivalenceOnSite'`: the equivalence
  `QCoh(𝒪_S) ≌ QCoh((Sch/S)_τ, 𝒪)` of Stacks 03DX (1), at an arbitrary `τ`.
* `AlgebraicGeometry.smallEtaleBigSiteQuasicoherentEquivalence'`: the equivalence
  `QCoh(S_étale, 𝒪) ≌ QCoh((Sch/S)_τ, 𝒪)` of Stacks 0DEW, at an arbitrary `τ`.
* `AlgebraicGeometry.smallEtaleBigEtaleQuasicoherentEquivalence'` and
  `AlgebraicGeometry.smallEtaleBigFppfQuasicoherentEquivalence'`: its instances at
  `τ = étale` and `τ = fppf`, which are clauses (4) and (5) of Stacks 0DEW.

## Main results

* `AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcohOnSite`: the functor of
  Stacks 03DX (1) is fully faithful at every `τ`.
* `AlgebraicGeometry.BigFppfOver.essSurj_baseAssociatedModuleQcohOnSite'` and
  `AlgebraicGeometry.BigFppfOver.isEquivalence_baseAssociatedModuleQcohOnSite'`: it is
  essentially surjective at every `τ`, and hence an equivalence.

## Implementation notes

The source's proof cites Descent, Proposition 03DX twice, once for the small étale site of `S`
and once for the big site `(Sch/S)_τ`, and both citations are theorems of this library.  The
small-étale one is `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleCounit.lean:332`), proved
there out of the counit of the associated-module adjunction, and the equivalence it yields is
`AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`.  The big-site one is essential
surjectivity of `𝓕 ↦ 𝓕^a` onto the quasi-coherent modules of `(Sch/S)_τ`,
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseEssentialSurjectivity.lean`),
which reduces the `τ` case to the fppf case by showing that a quasi-coherent module on
`(Sch/S)_τ` is a sheaf for the fppf topology.

The `τ`-indexed functor of Stacks 03DX (1) is assembled here out of two theorems:
Stacks 03DV (1) at every `τ`,
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`,
which corestricts the functor into the quasi-coherent modules; and Stacks 0GN7 for the big
site at every `τ`, `AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`.  The
`τ = fppf` case is `AlgebraicGeometry.BigFppfOver.associatedModuleQcohOnSite'`, which is not
re-proved; the point of the present family is that the *étale* topology is covered too, which
is what clause (4) needs and what the fppf-only declarations cannot supply.

What is **not** claimed here is the rest of Stacks 0DEW.  Clause (1), the fppf sheaf condition
for the rule `(f : T → S) ↦ Γ(T, f_small^*𝓕)`, and clauses (2), (3), (6) and (7) all speak of
that rule as a presheaf on `(Sch/S)`, that is of `f_small^*` together with its composition
comparisons; `f_small^*` itself is
`AlgebraicGeometry.smallEtalePullbackModules` (Stacks 03D6 (2)), but the functoriality of
`(f : T → S) ↦ Γ(T, f_small^*𝓕)` in `f` is not in the library, and no tag here mentions those
clauses.

## References

* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Essential surjectivity of `𝓕 ↦ 𝓕^a` on the big site `(Sch/S)_τ`**, as a hypothesis:
every quasi-coherent module on `(Sch/S)_τ` is isomorphic to an `𝓕^a` for a quasi-coherent
`𝒪_S`-module `𝓕`.

At `τ = fppf` this is `AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`
read through `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleQcoh`. -/
public abbrev BaseQuasicoherentIsEssImageAssociatedModule (τ : SiteKind) : Prop :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.baseRingStructureSheaf B S hS τ) ≤
    (baseAssociatedModuleQcoh B S hS τ).essImage

/-- **The functor of Stacks 03DX (1) at an arbitrary `τ`**: `𝓕 ↦ 𝓕^a` as a
functor `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)`.

This is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleQcoh`, whose target is *all* modules
on `(Sch/S)_τ`, corestricted to the quasi-coherent ones along Stacks 03DV (1). -/
public noncomputable abbrev baseAssociatedModuleQcohOnSite (τ : SiteKind) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf B S hS τ)).FullSubcategory :=
  ObjectProperty.lift _ (baseAssociatedModuleQcoh B S hS τ) fun M =>
    isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B S hS τ M.obj M.property

/-- **The corestricted functor `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)` is fully faithful**, at every
`τ`: the content is Stacks 0GN7 for the big site,
`AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`. -/
public noncomputable def fullyFaithfulBaseAssociatedModuleQcohOnSite (τ : SiteKind) :
    (baseAssociatedModuleQcohOnSite B S hS τ).FullyFaithful :=
  have := full_baseAssociatedModuleQcoh B S hS τ
  have := faithful_baseAssociatedModuleQcoh B S hS τ
  .ofFullyFaithful _

/-- The corestricted functor `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)` is essentially surjective, over
`AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule`: an isomorphism in
a full subcategory is an isomorphism of the underlying modules. -/
public theorem essSurj_baseAssociatedModuleQcohOnSite (τ : SiteKind)
    (hsurj : BaseQuasicoherentIsEssImageAssociatedModule B S hS τ) :
    (baseAssociatedModuleQcohOnSite B S hS τ).EssSurj where
  mem_essImage G := by
    obtain ⟨𝓕, ⟨e⟩⟩ := hsurj G.obj G.property
    exact ⟨𝓕, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **The corestricted functor `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)` is essentially surjective**, at
every `τ`, with no hypothesis.  Essential surjectivity of `𝓕 ↦ 𝓕^a` into *all* modules of
`(Sch/S)_τ` is `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`, and
an isomorphism in a full subcategory is an isomorphism of the underlying modules.

This discharges the hypothesis of
`AlgebraicGeometry.BigFppfOver.essSurj_baseAssociatedModuleQcohOnSite`. -/
public theorem essSurj_baseAssociatedModuleQcohOnSite' (τ : SiteKind) :
    (baseAssociatedModuleQcohOnSite B S hS τ).EssSurj :=
  essSurj_baseAssociatedModuleQcohOnSite B S hS τ
    (baseQuasicoherentIsEssImageAssociatedModule B S hS τ)

/-- `𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)`, over essential surjectivity
alone. -/
public theorem isEquivalence_baseAssociatedModuleQcohOnSite (τ : SiteKind)
    (hsurj : BaseQuasicoherentIsEssImageAssociatedModule B S hS τ) :
    (baseAssociatedModuleQcohOnSite B S hS τ).IsEquivalence :=
  have hff := fullyFaithfulBaseAssociatedModuleQcohOnSite B S hS τ
  have := hff.full
  have := hff.faithful
  have := essSurj_baseAssociatedModuleQcohOnSite B S hS τ hsurj
  {}

/-- **Stacks 03DX (1) at every `τ`**: `𝓕 ↦ 𝓕^a` is an equivalence
`QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)`, with no hypothesis. -/
public theorem isEquivalence_baseAssociatedModuleQcohOnSite' (τ : SiteKind) :
    (baseAssociatedModuleQcohOnSite B S hS τ).IsEquivalence :=
  isEquivalence_baseAssociatedModuleQcohOnSite B S hS τ
    (baseQuasicoherentIsEssImageAssociatedModule B S hS τ)

/-- The equivalence of categories `QCoh(𝒪_S) ≌ QCoh((Sch/S)_τ, 𝒪)` of Stacks 03DX (1) at an
arbitrary `τ`, over essential surjectivity alone, with `𝓕 ↦ 𝓕^a` as its functor. -/
public noncomputable def baseAssociatedModuleEquivalenceOnSite (τ : SiteKind)
    (hsurj : BaseQuasicoherentIsEssImageAssociatedModule B S hS τ) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf B S hS τ)).FullSubcategory :=
  have := isEquivalence_baseAssociatedModuleQcohOnSite B S hS τ hsurj
  (baseAssociatedModuleQcohOnSite B S hS τ).asEquivalence

/-- **Stacks 03DX (1) at every `τ`, as an equivalence of categories**:
`QCoh(𝒪_S) ≌ QCoh((Sch/S)_τ, 𝒪)`, with `𝓕 ↦ 𝓕^a` as its functor and with no hypothesis. -/
@[stacks 03DX "clause (1) at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}: 𝓕 ↦ 𝓕ᵃ is an \
equivalence QCoh(𝒪_S) ≌ QCoh((Sch/S)_τ, 𝒪)"]
public noncomputable def baseAssociatedModuleEquivalenceOnSite' (τ : SiteKind) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf B S hS τ)).FullSubcategory :=
  baseAssociatedModuleEquivalenceOnSite B S hS τ
    (baseQuasicoherentIsEssImageAssociatedModule B S hS τ)

end BigFppfOver

/-- **The equivalence of Stacks 0DEW between the quasi-coherent modules on the small étale site
of `S` and the quasi-coherent modules on the big site `(Sch/S)_τ`**, at an arbitrary `τ`.

The source proves its clauses (4) and (5) by citing Descent, Proposition 03DX twice, and that
is what this is: the small-étale equivalence `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)` run backwards,
followed by the big-site equivalence `QCoh(𝒪_S) ≌ QCoh((Sch/S)_τ, 𝒪)`.  Both are equivalences
over essential surjectivity of `𝓕 ↦ 𝓕^a` on the site concerned, and those are the two
hypotheses; the common source `QCoh(𝒪_S)` needs no compatibility between the two chosen size
cutoffs, since it is a category of modules on the scheme `S` and sees neither site. -/
public noncomputable def smallEtaleBigSiteQuasicoherentEquivalence
    (BE : BigEtaleSite.{u}) (BF : BigFppfSite.{u}) (S : Scheme.{u})
    (hE : BE.Contains S) (hF : BF.Contains S) (τ : SiteKind)
    (hsmall : SmallEtale.QuasicoherentIsEssImageAssociatedModule BE S hE)
    (hbig : BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule BF S hF τ) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf BE S hE)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf BF S hF τ)).FullSubcategory :=
  (SmallEtale.associatedModuleEquivalence BE S hE hsmall).symm.trans
    (BigFppfOver.baseAssociatedModuleEquivalenceOnSite BF S hF τ hbig)

/-- **The equivalence of Stacks 0DEW between the quasi-coherent modules on the small étale site
of `S` and the quasi-coherent modules on the big site `(Sch/S)_τ`**, at an arbitrary `τ` and
with no hypothesis.

The source proves its clauses (4) and (5) by citing Descent, Proposition 03DX twice, and that
is what this is: the small-étale equivalence `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)` run backwards,
followed by the big-site equivalence `QCoh(𝒪_S) ≌ QCoh((Sch/S)_τ, 𝒪)`.  The two citations are
the theorems `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'` and
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleEquivalenceOnSite'`, so the two essential
surjectivity hypotheses of
`AlgebraicGeometry.smallEtaleBigSiteQuasicoherentEquivalence` are discharged.  The common
source `QCoh(𝒪_S)` needs no compatibility between the two chosen size cutoffs, since it is a
category of modules on the scheme `S` and sees neither site. -/
public noncomputable def smallEtaleBigSiteQuasicoherentEquivalence'
    (BE : BigEtaleSite.{u}) (BF : BigFppfSite.{u}) (S : Scheme.{u})
    (hE : BE.Contains S) (hF : BF.Contains S) (τ : SiteKind) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf BE S hE)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf BF S hF τ)).FullSubcategory :=
  (SmallEtale.associatedModuleEquivalence' BE S hE).symm.trans
    (BigFppfOver.baseAssociatedModuleEquivalenceOnSite' BF S hF τ)

/-- Stacks 0DEW, clause (4), over essential surjectivity of `𝓕 ↦ 𝓕^a` on `S_étale` and on
`(Sch/S)_étale`.  The unconditional statement is
`AlgebraicGeometry.smallEtaleBigEtaleQuasicoherentEquivalence'`, which is where the tag sits. -/
public noncomputable def smallEtaleBigEtaleQuasicoherentEquivalence
    (BE : BigEtaleSite.{u}) (BF : BigFppfSite.{u}) (S : Scheme.{u})
    (hE : BE.Contains S) (hF : BF.Contains S)
    (hsmall : SmallEtale.QuasicoherentIsEssImageAssociatedModule BE S hE)
    (hbig : BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule BF S hF .etale) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf BE S hE)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf BF S hF .etale)).FullSubcategory :=
  smallEtaleBigSiteQuasicoherentEquivalence BE BF S hE hF .etale hsmall hbig

/-- **Stacks 0DEW, clause (4).**  The rule `𝓕 ↦ 𝓕^a` is an equivalence between the
quasi-coherent `𝒪_S`-modules on `S_étale` and the quasi-coherent modules on
`((Sch/S)_étale, 𝒪)`.

The source's proof of this clause cites Descent, Proposition 03DX twice, and both citations are
theorems of this library.  The small-étale one is
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`; the big-site one at
`τ = étale` is `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseEssentialSurjectivity.lean`). -/
@[stacks 0DEW "clause (4): 𝓕 ↦ 𝓕ᵃ is an equivalence between QCoh(S_étale, 𝒪) and \
QCoh((Sch/S)_étale, 𝒪)"]
public noncomputable def smallEtaleBigEtaleQuasicoherentEquivalence'
    (BE : BigEtaleSite.{u}) (BF : BigFppfSite.{u}) (S : Scheme.{u})
    (hE : BE.Contains S) (hF : BF.Contains S) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf BE S hE)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf BF S hF .etale)).FullSubcategory :=
  smallEtaleBigSiteQuasicoherentEquivalence' BE BF S hE hF .etale

/-- Stacks 0DEW, clause (5), over essential surjectivity of `𝓕 ↦ 𝓕^a` on `S_étale` and on
`(Sch/S)_fppf`.  The unconditional statement is
`AlgebraicGeometry.smallEtaleBigFppfQuasicoherentEquivalence'`, which is where the tag sits. -/
public noncomputable def smallEtaleBigFppfQuasicoherentEquivalence
    (BE : BigEtaleSite.{u}) (BF : BigFppfSite.{u}) (S : Scheme.{u})
    (hE : BE.Contains S) (hF : BF.Contains S)
    (hsmall : SmallEtale.QuasicoherentIsEssImageAssociatedModule BE S hE)
    (hbig : BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule BF S hF .fppf) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf BE S hE)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf BF S hF .fppf)).FullSubcategory :=
  smallEtaleBigSiteQuasicoherentEquivalence BE BF S hE hF .fppf hsmall hbig

/-- **Stacks 0DEW, clause (5).**  The rule `𝓕 ↦ 𝓕^a` is an equivalence between the
quasi-coherent `𝒪_S`-modules on `S_étale` and the quasi-coherent modules on
`((Sch/S)_fppf, 𝒪)`.

The source's proof of this clause cites Descent, Proposition 03DX twice, and both citations are
theorems of this library.  The small-étale one is
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`; the big-site one, at
`τ = fppf`, is `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementTransport.lean`
`:512`).  The equivalence used below is the `τ`-indexed one, whose essential surjectivity is
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`; that theorem is
proved by reducing the `τ` case to this `fppf` one. -/
@[stacks 0DEW "clause (5): 𝓕 ↦ 𝓕ᵃ is an equivalence between QCoh(S_étale, 𝒪) and \
QCoh((Sch/S)_fppf, 𝒪)"]
public noncomputable def smallEtaleBigFppfQuasicoherentEquivalence'
    (BE : BigEtaleSite.{u}) (BF : BigFppfSite.{u}) (S : Scheme.{u})
    (hE : BE.Contains S) (hF : BF.Contains S) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (SmallEtale.structureSheaf BE S hE)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf BF S hF .fppf)).FullSubcategory :=
  smallEtaleBigSiteQuasicoherentEquivalence' BE BF S hE hF .fppf

end AlgebraicGeometry

end
