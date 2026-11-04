module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FinitePresentationAgreement03DX
import StacksCore.Tactic.StacksAttribute

/-!
# Descent, Lemma 05VG: finite presentation, site by site

Let `S` be a scheme and `𝓕` a quasi-coherent `𝒪_S`-module, and let `𝓕^a` be the
`𝒪`-module on a site associated to `𝓕` by Descent, Proposition 03DX.  Descent, Lemma 05VG asserts
that `𝓕` has a property of Modules on Sites, Definitions 03DE, 03DL and 03ER, if and only if `𝓕^a`
has it.  This file records the property *of finite presentation*, Modules on Sites, Definition 03DL
(7), at each of the ten sites of the lemma, one statement per site.  On both sides the property is
`SheafOfModules.IsFinitePresentationOnSite`: every object has a covering on whose members the
restricted module has a finite global presentation.  On the side of `S` it is read on the ringed
site of opens of `S` with its structure sheaf, on the other side on the ringed site of `𝓕^a`.

## Main results

The ten cells of the row, in namespace `AlgebraicGeometry`, each of the form
`𝓕` of finite presentation `↔` `𝓕^a` of finite presentation:

* big site `(Sch/S)_Zar`:
  `Cells05VG.isFinitePresentationOnSite_iff_baseAssociatedModule_zariski`;
* big site `(Sch/S)_étale`:
  `Cells05VG.isFinitePresentationOnSite_iff_baseAssociatedModule_etale`;
* big site `(Sch/S)_smooth`:
  `Cells05VG.isFinitePresentationOnSite_iff_baseAssociatedModule_smooth`;
* big site `(Sch/S)_syntomic`:
  `Cells05VG.isFinitePresentationOnSite_iff_baseAssociatedModule_syntomic`;
* big site `(Sch/S)_fppf`:
  `Cells05VG.isFinitePresentationOnSite_iff_baseAssociatedModule_fppf`;
* small site `S_Zar`: `Cells05VG.isFinitePresentationOnSite_iff_smallZariskiAssociatedModule`;
* small site `S_étale`: `Cells05VG.isFinitePresentationOnSite_iff_smallEtaleAssociatedModule`;
* small site `S_smooth`:
  `Cells05VG.isFinitePresentationOnSite_iff_smallFlatSiteAssociatedModule_smooth`;
* small site `S_syntomic`:
  `Cells05VG.isFinitePresentationOnSite_iff_smallFlatSiteAssociatedModule_syntomic`;
* small site `S_fppf`:
  `Cells05VG.isFinitePresentationOnSite_iff_smallFlatSiteAssociatedModule_fppf`.

## Implementation notes

The big sites `(Sch/S)_τ` are the five topologies on one chosen big fppf site, and the comparison
functor is `AlgebraicGeometry.BigFppfOver.baseAssociatedModule` at the topology `τ`.  The small
sites `S_smooth`, `S_syntomic` and `S_fppf` are those of
`AlgebraicGeometry.SmallFlatSite.associatedModule`; `S_Zar` and `S_étale` are those of
`AlgebraicGeometry.SmallZariski.associatedModule` and
`AlgebraicGeometry.SmallEtale.associatedModule`, built on a big Zariski and a big étale site
respectively.

Each cell is the specialization of the corresponding statement of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FinitePresentationAgreement03DX`, which
already reads Definition 03DL (7) on both sides.  At the small Zariski site the equivalence holds
for every `𝒪_S`-module
(`AlgebraicGeometry.SmallZariski.isFinitePresentationOnSite_iff_associatedModule`); the cell is
stated under the source's hypothesis of quasi-coherence.

## References

* [Stacks, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Cells05VG

section Big

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG, finite presentation, big Zariski site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`(Sch/S)_Zar`. -/
@[stacks 05VG "of finite presentation, big site (Sch/S)_Zar"]
theorem isFinitePresentationOnSite_iff_baseAssociatedModule_zariski (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((BigFppfOver.baseAssociatedModule B S hS .zariski).obj 𝓕) :=
  BigFppfOver.isFinitePresentationOnSite_baseAssociatedModule_iff B S hS .zariski 𝓕

/-- **Descent, Lemma 05VG, finite presentation, big étale site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`(Sch/S)_étale`. -/
@[stacks 05VG "of finite presentation, big site (Sch/S)_étale"]
theorem isFinitePresentationOnSite_iff_baseAssociatedModule_etale (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((BigFppfOver.baseAssociatedModule B S hS .etale).obj 𝓕) :=
  BigFppfOver.isFinitePresentationOnSite_baseAssociatedModule_iff B S hS .etale 𝓕

/-- **Descent, Lemma 05VG, finite presentation, big smooth site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`(Sch/S)_smooth`. -/
@[stacks 05VG "of finite presentation, big site (Sch/S)_smooth"]
theorem isFinitePresentationOnSite_iff_baseAssociatedModule_smooth (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((BigFppfOver.baseAssociatedModule B S hS .smooth).obj 𝓕) :=
  BigFppfOver.isFinitePresentationOnSite_baseAssociatedModule_iff B S hS .smooth 𝓕

/-- **Descent, Lemma 05VG, finite presentation, big syntomic site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`(Sch/S)_syntomic`. -/
@[stacks 05VG "of finite presentation, big site (Sch/S)_syntomic"]
theorem isFinitePresentationOnSite_iff_baseAssociatedModule_syntomic (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((BigFppfOver.baseAssociatedModule B S hS .syntomic).obj 𝓕) :=
  BigFppfOver.isFinitePresentationOnSite_baseAssociatedModule_iff B S hS .syntomic 𝓕

/-- **Descent, Lemma 05VG, finite presentation, big fppf site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`(Sch/S)_fppf`. -/
@[stacks 05VG "of finite presentation, big site (Sch/S)_fppf"]
theorem isFinitePresentationOnSite_iff_baseAssociatedModule_fppf (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((BigFppfOver.baseAssociatedModule B S hS .fppf).obj 𝓕) :=
  BigFppfOver.isFinitePresentationOnSite_baseAssociatedModule_iff B S hS .fppf 𝓕

end Big

/-- **Descent, Lemma 05VG, finite presentation, small Zariski site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`S_Zar`. -/
@[stacks 05VG "of finite presentation, small site S_Zar"]
theorem isFinitePresentationOnSite_iff_smallZariskiAssociatedModule (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((SmallZariski.associatedModule B S hS).obj 𝓕) :=
  SmallZariski.isFinitePresentationOnSite_iff_associatedModule B S hS 𝓕

/-- **Descent, Lemma 05VG, finite presentation, small étale site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`S_étale`. -/
@[stacks 05VG "of finite presentation, small site S_étale"]
theorem isFinitePresentationOnSite_iff_smallEtaleAssociatedModule (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((SmallEtale.associatedModule B S hS).obj 𝓕) :=
  SmallEtale.isFinitePresentationOnSite_iff_associatedModule B S hS 𝓕

section SmallFlat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG, finite presentation, small smooth site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`S_smooth`. -/
@[stacks 05VG "of finite presentation, small site S_smooth"]
theorem isFinitePresentationOnSite_iff_smallFlatSiteAssociatedModule_smooth (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((SmallFlatSite.associatedModule B S hS .smooth).obj 𝓕) :=
  SmallFlatSite.isFinitePresentationOnSite_iff_associatedModule B S hS .smooth 𝓕

/-- **Descent, Lemma 05VG, finite presentation, small syntomic site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`S_syntomic`. -/
@[stacks 05VG "of finite presentation, small site S_syntomic"]
theorem isFinitePresentationOnSite_iff_smallFlatSiteAssociatedModule_syntomic (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((SmallFlatSite.associatedModule B S hS .syntomic).obj 𝓕) :=
  SmallFlatSite.isFinitePresentationOnSite_iff_associatedModule B S hS .syntomic 𝓕

/-- **Descent, Lemma 05VG, finite presentation, small fppf site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is of finite presentation if and only if `𝓕^a` is of finite presentation on
`S_fppf`. -/
@[stacks 05VG "of finite presentation, small site S_fppf"]
theorem isFinitePresentationOnSite_iff_smallFlatSiteAssociatedModule_fppf (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentationOnSite (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitePresentationOnSite
        ((SmallFlatSite.associatedModule B S hS .fppf).obj 𝓕) :=
  SmallFlatSite.isFinitePresentationOnSite_iff_associatedModule B S hS .fppf 𝓕

end SmallFlat

end AlgebraicGeometry.Cells05VG

end
