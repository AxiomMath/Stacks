module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteTypesComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiTypesComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Descent, Lemma 05VG: finite freeness, site by site

Let `S` be a scheme and `𝓕` a quasi-coherent `𝒪_S`-module, and let `𝓕^a` be the
`𝒪`-module on a site associated to `𝓕` by Descent, Proposition 03DX.  Descent, Lemma 05VG asserts
that `𝓕` has a property of Modules on Sites, Definitions 03DE, 03DL and 03ER, if and only if `𝓕^a`
has it.  This file records the property *finite free*, Modules on Sites, Definition 03DE (2), at
each of the ten sites of the lemma, one statement per site.  On both sides the property is
`SheafOfModules.IsFiniteFree`, the declaration registered as `add_to_stacks 03DE "finite free"`:
on the side of `S` for the structure sheaf `S.ringCatSheaf`, on the other side for the structure
sheaf of the site of `𝓕^a`.

## Main results

The ten cells of the row, in namespace `AlgebraicGeometry`, each of the form
`𝓕` finite free `↔` `𝓕^a` finite free:

* big site `(Sch/S)_Zar`: `Cells05VG.isFiniteFree_iff_baseAssociatedModule_zariski`;
* big site `(Sch/S)_étale`: `Cells05VG.isFiniteFree_iff_baseAssociatedModule_etale`;
* big site `(Sch/S)_smooth`: `Cells05VG.isFiniteFree_iff_baseAssociatedModule_smooth`;
* big site `(Sch/S)_syntomic`: `Cells05VG.isFiniteFree_iff_baseAssociatedModule_syntomic`;
* big site `(Sch/S)_fppf`: `Cells05VG.isFiniteFree_iff_baseAssociatedModule_fppf`;
* small site `S_Zar`: `Cells05VG.isFiniteFree_iff_smallZariskiAssociatedModule`;
* small site `S_étale`: `Cells05VG.isFiniteFree_iff_smallEtaleAssociatedModule`;
* small site `S_smooth`: `Cells05VG.isFiniteFree_iff_smallFlatSiteAssociatedModule_smooth`;
* small site `S_syntomic`: `Cells05VG.isFiniteFree_iff_smallFlatSiteAssociatedModule_syntomic`;
* small site `S_fppf`: `Cells05VG.isFiniteFree_iff_smallFlatSiteAssociatedModule_fppf`.

## Implementation notes

The big sites `(Sch/S)_τ` are the five topologies on one chosen big fppf site, and the comparison
functor is `AlgebraicGeometry.BigFppfOver.baseAssociatedModule` at the topology `τ`.  The small
sites `S_smooth`, `S_syntomic` and `S_fppf` are those of
`AlgebraicGeometry.SmallFlatSite.associatedModule`; `S_Zar` and `S_étale` are those of
`AlgebraicGeometry.SmallZariski.associatedModule` and
`AlgebraicGeometry.SmallEtale.associatedModule`, built on a big Zariski and a big étale site
respectively.

The proofs specialize the existing comparisons
`AlgebraicGeometry.BigFppfOver.isFiniteFree_iff_baseAssociatedModule`,
`AlgebraicGeometry.SmallZariski.isFiniteFree_iff_associatedModule`,
`AlgebraicGeometry.SmallEtale.isFiniteFree_iff_associatedModule` and
`AlgebraicGeometry.SmallFlatSite.isFiniteFree_iff_associatedModule`.  At the small Zariski site
the equivalence holds for every `𝒪_S`-module; the cell is stated under the source's hypothesis of
quasi-coherence.

## References

* [Stacks, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Cells05VG

section Big

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG, finite freeness, big Zariski site.**  A quasi-coherent `𝒪_S`-module
`𝓕` is finite free if and only if `𝓕^a` is finite free on `(Sch/S)_Zar`. -/
@[stacks 05VG "finite free, big site (Sch/S)_Zar"]
theorem isFiniteFree_iff_baseAssociatedModule_zariski (𝓕 : S.Modules) [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _ ((BigFppfOver.baseAssociatedModule B S hS .zariski).obj 𝓕) :=
  BigFppfOver.isFiniteFree_iff_baseAssociatedModule B S hS .zariski ⟨𝓕, h𝓕⟩

/-- **Descent, Lemma 05VG, finite freeness, big étale site.**  A quasi-coherent `𝒪_S`-module
`𝓕` is finite free if and only if `𝓕^a` is finite free on `(Sch/S)_étale`. -/
@[stacks 05VG "finite free, big site (Sch/S)_étale"]
theorem isFiniteFree_iff_baseAssociatedModule_etale (𝓕 : S.Modules) [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _ ((BigFppfOver.baseAssociatedModule B S hS .etale).obj 𝓕) :=
  BigFppfOver.isFiniteFree_iff_baseAssociatedModule B S hS .etale ⟨𝓕, h𝓕⟩

/-- **Descent, Lemma 05VG, finite freeness, big smooth site.**  A quasi-coherent `𝒪_S`-module
`𝓕` is finite free if and only if `𝓕^a` is finite free on `(Sch/S)_smooth`. -/
@[stacks 05VG "finite free, big site (Sch/S)_smooth"]
theorem isFiniteFree_iff_baseAssociatedModule_smooth (𝓕 : S.Modules) [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _ ((BigFppfOver.baseAssociatedModule B S hS .smooth).obj 𝓕) :=
  BigFppfOver.isFiniteFree_iff_baseAssociatedModule B S hS .smooth ⟨𝓕, h𝓕⟩

/-- **Descent, Lemma 05VG, finite freeness, big syntomic site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is finite free if and only if `𝓕^a` is finite free on `(Sch/S)_syntomic`. -/
@[stacks 05VG "finite free, big site (Sch/S)_syntomic"]
theorem isFiniteFree_iff_baseAssociatedModule_syntomic (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _
        ((BigFppfOver.baseAssociatedModule B S hS .syntomic).obj 𝓕) :=
  BigFppfOver.isFiniteFree_iff_baseAssociatedModule B S hS .syntomic ⟨𝓕, h𝓕⟩

/-- **Descent, Lemma 05VG, finite freeness, big fppf site.**  A quasi-coherent `𝒪_S`-module
`𝓕` is finite free if and only if `𝓕^a` is finite free on `(Sch/S)_fppf`. -/
@[stacks 05VG "finite free, big site (Sch/S)_fppf"]
theorem isFiniteFree_iff_baseAssociatedModule_fppf (𝓕 : S.Modules) [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _ ((BigFppfOver.baseAssociatedModule B S hS .fppf).obj 𝓕) :=
  BigFppfOver.isFiniteFree_iff_baseAssociatedModule B S hS .fppf ⟨𝓕, h𝓕⟩

end Big

/-- **Descent, Lemma 05VG, finite freeness, small Zariski site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is finite free if and only if `𝓕^a` is finite free on `S_Zar`. -/
@[stacks 05VG "finite free, small site S_Zar"]
theorem isFiniteFree_iff_smallZariskiAssociatedModule (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _ ((SmallZariski.associatedModule B S hS).obj 𝓕) :=
  SmallZariski.isFiniteFree_iff_associatedModule B S hS 𝓕

/-- **Descent, Lemma 05VG, finite freeness, small étale site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is finite free if and only if `𝓕^a` is finite free on `S_étale`. -/
@[stacks 05VG "finite free, small site S_étale"]
theorem isFiniteFree_iff_smallEtaleAssociatedModule (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (𝓕 : S.Modules) [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _ ((SmallEtale.associatedModule B S hS).obj 𝓕) :=
  SmallEtale.isFiniteFree_iff_associatedModule B S hS ⟨𝓕, h𝓕⟩

section SmallFlat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG, finite freeness, small smooth site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is finite free if and only if `𝓕^a` is finite free on `S_smooth`. -/
@[stacks 05VG "finite free, small site S_smooth"]
theorem isFiniteFree_iff_smallFlatSiteAssociatedModule_smooth (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _ ((SmallFlatSite.associatedModule B S hS .smooth).obj 𝓕) :=
  SmallFlatSite.isFiniteFree_iff_associatedModule B S hS .smooth ⟨𝓕, h𝓕⟩

/-- **Descent, Lemma 05VG, finite freeness, small syntomic site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is finite free if and only if `𝓕^a` is finite free on `S_syntomic`. -/
@[stacks 05VG "finite free, small site S_syntomic"]
theorem isFiniteFree_iff_smallFlatSiteAssociatedModule_syntomic (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _ ((SmallFlatSite.associatedModule B S hS .syntomic).obj 𝓕) :=
  SmallFlatSite.isFiniteFree_iff_associatedModule B S hS .syntomic ⟨𝓕, h𝓕⟩

/-- **Descent, Lemma 05VG, finite freeness, small fppf site.**  A quasi-coherent
`𝒪_S`-module `𝓕` is finite free if and only if `𝓕^a` is finite free on `S_fppf`. -/
@[stacks 05VG "finite free, small site S_fppf"]
theorem isFiniteFree_iff_smallFlatSiteAssociatedModule_fppf (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.IsFiniteFree S.ringCatSheaf 𝓕 ↔
      SheafOfModules.IsFiniteFree _ ((SmallFlatSite.associatedModule B S hS .fppf).obj 𝓕) :=
  SmallFlatSite.isFiniteFree_iff_associatedModule B S hS .fppf ⟨𝓕, h𝓕⟩

end SmallFlat

end AlgebraicGeometry.Cells05VG

end
