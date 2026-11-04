module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerationComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteTypesComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiTypesComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SubsiteLowerShriekQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallFlatSites
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
import StacksCore.Tactic.StacksAttribute

/-!
# Descent, Lemma 05VG: having a global presentation, site by site

Let `S` be a scheme and `𝓕` a quasi-coherent `𝒪_S`-module, and let `𝓕^a` be the
`𝒪`-module on a site associated to `𝓕` by Descent, Proposition 03DX.  Descent, Lemma 05VG asserts
that `𝓕` has a property of Modules on Sites, Definitions 03DE, 03DL and 03ER, if and only if `𝓕^a`
has it.  This file records the property *having a global presentation*, Modules on Sites,
Definition 03DE (6), at each of the ten sites of the lemma, one statement per site.  On both sides
the property is `SheafOfModules.HasGlobalPresentation`, the declaration registered for 03DE
"global presentation": on the side of `S` it is read on the ringed site of opens of `S` with its
structure sheaf, on the other side on the ringed site of `𝓕^a`.

## Main results

* `Stacks.SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation_of_isTerminal`: on
  a site with a final object, a global presentation at the universe of the sections
  (`SheafOfModules.IsPresentedByGlobalSections`) is the same as a global presentation in the
  presentation universe of the site (`SheafOfModules.HasGlobalPresentation`).

The ten cells of the row, in namespace `AlgebraicGeometry`, each of the form
`𝓕` has a global presentation `↔` `𝓕^a` has a global presentation:

* big site `(Sch/S)_Zar`: `Cells05VG.hasGlobalPresentation_iff_baseAssociatedModule_zariski`;
* big site `(Sch/S)_étale`: `Cells05VG.hasGlobalPresentation_iff_baseAssociatedModule_etale`;
* big site `(Sch/S)_smooth`: `Cells05VG.hasGlobalPresentation_iff_baseAssociatedModule_smooth`;
* big site `(Sch/S)_syntomic`: `Cells05VG.hasGlobalPresentation_iff_baseAssociatedModule_syntomic`;
* big site `(Sch/S)_fppf`: `Cells05VG.hasGlobalPresentation_iff_baseAssociatedModule_fppf`;
* small site `S_Zar`: `Cells05VG.hasGlobalPresentation_iff_smallZariskiAssociatedModule`;
* small site `S_étale`: `Cells05VG.hasGlobalPresentation_iff_smallEtaleAssociatedModule`;
* small site `S_smooth`:
  `Cells05VG.hasGlobalPresentation_iff_smallFlatSiteAssociatedModule_smooth`;
* small site `S_syntomic`:
  `Cells05VG.hasGlobalPresentation_iff_smallFlatSiteAssociatedModule_syntomic`;
* small site `S_fppf`: `Cells05VG.hasGlobalPresentation_iff_smallFlatSiteAssociatedModule_fppf`.

## Implementation notes

The library has two renderings of 03DE (6).  `SheafOfModules.IsPresentedByGlobalSections` takes
its two coproducts and its cokernel among the sheaves of modules themselves, while
`SheafOfModules.HasGlobalPresentation`, the one registered for 03DE "global presentation", takes
them after raising the sections to the universe `max u v r` of the site.  On the opens of `S` the
two agree outright (`SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation`).  On
the big sites `(Sch/S)_τ` and on the small sites, whose objects lie one universe above their
sections, the raised universe is strictly larger; the two still agree because each of these sites
has a final object, so that global sections are small and a global presentation in the raised
universe can be shrunk back to a `SheafOfModules.Presentation`
(`SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_isTerminal`).  The converse is
`Stacks.SheafOfModules.hasGlobalPresentation_of_isPresentedByGlobalSections`.

Each cell is then the existing cell for `SheafOfModules.IsPresentedByGlobalSections` at the same
comparison functor, read on both sides through these two agreements.

## References

* [Stacks, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w r

namespace Stacks.SheafOfModules

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- **The two renderings of Stacks 03DE (6) agree on a site with a final object.**  A sheaf of
modules is a cokernel of a map of coproducts of copies of the structure sheaf at the universe of
its sections if and only if it is one after raising the sections to the universe of the site.
The forward half is `Stacks.SheafOfModules.hasGlobalPresentation_of_isPresentedByGlobalSections`;
for the reverse half the final object makes global sections small, so the global presentation is
shrunk to a `SheafOfModules.Presentation`, whose free modules and cokernel are a global
presentation at the universe of the sections. -/
theorem isPresentedByGlobalSections_iff_hasGlobalPresentation_of_isTerminal {T : C}
    (hT : IsTerminal T) (M : _root_.SheafOfModules.{r} R) :
    M.IsPresentedByGlobalSections ↔ M.HasGlobalPresentation := by
  refine ⟨hasGlobalPresentation_of_isPresentedByGlobalSections, fun h ↦ ?_⟩
  have := AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective (J := J)
  obtain ⟨p⟩ := h.nonempty_presentation_of_isTerminal hT
  exact ⟨p.generators.I, p.relations.I, _root_.SheafOfModules.free p.generators.I,
    _root_.SheafOfModules.free p.relations.I, _root_.SheafOfModules.ιFree,
    _root_.SheafOfModules.ιFree, ⟨_root_.SheafOfModules.isColimitFreeCofan _⟩,
    ⟨_root_.SheafOfModules.isColimitFreeCofan _⟩, _, p.generators.π, _, ⟨p.isColimit⟩⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Cells05VG

open Stacks.SheafOfModules (isPresentedByGlobalSections_iff_hasGlobalPresentation_of_isTerminal)

/-- Transport the iff between global presentations through an iff of the versions at the
universe of the sections, on a site with a final object. -/
private theorem hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff {S : Scheme.{u}}
    (𝓕 : S.Modules) {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {T : C} (hT : IsTerminal T)
    {M : _root_.SheafOfModules.{u} R}
    (h : SheafOfModules.IsPresentedByGlobalSections (R := S.ringCatSheaf) 𝓕 ↔
      M.IsPresentedByGlobalSections) :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔ M.HasGlobalPresentation :=
  (SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation.{u, u, u} 𝓕).symm.trans <|
    h.trans <| isPresentedByGlobalSections_iff_hasGlobalPresentation_of_isTerminal hT _

section Big

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG, having a global presentation, big Zariski site.**  A quasi-coherent
`𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global presentation on
`(Sch/S)_Zar`. -/
@[stacks 05VG "having a global presentation, big site (Sch/S)_Zar"]
theorem hasGlobalPresentation_iff_baseAssociatedModule_zariski (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .zariski).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (BigFppfOver.isTerminalOpensObjTop B S hS)
    (BigFppfOver.isPresentedByGlobalSections_iff_baseAssociatedModule B S hS .zariski ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global presentation, big étale site.**  A quasi-coherent
`𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global presentation on
`(Sch/S)_étale`. -/
@[stacks 05VG "having a global presentation, big site (Sch/S)_étale"]
theorem hasGlobalPresentation_iff_baseAssociatedModule_etale (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .etale).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (BigFppfOver.isTerminalOpensObjTop B S hS)
    (BigFppfOver.isPresentedByGlobalSections_iff_baseAssociatedModule B S hS .etale ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global presentation, big smooth site.**  A quasi-coherent
`𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global presentation on
`(Sch/S)_smooth`. -/
@[stacks 05VG "having a global presentation, big site (Sch/S)_smooth"]
theorem hasGlobalPresentation_iff_baseAssociatedModule_smooth (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .smooth).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (BigFppfOver.isTerminalOpensObjTop B S hS)
    (BigFppfOver.isPresentedByGlobalSections_iff_baseAssociatedModule B S hS .smooth ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global presentation, big syntomic site.**  A quasi-coherent
`𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global presentation on
`(Sch/S)_syntomic`. -/
@[stacks 05VG "having a global presentation, big site (Sch/S)_syntomic"]
theorem hasGlobalPresentation_iff_baseAssociatedModule_syntomic (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .syntomic).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (BigFppfOver.isTerminalOpensObjTop B S hS)
    (BigFppfOver.isPresentedByGlobalSections_iff_baseAssociatedModule B S hS .syntomic ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global presentation, big fppf site.**  A quasi-coherent
`𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global presentation on
`(Sch/S)_fppf`. -/
@[stacks 05VG "having a global presentation, big site (Sch/S)_fppf"]
theorem hasGlobalPresentation_iff_baseAssociatedModule_fppf (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .fppf).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (BigFppfOver.isTerminalOpensObjTop B S hS)
    (BigFppfOver.isPresentedByGlobalSections_iff_baseAssociatedModule B S hS .fppf ⟨𝓕, h𝓕⟩)

end Big

/-- **Descent, Lemma 05VG, having a global presentation, small Zariski site.**  A quasi-coherent
`𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global presentation on
`S_Zar`. -/
@[stacks 05VG "having a global presentation, small site S_Zar"]
theorem hasGlobalPresentation_iff_smallZariskiAssociatedModule (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation ((SmallZariski.associatedModule B S hS).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (SmallZariski.isTerminalOpensObjTop B S hS)
    (SmallZariski.isPresentedByGlobalSections_iff_associatedModule B S hS 𝓕)

/-- **Descent, Lemma 05VG, having a global presentation, small étale site.**  A quasi-coherent
`𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global presentation on
`S_étale`. -/
@[stacks 05VG "having a global presentation, small site S_étale"]
theorem hasGlobalPresentation_iff_smallEtaleAssociatedModule (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (𝓕 : S.Modules) [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation ((SmallEtale.associatedModule B S hS).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (SmallEtale.isTerminalOpensObjTop B S hS)
    (SmallEtale.isPresentedByGlobalSections_iff_associatedModule B S hS ⟨𝓕, h𝓕⟩)

section SmallFlat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG, having a global presentation, small smooth site.**  A quasi-coherent
`𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global presentation on
`S_smooth`. -/
@[stacks 05VG "having a global presentation, small site S_smooth"]
theorem hasGlobalPresentation_iff_smallFlatSiteAssociatedModule_smooth (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation
        ((SmallFlatSite.associatedModule B S hS .smooth).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (SmallFlatSite.isTerminalFinal B S hS .smooth)
    (SmallFlatSite.isPresentedByGlobalSections_iff_associatedModule B S hS .smooth ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global presentation, small syntomic site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global
presentation on `S_syntomic`. -/
@[stacks 05VG "having a global presentation, small site S_syntomic"]
theorem hasGlobalPresentation_iff_smallFlatSiteAssociatedModule_syntomic (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation
        ((SmallFlatSite.associatedModule B S hS .syntomic).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (SmallFlatSite.isTerminalFinal B S hS .syntomic)
    (SmallFlatSite.isPresentedByGlobalSections_iff_associatedModule B S hS .syntomic ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global presentation, small fppf site.**  A quasi-coherent
`𝒪_S`-module `𝓕` has a global presentation if and only if `𝓕^a` has a global presentation on
`S_fppf`. -/
@[stacks 05VG "having a global presentation, small site S_fppf"]
theorem hasGlobalPresentation_iff_smallFlatSiteAssociatedModule_fppf (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasGlobalPresentation
        ((SmallFlatSite.associatedModule B S hS .fppf).obj 𝓕) :=
  hasGlobalPresentation_iff_of_isPresentedByGlobalSections_iff 𝓕
    (SmallFlatSite.isTerminalFinal B S hS .fppf)
    (SmallFlatSite.isPresentedByGlobalSections_iff_associatedModule B S hS .fppf ⟨𝓕, h𝓕⟩)

end SmallFlat

end AlgebraicGeometry.Cells05VG

end
