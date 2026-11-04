module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PropertiesOfModulesComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
import StacksCore.Tactic.StacksAttribute

/-!
# Descent, Lemma 05VG: having a global finite presentation, site by site

Let `S` be a scheme and `𝓕` a quasi-coherent `𝒪_S`-module, and let `𝓕^a` be the
`𝒪`-module on a site associated to `𝓕` by Descent, Proposition 03DX.  Descent, Lemma 05VG asserts
that `𝓕` has a property of Modules on Sites, Definitions 03DE, 03DL and 03ER, if and only if `𝓕^a`
has it.  This file records the property *having a global finite presentation*, Modules on Sites,
Definition 03DE (7), at each of the ten sites of the lemma, one statement per site.  On both sides
the property is `SheafOfModules.HasFiniteGlobalPresentation`, the declaration registered as
Stacks 03DE "finite global presentation": `𝓕` is the cokernel of a map
`𝒪^{⊕k} ⟶ 𝒪^{⊕n}`.  On the side of `S` it is read on the ringed site of opens of `S` with its
structure sheaf, on the other side on the ringed site of `𝓕^a`.

## Main results

The ten cells of the row, in namespace `AlgebraicGeometry`, each of the form
`𝓕` has a global finite presentation `↔` `𝓕^a` has a global finite presentation:

* big site `(Sch/S)_Zar`:
  `Cells05VG.hasFiniteGlobalPresentation_iff_baseAssociatedModule_zariski`;
* big site `(Sch/S)_étale`:
  `Cells05VG.hasFiniteGlobalPresentation_iff_baseAssociatedModule_etale`;
* big site `(Sch/S)_smooth`:
  `Cells05VG.hasFiniteGlobalPresentation_iff_baseAssociatedModule_smooth`;
* big site `(Sch/S)_syntomic`:
  `Cells05VG.hasFiniteGlobalPresentation_iff_baseAssociatedModule_syntomic`;
* big site `(Sch/S)_fppf`:
  `Cells05VG.hasFiniteGlobalPresentation_iff_baseAssociatedModule_fppf`;
* small site `S_Zar`: `Cells05VG.hasFiniteGlobalPresentation_iff_smallZariskiAssociatedModule`;
* small site `S_étale`: `Cells05VG.hasFiniteGlobalPresentation_iff_smallEtaleAssociatedModule`;
* small site `S_smooth`:
  `Cells05VG.hasFiniteGlobalPresentation_iff_smallFlatSiteAssociatedModule_smooth`;
* small site `S_syntomic`:
  `Cells05VG.hasFiniteGlobalPresentation_iff_smallFlatSiteAssociatedModule_syntomic`;
* small site `S_fppf`:
  `Cells05VG.hasFiniteGlobalPresentation_iff_smallFlatSiteAssociatedModule_fppf`.

The comparison of the two renderings of Definition 03DE (7) in an arbitrary module universe is
`SheafOfModules.hasFiniteGlobalPresentation_iff_isFinitelyPresentedByGlobalSections`.

## Implementation notes

The library has two renderings of Definition 03DE (7). `SheafOfModules.HasFiniteGlobalPresentation`
(registered as 03DE "finite global presentation") raises the sections of the module to a universe
containing the site before writing the two finite coproducts and the cokernel;
`SheafOfModules.IsFinitelyPresentedByGlobalSections` (03DE "finite global presentation, at a single
universe of sections") writes them in the module's own universe.  The existing site-by-site
comparisons across `𝓕 ↦ 𝓕^a` are stated for the latter.  The two agree in every module universe:
the universe lift of the sections preserves colimits and zero morphisms, which carries a
presentation up, and a finite global presentation in the raised universe yields a finite
`SheafOfModules.Presentation`
(`SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation'`), which is a
presentation in the module's own universe
(`Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_presentation`).  The base comparison
`SheafOfModules.isFinitelyPresentedByGlobalSections_iff_hasFiniteGlobalPresentation` covers only a
module universe containing the site, which the big sites and the small sites built on them, whose
objects lie one universe above their sections, do not satisfy.

The big sites `(Sch/S)_τ` are the five topologies on one chosen big fppf site, and the comparison
functor is `AlgebraicGeometry.BigFppfOver.baseAssociatedModule` at the topology `τ`.  The small
sites `S_smooth`, `S_syntomic` and `S_fppf` are those of
`AlgebraicGeometry.SmallFlatSite.associatedModule`; `S_Zar` and `S_étale` are those of
`AlgebraicGeometry.SmallZariski.associatedModule` and
`AlgebraicGeometry.SmallEtale.associatedModule`, built on a big Zariski and a big étale site
respectively.  At the small Zariski site the equivalence holds for every `𝒪_S`-module; the cell is
stated under the source's hypothesis of quasi-coherence.

## References

* [Stacks, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

universe u v m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{m}}
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **The two renderings of Stacks 03DE (7) agree, in an arbitrary module universe.**  A sheaf of
modules has a finite global presentation after raising its sections to a universe containing the
site if and only if it has one in its own universe.  Raising the sections is a functor preserving
colimits and zero morphisms, so it carries the two finite coproducts and the cokernel of a
presentation in the module's own universe up; conversely a finite global presentation in the
raised universe gives a finite `SheafOfModules.Presentation`, which is one in the module's own
universe. -/
theorem hasFiniteGlobalPresentation_iff_isFinitelyPresentedByGlobalSections
    (M : SheafOfModules.{m} R) :
    M.HasFiniteGlobalPresentation ↔ M.IsFinitelyPresentedByGlobalSections := by
  let : HasSheafify J AddCommGrpCat.{m} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨p, hp⟩ := exists_isFinite_presentation_of_hasFiniteGlobalPresentation' h
    exact Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_presentation (P := p)
  · obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcok⟩⟩ := h
    let : HasSheafify J AddCommGrpCat.{max u v m} :=
      GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v m, v, u} J
    let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v m} :=
      AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v m, u, v} J
    let U := uliftForPresentationFunctor.{u, v, m, m, max u v m} (R := R)
    have : PreservesColimitsOfSize.{m, m} U :=
      uliftForPresentationFunctor_preservesColimits.{u, v, m, m, max u v m} (R := R)
    have : PreservesColimitsOfSize.{0, 0} U := preservesColimitsOfSize_shrink U
    have : U.PreservesZeroMorphisms :=
      preservesZeroMorphisms_uliftForPresentationFunctor.{u, v, m, m, max u v m} (R := R)
    exact ⟨n, k, U.obj P, U.obj Q, fun i => U.map (ι i), fun i => U.map (κ i),
      ⟨(Cofan.isColimitMapCoconeEquiv U _ (Cofan.mk P ι)) (isColimitOfPreserves U hP)⟩,
      ⟨(Cofan.isColimitMapCoconeEquiv U _ (Cofan.mk Q κ)) (isColimitOfPreserves U hQ)⟩,
      U.map a, U.map b, _, ⟨isColimitCoforkMapOfIsColimit' U hab hcok⟩⟩

end SheafOfModules

universe u

namespace AlgebraicGeometry.Cells05VG

/-- A finite global presentation of `𝓕` on `S` transfers to `M` as soon as the single-universe
renderings correspond. -/
private theorem hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections
    {S : Scheme.{u}} (𝓕 : S.Modules) {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M : SheafOfModules.{u} R}
    (h : SheafOfModules.IsFinitelyPresentedByGlobalSections (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.IsFinitelyPresentedByGlobalSections M) :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation M :=
  (_root_.SheafOfModules.hasFiniteGlobalPresentation_iff_isFinitelyPresentedByGlobalSections
    _).trans (h.trans
      (_root_.SheafOfModules.hasFiniteGlobalPresentation_iff_isFinitelyPresentedByGlobalSections
        _).symm)

section Big

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG, having a global finite presentation, big Zariski site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`(Sch/S)_Zar`. -/
@[stacks 05VG "having a global finite presentation, big site (Sch/S)_Zar"]
theorem hasFiniteGlobalPresentation_iff_baseAssociatedModule_zariski (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .zariski).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (BigFppfOver.isFinitelyPresentedByGlobalSections_iff_baseAssociatedModule B S hS .zariski
      ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global finite presentation, big étale site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`(Sch/S)_étale`. -/
@[stacks 05VG "having a global finite presentation, big site (Sch/S)_étale"]
theorem hasFiniteGlobalPresentation_iff_baseAssociatedModule_etale (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .etale).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (BigFppfOver.isFinitelyPresentedByGlobalSections_iff_baseAssociatedModule B S hS .etale
      ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global finite presentation, big smooth site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`(Sch/S)_smooth`. -/
@[stacks 05VG "having a global finite presentation, big site (Sch/S)_smooth"]
theorem hasFiniteGlobalPresentation_iff_baseAssociatedModule_smooth (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .smooth).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (BigFppfOver.isFinitelyPresentedByGlobalSections_iff_baseAssociatedModule B S hS .smooth
      ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global finite presentation, big syntomic site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`(Sch/S)_syntomic`. -/
@[stacks 05VG "having a global finite presentation, big site (Sch/S)_syntomic"]
theorem hasFiniteGlobalPresentation_iff_baseAssociatedModule_syntomic (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .syntomic).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (BigFppfOver.isFinitelyPresentedByGlobalSections_iff_baseAssociatedModule B S hS .syntomic
      ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global finite presentation, big fppf site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`(Sch/S)_fppf`. -/
@[stacks 05VG "having a global finite presentation, big site (Sch/S)_fppf"]
theorem hasFiniteGlobalPresentation_iff_baseAssociatedModule_fppf (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((BigFppfOver.baseAssociatedModule B S hS .fppf).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (BigFppfOver.isFinitelyPresentedByGlobalSections_iff_baseAssociatedModule B S hS .fppf
      ⟨𝓕, h𝓕⟩)

end Big

/-- **Descent, Lemma 05VG, having a global finite presentation, small Zariski site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`S_Zar`. -/
@[stacks 05VG "having a global finite presentation, small site S_Zar"]
theorem hasFiniteGlobalPresentation_iff_smallZariskiAssociatedModule (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (𝓕 : S.Modules) [𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((SmallZariski.associatedModule B S hS).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (SmallZariski.isFinitelyPresentedByGlobalSections_iff_associatedModule B S hS 𝓕)

/-- **Descent, Lemma 05VG, having a global finite presentation, small étale site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`S_étale`. -/
@[stacks 05VG "having a global finite presentation, small site S_étale"]
theorem hasFiniteGlobalPresentation_iff_smallEtaleAssociatedModule (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (𝓕 : S.Modules) [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((SmallEtale.associatedModule B S hS).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (SmallEtale.isFinitelyPresentedByGlobalSections_iff_associatedModule B S hS ⟨𝓕, h𝓕⟩)

section SmallFlat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG, having a global finite presentation, small smooth site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`S_smooth`. -/
@[stacks 05VG "having a global finite presentation, small site S_smooth"]
theorem hasFiniteGlobalPresentation_iff_smallFlatSiteAssociatedModule_smooth (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((SmallFlatSite.associatedModule B S hS .smooth).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (SmallFlatSite.isFinitelyPresentedByGlobalSections_iff_associatedModule B S hS .smooth
      ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global finite presentation, small syntomic site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`S_syntomic`. -/
@[stacks 05VG "having a global finite presentation, small site S_syntomic"]
theorem hasFiniteGlobalPresentation_iff_smallFlatSiteAssociatedModule_syntomic (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((SmallFlatSite.associatedModule B S hS .syntomic).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (SmallFlatSite.isFinitelyPresentedByGlobalSections_iff_associatedModule B S hS .syntomic
      ⟨𝓕, h𝓕⟩)

/-- **Descent, Lemma 05VG, having a global finite presentation, small fppf site.**  A
quasi-coherent `𝒪_S`-module `𝓕` has a global finite presentation if and only if `𝓕^a` has one on
`S_fppf`. -/
@[stacks 05VG "having a global finite presentation, small site S_fppf"]
theorem hasFiniteGlobalPresentation_iff_smallFlatSiteAssociatedModule_fppf (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent] :
    SheafOfModules.HasFiniteGlobalPresentation (R := S.ringCatSheaf) 𝓕 ↔
      SheafOfModules.HasFiniteGlobalPresentation
        ((SmallFlatSite.associatedModule B S hS .fppf).obj 𝓕) :=
  hasFiniteGlobalPresentation_iff_of_isFinitelyPresentedByGlobalSections 𝓕
    (SmallFlatSite.isFinitelyPresentedByGlobalSections_iff_associatedModule B S hS .fppf
      ⟨𝓕, h𝓕⟩)

end SmallFlat

end AlgebraicGeometry.Cells05VG

end
