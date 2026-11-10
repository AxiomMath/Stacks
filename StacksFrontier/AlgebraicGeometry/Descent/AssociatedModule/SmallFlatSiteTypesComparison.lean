module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerationComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.LocalGenerationBySectionsAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteFiniteLocallyFreeAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteFinitePresentationAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteLocalGenerationFinitenessAgreement
import StacksCore.Tactic.StacksAttribute

/-!
# Descent, Lemma 05VG on the small smooth, syntomic and fppf sites

Descent, Lemma 05VG compares the properties of modules of Modules on Sites, Definitions 03DE, 03DL
and 03ER across the equivalences `QCoh(𝒪_S) ⟶ QCoh((Sch/S)_τ, 𝒪)` and
`QCoh(𝒪_S) ⟶ QCoh(S_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, of Descent, Proposition 03DX.  The source has small sites
`S_τ` only for `τ ∈ {Zariski, étale}`; the library extends them to the three remaining
topologies `τ ∈ {smooth, syntomic, fppf}` as `AlgebraicGeometry.SmallFlatSite` (the full
subcategory of `(Sch/S)_τ` on the schemes smooth, syntomic, respectively flat and locally of
finite presentation over `S`, with the induced `τ`-coverings), and proves 03DX (2) for them in
`AlgebraicGeometry.SmallFlatSite.isEquivalence_associatedModuleQcohOnSite`.

**This file proves 05VG on those three small sites**, for every property of the source's list
except local freeness and coherence, which the source itself excepts (and asserts coherence only
for the small Zariski and étale sites): the seven global properties of 03DE, local generation by
sections, local generation by `r` sections, finite type, finite presentation and finite local
freeness of 03DL; flatness of 03ER is
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallFlatSiteFlatAgreement.lean`.  Each
statement is an equivalence between "`𝓕` has the property" and "`𝓕^a` has the property on
`S_τ`", under quasi-coherence of `𝓕` and nothing else.

## How the properties are compared

Let `ι : S_τ ⊆ (Sch/S)_τ` be the inclusion and `ι_!` its lower shriek.

* **The global properties** are compared exactly as on the big site
  (`Stacks.Sheaves.QcohTypeComparison`): `𝓕 ↦ 𝓕^a|_{S_τ}` preserves colimits, carries the
  structure sheaf to the structure sheaf, and is fully faithful on `QCoh(𝒪_S)`
  (`AlgebraicGeometry.SmallFlatSite.fullyFaithfulAssociatedModuleQcoh`).
* **The local properties** go through the big site: `ι_!(𝓕^a|_{S_τ}) ≅ 𝓕^a|_{(Sch/S)_τ}`
  (`AlgebraicGeometry.SmallFlatSite.associatedModuleCompLowerShriekIso`), a module on `S_τ` has
  each of the local properties exactly when its lower shriek has it
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallFlatSiteLocalTypes.lean`), and
  the big-site clauses of 05VG settle the comparison with `𝓕`.

## Main results

For `τ ∈ {smooth, syntomic, fppf}` and a quasi-coherent `𝒪_S`-module `𝓕`:

* `AlgebraicGeometry.SmallFlatSite.isFree_iff_associatedModule`,
  `.isFiniteFree_iff_associatedModule`, `.isGeneratedByGlobalSections_iff_associatedModule`,
  `.isGeneratedByGlobalSectionsOfCard_iff_associatedModule`,
  `.exists_isGeneratedByGlobalSectionsOfCard_iff_associatedModule`,
  `.isPresentedByGlobalSections_iff_associatedModule` and
  `.isFinitelyPresentedByGlobalSections_iff_associatedModule`: 05VG for 03DE (1)–(7) on `S_τ`;
* `AlgebraicGeometry.SmallFlatSite.isFiniteLocallyFreeOnSite_iff_associatedModule`,
  `.isLocallyGeneratedBySectionsOnSite_iff_associatedModule`,
  `.isLocallyGeneratedByOnSite_iff_associatedModule`, `.isFiniteType_iff_associatedModule` and
  `.isFinitePresentation_iff_associatedModule`: 05VG for 03DL (2), (3), (4), (5) and (7) on `S_τ`.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallFlatSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-- The associated-module functor of the small `τ`-site preserves colimits, recorded at the
retyping `AlgebraicGeometry.SmallFlatSite.associatedModuleOfSheaf`. -/
theorem preservesColimitsOfSize_associatedModuleOfSheaf.{w, w'} :
    PreservesColimitsOfSize.{w, w'} (associatedModuleOfSheaf B S hS κ) :=
  have h : PreservesColimitsOfSize.{w, w'} (associatedModule B S hS κ) := inferInstance
  h

/-- The associated-module functor of the small `τ`-site preserves epimorphisms, being a left
adjoint. -/
theorem preservesEpimorphisms_associatedModuleOfSheaf :
    (associatedModuleOfSheaf B S hS κ).PreservesEpimorphisms :=
  have : (associatedModule B S hS κ).IsLeftAdjoint :=
    (associatedModuleAdjunction B S hS κ).isLeftAdjoint
  have h : (associatedModule B S hS κ).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_isLeftAdjoint _
  h

/-- The associated-module functor of the small `τ`-site preserves zero morphisms, being a left
adjoint. -/
theorem preservesZeroMorphisms_associatedModuleOfSheaf :
    (associatedModuleOfSheaf B S hS κ).PreservesZeroMorphisms :=
  have h : (associatedModule B S hS κ).PreservesZeroMorphisms := inferInstance
  h

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (1), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module is free if and only if
`𝓕^a` is so as an `𝒪`-module on `S_τ`. -/
@[stacks 05VG "free (03DE (1)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ {smooth, syntomic, fppf} \
(the small sites extending the source's)"]
theorem isFree_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsFree ↔ ((associatedModuleQcoh B S hS κ).obj F).IsFree :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS κ
  Stacks.Sheaves.QcohTypeComparison.isFree_iff _ (associatedModuleUnitIso B S hS κ) _
    (fullyFaithfulAssociatedModuleQcoh B S hS κ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (2), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module is finite free, with the
same rank if and only if `𝓕^a` is so as an `𝒪`-module on `S_τ`. -/
@[stacks 05VG "finite free (03DE (2)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ {smooth, syntomic, \
fppf} (the small sites extending the source's)"]
theorem isFiniteFree_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    SheafOfModules.IsFiniteFree S.ringCatSheaf F.obj ↔
      SheafOfModules.IsFiniteFree (ringStructureSheaf B S hS κ)
        ((associatedModuleQcoh B S hS κ).obj F) :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS κ
  Stacks.Sheaves.QcohTypeComparison.isFiniteFree_iff _ (associatedModuleUnitIso B S hS κ) _
    (fullyFaithfulAssociatedModuleQcoh B S hS κ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (3), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module is generated by global
sections if and only if `𝓕^a` is so as an `𝒪`-module on `S_τ`. -/
@[stacks 05VG "generated by global sections (03DE (3)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ \
{smooth, syntomic, fppf} (the small sites extending the source's)"]
theorem isGeneratedByGlobalSections_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsGeneratedByGlobalSections ↔
      ((associatedModuleQcoh B S hS κ).obj F).IsGeneratedByGlobalSections :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS κ
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS κ
  Stacks.Sheaves.QcohTypeComparison.isGeneratedByGlobalSections_iff _
    (associatedModuleUnitIso B S hS κ) _
    (fullyFaithfulAssociatedModuleQcoh B S hS κ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (4), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module is generated by `r`
global sections, with the same `r` if and only if `𝓕^a` is so as an `𝒪`-module on `S_τ`. -/
@[stacks 05VG "generated by r global sections (03DE (4)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ \
{smooth, syntomic, fppf} (the small sites extending the source's)"]
theorem isGeneratedByGlobalSectionsOfCard_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) (r : ℕ) :
    F.obj.IsGeneratedByGlobalSectionsOfCard r ↔
      ((associatedModuleQcoh B S hS κ).obj F).IsGeneratedByGlobalSectionsOfCard r :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS κ
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS κ
  Stacks.Sheaves.QcohTypeComparison.isGeneratedByGlobalSectionsOfCard_iff _
    (associatedModuleUnitIso B S hS κ) _
    (fullyFaithfulAssociatedModuleQcoh B S hS κ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property r

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (5), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module is generated by finitely
many global sections if and only if `𝓕^a` is so as an `𝒪`-module on `S_τ`. -/
@[stacks 05VG "generated by finitely many global sections (03DE (5)): 𝓕 ↔ 𝓕^a, small site S_τ at \
every τ ∈ {smooth, syntomic, fppf} (the small sites extending the source's)"]
theorem exists_isGeneratedByGlobalSectionsOfCard_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (∃ r : ℕ, F.obj.IsGeneratedByGlobalSectionsOfCard r) ↔
      ∃ r : ℕ, ((associatedModuleQcoh B S hS κ).obj F).IsGeneratedByGlobalSectionsOfCard r :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS κ
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS κ
  Stacks.Sheaves.QcohTypeComparison.exists_isGeneratedByGlobalSectionsOfCard_iff _
    (associatedModuleUnitIso B S hS κ) _
    (fullyFaithfulAssociatedModuleQcoh B S hS κ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (6), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module is has a global
presentation, with the same two index types if and only if `𝓕^a` is so as an `𝒪`-module on
`S_τ`. -/
@[stacks 05VG "having a global presentation (03DE (6)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ \
{smooth, syntomic, fppf} (the small sites extending the source's)"]
theorem isPresentedByGlobalSections_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsPresentedByGlobalSections ↔
      ((associatedModuleQcoh B S hS κ).obj F).IsPresentedByGlobalSections :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS κ
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS κ
  have := preservesZeroMorphisms_associatedModuleOfSheaf B S hS κ
  Stacks.Sheaves.QcohTypeComparison.isPresentedByGlobalSections_iff _
    (associatedModuleUnitIso B S hS κ) _
    (fullyFaithfulAssociatedModuleQcoh B S hS κ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (7), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module is has a finite global
presentation, with the same two finite index types if and only if `𝓕^a` is so as an `𝒪`-module
on `S_τ`. -/
@[stacks 05VG "having a global finite presentation (03DE (7)): 𝓕 ↔ 𝓕^a, small site S_τ at every \
τ ∈ {smooth, syntomic, fppf} (the small sites extending the source's)"]
theorem isFinitelyPresentedByGlobalSections_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsFinitelyPresentedByGlobalSections ↔
      ((associatedModuleQcoh B S hS κ).obj F).IsFinitelyPresentedByGlobalSections :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS κ
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS κ
  have := preservesZeroMorphisms_associatedModuleOfSheaf B S hS κ
  Stacks.Sheaves.QcohTypeComparison.isFinitelyPresentedByGlobalSections_iff _
    (associatedModuleUnitIso B S hS κ) _
    (fullyFaithfulAssociatedModuleQcoh B S hS κ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-! ### The local properties of Definition 03DL -/

/-- A property invariant under isomorphism transports a comparison along an isomorphism. -/
private theorem iff_of_iso_of_iff {C : Type*} [Category C] {P : C → Prop}
    (hP : ∀ {M N : C}, (M ≅ N) → P M → P N) {M N : C} (e : M ≅ N) {a b : Prop}
    (ha : a ↔ P N) (hb : b ↔ P M) : a ↔ b :=
  ha.trans ⟨fun h ↦ hb.2 (hP e.symm h), fun h ↦ hP e (hb.1 h)⟩

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module `𝓗` is finite locally free
if and only if `𝓗^a` is finite locally free as an `𝒪`-module on `S_τ`.

The lower shriek to the big `τ`-site carries `𝓗^a|_{S_τ}` to `𝓗^a|_{(Sch/S)_τ}`, finite local
freeness holds for a module on `S_τ` exactly when it holds for its lower shriek
(`AlgebraicGeometry.SmallFlatSite.isFiniteLocallyFreeOnSite_lowerShriek_iff`), and on the big site
this is `AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_iff`. -/
@[stacks 05VG "finite locally free (03DL (2)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ {smooth, \
syntomic, fppf} (the small sites extending the source's)"]
theorem isFiniteLocallyFreeOnSite_iff_associatedModule (𝓗 : S.Modules)
    [𝓗.IsQuasicoherent] :
    SheafOfModules.IsFiniteLocallyFreeOnSite (R := S.ringCatSheaf) 𝓗 ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite ((associatedModule B S hS κ).obj 𝓗) :=
  iff_of_iso_of_iff (P := SheafOfModules.IsFiniteLocallyFreeOnSite)
    (fun e ↦ Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_iso e.symm)
    ((associatedModuleCompLowerShriekIso B S hS κ).app 𝓗)
    (BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_iff B S hS κ.toSiteKind 𝓗)
    (isFiniteLocallyFreeOnSite_lowerShriek_iff B S hS κ _)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (3), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module `𝓕` is locally generated
by sections if and only if `𝓕^a` is locally generated by sections as an `𝒪`-module on `S_τ`.

Both sides hold: a quasi-coherent module is locally generated by sections, and `𝓕^a` is
quasi-coherent on `S_τ` (`AlgebraicGeometry.SmallFlatSite.isQuasicoherentOnSite_associatedModule`).
-/
@[stacks 05VG "locally generated by sections (03DL (3)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ \
{smooth, syntomic, fppf} (the small sites extending the source's)"]
theorem isLocallyGeneratedBySectionsOnSite_iff_associatedModule (𝓕 : S.Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕) :
    SheafOfModules.IsLocallyGeneratedBySectionsOnSite 𝓕 ↔
      SheafOfModules.IsLocallyGeneratedBySectionsOnSite ((associatedModule B S hS κ).obj 𝓕) :=
  ⟨fun _ ↦ Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_of_localGeneratorsData _
      (Stacks.SheafOfModules.nonempty_quasicoherentData_of_isQuasicoherentOnSite _
        (isQuasicoherentOnSite_associatedModule B S hS κ 𝓕 h𝓕)).some.localGeneratorsData,
    fun _ ↦ Stacks.SheafOfModules.isLocallyGeneratedBySectionsOnSite_of_localGeneratorsData _
      h𝓕.nonempty_quasicoherentData.some.localGeneratorsData⟩

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (4), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module `𝓗` is locally generated
by `r` sections if and only if `𝓗^a` is locally generated by `r` sections as an `𝒪`-module on
`S_τ`.  The route is that of
`AlgebraicGeometry.SmallFlatSite.isFiniteLocallyFreeOnSite_iff_associatedModule`, through
`AlgebraicGeometry.SmallFlatSite.isLocallyGeneratedByOnSite_lowerShriek_iff` and
`AlgebraicGeometry.BigFppfOver.isLocallyGeneratedByOnSite_baseAssociatedModule_iff`. -/
@[stacks 05VG "locally generated by r sections (03DL (4)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ \
{smooth, syntomic, fppf} (the small sites extending the source's)"]
theorem isLocallyGeneratedByOnSite_iff_associatedModule (𝓗 : S.Modules)
    [𝓗.IsQuasicoherent] (r : ℕ) :
    SheafOfModules.IsLocallyGeneratedByOnSite (R := S.ringCatSheaf) 𝓗 r ↔
      SheafOfModules.IsLocallyGeneratedByOnSite ((associatedModule B S hS κ).obj 𝓗) r :=
  iff_of_iso_of_iff (fun e ↦ Stacks.SheafOfModules.Intrinsic.isLocallyGeneratedByOnSite_of_iso e r)
    ((associatedModuleCompLowerShriekIso B S hS κ).app 𝓗)
    (BigFppfOver.isLocallyGeneratedByOnSite_baseAssociatedModule_iff B S hS κ.toSiteKind 𝓗 r)
    (isLocallyGeneratedByOnSite_lowerShriek_iff B S hS κ _ r)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (5), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module `𝓗` is of finite type if
and only if `𝓗^a` is of finite type as an `𝒪`-module on `S_τ`, through
`AlgebraicGeometry.SmallFlatSite.isFiniteType_lowerShriek_iff` and
`AlgebraicGeometry.BigFppfOver.isFiniteType_baseAssociatedModule_iff`. -/
@[stacks 05VG "finite type (03DL (5)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ {smooth, syntomic, \
fppf} (the small sites extending the source's)"]
theorem isFiniteType_iff_associatedModule (𝓗 : S.Modules) [𝓗.IsQuasicoherent] :
    SheafOfModules.IsFiniteType (R := S.ringCatSheaf) 𝓗 ↔
      SheafOfModules.IsFiniteType ((associatedModule B S hS κ).obj 𝓗) :=
  iff_of_iso_of_iff Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
    ((associatedModuleCompLowerShriekIso B S hS κ).app 𝓗)
    (BigFppfOver.isFiniteType_baseAssociatedModule_iff B S hS κ.toSiteKind 𝓗)
    (isFiniteType_lowerShriek_iff B S hS κ _)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (7), on the small `τ`-site, for
every `τ ∈ {smooth, syntomic, fppf}`.**  A quasi-coherent `𝒪_S`-module `𝓗` is of finite
presentation if and only if `𝓗^a` is of finite presentation as an `𝒪`-module on `S_τ`, through
`AlgebraicGeometry.SmallFlatSite.isFinitePresentation_lowerShriek_iff` and
`AlgebraicGeometry.BigFppfOver.isFinitePresentation_baseAssociatedModule_iff`. -/
@[stacks 05VG "finite presentation (03DL (7)): 𝓕 ↔ 𝓕^a, small site S_τ at every τ ∈ {smooth, \
syntomic, fppf} (the small sites extending the source's)"]
theorem isFinitePresentation_iff_associatedModule (𝓗 : S.Modules) [𝓗.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf) 𝓗 ↔
      ((associatedModule B S hS κ).obj 𝓗).IsFinitePresentation :=
  iff_of_iso_of_iff Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    ((associatedModuleCompLowerShriekIso B S hS κ).app 𝓗)
    (BigFppfOver.isFinitePresentation_baseAssociatedModule_iff B S hS κ.toSiteKind 𝓗)
    (isFinitePresentation_lowerShriek_iff B S hS κ _)

end AlgebraicGeometry.SmallFlatSite

end
