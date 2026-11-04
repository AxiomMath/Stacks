module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRestrictionRightExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.QuasiCoherentAffineAcyclicity
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineRingedToposTopologies
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EnoughPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CohomologyAfterRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverTopologyInstances

/-!
# Clause (4) of Stacks 0GNC on the big `τ`-site of a scheme, at every `τ`

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseExtensionClosure.lean` reduces clause
(4) of Descent, Lemma 0GNC at an arbitrary `τ` to two hypotheses, and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExact.lean` discharges
both at `τ = fppf`.  **This file discharges them at every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`**, and with that clause (4) holds at all five
topologies.

## What was missing, and what supplies it

The step that did not transfer was the vanishing.  Step 1 of the fppf argument consumes
positive-degree vanishing of `Sheaf.H'` of `𝓕ᵃ` at an object with affine total space, and
`AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_baseAssociatedSheaf_affine` states it for
the localized **fppf** topology only.  Its engine
`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine` is already generic in a
`AlgebraicGeometry.CoveringTopology`, together with every input of the Čech criterion it runs on
(`AlgebraicGeometry.overStandardCoverings_cofinal` and its four companions); what was absent was
only the bridge between the two families of topologies this library carries — `overTopology τ' B'`
for `τ' : CoveringTopology` and a big site `B'` of that covering topology, against
`AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ` for `τ : SiteKind`, the `τ`-topology
carried on the fppf category.

That bridge is available, in both halves, and this file puts them together:

* the **categories are literally the same**.  Each of the four coarser sites a big fppf site
  carries — `AlgebraicGeometry.BigFppfSite.toBigZariskiSite` and its three companions, Stacks
  03FF — is built from `B`'s own data, with `B`'s cutoff by `rfl`
  (`AlgebraicGeometry.BigFppfSite.toBigEtaleSite_cutoff` and companions).  So
  `Over (base B.toBigZariskiSite S hS)` *is* `AlgebraicGeometry.BigFppfOver B S hS`, with no
  transport and no cutoff-equality hypothesis;
* the **topologies agree**, as four equations:
  `AlgebraicGeometry.BigFppfSite.bigZariskiOver_topology_toBigZariskiSite`,
  `…bigEtaleOver_topology_toBigEtaleSite`, `…bigSmoothOver_topology_toBigSmoothSite` and
  `…bigSyntomicOver_topology_toBigSyntomicSite`, whose right-hand sides are
  `baseOverTopology B S hS τ` by reduction of the `baseTopology` match.

Transporting a `Sheaf.H'`-vanishing along such an equation is
`Stacks.Cohomology.ObjectSections.isZero_sheafH'_of_topology_eq` below.  It is stated with its
four homological inputs as **explicit** arguments rather than instance arguments: the two
topologies are equal but not definitionally equal, their `HasSheafify` and `HasExt` instances are
found by different declarations on the two sides, and instance search at `overTopology τ' B' S hS`
does not fire from `hS : B.Contains S` because `AlgebraicGeometry.cutoff τ' B'` does not reduce to
`B.cutoff` at reducible transparency.  Naming the four inputs removes every search.

## Main results

* `Stacks.Cohomology.ObjectSections.isZero_sheafH'_of_topology_eq`: vanishing of `Sheaf.H'`
  transports along an equality of Grothendieck topologies on one category.
* `AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_baseAssociatedSheaf_affine_all`: **the
  positive-degree cohomology of `𝓕ᵃ` on `(Sch/S)_τ` vanishes at an object with affine total
  space, at every `τ`** (Stacks 03P2 at an affine object).
* `AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_isQuasicoherentOnSite_affine_all`: the
  same for an arbitrary quasi-coherent `𝒪`-module on `(Sch/S)_τ`.
* `AlgebraicGeometry.BigFppfOver.surjective_val_app_of_shortExact_affine_all`: a section over
  such an object lifts.
* `AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map_all`: **the hypothesis `hepi` of
  `BaseExtensionClosure`, discharged at every `τ`** — restriction to the small Zariski site is
  right exact at a short exact sequence with quasi-coherent kernel.  This is the source's
  `H¹(U, 𝓕₁) = 0` step, Descent, Proposition 03DW.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all` and
  `AlgebraicGeometry.BigFppfOver.isClosedUnderExtensions_baseIsQuasicoherentOnSite_all`:
  **clause (4) of Stacks 0GNC at every `τ`**, and the
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions` instance it gives, which is
  unconditional and therefore safe as an instance.

## Implementation notes

The other hypothesis `BaseExtensionClosure` carried, essential surjectivity of `𝓕 ↦ 𝓕^a` onto the
quasi-coherent modules of `(Sch/S)_τ`, is Descent, Proposition 03DX (1) and is discharged at every
`τ` by `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`, so nothing
below is conditional.

The registrations here are the only ones for clause (4). There is no separate `τ = fppf` form:
it would be the `τ`-indexed statement below with `τ` pinned, and the clause strings here, "at
every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, unconditionally", cover `τ = fppf` as well.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Cohomology.ObjectSections

/-- **Vanishing of `Sheaf.H'` transports along an equality of Grothendieck topologies.**  Two
topologies on the same category which are equal, but whose `HasSheafify` and `HasExt` inputs are
supplied by different declarations, carry the same cohomology of two sheaves with the same
underlying presheaf.

The four homological inputs are explicit arguments, not instance arguments, so that a caller can
name them: the equality below is between topologies that are not definitionally equal, so instance
search has to be run separately on each side, and on one side it may not fire at all. -/
public theorem isZero_sheafH'_of_topology_eq {C : Type w} [Category.{v} C]
    {J J' : GrothendieckTopology C}
    (i1 : HasSheafify J AddCommGrpCat.{v}) (i2 : HasExt.{v} (Sheaf J AddCommGrpCat.{v}))
    (i1' : HasSheafify J' AddCommGrpCat.{v}) (i2' : HasExt.{v} (Sheaf J' AddCommGrpCat.{v}))
    (h : J = J') (F : Sheaf J AddCommGrpCat.{v}) (F' : Sheaf J' AddCommGrpCat.{v})
    (hF : F.val = F'.val) (p : ℕ) (U : C)
    (hz : IsZero (@Sheaf.H'.{v} C _ J i1 i2 F p U)) :
    IsZero (@Sheaf.H'.{v} C _ J' i1' i2' F' p U) := by
  subst h
  obtain ⟨a, ha⟩ := F
  obtain ⟨b, hb⟩ := F'
  cases hF
  exact hz

end Stacks.Cohomology.ObjectSections

namespace AlgebraicGeometry.BigFppfOver

-- A localized big site is essentially small at the universe of its morphisms, so these two
-- supply its `Ext` universe and enough injectives.  `CategoryTheory.Sheaf.H'` is defined through
-- `Ext`, so without them the statements below do not even elaborate.
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The vanishing at every `τ` -/

section Vanishing

variable (F : S.Modules) [F.IsQuasicoherent]

/-- `Sheaf.H'` of a sheaf on `J'` vanishes at an affine object of a localized big `τ'`-site, when
`J'` is `overTopology τ' B' S hS'` and the sheaf is `Fᵃ` pulled back along `overToSlice`. -/
private theorem isZero_sheafH'_of_overTopology_eq {τ' : CoveringTopology}
    (B' : BigSite.{u} τ') (hS' : S.size < cutoff τ' B')
    (J' : GrothendieckTopology (Over (base B' S hS')))
    (i1' : HasSheafify J' AddCommGrpCat.{u}) (h : overTopology τ' B' S hS' = J')
    (F' : Sheaf J' AddCommGrpCat.{u})
    (hF : F'.obj =
      (overToSlice τ' B' S hS').op ⋙ (fpqcOverAssociatedSheaf S F).obj)
    (W : Over (base B' S hS')) (hW : W ∈ overAffineObjects τ' B' S hS') (p : ℕ) (hp : 0 < p) :
    IsZero (@Sheaf.H'.{u} _ _ J' i1'
      (Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite _) F' p W) := by
  have := essentiallySmall_overBase B' S hS'
  have i1 : HasSheafify (overTopology τ' B' S hS') AddCommGrpCat.{u} :=
    hasSheafify_overTopology_addCommGrp τ' B' S hS'
  have i2 : HasExt.{u} (Sheaf (overTopology τ' B' S hS') AddCommGrpCat.{u}) :=
    Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite _
  have : (overToSlice τ' B' S hS').IsContinuous (overTopology τ' B' S hS')
      (Scheme.fpqcTopology.{u}.over S) := isContinuous_overToSlice_fpqc τ' B' S hS'
  exact Stacks.Cohomology.ObjectSections.isZero_sheafH'_of_topology_eq i1 i2 i1' _ h _ F'
    hF.symm p W
    (isZero_sheafCohomology_succ_overAffine S F τ' B' hS' W hW p hp)

/-- **The positive-degree cohomology of `𝓕ᵃ` on `(Sch/S)_τ` vanishes at an object with affine
total space**, for `τ` the Zariski topology.

`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine` read on the big Zariski site which `B`
itself carries (Stacks 03FF) — whose category is `AlgebraicGeometry.BigFppfOver B S hS` on the nose
— transported along `AlgebraicGeometry.BigFppfSite.bigZariskiOver_topology_toBigZariskiSite` by
`Stacks.Cohomology.ObjectSections.isZero_sheafH'_of_topology_eq`.  The two sheaves have the same
underlying presheaf by `rfl`, both being the pullback-sections presheaf of Stacks 03DS. -/
public theorem isZero_sheafCohomology_baseAssociatedSheaf_affine_zariski
    (W : BigFppfOver B S hS) (hW : IsAffineOver B S hS W) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf
      (FibredSite.baseRingStructureSheaf B S hS SiteKind.zariski)).obj
      (baseAssociatedSheaf B S hS F SiteKind.zariski)) p W) := by
  exact isZero_sheafH'_of_overTopology_eq S F (τ' := CoveringTopology.zariski)
    B.toBigZariskiSite hS _
    (hasSheafify_baseOverTopology B S hS SiteKind.zariski)
    (B.bigZariskiOver_topology_toBigZariskiSite S hS) _ rfl W hW p hp

/-- **The positive-degree cohomology of `𝓕ᵃ` on `(Sch/S)_τ` vanishes at an object with affine
total space**, for `τ` the étale topology.

`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine` read on the big étale site which `B`
itself carries (Stacks 03FF) — whose category is `AlgebraicGeometry.BigFppfOver B S hS` on the
nose — transported along `AlgebraicGeometry.BigFppfSite.bigEtaleOver_topology_toBigEtaleSite` by
`Stacks.Cohomology.ObjectSections.isZero_sheafH'_of_topology_eq`.  The two sheaves have the same
underlying presheaf by `rfl`, both being the pullback-sections presheaf of Stacks 03DS. -/
public theorem isZero_sheafCohomology_baseAssociatedSheaf_affine_etale
    (W : BigFppfOver B S hS) (hW : IsAffineOver B S hS W) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf
      (FibredSite.baseRingStructureSheaf B S hS SiteKind.etale)).obj
      (baseAssociatedSheaf B S hS F SiteKind.etale)) p W) := by
  exact isZero_sheafH'_of_overTopology_eq S F (τ' := CoveringTopology.etale)
    B.toBigEtaleSite hS _
    (hasSheafify_baseOverTopology B S hS SiteKind.etale)
    (B.bigEtaleOver_topology_toBigEtaleSite S hS) _ rfl W hW p hp

/-- **The positive-degree cohomology of `𝓕ᵃ` on `(Sch/S)_τ` vanishes at an object with affine
total space**, for `τ` the smooth topology.

`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine` read on the big smooth site which `B`
itself carries (Stacks 03FF) — whose category is `AlgebraicGeometry.BigFppfOver B S hS` on the
nose — transported along `AlgebraicGeometry.BigFppfSite.bigSmoothOver_topology_toBigSmoothSite` by
`Stacks.Cohomology.ObjectSections.isZero_sheafH'_of_topology_eq`.  The two sheaves have the same
underlying presheaf by `rfl`, both being the pullback-sections presheaf of Stacks 03DS. -/
public theorem isZero_sheafCohomology_baseAssociatedSheaf_affine_smooth
    (W : BigFppfOver B S hS) (hW : IsAffineOver B S hS W) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf
      (FibredSite.baseRingStructureSheaf B S hS SiteKind.smooth)).obj
      (baseAssociatedSheaf B S hS F SiteKind.smooth)) p W) := by
  exact isZero_sheafH'_of_overTopology_eq S F (τ' := CoveringTopology.smooth)
    B.toBigSmoothSite hS _
    (hasSheafify_baseOverTopology B S hS SiteKind.smooth)
    (B.bigSmoothOver_topology_toBigSmoothSite S hS) _ rfl W hW p hp

/-- **The positive-degree cohomology of `𝓕ᵃ` on `(Sch/S)_τ` vanishes at an object with affine
total space**, for `τ` the syntomic topology.

`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine` read on the big syntomic site which `B`
itself carries (Stacks 03FF) — whose category is `AlgebraicGeometry.BigFppfOver B S hS` on the nose
— transported along `AlgebraicGeometry.BigFppfSite.bigSyntomicOver_topology_toBigSyntomicSite` by
`Stacks.Cohomology.ObjectSections.isZero_sheafH'_of_topology_eq`.  The two sheaves have the same
underlying presheaf by `rfl`, both being the pullback-sections presheaf of Stacks 03DS. -/
public theorem isZero_sheafCohomology_baseAssociatedSheaf_affine_syntomic
    (W : BigFppfOver B S hS) (hW : IsAffineOver B S hS W) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf
      (FibredSite.baseRingStructureSheaf B S hS SiteKind.syntomic)).obj
      (baseAssociatedSheaf B S hS F SiteKind.syntomic)) p W) := by
  exact isZero_sheafH'_of_overTopology_eq S F (τ' := CoveringTopology.syntomic)
    B.toBigSyntomicSite hS _
    (hasSheafify_baseOverTopology B S hS SiteKind.syntomic)
    (B.bigSyntomicOver_topology_toBigSyntomicSite S hS) _ rfl W hW p hp

/-- **The positive-degree cohomology of `𝓕ᵃ` on `(Sch/S)_τ` vanishes at an object with affine
total space, at every `τ`.**  This is [Stacks, Tag 03P2] at an affine object.

At `τ = fppf` it is
`AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_baseAssociatedSheaf_affine`; the four
coarser topologies are the four statements above.  They are separate declarations rather than
branches of one `cases τ` because each spends most of a heartbeat budget on the definitional
identification of the two spellings of the pullback-sections presheaf, and the budget is
per-declaration. -/
public theorem isZero_sheafCohomology_baseAssociatedSheaf_affine_all (τ : SiteKind)
    (W : BigFppfOver B S hS) (hW : IsAffineOver B S hS W) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf
      (FibredSite.baseRingStructureSheaf B S hS τ)).obj
      (baseAssociatedSheaf B S hS F τ)) p W) := by
  cases τ with
  | fppf => exact isZero_sheafCohomology_baseAssociatedSheaf_affine B S hS F W hW p hp
  | zariski => exact isZero_sheafCohomology_baseAssociatedSheaf_affine_zariski B S hS F W hW p hp
  | etale => exact isZero_sheafCohomology_baseAssociatedSheaf_affine_etale B S hS F W hW p hp
  | smooth => exact isZero_sheafCohomology_baseAssociatedSheaf_affine_smooth B S hS F W hW p hp
  | syntomic =>
      exact isZero_sheafCohomology_baseAssociatedSheaf_affine_syntomic B S hS F W hW p hp

end Vanishing

/-- **The positive-degree cohomology of a quasi-coherent `𝒪`-module on `(Sch/S)_τ` vanishes at an
object with affine total space, at every `τ`.**

A quasi-coherent module on `(Sch/S)_τ` is the associated module of a quasi-coherent `𝒪_S`-module,
by Descent, Proposition 03DX (1) in the form
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`; the associated
module is the pullback-sections sheaf `𝓕ᵃ` by Stacks 070S (1),
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoBaseAssociatedSheaf`; and the vanishing for
`𝓕ᵃ` is
`AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_baseAssociatedSheaf_affine_all`.  The
transport of `IsZero` along the resulting isomorphism of abelian sheaves goes through
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections`, which exhibits
`Sheaf.H' · p W` as a functor of the sheaf. -/
public theorem isZero_sheafCohomology_isQuasicoherentOnSite_affine_all (τ : SiteKind)
    (G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))
    (hG : G.IsQuasicoherentOnSite) (W : BigFppfOver B S hS) (hW : IsAffineOver B S hS W)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf
      (FibredSite.baseRingStructureSheaf B S hS τ)).obj G) p W) := by
  obtain ⟨F, ⟨e⟩⟩ := baseQuasicoherentIsEssImageAssociatedModule B S hS τ G hG
  have : F.obj.IsQuasicoherent := F.property
  have eab : (SheafOfModules.toSheaf (FibredSite.baseRingStructureSheaf B S hS τ)).obj
        (baseAssociatedSheaf B S hS F.obj τ) ≅
      (SheafOfModules.toSheaf (FibredSite.baseRingStructureSheaf B S hS τ)).obj G :=
    (SheafOfModules.toSheaf _).mapIso
      ((baseAssociatedModuleIsoBaseAssociatedSheaf B S hS τ F.obj).symm ≪≫ e)
  refine (isZero_sheafCohomology_baseAssociatedSheaf_affine_all B S hS F.obj τ W hW p hp).of_iso ?_
  exact Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{u}
      (baseOverTopology B S hS τ) _ p W ≪≫
    (((sheafSections (baseOverTopology B S hS τ) AddCommGrpCat.{u}).obj
      (op W)).rightDerived p).mapIso eab.symm ≪≫
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{u}
      (baseOverTopology B S hS τ) _ p W).symm

/-! ### Step 1 and step 2 at every `τ` -/

/-- **A section of `C.X₃` over an object of `(Sch/S)_τ` with affine total space lifts to
`C.X₂`**, at every `τ`, for `C` a short exact sequence of `𝒪`-modules with `C.X₁` quasi-coherent.

The vanishing of `H¹(W, C.X₁)` is
`AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_isQuasicoherentOnSite_affine_all` and the
passage to surjectivity is
`Stacks.Cohomology.ObjectSections.surjective_val_app_of_isZero_sheafH'`. -/
public theorem surjective_val_app_of_shortExact_affine_all (τ : SiteKind)
    {C : ShortComplex (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))}
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) (W : BigFppfOver B S hS)
    (hW : IsAffineOver B S hS W) :
    Function.Surjective (C.g.val.app (op W)) :=
  Stacks.Cohomology.ObjectSections.surjective_val_app_of_isZero_sheafH'.{u}
    (baseOverTopology B S hS τ) _ hC W
    (isZero_sheafCohomology_isQuasicoherentOnSite_affine_all B S hS τ C.X₁ h₁ W hW 1 Nat.one_pos)

/-- **The hypothesis `hepi` of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseExtensionClosure`, discharged at every
`τ`.**  For a short exact sequence `C` of `𝒪`-modules on `(Sch/S)_τ` with `C.X₁` quasi-coherent,
the restriction of `C.g` along the inclusion of the small Zariski site of `S` is an epimorphism.

This is the source's `H¹(U, 𝓕₁) = 0` step, Descent, Proposition 03DW.  Step 2, the passage from
surjectivity over the affine opens of `S` read in the big site to an epimorphism of sheaves of
modules on `S_Zar`, is already `τ`-generic:
`AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map_of_surjective_on_affineOpens`. -/
public theorem epi_baseRestrictModule_map_all (τ : SiteKind)
    {C : ShortComplex (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))}
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) :
    Epi ((baseRestrictModule B S hS τ).map C.g) :=
  epi_baseRestrictModule_map_of_surjective_on_affineOpens B S hS τ C.g
    fun _ hU ↦ surjective_val_app_of_shortExact_affine_all B S hS τ hC h₁ _ hU

/-! ### Clause (4) of Stacks 0GNC at every `τ` -/

section

variable {B S hS}
variable {τ : SiteKind}
  {C : ShortComplex (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))}

/-- **Clause (4) of Stacks 0GNC on the big `τ`-site of a scheme, at every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  Given a short exact sequence
`0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` of `𝒪`-modules on `(Sch/S)_τ` with `𝓕₁` and `𝓕₃` quasi-coherent, the
middle term `𝓕₂` is quasi-coherent.

The source's three steps are
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseExtensionClosure.lean`.  Of the two
hypotheses they carried, essential surjectivity of `𝓕 ↦ 𝓕^a` is Descent, Proposition 03DX (1) and
is `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`, and right
exactness of restriction to `S_Zar` is
`AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map_all` above. -/
@[stacks 0GNC "part (4), big site at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, \
unconditionally"]
public theorem isQuasicoherentOnSite_shortExact_X₂_all (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherentOnSite
      (R := AlgebraicGeometry.FibredSite.baseRingStructureSheaf B S hS τ) C.X₂ :=
  isQuasicoherentOnSite_X₂_of_shortExact_of_epi_baseRestrictModule hC h₁ h₃
    (baseQuasicoherentIsEssImageAssociatedModule B S hS τ)
    (epi_baseRestrictModule_map_all B S hS τ hC h₁)

end

/-- Quasi-coherence of `𝒪`-modules on the big `τ`-site of a scheme is closed under extensions, at
every `τ`.  This is clause (4) of Stacks 0GNC in the shape
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions` records; it has no hypothesis, so it is
safe as an instance. -/
@[stacks 0GNC "part (4), big site at every τ, as a closure-under-extensions instance"]
public instance isClosedUnderExtensions_baseIsQuasicoherentOnSite_all (τ : SiteKind) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.baseRingStructureSheaf B S hS τ)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hC h₁ h₃ := isQuasicoherentOnSite_shortExact_X₂_all hC h₁ h₃

end AlgebraicGeometry.BigFppfOver

end
