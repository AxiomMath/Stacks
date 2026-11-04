module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedAffineSections
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedSheafFunctor
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.BaseTopologyComparison

/-!
# The comparison of quasi-coherent and adequate modules on a chosen big site

Let `S` be a scheme and let `B` be a chosen big `τ`-site over `S`, for `τ` any of the five
topologies `Zar`, `étale`, `smooth`, `syntomic`, `fppf`. The associated-module functor
`u : 𝓕 ↦ 𝓕^a` and restriction to the small Zariski site `v : 𝓖 ↦ 𝓖|_{S_Zar}` restrict to
functors `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` and `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)`, which are adjoint, with
`Hom_{𝒪_S}(𝓕, v𝓖) = Hom_𝒪(u𝓕, 𝓖)`, and the unit `𝓕 → vu𝓕` is an isomorphism at every
quasi-coherent `𝒪_S`-module. This is [Stacks, Tag 06VN].

## Main definitions

* `Stacks.Adequate.BigSite.associatedModuleFunctor` — `u` on all `𝒪_S`-modules: the pullback of
  sheaves of modules along the morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)` whose
  pushforward is `Stacks.Adequate.BigSite.zariskiRestrictModule`.
* `Stacks.Adequate.BigSite.associatedModuleAdjunction` — the pullback–pushforward adjunction
  between them.
* `Stacks.Adequate.BigSite.associatedModuleAdeq` and `Stacks.Adequate.BigSite.restrictModuleQCoh`
  — **[Stacks, Tag 06VN]**, the functors `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` and
  `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)`.
* `Stacks.Adequate.BigSite.adeqAdjunction` — **[Stacks, Tag 06VN]**, the adjunction `u ⊣ v`.

## Main results

* `Stacks.Adequate.BigSite.exists_baseOverTopology` — the topology of a chosen big `τ`-site over
  `S` is the topology of `τ` on the big fppf category over `S` of a chosen big fppf site with
  the same cutoff.
* `Stacks.Adequate.BigSite.nonempty_associatedModuleFunctor_obj_iso` — the pullback of a
  quasi-coherent `𝒪_S`-module is its associated module `𝓕^a` of [Stacks, Tag 03DU], whose
  sections over `T/S` are `Γ(T, 𝓕|_T)`: Descent, [Stacks, Tag 03FH].
* `Stacks.Adequate.BigSite.isAdequate_associatedModuleFunctor_obj` — `𝓕^a` is adequate,
  [Stacks, Tag 06VK].
* `Stacks.Adequate.BigSite.isIso_associatedModuleAdjunction_unit_app` and
  `Stacks.Adequate.BigSite.isIso_adeqAdjunction_unit_app` — **[Stacks, Tag 06VN]**, the unit
  `𝓕 → vu𝓕` is an isomorphism at a quasi-coherent module.
* `Stacks.Adequate.BigSite.fullyFaithfulAssociatedModuleAdeq` — **[Stacks, Tag 06VN]**,
  `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` is fully faithful, the unit being an isomorphism; its two halves
  are `Stacks.Adequate.BigSite.full_associatedModuleAdeq` and
  `Stacks.Adequate.BigSite.faithful_associatedModuleAdeq`.

## Implementation notes

The chosen big site `B` is its own structure, but its topology is one of the five localized
topologies of a big site of schemes (`Stacks.Adequate.BigSite.exists_eq_ofAmbient`), and that
is the topology of `τ` on the big fppf category over `S` of the chosen big fppf site
`AlgebraicGeometry.bigFppfSiteOfCutoff` with the same cutoff
(`AlgebraicGeometry.overTopology_eq_baseOverTopology`). The two underlying categories are then
the same, `Over ⟨S, _⟩` in the schemes below the cutoff, and so are the structure sheaves of
rings, the inclusions of the small Zariski site and the comparisons of structure sheaves
(`Stacks.Adequate.BigSite.zariskiStructureMap` and
`AlgebraicGeometry.BigFppfOver.baseStructureMap`), up to proofs of propositions. So the
pullback and pushforward of sheaves of modules along `B`'s morphism of ringed sites are,
definitionally, those of `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleAdjunction`, and
each property of a single object proved there for every `τ : AlgebraicGeometry.SiteKind` holds
for `B`: `Stacks.Adequate.BigSite.exists_baseOverTopology` substitutes the topology, after which
the statement *is* the one about the big fppf category.

The functors are defined for `B` itself — the pullback is the left adjoint of
`Stacks.Adequate.BigSite.zariskiRestrictModule` — and only propositions are transported, so
nothing here depends on a choice of big fppf site.

The source writes the adjunction as `𝓗om_{𝒪_S}(𝓕, v𝓖) = 𝓗om_𝒪(u𝓕, 𝓖)`, with sheaf-Hom symbols
on two different sites; what it states is that `u` and `v` are adjoint ("we see that `u` and
`v` are adjoint as follows"), and the global sections of the two sides are the two hom-sets of
the adjunction. The adjunction is `Stacks.Adequate.BigSite.adeqAdjunction`, and its hom-set
bijection is `Stacks.Adequate.BigSite.adeqAdjunction.homEquiv`. The local form of the display,
an identification `𝓗om_{𝒪_S}(𝓕, v𝓖) ≅ v𝓗om_𝒪(u𝓕, 𝓖)` of sheaves on `S_Zar`, is not stated here:
the library's internal Hom of sheaves of modules
(`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor`) takes values in the universe of
the objects of the site, which for the big site is one universe above that of its modules.

The two functors take values in full subcategories: `QCoh(𝒪_S)` is the quasi-coherent
`𝒪_S`-modules, through `AlgebraicGeometry.SheafOfModules.isQuasicoherent`, and `Adeq(𝒪)` is
`Stacks.Adequate.adequate`. The lift of `u` uses [Stacks, Tag 06VK],
`Stacks.Adequate.BigSite.isAdequate_associatedModuleFunctor_obj`, and the lift of `v` uses
[Stacks, Tag 06VM] (1), `Stacks.Adequate.BigSite.isQuasicoherent_zariskiRestrictModule`. The
adjunction between them is the ambient adjunction restricted along the two fully faithful
inclusions, and its unit is invertible because the inclusion of `QCoh(𝒪_S)` reflects
isomorphisms and carries it to the ambient unit.

## References

* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### A chosen big site is a site of the big fppf category -/

/-- **The topology of a chosen big `τ`-site over `S` is the topology of `τ` on the big fppf
category over `S` of a chosen big fppf site with the same cutoff.** The chosen big site is the
localization at `S` of a big `τ`-site, and the topology of that is the topology of `τ` on the
big fppf site `AlgebraicGeometry.bigFppfSiteOfCutoff` with the same cutoff. -/
public theorem BigSite.exists_baseOverTopology (B : BigSite τ S) :
    ∃ (P : BigFppfSite.{u}) (hP : P.Contains S) (_e : P.cutoff = B.cutoff),
      HEq B.topology (BigFppfOver.baseOverTopology P S hP τ.toSiteKind) := by
  obtain ⟨𝒮, hS, rfl⟩ := B.exists_eq_ofAmbient
  exact ⟨bigFppfSiteOfCutoff τ 𝒮, hS, rfl,
    heq_of_eq (overTopology_eq_baseOverTopology τ 𝒮 S hS)⟩

/-! ### The morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)` -/

/-- Abelian presheaves on a chosen big site have a sheafification. -/
public instance BigSite.hasWeakSheafify_addCommGrpCat (B : BigSite τ S) :
    HasWeakSheafify B.topology AddCommGrpCat.{u} :=
  have := B.essentiallySmall_category
  have : HasSheafify B.topology AddCommGrpCat.{u} := hasSheafifyEssentiallySmallSite _ _
  inferInstance

/-- The pushforward of presheaves of modules along the comparison of structure sheaves of a
chosen big site has a left adjoint. -/
public instance BigSite.presheafPushforward_isRightAdjoint (B : BigSite τ S) :
    (PresheafOfModules.pushforward.{u} B.zariskiStructureMap.hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- Restriction of modules to the small Zariski site of `S`, the pushforward along the morphism
of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`, has a left adjoint. -/
public instance BigSite.sheafPushforward_isRightAdjoint (B : BigSite τ S) :
    (SheafOfModules.pushforward.{u} B.zariskiStructureMap).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} B.zariskiStructureMap).isRightAdjoint

/-- **The functor `u : 𝓕 ↦ 𝓕^a` of [Stacks, Tag 06VN] on all `𝒪_S`-modules**: the pullback of
sheaves of modules along the morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`. That this
is the associated module of [Stacks, Tag 03DU] on a quasi-coherent module is
`Stacks.Adequate.BigSite.nonempty_associatedModuleFunctor_obj_iso`. -/
public noncomputable def BigSite.associatedModuleFunctor (B : BigSite τ S) :
    S.Modules ⥤ SheafOfModules.{u} B.structureSheaf :=
  SheafOfModules.pullback.{u} B.zariskiStructureMap

/-- The associated-module functor is left adjoint to restriction to the small Zariski site, the
pushforward along the same morphism of ringed sites, so `Hom_{𝒪_S}(𝓕, v𝓖) = Hom_𝒪(u𝓕, 𝓖)`. -/
public noncomputable def BigSite.associatedModuleAdjunction (B : BigSite τ S) :
    B.associatedModuleFunctor ⊣ B.zariskiRestrictModule :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} B.zariskiStructureMap

/-- A property of a chosen big site holds once it holds for the sites whose topology is the
topology of `τ` on the big fppf category over `S`. -/
private theorem BigSite.induction_baseOverTopology {motive : BigSite τ S → Prop} (B : BigSite τ S)
    (h : ∀ (P : BigFppfSite.{u}) (hP : P.Contains S) isSheaf chosen,
      motive ⟨P.cutoff, hP, BigFppfOver.baseOverTopology P S hP τ.toSiteKind, isSheaf, chosen⟩) :
    motive B := by
  obtain ⟨κ, base_mem, J, isSheaf, chosen⟩ := B
  obtain ⟨P, hP, e, hJ⟩ := BigSite.exists_baseOverTopology ⟨κ, base_mem, J, isSheaf, chosen⟩
  cases e
  obtain rfl := eq_of_heq hJ
  exact h P hP isSheaf chosen

/-- **The unit `𝓕 → vu𝓕` of the associated-module adjunction is an isomorphism at every
quasi-coherent `𝒪_S`-module**, on a chosen big `τ`-site for each of the five topologies. After
`Stacks.Adequate.BigSite.exists_baseOverTopology` substitutes the topology this is
`AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app`. -/
public theorem BigSite.isIso_associatedModuleAdjunction_unit_app (B : BigSite τ S)
    (F : S.Modules) [F.IsQuasicoherent] :
    IsIso (B.associatedModuleAdjunction.unit.app F) := by
  induction B using BigSite.induction_baseOverTopology with | _ P hP _ _ => ?_
  exact BigFppfOver.isIso_baseUnit_app P S hP τ.toSiteKind F

/-- **The pullback of a quasi-coherent `𝒪_S`-module is its associated module `𝓕^a`** of
[Stacks, Tag 03DU], whose sections over `T/S` are the global sections of the pullback of `𝓕` to
`T`. This is the description of `𝓕^a` as a pullback in Descent, [Stacks, Tag 03FH], which
[Stacks, Tag 06VN] invokes. After `Stacks.Adequate.BigSite.exists_baseOverTopology` substitutes
the topology it is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSectionsSheaf`. -/
@[stacks 06VN "`F^a` is the pullback of `F` under the morphism of ringed topoi
`((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)` whose pushforward is restriction to `S_Zar`"]
public theorem BigSite.nonempty_associatedModuleFunctor_obj_iso (B : BigSite τ S)
    (F : S.Modules) [F.IsQuasicoherent] :
    Nonempty (B.associatedModuleFunctor.obj F ≅
      B.associatedModule F (isSheaf_associatedPresheaf B F)) := by
  induction B using BigSite.induction_baseOverTopology with | _ P hP _ _ => ?_
  exact ⟨BigFppfOver.baseAssociatedModuleIsoSectionsSheaf P S hP τ.toSiteKind F⟩

/-! ### Adequacy of the associated module -/

/-- The associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module is a kernel of associated
modules, by the zero map from it to itself. -/
public theorem BigSite.isAssociatedKernel_associatedModule (B : BigSite τ S) (F : S.Modules)
    [F.IsQuasicoherent] :
    IsAssociatedKernel B (B.associatedModule F (isSheaf_associatedPresheaf B F)) :=
  ⟨{ source := F
     target := F
     source_isSheaf := isSheaf_associatedPresheaf B F
     target_isSheaf := isSheaf_associatedPresheaf B F
     hom := 0
     iso := kernelZeroIsoSource.symm }⟩

/-- **The associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module is adequate**,
[Stacks, Tag 06VK] (5) ⇒ (1) with the zero map: read by its sections it is the kernel of the zero
map from it to itself, and adequacy is stable under isomorphism, so it transports to the
pullback along `Stacks.Adequate.BigSite.nonempty_associatedModuleFunctor_obj_iso`. -/
public theorem BigSite.isAdequate_associatedModuleFunctor_obj (B : BigSite τ S) (F : S.Modules)
    [F.IsQuasicoherent] :
    IsAdequate B (B.associatedModuleFunctor.obj F) := by
  obtain ⟨e⟩ := B.nonempty_associatedModuleFunctor_obj_iso F
  exact (adequate.{u, u} B).prop_of_iso e.symm
    (isAdequate_of_isAssociatedKernel B _ (B.isAssociatedKernel_associatedModule F))

/-! ### The functors between `QCoh(𝒪_S)` and `Adeq(𝒪)` -/

/-- The associated-module functor retyped so that its source carries the category instance of
`SheafOfModules.{u} S.ringCatSheaf`, in which the quasi-coherent modules are a full
subcategory. -/
public noncomputable abbrev BigSite.associatedModuleOfSheaf (B : BigSite τ S) :
    SheafOfModules.{u} S.ringCatSheaf ⥤ SheafOfModules.{u} B.structureSheaf :=
  B.associatedModuleFunctor

/-- Restriction to the small Zariski site retyped so that its target carries the category
instance of `SheafOfModules.{u} S.ringCatSheaf`. -/
public noncomputable abbrev BigSite.restrictModuleOfSheaf (B : BigSite τ S) :
    SheafOfModules.{u} B.structureSheaf ⥤ SheafOfModules.{u} S.ringCatSheaf :=
  B.zariskiRestrictModule

/-- The associated-module adjunction between the retyped functors. -/
public noncomputable abbrev BigSite.adjunctionOfSheaf (B : BigSite τ S) :
    B.associatedModuleOfSheaf ⊣ B.restrictModuleOfSheaf :=
  B.associatedModuleAdjunction

/-- Restriction to the small Zariski site of `S` is additive: on underlying presheaves of abelian
groups it is restriction along the opposite of the inclusion of sites. -/
public instance BigSite.additive_restrictModuleOfSheaf (B : BigSite τ S) :
    B.restrictModuleOfSheaf.Additive :=
  Stacks.SheafOfModules.PushforwardRightExact.additive_pushforward B.opensToBig
    B.zariskiStructureMap

/-- Restriction to the small Zariski site of `S` preserves finite limits, being the direct image
of sheaves of modules along a morphism of ringed sites. -/
public instance BigSite.preservesFiniteLimits_restrictModuleOfSheaf (B : BigSite τ S) :
    PreservesFiniteLimits B.restrictModuleOfSheaf :=
  SheafOfModules.preservesFiniteLimits_pushforward B.zariskiStructureMap

/-- The associated-module functor on all sheaves of modules is additive, being a left adjoint
whose right adjoint, restriction to the small Zariski site, is additive. -/
public instance BigSite.additive_associatedModuleOfSheaf (B : BigSite τ S) :
    B.associatedModuleOfSheaf.Additive :=
  B.adjunctionOfSheaf.left_adjoint_additive

/-- The associated-module functor on the quasi-coherent `𝒪_S`-modules, with target the
`𝒪`-modules of the chosen big site. This is the functor of [Stacks, Tag 0GN7]. -/
public noncomputable abbrev BigSite.associatedModuleQcoh (B : BigSite τ S) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} B.structureSheaf :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ B.associatedModuleOfSheaf

/-- The associated module of a quasi-coherent `𝒪_S`-module is adequate, read on the full
subcategory `QCoh(𝒪_S)`: [Stacks, Tag 06VK],
`Stacks.Adequate.BigSite.isAdequate_associatedModuleFunctor_obj`. -/
public theorem BigSite.isAdequate_associatedModuleQcoh_obj (B : BigSite τ S)
    (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    IsAdequate B (B.associatedModuleQcoh.obj M) :=
  have : M.obj.IsQuasicoherent := M.property
  B.isAdequate_associatedModuleFunctor_obj M.obj

/-- The unit of the associated-module adjunction is an isomorphism at every quasi-coherent
module, in the shape the full-faithfulness criteria consume. -/
public theorem BigSite.isIso_adjunctionOfSheaf_unit_app (B : BigSite τ S)
    (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    IsIso (B.adjunctionOfSheaf.unit.app M.obj) := by
  have : M.obj.IsQuasicoherent := M.property
  exact B.isIso_associatedModuleAdjunction_unit_app M.obj

/-- The associated-module functor is full on quasi-coherent modules, by [Stacks, Tag 0GN7]: the
unit of the adjunction is an isomorphism there. -/
public theorem BigSite.full_associatedModuleQcoh (B : BigSite τ S) :
    B.associatedModuleQcoh.Full :=
  B.adjunctionOfSheaf.full_comp_L_of_isIso_unit_app
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (ObjectProperty.full_ι _)
    B.isIso_adjunctionOfSheaf_unit_app

/-- The associated-module functor is faithful on quasi-coherent modules, by
[Stacks, Tag 0GN7]. -/
public theorem BigSite.faithful_associatedModuleQcoh (B : BigSite τ S) :
    B.associatedModuleQcoh.Faithful :=
  B.adjunctionOfSheaf.faithful_comp_L_of_mono_unit_app
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (ObjectProperty.faithful_ι _) fun M => by
      have := B.isIso_adjunctionOfSheaf_unit_app M
      exact inferInstanceAs (Mono (B.adjunctionOfSheaf.unit.app M.obj))

/-- **[Stacks, Tag 06VN], the functor `u`.** The associated-module functor
`u : QCoh(𝒪_S) ⥤ Adeq(𝒪)`, `𝓕 ↦ 𝓕^a`, on a chosen big `τ`-site over `S`; it lands in the
adequate modules by [Stacks, Tag 06VK]. -/
@[stacks 06VN "the functor `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)`, `F ↦ F^a`"]
public noncomputable abbrev BigSite.associatedModuleAdeq (B : BigSite τ S) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (adequate.{u, u} B).FullSubcategory :=
  (adequate.{u, u} B).lift B.associatedModuleQcoh B.isAdequate_associatedModuleQcoh_obj

/-- **[Stacks, Tag 06VN], the functor `v`.** Restriction to the small Zariski site of `S` as a
functor `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)`, `𝓖 ↦ 𝓖|_{S_Zar}`, on a chosen big `τ`-site over `S`; it
lands in the quasi-coherent modules by [Stacks, Tag 06VM] (1). -/
@[stacks 06VN "the functor `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)`, `G ↦ G|_{S_Zar}`"]
public noncomputable abbrev BigSite.restrictModuleQCoh (B : BigSite τ S) :
    (adequate.{u, u} B).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).lift
    ((adequate.{u, u} B).ι ⋙ B.restrictModuleOfSheaf)
    fun G => B.isQuasicoherent_zariskiRestrictModule G.obj G.property

/-- **`u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` is additive.** It is the additive functor
`Stacks.Adequate.BigSite.associatedModuleQcoh` lifted to the adequate modules, and additivity
descends along the faithful inclusion of a full subcategory. -/
public instance BigSite.additive_associatedModuleAdeq (B : BigSite τ S) :
    B.associatedModuleAdeq.Additive :=
  letI : (B.associatedModuleAdeq ⋙ (adequate.{u, u} B).ι).Additive :=
    Functor.additive_of_iso
      (((adequate.{u, u} B).liftCompιIso B.associatedModuleQcoh
        B.isAdequate_associatedModuleQcoh_obj).symm)
  Functor.additive_of_comp_faithful _ (adequate.{u, u} B).ι

/-- `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` is full: it is the fully faithful functor of
[Stacks, Tag 0GN7] lifted to the adequate modules. -/
public theorem BigSite.full_associatedModuleAdeq (B : BigSite τ S) :
    B.associatedModuleAdeq.Full := by
  have := B.full_associatedModuleQcoh
  exact Functor.Full.of_comp_faithful_iso
    ((adequate.{u, u} B).liftCompιIso B.associatedModuleQcoh
      B.isAdequate_associatedModuleQcoh_obj)

/-- `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` is faithful, by the same lift of [Stacks, Tag 0GN7]. -/
public theorem BigSite.faithful_associatedModuleAdeq (B : BigSite τ S) :
    B.associatedModuleAdeq.Faithful := by
  have := B.faithful_associatedModuleQcoh
  exact Functor.Faithful.of_comp_iso
    ((adequate.{u, u} B).liftCompιIso B.associatedModuleQcoh
      B.isAdequate_associatedModuleQcoh_obj)

/-- **[Stacks, Tag 06VN], the adjunction.** On a chosen big `τ`-site over `S`, for each of the
five topologies, the associated-module functor `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` is left adjoint to
restriction `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)`, so `Hom_{𝒪_S}(𝓕, v𝓖) = Hom_𝒪(u𝓕, 𝓖)`
(`Stacks.Adequate.BigSite.adeqAdjunction.homEquiv`). It is the pullback–pushforward adjunction
of the morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`, restricted to the two full
subcategories. -/
@[stacks 06VN "the adjunction `u ⊣ v` between `QCoh(𝒪_S)` and `Adeq(𝒪)`, whose hom-set
bijection is `Hom_{𝒪_S}(F, vG) = Hom_𝒪(uF, G)`"]
public noncomputable def BigSite.adeqAdjunction (B : BigSite τ S) :
    B.associatedModuleAdeq ⊣ B.restrictModuleQCoh :=
  Adjunction.restrictFullyFaithful B.adjunctionOfSheaf
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).fullyFaithfulι
    (adequate.{u, u} B).fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- **[Stacks, Tag 06VN], the unit.** The unit `𝓕 → vu𝓕` of the adjunction between
`QCoh(𝒪_S)` and `Adeq(𝒪)` is an isomorphism at every quasi-coherent `𝒪_S`-module, on a chosen
big `τ`-site over `S` for each of the five topologies. -/
@[stacks 06VN "the map `F → vuF` is an isomorphism for every `F` in `QCoh(𝒪_S)`"]
public theorem BigSite.isIso_adeqAdjunction_unit_app (B : BigSite τ S)
    (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    IsIso (B.adeqAdjunction.unit.app M) := by
  have key : (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map
      (B.adeqAdjunction.unit.app M) = B.adjunctionOfSheaf.unit.app M.obj := by
    have h := Adjunction.map_restrictFullyFaithful_unit_app B.adjunctionOfSheaf
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).fullyFaithfulι
      (adequate.{u, u} B).fullyFaithfulι
      (L := B.associatedModuleAdeq) (R := B.restrictModuleQCoh) (Iso.refl _) (Iso.refl _) M
    simp only [Iso.refl_hom, NatTrans.id_app] at h
    exact h
  have h : IsIso ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map
      (B.adeqAdjunction.unit.app M)) := by
    rw [key]
    exact B.isIso_adjunctionOfSheaf_unit_app M
  exact isIso_of_reflects_iso _ (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι

/-- **[Stacks, Tag 06VN], consequence of the unit.** `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` is fully
faithful, on a chosen big `τ`-site over `S` for each of the five topologies: the unit
`𝓕 → vu𝓕` of the adjunction `u ⊣ v` is an isomorphism at every object of `QCoh(𝒪_S)`
(`Stacks.Adequate.BigSite.isIso_adeqAdjunction_unit_app`). -/
@[stacks 06VN "consequence of `F → vuF` being an isomorphism: `u : QCoh(𝒪_S) ⥤ Adeq(𝒪)` is fully
faithful"]
public noncomputable def BigSite.fullyFaithfulAssociatedModuleAdeq (B : BigSite τ S) :
    B.associatedModuleAdeq.FullyFaithful :=
  haveI : ∀ M, IsIso (B.adeqAdjunction.unit.app M) := B.isIso_adeqAdjunction_unit_app
  haveI : IsIso B.adeqAdjunction.unit := NatIso.isIso_of_isIso_app _
  B.adeqAdjunction.fullyFaithfulLOfIsIsoUnit

end Stacks.Adequate

end
