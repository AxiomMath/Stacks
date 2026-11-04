module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEquivalencePresentationReduction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseMemberLocalStep
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EssentialImage
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullOnFree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.MemberLocalStep
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteFiniteLocallyFreeAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteLocalGenerationFinitenessAgreement

/-!
# Descent, Lemma 05VG for Modules on Sites, Definition 03DL (7) at the big site

Descent, Lemma 05VG compares the properties of Modules on Sites, Definitions 03DE, 03DL and
03ER across the comparison functors `𝓗 ↦ 𝓗ᵃ` of Descent, Proposition 03DX.  This file settles
the clause of Definition 03DL (7), **finite presentation**, at the five big sites `(Sch/S)_τ`
for `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`:

    `𝓗` is of finite presentation on `S_Zar`  ↔  `𝓗ᵃ` is of finite presentation on `(Sch/S)_τ`,

for a quasi-coherent `𝒪_S`-module `𝓗`, which is
`AlgebraicGeometry.BigFppfOver.isFinitePresentation_baseAssociatedModule_iff`.  The two small
sites are already in the library:
`AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff` and
`AlgebraicGeometry.SmallZariski.isFinitePresentation_iff_associatedModule`.

## The two halves

**The forward half carries no quasi-coherence and no descent.**  Finite presentation of `𝓗` is a
Zariski covering of `S` together with a *finite* presentation of `𝓗|_V` on each member, and
Stacks 03DV, available at every `τ` as
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentDataAssociatedModule`, carries such data to
quasi-coherent data for `𝓗ᵃ` on the image of the same covering.  The transport is along the
associated-module functor of the localized site, which preserves finite colimits and fixes the
unit object, so it leaves the two index types of a presentation untouched; that is the content of
`AlgebraicGeometry.BigFppfOver.isFinite_baseFinitePresentationAssociatedModuleOver`, and it is
all the forward half needs.

**The reverse half is fpqc descent on `S`**, and it is confined to `τ = fppf` exactly as the
reverse half of clause 03DL (2) is in `…/BigSiteFiniteLocallyFreeAgreement.lean`: the
`τ`-analogue of Stacks 03DV functorial in an arbitrary object exists only at `τ = fppf`
(`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`), and the four coarser
topologies are carried up to fppf by a monotonicity.

At `τ = fppf` the route is the source's own.  Finite presentation of `𝓗ᵃ` gives, by Stacks 03DN
(`Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations`), a family
`X : I → (Sch/S)_fppf` covering the final object together with a finite *global* presentation of
`(𝓗ᵃ)|_{X i}` for each `i`.  The members of such a family are arbitrary schemes over `S`, so
`AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement` refines it, unconditionally, to
a family `Y` whose structure morphisms *are* an fpqc covering family of `S`, each member mapping
into a member of `X`; a finite presentation survives that refinement because it restricts along
any arrow of the site
(`Stacks.SheafOfModules.LocalCokernel.exists_finitePresentation_overMap`).  On each `Y j`, with
`X_j` its scheme and `f_j : X_j ⟶ S` its structure morphism, the reindexing of Stacks 06WI and
Stacks 03DV functorial in the object turn the presentation into a finite global presentation of
`(f_j^*𝓗)ᵃ`, which
`AlgebraicGeometry.BigFppfOver.isFinitePresentation_of_presentation_baseAssociatedModule`
reflects to finite presentation of `f_j^*𝓗` on `X_j`; Stacks 05B0,
`AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`, descends the conclusion to `S`.

## The reflection step

The reflection step is where full faithfulness of `𝓗 ↦ 𝓗ᵃ` on the quasi-coherent modules
(Stacks 0GN7, available at every `τ` as
`AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`) is used, and it is why
quasi-coherence appears in the reverse half and not in the forward one.  A finite global
presentation of `𝓗ᵃ` presents it as a cokernel of a morphism of free modules on two finite index
types; that morphism comes from one of free `𝒪_S`-modules on the same index types by
`AlgebraicGeometry.BigFppfOver.baseIsFullOnFree`, its cokernel downstairs is
quasi-coherent, and full faithfulness identifies that cokernel with `𝓗`.  The tautological
presentation of the cokernel has the two given finite index types, so `𝓗` is of finite
presentation by `Stacks.SheafOfModules.SliceFinite.isFinitePresentation_of_presentation`.

## The monotonicity

`Stacks.SheafOfModules.isFinitePresentation_of_comparisonPushforward` is the analogue for
clause 03DL (7) of `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_comparisonPushforward`:
for `K ≤ J` two topologies on one category, a sheaf of modules for `J` whose reading for `K` is
of finite presentation is of finite presentation.  It is *not* proved by the full-faithfulness
trick that serves finite freeness — a presentation is a cokernel, not a cofan of copies of the
structure sheaf, and `Stacks.Sheaves.GlobalTypeComparison.isColimitCofanOfMap` has nothing to say
about it.  Instead the *left* adjoint `Stacks.SheafOfModules.comparisonPullback`, sheafification
for the finer topology, is applied to the `K`-presentation: it preserves finite colimits, and it
fixes both the structure sheaf and the module, both of which are `J`-sheaves already
(`Stacks.SheafOfModules.comparisonPullbackUnitIso` and
`…comparisonPullbackObjIso`).  This is the route of
`Stacks.SheafOfModules.hasGlobalPresentation_of_le`, and of the clauses 03DL (4) and 03DL (5)
in `…/BigSiteLocalGenerationFinitenessAgreement.lean`, with the two index types tracked so that
a *finite* presentation comes back finite.

## Main results

* `Stacks.SheafOfModules.exists_finitePresentation_of_comparisonPushforward`: sheafification for
  the finer topology carries a finite global presentation for the coarser topology to one for the
  finer.
* `Stacks.SheafOfModules.isFinitePresentation_of_comparisonPushforward`: **finite presentation
  for a coarser topology implies finite presentation for a finer one**, for an arbitrary pair of
  topologies on one category and with no further hypothesis.
* `AlgebraicGeometry.BigFppfOver.baseFinitePresentationAssociatedModuleOver` and
  `…isFinite_baseFinitePresentationAssociatedModuleOver`: the transport of Stacks 03DV to a
  member of the covering leaves a finite presentation finite.
* `…isFinitePresentation_baseAssociatedModule_of_isFinitePresentation`: the forward half, at
  every `τ`, with no quasi-coherence hypothesis.
* `AlgebraicGeometry.BigFppfOver.isFinitePresentation_of_presentation_baseAssociatedModule`: the
  reflection step, at every `τ`.
* `AlgebraicGeometry.BigFppfOver.isFinitePresentation_of_associatedModule`: **the descent
  direction of 05VG for 03DL (7) at the big fppf site.**
* `AlgebraicGeometry.BigFppfOver.isFinitePresentation_baseAssociatedModule_iff`:
  **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (7), at the big site `(Sch/S)_τ`
  for every `τ`, as an equivalence.**

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

section OfLe

variable {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : K ≤ J)
  (R : Sheaf J RingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A finite global presentation for a coarser topology gives one for a finer topology.**
Sheafification for `J` carries the two free modules and the cokernel of the `K`-presentation to
colimits of `J`-sheaves, leaving the two index types untouched, and it fixes both the structure
sheaf and the module, both of which are `J`-sheaves already.

This is the finite refinement of `Stacks.SheafOfModules.hasGlobalPresentation_of_le`. -/
public theorem exists_finitePresentation_of_comparisonPushforward
    [HasSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    (M : _root_.SheafOfModules.{w} R)
    (P : ((comparisonPushforward.{u, v, w, w} h R).obj M).Presentation) (hP : P.IsFinite) :
    ∃ Q : M.Presentation, Q.IsFinite := by
  let := hP
  let : PreservesColimitsOfSize.{w, w} (comparisonPullback.{u, v, w, w} h R) :=
    preservesColimitsOfSize_comparisonPullback.{u, v, w, w} h R
  let : PreservesColimitsOfSize.{0, 0} (comparisonPullback.{u, v, w, w} h R) :=
    preservesColimitsOfSize_shrink _
  let : PreservesFiniteColimits (comparisonPullback.{u, v, w, w} h R) := inferInstance
  let : (LocalCokernel.mapFinitePresentation P (comparisonPullback.{u, v, w, w} h R)
      (comparisonPullbackUnitIso h R).symm).IsFinite :=
    LocalCokernel.mapFinitePresentation_isFinite P _ _
  exact ⟨(LocalCokernel.mapFinitePresentation P (comparisonPullback.{u, v, w, w} h R)
    (comparisonPullbackUnitIso h R).symm).ofIsIso
      (comparisonPullbackObjIso.{u, v, w, w} h R M).hom, inferInstance⟩

/-- **Finite presentation for a coarser topology implies finite presentation for a finer one.**
For `K ≤ J` two topologies on one category and `M` a sheaf of modules for `J`: if the reading of
`M` for `K` is of finite presentation on `(C, K)`, then `M` is of finite presentation on
`(C, J)`.

Both ingredients are free of hypotheses.  A `K`-covering family of the final object is a
`J`-covering family of it, since `K ≤ J`; and on each member a finite global presentation of the
reading of the restriction upgrades to one of the restriction itself by
`Stacks.SheafOfModules.exists_finitePresentation_of_comparisonPushforward` at the slice
topologies (`Stacks.SheafOfModules.over_le_over_of_le`).  The two readings of the restriction are
literally the same sheaf of modules: restriction to a slice site changes only the underlying
presheaf's index category, not the sheaf condition being asserted.

This is the monotonicity that confines the mathematics of clause 03DL (7) of Descent, Lemma 05VG
at the big sites to one topology; it carries no `stacks` attribute, being one implication of a
clause whose equivalence is
`AlgebraicGeometry.BigFppfOver.isFinitePresentation_baseAssociatedModule_iff`. -/
public theorem isFinitePresentation_of_comparisonPushforward
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : C, HasWeakSheafify (K.over U) AddCommGrpCat.{w}]
    [∀ U : C, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : _root_.SheafOfModules.{w} R)
    (hM : ((comparisonPushforward.{u, v, w, w} h R).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  obtain ⟨I, V, hcov, hP⟩ :=
    (isFinitePresentation_iff_exists_cover_finite_presentations
      ((comparisonPushforward.{u, v, w, w} h R).obj M)).1 hM
  refine (isFinitePresentation_iff_exists_cover_finite_presentations M).2
    ⟨I, V, fun U => h _ (hcov U), fun i => ?_⟩
  obtain ⟨P, hPfin⟩ := hP i
  let : HasSheafify (J.over (V i)) AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : HasSheafify (K.over (V i)) AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  exact exists_finitePresentation_of_comparisonPushforward (over_le_over_of_le h (V i))
    (R.over (V i)) (M.over (V i)) P hPfin

end OfLe

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The transport of Stacks 03DV to a member of the covering, keeping a presentation finite.**
A finite presentation of the restriction of an `𝒪_S`-module `𝓗` to an open `V` of `S` gives a
finite presentation of the restriction of `𝓗ᵃ` to the localization of `(Sch/S)_τ` at `V`.

The two transports are those of
`AlgebraicGeometry.BigFppfOver.basePresentationAssociatedModuleOver`, the associated-module
functor of the localized site and the identification `(𝓗|_V)ᵃ ≅ (𝓗ᵃ)|_{(Sch/V)_τ}`; here they
are taken through `Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation`, whose index types
of generators and of relations are the given ones on the nose, so that finiteness is
`Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation_isFinite`. -/
public noncomputable def baseFinitePresentationAssociatedModuleOver (τ : SiteKind) (V : S.Opens)
    {𝓗 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓗 V).Presentation) [P.IsFinite] :
    (((baseAssociatedModule B S hS τ).obj 𝓗).over
      ((opensToBig B S hS).obj V)).Presentation :=
  (Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation P
      (SheafOfModules.pullback.{u} (baseSliceStructureMap B S hS τ V))
      (asIso (SheafOfModules.pullbackObjUnitToUnit.{u}
        (baseSliceStructureMap B S hS τ V))).symm).ofIsIso
    (baseAssociatedModuleOverObjIso B S hS τ V 𝓗).hom

/-- The presentation of `AlgebraicGeometry.BigFppfOver.baseFinitePresentationAssociatedModuleOver`
is finite: both transports preserve the index types of generators and relations. -/
public instance isFinite_baseFinitePresentationAssociatedModuleOver (τ : SiteKind) (V : S.Opens)
    {𝓗 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓗 V).Presentation) [P.IsFinite] :
    (baseFinitePresentationAssociatedModuleOver B S hS τ V P).IsFinite :=
  letI := Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation_isFinite P
    (SheafOfModules.pullback.{u} (baseSliceStructureMap B S hS τ V))
    (asIso (SheafOfModules.pullbackObjUnitToUnit.{u}
      (baseSliceStructureMap B S hS τ V))).symm
  inferInstanceAs ((Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation P
      (SheafOfModules.pullback.{u} (baseSliceStructureMap B S hS τ V))
      (asIso (SheafOfModules.pullbackObjUnitToUnit.{u}
        (baseSliceStructureMap B S hS τ V))).symm).ofIsIso
    (baseAssociatedModuleOverObjIso B S hS τ V 𝓗).hom).IsFinite

/-- **The forward half of Descent, Lemma 05VG for Modules on Sites, Definition 03DL (7) at the
big site `(Sch/S)_τ`, at every `τ`.**  The associated module `𝓗ᵃ` of an `𝒪_S`-module `𝓗` of
finite presentation is an `𝒪`-module of finite presentation on `(Sch/S)_τ`.

No quasi-coherence is needed: finite presentation of `𝓗` already supplies the quasi-coherent
data, and Stacks 03DV carries it to `(Sch/S)_τ` with the two index types of each presentation
unchanged.

The reverse implication, which is what makes 05VG an equivalence for this clause, is not proved
here. -/
public theorem isFinitePresentation_baseAssociatedModule_of_isFinitePresentation (τ : SiteKind)
    (𝓗 : S.Modules) (h : SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf) 𝓗) :
    ((baseAssociatedModule B S hS τ).obj 𝓗).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := h.exists_quasicoherentData
  have hqf : ∀ i, (q.presentation i).IsFinite := hq.isFinite_presentation
  refine ⟨{ I := ULift.{u + 1} q.I
            X := fun i => (opensToBig B S hS).obj (q.X i.down)
            coversTop := coversTop_baseOpensToBig_ulift B S hS τ q.X q.coversTop
            presentation := fun i =>
              baseFinitePresentationAssociatedModuleOver B S hS τ (q.X i.down)
                (q.presentation i.down) }, ⟨fun i => ?_⟩⟩
  exact isFinite_baseFinitePresentationAssociatedModuleOver B S hS τ (q.X i.down)
    (q.presentation i.down)

/-- **A finite global presentation of `𝓗ᵃ` is reflected to one of `𝓗`, at every `τ`.**  Let `𝓗`
be a quasi-coherent `𝒪_S`-module whose associated module on `(Sch/S)_τ` is the cokernel of a
morphism between free modules on finite index types.  Then `𝓗` is of finite presentation.

The morphism of free modules on `(Sch/S)_τ` comes from a morphism `β` of free `𝒪_S`-modules on
the same two index types, by fullness of `𝓗 ↦ 𝓗ᵃ` on free modules
(`AlgebraicGeometry.BigFppfOver.baseIsFullOnFree`).  The associated module of
`coker β` is then the given cokernel, by
`SheafOfModules.nonempty_iso_pullbackObj_cokernel_free`, hence is isomorphic to `𝓗ᵃ`; both
`coker β` and `𝓗` are quasi-coherent, so full faithfulness of `𝓗 ↦ 𝓗ᵃ` on the quasi-coherent
modules (Stacks 0GN7,
`AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`) turns that into an
isomorphism `coker β ≅ 𝓗` downstairs.  The tautological presentation of `coker β` has the two
given finite index types, and transports along it. -/
public theorem isFinitePresentation_of_presentation_baseAssociatedModule (τ : SiteKind)
    (𝓗 : S.Modules) (h𝓗 : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓗)
    {G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (e : G ≅ (baseAssociatedModule B S hS τ).obj 𝓗)
    (P₀ : G.Presentation) (hP₀ : P₀.IsFinite) :
    SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf) 𝓗 := by
  let := hP₀
  obtain ⟨P, hP⟩ : ∃ P : ((baseAssociatedModule B S hS τ).obj 𝓗).Presentation, P.IsFinite :=
    ⟨P₀.ofIsIso e.hom, inferInstance⟩
  let := hP
  let := h𝓗
  let : HasSheafify (baseOverTopology B S hS τ) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : (SheafOfModules.free (R := S.ringCatSheaf) P.relations.I).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free P.relations.I
  let : (SheafOfModules.free (R := S.ringCatSheaf) P.generators.I).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free P.generators.I
  set α : SheafOfModules.free
        (R := FibredSite.baseRingStructureSheaf B S hS τ) P.relations.I ⟶
      SheafOfModules.free P.generators.I :=
    (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π with hα
  have hπ : α ≫ P.generators.π = 0 := by simp [hα]
  have hc : IsColimit (CokernelCofork.ofπ P.generators.π hπ) := P.isColimit
  obtain ⟨β, hβ⟩ := baseIsFullOnFree B S hS τ _ _
    ((SheafOfModules.pullbackObjFreeIso (baseStructureMap B S hS τ) P.relations.I).hom ≫ α ≫
      (SheafOfModules.pullbackObjFreeIso (baseStructureMap B S hS τ) P.generators.I).inv)
  have hQ : (cokernel β).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel (X := S) β
  obtain ⟨e⟩ := SheafOfModules.nonempty_iso_pullbackObj_cokernel_free
    (baseStructureMap B S hS τ) α β hβ hπ hc
  let e' : (⟨cokernel β, hQ⟩ :
        (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) ≅ ⟨𝓗, h𝓗⟩ :=
    (fullyFaithfulBaseAssociatedModuleQcoh B S hS τ).preimageIso e
  let Pc : (cokernel β).Presentation :=
    SheafOfModules.presentationOfIsCokernelFree β (cokernel.π β) (cokernel.condition β)
      (cokernelIsCokernel β)
  let Pc' := Pc.ofIsIso ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.mapIso e').hom
  have : Pc'.IsFinite :=
    ⟨⟨inferInstanceAs (Finite P.generators.I)⟩, ⟨inferInstanceAs (Finite P.relations.I)⟩⟩
  exact Stacks.SheafOfModules.SliceFinite.isFinitePresentation_of_presentation Pc'

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (7): the descent direction, at
the big fppf site.**  If the associated module `𝓗ᵃ` of a quasi-coherent `𝒪_S`-module is of finite
presentation as an `𝒪`-module on `(Sch/S)_fppf`, then `𝓗` is of finite presentation on the small
Zariski site of `S`.

This is the half of the clause that carries the mathematics, and it is the source's own argument.
Stacks 03DN produces a family covering the final object of `(Sch/S)_fppf` on whose members `𝓗ᵃ`
has a finite global presentation; its members are arbitrary schemes over `S`, so
`AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement` refines it to one whose
structure morphisms are an fpqc covering family of `S`, and the presentation follows the
refinement because it restricts along every arrow of the site
(`Stacks.SheafOfModules.LocalCokernel.exists_finitePresentation_overMap`).  On each member the
reindexing of Stacks 06WI (`AlgebraicGeometry.BigFppfOver.objRestrictEquivalence`) and Stacks
03DV functorial in the object
(`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`) turn the verdict into a
finite global presentation of `(f_j^*𝓗)ᵃ`, which
`AlgebraicGeometry.BigFppfOver.isFinitePresentation_of_presentation_baseAssociatedModule`
reflects; Stacks 05B0 descends the conclusion to `S`.

No `stacks` attribute: this is one implication, and the equivalence is
`AlgebraicGeometry.BigFppfOver.isFinitePresentation_baseAssociatedModule_iff`. -/
public theorem isFinitePresentation_of_associatedModule (𝓗 : S.Modules)
    [h𝓗 : 𝓗.IsQuasicoherent]
    (h : ((associatedModule B S hS).obj 𝓗).IsFinitePresentation) :
    SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf) 𝓗 := by
  classical
  obtain ⟨I, X, hX, hP⟩ :=
    (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations
      ((associatedModule B S hS).obj 𝓗)).1 h
  obtain ⟨I', Y, hY, hfpqc, hre⟩ := exists_coversTop_fpqc_refinement B S hS X hX
  let 𝒰 : S.Cover.{u + 1} Scheme.fpqcPrecoverage := ⟨objHypercover B S hS Y, hfpqc⟩
  refine AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover 𝓗 𝒰 fun j => ?_
  obtain ⟨i, ⟨g⟩⟩ := hre j
  obtain ⟨P, hPfin⟩ := hP i
  let := hPfin
  let : HasSheafify (topology B S hS) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : HasSheafify (topology B (objScheme B S hS (Y j))
      (contains_objScheme B S hS (Y j))) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let : (objRestrictFunctor B S hS (Y j)).IsEquivalence :=
    inferInstanceAs ((objRestrictEquivalence B S hS (Y j)).functor.IsEquivalence)
  obtain ⟨Q, hQ⟩ := Stacks.SheafOfModules.LocalCokernel.exists_finitePresentation_overMap
    ((associatedModule B S hS).obj 𝓗) g P
  let := hQ
  have hf : (𝒰.f j) = objHom B S hS (Y j) := rfl
  rw [hf]
  have hqc : ((Scheme.Modules.pullback (objHom B S hS (Y j))).obj 𝓗).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (objHom B S hS (Y j)) 𝓗 h𝓗
  exact isFinitePresentation_of_presentation_baseAssociatedModule B
    (objScheme B S hS (Y j)) (contains_objScheme B S hS (Y j)) .fppf
    ((Scheme.Modules.pullback (objHom B S hS (Y j))).obj 𝓗) hqc
    ((associatedModuleObjRestrictNatIso B S hS (Y j)).app 𝓗).symm
    (Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation Q
      (objRestrictFunctor B S hS (Y j)) (Iso.refl _))
    (Stacks.SheafOfModules.LocalCokernel.mapFinitePresentation_isFinite Q
      (objRestrictFunctor B S hS (Y j)) (Iso.refl _))

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (7), on the big site, as an
equivalence.**  A quasi-coherent `𝒪_S`-module `𝓗` is of finite presentation on the small Zariski
site of `S` if and only if `𝓗ᵃ` is of finite presentation as an `𝒪`-module on `(Sch/S)_τ`, for
every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.

The forward half is
`AlgebraicGeometry.BigFppfOver.isFinitePresentation_baseAssociatedModule_of_isFinitePresentation`,
proved at every `τ` and needing no quasi-coherence.  The reverse half is proved at `τ = fppf` by
`AlgebraicGeometry.BigFppfOver.isFinitePresentation_of_associatedModule`, and carried to the four
coarser topologies by the monotonicity
`Stacks.SheafOfModules.isFinitePresentation_of_comparisonPushforward` through the key to
Stacks 0GNE, `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso`, which exhibits
`𝓗ᵃ` on `(Sch/S)_τ` as `𝓗ᵃ` on `(Sch/S)_fppf` read for the coarser topology.

The clause string records the scope: this is clause 03DL (7) of 05VG, at the **big** site
`(Sch/S)_τ` and at every `τ`.  The small sites are
`AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff` and
`AlgebraicGeometry.SmallZariski.isFinitePresentation_iff_associatedModule`. -/
@[stacks 05VG "finite presentation (03DL (7)), big site (Sch/S)_τ at every τ, at the \
comparison functor of 03DX itself"]
public theorem isFinitePresentation_baseAssociatedModule_iff (τ : SiteKind) (𝓗 : S.Modules)
    [h𝓗 : 𝓗.IsQuasicoherent] :
    SheafOfModules.IsFinitePresentation (R := S.ringCatSheaf) 𝓗 ↔
      ((baseAssociatedModule B S hS τ).obj 𝓗).IsFinitePresentation := by
  refine ⟨isFinitePresentation_baseAssociatedModule_of_isFinitePresentation B S hS τ 𝓗,
    fun h => ?_⟩
  refine isFinitePresentation_of_associatedModule B S hS 𝓗
    (Stacks.SheafOfModules.isFinitePresentation_of_comparisonPushforward
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)
      ((associatedModule B S hS).obj 𝓗) ?_)
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    (restrictTopologyAssociatedModuleIso B S hS τ 𝓗).symm h

end AlgebraicGeometry.BigFppfOver

end
