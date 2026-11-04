module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteTypeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.Coherent

/-!
# Coherent modules on a scheme and on the algebraic space it represents

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`.  Descent,
Proposition 03DX (2) at `τ = étale`, read across the identification of the small étale site of
`T` with the small étale site of the algebraic space `yoneda.obj U`, is the equivalence

`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence :
  QCoh(𝒪_T) ≌ QCoh(yoneda.obj U)`.

This file restricts it to the **coherent** modules: when `T` is locally Noetherian, a
quasi-coherent `𝒪_T`-module is coherent (Stacks 01BV) exactly when the module it becomes on the
small étale site of `yoneda.obj U` is coherent in the sense of Stacks 07UA, and the equivalence
cuts down to an equivalence `Coh(𝒪_T) ≌ Coh(yoneda.obj U)`.  This is the form in which a
statement about coherent modules on a locally Noetherian *scheme* — Stacks 0882, 0885, 088C,
0889 — is read on the algebraic space the scheme represents, in particular on an étale scheme
chart of an algebraic space (`AlgebraicGeometry.Space.chartSpace_eq_yoneda`).

## Main definitions

* `AlgebraicGeometry.Space.coherentToQuasicoherent`: the inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` of
  the coherent modules of a scheme into its quasi-coherent ones.
* `AlgebraicGeometry.Space.representedCoherentSchemeFunctor`: the comparison
  `Coh(𝒪_T) ⥤ Coh(yoneda.obj U)`; on underlying modules it is the functor of
  `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, on the nose.
* `AlgebraicGeometry.Space.representedCoherentSchemeEquivalence`: **the equivalence
  `Coh(𝒪_T) ≌ Coh(yoneda.obj U)`** for a locally Noetherian `T`.

## Main results

* `AlgebraicGeometry.Space.hasEtaleLocalProperty_yoneda_isLocallyNoetherian`: the algebraic space
  represented by a locally Noetherian scheme is locally Noetherian, in the form
  (`HasEtaleLocalProperty`) the coherence theory of algebraic spaces asks for.
* `AlgebraicGeometry.Space.isCoherent_representedQuasicoherentSchemeEquivalence_iff`: **coherence
  is invariant under the comparison**: for `T` locally Noetherian and `𝓕` quasi-coherent on `T`,
  `𝓕^a` is a coherent module on `yoneda.obj U` iff `𝓕` is a coherent `𝒪_T`-module.
* `AlgebraicGeometry.Space.fullyFaithfulRepresentedCoherentSchemeFunctor` and
  `AlgebraicGeometry.Space.essSurj_representedCoherentSchemeFunctor`: the comparison is fully
  faithful and essentially surjective.

## Related results

Here `U` is an object of the big fppf site over `S` with scheme `T`.

* **Quasi-coherent modules.** `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`
  and `AlgebraicGeometry.Space.representedQuasicoherentSheavesEquivalence`:
  `QCoh(𝒪_T) ≌ QCoh(yoneda.obj U)`; its functor is `AlgebraicGeometry.SmallEtale.associatedModule`
  followed by `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, by `rfl`
  (`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence_functor_obj_obj`).
  On a chart `V` of an algebraic space `X`, `AlgebraicGeometry.Space.chartSchemeModule` and
  `AlgebraicGeometry.Space.chartRestrictionSheaf` restrict a quasi-coherent `𝒪_X`-module to a
  quasi-coherent module on the chart's scheme.
* **Finite type and finite presentation.**
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence` and
  `AlgebraicGeometry.Space.isFinitePresentation_representedSmallEtaleModule_iff`.
* **Pullback along a morphism of schemes.**
  `AlgebraicGeometry.Space.representedQuasicoherentSchemePullbackIso` and
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`: the inverse image along
  `yoneda.map g` of the module a quasi-coherent `𝒪_T`-module becomes is the module its Zariski
  pullback becomes.
* **Pushforward along a morphism of schemes.**
  `AlgebraicGeometry.Space.representedModulePushforwardSquareIso` and
  `AlgebraicGeometry.Space.representedModulePushforwardObjIso`: the direct image along
  `yoneda.map g` is the small étale direct image of the morphism of schemes; for an affine
  morphism the small étale direct image of `𝓕^a` is `(g_*𝓕)^a`,
  `AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`, and likewise for a quasi-compact
  quasi-separated one.
* **Global sections and cohomology.** `AlgebraicGeometry.Space.representedGlobalSectionsIso` and
  `AlgebraicGeometry.Space.representedCohomologyAssociatedModuleIso`:
  `Hⁿ(yoneda.obj U, 𝓕^a) ≅ Hⁿ(T, 𝓕)`, linearly, in every degree (Stacks 03DW on the small étale
  site, carried to the represented space).
* **Restriction to the scheme, adic systems and completion.** The right adjoint
  `AlgebraicGeometry.Space.representedRestrictModule` of the transport, the restriction of
  coherent adic systems `AlgebraicGeometry.Space.representedRestrictAdic`, the comparison of
  completions `AlgebraicGeometry.Space.representedRestrictCompletionIso`, and the transfer of
  Grothendieck existence `AlgebraicGeometry.Space.isEquivalence_completionFunctor_of_scheme`;
  Grothendieck existence for the algebraic space a proper scheme over a complete Noetherian ring
  represents, `AlgebraicGeometry.Space.isEquivalence_completionFunctor_yoneda_of_isProper`.
* **Ideal sheaves and adic quotients on a chart.** `AlgebraicGeometry.Space.idealSheafDataOfChart`
  reads a sheaf of ideals cartesian on affine charts as an `IdealSheafData` on the scheme of a
  chart; `AlgebraicGeometry.Space.isIso_chartRestrictionQuotientHom` and
  `AlgebraicGeometry.Space.chartRestrictionCompletionIso` say that the chart restriction of
  `M / 𝓘 ⁿ M` is the quotient of the chart restriction of `M`, so the completion of Stacks 08B4 is
  read on a chart as the completion of Stacks 0880.

## Universes

Everything is at the module universe `u` of the schemes, which is forced by Descent,
Proposition 03DX (2).

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The algebraic space represented by a locally Noetherian scheme is locally Noetherian**, in
the form `AlgebraicGeometry.Space.HasEtaleLocalProperty` that the coherence theory of algebraic
spaces is stated with: the identity chart is a surjective étale chart with locally Noetherian
scheme. -/
theorem hasEtaleLocalProperty_yoneda_isLocallyNoetherian
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    HasEtaleLocalProperty B S hS (yoneda.obj U) (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  hasEtaleLocalProperty_of_representable B S hS _ _ U (Iso.refl _) inferInstance

/-- **Coherence is invariant under the comparison of a scheme with the algebraic space it
represents.**  Let `T` be the scheme underlying `U`, assumed locally Noetherian, and let `𝓕` be a
quasi-coherent `𝒪_T`-module.  Then `𝓕^a`, the `𝒪`-module that `𝓕` becomes on the small étale site
of `yoneda.obj U` through `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, is
coherent (Stacks 07UA) if and only if `𝓕` is coherent (Stacks 01BV). -/
theorem isCoherent_representedQuasicoherentSchemeEquivalence_iff
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    IsCoherent B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ↔
      SheafOfModules.IsCoherent M.obj := by
  have : Fact (HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_yoneda_isLocallyNoetherian B S hS U⟩
  have : SheafOfModules.IsQuasicoherent M.obj := M.property
  refine (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS _ _ _).trans ⟨?_, ?_⟩
  · rintro ⟨-, hft⟩
    have h2 := Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_reindex
      (J' := SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeStructureSheaf B S hS U) _
      (Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType _ hft)
    have := AlgebraicGeometry.SmallEtale.isFiniteType_of_isFiniteTypeOnSite_associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property M.obj h2
    exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
      M.obj
  · intro h
    obtain ⟨-, hft⟩ :=
      Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M.obj
    exact ⟨((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property,
      Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _
        (isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B S hS U M.obj M.property
          hft)⟩

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` of the coherent modules of a scheme into its
quasi-coherent ones: a coherent module is quasi-coherent (Stacks 01XZ, (1) ⇒ (2)). -/
noncomputable def coherentToQuasicoherent (X : Scheme.{u}) :
    SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _) fun M =>
    have : SheafOfModules.IsCoherent M.obj := M.property
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M.obj).1

/-- The inclusion of the coherent modules of a scheme into its quasi-coherent ones is fully
faithful, both being full subcategories of the modules. -/
noncomputable def fullyFaithfulCoherentToQuasicoherent (X : Scheme.{u}) :
    (coherentToQuasicoherent X).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι)
    (ObjectProperty.fullyFaithfulι _)

/-- **The comparison `Coh(𝒪_T) ⥤ Coh(yoneda.obj U)`**, for `T` the locally Noetherian scheme
underlying `U`.  On underlying modules this is the functor of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, on the nose. -/
noncomputable def representedCoherentSchemeFunctor
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    SheafOfModules.CoherentModules ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⥤
      CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  ObjectProperty.lift _
    (coherentToQuasicoherent ((BigFppfOver.toScheme B S hS).obj U) ⋙
      (representedQuasicoherentSchemeEquivalence B S hS U).functor ⋙ ObjectProperty.ι _)
    fun M => (isCoherent_representedQuasicoherentSchemeEquivalence_iff B S hS U _).2 M.property

/-- The underlying module of the comparison of a coherent module is the module of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, by `rfl`. -/
theorem representedCoherentSchemeFunctor_obj_obj
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : SheafOfModules.CoherentModules ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) :
    ((representedCoherentSchemeFunctor B S hS U).obj M).obj =
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
        ((coherentToQuasicoherent ((BigFppfOver.toScheme B S hS).obj U)).obj M)).obj :=
  rfl

/-- **The comparison `Coh(𝒪_T) ⥤ Coh(yoneda.obj U)` is fully faithful.** -/
noncomputable def fullyFaithfulRepresentedCoherentSchemeFunctor
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    (representedCoherentSchemeFunctor B S hS U).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := (isCoherent.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).ι)
    ((fullyFaithfulCoherentToQuasicoherent _).comp
      ((representedQuasicoherentSchemeEquivalence B S hS U).fullyFaithfulFunctor.comp
        (ObjectProperty.fullyFaithfulι _)))

/-- **The comparison `Coh(𝒪_T) ⥤ Coh(yoneda.obj U)` is essentially surjective.** -/
instance essSurj_representedCoherentSchemeFunctor
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    (representedCoherentSchemeFunctor B S hS U).EssSurj where
  mem_essImage N := by
    let E := representedQuasicoherentSchemeEquivalence B S hS U
    let Nq : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedStructureRingSheaf B S hS U)).FullSubcategory :=
      ⟨N.obj, N.property.toIsQuasicoherentOnSite⟩
    let e : (E.functor.obj (E.inverse.obj Nq)).obj ≅ N.obj :=
      (ObjectProperty.ι _).mapIso (E.counitIso.app Nq)
    exact ⟨⟨(E.inverse.obj Nq).obj,
      (isCoherent_representedQuasicoherentSchemeEquivalence_iff B S hS U _).1
        (isCoherent_of_iso B S hS (isAlgebraicSpace_yoneda B S hS U) e.symm N.property)⟩,
      ⟨ObjectProperty.isoMk _ e⟩⟩

/-- The comparison `Coh(𝒪_T) ⥤ Coh(yoneda.obj U)` is an equivalence of categories. -/
instance isEquivalence_representedCoherentSchemeFunctor
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    (representedCoherentSchemeFunctor B S hS U).IsEquivalence where
  faithful := (fullyFaithfulRepresentedCoherentSchemeFunctor B S hS U).faithful
  full := (fullyFaithfulRepresentedCoherentSchemeFunctor B S hS U).full

/-- **The coherent modules on a locally Noetherian scheme are the coherent modules on the
algebraic space it represents**: `Coh(𝒪_T) ≌ Coh(yoneda.obj U)` for `T` the scheme underlying
`U`, with functor `AlgebraicGeometry.Space.representedCoherentSchemeFunctor`; it is the
restriction to the coherent modules of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`. -/
noncomputable def representedCoherentSchemeEquivalence
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    SheafOfModules.CoherentModules ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ≌
      CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  (representedCoherentSchemeFunctor B S hS U).asEquivalence

/-- The functor of `AlgebraicGeometry.Space.representedCoherentSchemeEquivalence` is
`AlgebraicGeometry.Space.representedCoherentSchemeFunctor`. -/
theorem representedCoherentSchemeEquivalence_functor
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    (representedCoherentSchemeEquivalence B S hS U).functor =
      representedCoherentSchemeFunctor B S hS U :=
  rfl

end AlgebraicGeometry.Space

end
