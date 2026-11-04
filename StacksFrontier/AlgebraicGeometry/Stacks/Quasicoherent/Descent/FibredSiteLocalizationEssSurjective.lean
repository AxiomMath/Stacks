module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKind
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationSiteKindExtensions

/-!
# `𝓕 ↦ 𝓕^a` on the slice of a fibred site at an object, and its essential surjectivity

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `x` an object of `𝒳` lying
over a scheme `U`.  By Stacks 06W0 the slice `𝒳_τ/x` *is* the big `τ`-site `(Sch/U)_τ` of `U`,
and `AlgebraicGeometry.FibredSite.localizationModulesEquivalenceKind'` transports a sheaf of
modules across that identification.  This file reads the functor `𝓕 ↦ 𝓕^a` of Definition 03DU
through that transport and proves it **essentially surjective onto the quasi-coherent modules of
the slice**, at every `AlgebraicGeometry.SiteKind` and with no hypothesis.

So the essential-surjectivity half of Descent, Proposition 03DX (1) — which is a theorem of this
library at every big site and every base, `AlgebraicGeometry.BigFppfOver`
`.baseQuasicoherentIsEssImageAssociatedModule` — is made to **apply on the slice**.  At
`τ = AlgebraicGeometry.SiteKind.etale` that is Descent, Section 03DR for the scheme `U`, read on
`𝒳_étale/x`, which is the input the proof of Stacks 0GQD appeals to after passing to a chart.

## What is reused rather than rebuilt

Nothing about the identification of the slice with the big site is proved here.  The equivalence
of categories is `AlgebraicGeometry.FibredSite.localizationEquivalence'` (Stacks 06W0 through
`AlgebraicGeometry.Stack.isEquivalence_overPost`), its two dense-subsite witnesses at an
arbitrary topology are `AlgebraicGeometry.FibredSite`
`.isDenseSubsite_localizationEquivalence_functor_kind` and `…_inverse_kind`, the identification
of the two structure sheaves is `AlgebraicGeometry.FibredSite`
`.reindexRing_localizationEquivalence_kind` (an equality), the transport of modules is
`AlgebraicGeometry.FibredSite.localizationModulesEquivalenceKind'`, and the transport of
quasi-coherence across it is `AlgebraicGeometry.FibredSite`
`.isQuasicoherentOnSite_localization_iff_kind` — ultimately
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`, whose two sites live in independent
universes of objects and of morphisms.  All of that is already in the tree; the content of this
file is only the composition with Descent, Proposition 03DX (1).

## Main definitions

* `AlgebraicGeometry.FibredSite.localizationAssociatedModuleKind`: the functor `𝓕 ↦ 𝓕^a` of the
  scheme `U` below `x`, read on the slice `𝒳_τ/x`.
* `AlgebraicGeometry.FibredSite.localizationAssociatedModuleQcohKind`: the same functor
  corestricted to the quasi-coherent modules of the slice.

## Main results

* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_localizationAssociatedModuleKind`:
  Stacks 03DV (1) on the slice — `𝓕^a` read on `𝒳_τ/x` is quasi-coherent there.
* `AlgebraicGeometry.FibredSite.quasicoherentIsEssImageLocalizationAssociatedModuleKind`:
  **the essential-surjectivity half of Descent, Proposition 03DX (1) on the slice `𝒳_τ/x`**, at
  every `τ` and with no hypothesis.
* `AlgebraicGeometry.FibredSite.essImage_localizationAssociatedModuleKind`: the quasi-coherent
  modules of the slice are exactly the essential image of `𝓕 ↦ 𝓕^a`.
* `AlgebraicGeometry.FibredSite.isEquivalence_localizationAssociatedModuleQcohKind` and
  `AlgebraicGeometry.FibredSite.localizationAssociatedModuleEquivalenceKind`: **Descent,
  Proposition 03DX (1) on the slice in its equivalence form**, `QCoh(𝒪_U) ≌ QCoh(𝒳_τ/x, 𝒪_𝒳)`,
  with no hypothesis.

## Implementation notes

No `stacks` attribute.  Clause (1) of Descent, Proposition 03DX is about the five big sites of a
scheme, and the statements below are that clause transported along Stacks 06W0 to the slice of a
fibred site; the clause itself is covered — as far as this library covers it — by
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule` and the declarations
around it, whose own implementation notes record why the tag is not earned there either (clause
(2), the small sites, is a different construction).

**The module universe is `u`, the universe of the schemes, and that is forced by Descent,
Proposition 03DX (1) rather than chosen here.**  `CategoryTheory.SheafOfModules.isQuasicoherent`
takes the module universe to *be* the universe of the sections of its sheaf of rings, so the
source of `𝓕 ↦ 𝓕^a` on the scheme `U` is `AlgebraicGeometry.Scheme.Modules`, which is
`CategoryTheory.SheafOfModules.{u}` with no module universe parameter at all.  Nothing else below
constrains it: the identification of the slice with the big site, the transport of modules and
the transport of quasi-coherence all leave the module universe free, and the two universes `v`
and `w` of `𝒳` stay independent of `u` throughout — the slice has objects in `Type (max v w)` and
morphisms in `Type w` while the big site of `U` has objects in `Type (u + 1)` and morphisms in
`Type u`, and `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` asks for no relation
between the two pairs.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DR](https://stacks.math.columbia.edu/tag/03DR)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The functor `𝓕 ↦ 𝓕^a` read on the slice `𝒳_τ/x`.**  A quasi-coherent module on the scheme
`U = p(x)` has its associated module on the big `τ`-site of `U` (Definition 03DU), and
`AlgebraicGeometry.FibredSite.localizationModulesEquivalenceKind'` carries that across the
identification `𝒳_τ/x = (Sch/U)_τ` of Stacks 06W0. -/
public noncomputable abbrev localizationAssociatedModuleKind (τ : SiteKind) (x : 𝒳) :
    (SheafOfModules.isQuasicoherent (baseScheme' B S hS p x).ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp τ).over x) :=
  BigFppfOver.baseAssociatedModuleQcoh B (baseScheme' B S hS p x)
      (contains_baseScheme' B S hS p x) τ ⋙
    (localizationModulesEquivalenceKind' B S hS p hp τ x).functor

/-- **Stacks 03DV (1) on the slice.**  The associated module of a quasi-coherent `𝒪_U`-module,
read on `𝒳_τ/x`, is quasi-coherent there.

Downstairs this is `AlgebraicGeometry.BigFppfOver`
`.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`, and quasi-coherence is carried
across the identification of ringed sites by `AlgebraicGeometry.FibredSite`
`.isQuasicoherentOnSite_localization_iff_kind`. -/
public theorem isQuasicoherentOnSite_localizationAssociatedModuleKind (τ : SiteKind) (x : 𝒳)
    (𝓕 : (SheafOfModules.isQuasicoherent
      (baseScheme' B S hS p x).ringCatSheaf).FullSubcategory) :
    ((localizationAssociatedModuleKind B S hS p hp τ x).obj 𝓕).IsQuasicoherentOnSite := by
  refine (isQuasicoherentOnSite_localization_iff_kind' B S hS p hp τ x _).2 ?_
  refine (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
    ((localizationModulesEquivalenceKind' B S hS p hp τ x).unitIso.app _) ?_
  exact BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B
    (baseScheme' B S hS p x) (contains_baseScheme' B S hS p x) τ 𝓕.obj 𝓕.property

/-- **The essential-surjectivity half of Descent, Proposition 03DX (1) on the slice `𝒳_τ/x`, at
every `AlgebraicGeometry.SiteKind` and with no hypothesis**: every quasi-coherent module on the
slice of the associated `τ`-site of `𝒳` at an object `x` is isomorphic to `𝓕^a` for a
quasi-coherent module `𝓕` on the scheme `U = p(x)` that `x` lies over.

The module is transported to `(Sch/U)_τ` by `AlgebraicGeometry.FibredSite`
`.localizationModulesEquivalenceKind`, where it is quasi-coherent by
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_localization_iff_kind'`; there
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule` applies, at
the base `U` and with no hypothesis, and the resulting isomorphism is carried back by the same
transport.

At `τ = AlgebraicGeometry.SiteKind.etale` this is Descent, Section 03DR for the scheme `U` read
on `𝒳_étale/x`, which is the input the proof of Stacks 0GQD appeals to after passing to a
chart. -/
public theorem quasicoherentIsEssImageLocalizationAssociatedModuleKind (τ : SiteKind) (x : 𝒳) :
    SheafOfModules.isQuasicoherentOnSite.{max v w, w, u, u}
        ((ringStructureSheafCore B S hS p hp τ).over x) ≤
      (localizationAssociatedModuleKind B S hS p hp τ x).essImage := by
  intro N hN
  obtain ⟨𝓕, ⟨i⟩⟩ := BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule B
    (baseScheme' B S hS p x) (contains_baseScheme' B S hS p x) τ _
    ((isQuasicoherentOnSite_localization_iff_kind' B S hS p hp τ x N).1 hN)
  exact ⟨𝓕, ⟨(localizationModulesEquivalenceKind' B S hS p hp τ x).functor.mapIso i ≪≫
    (localizationModulesEquivalenceKind' B S hS p hp τ x).counitIso.app N⟩⟩

/-- **The quasi-coherent modules of the slice `𝒳_τ/x` are exactly the essential image of
`𝓕 ↦ 𝓕^a`.**  One inclusion is Stacks 03DV (1) on the slice and the other is the essential
surjectivity above; `SheafOfModules.essImage_eq_isQuasicoherentOnSite` assembles them. -/
public theorem essImage_localizationAssociatedModuleKind (τ : SiteKind) (x : 𝒳) :
    (localizationAssociatedModuleKind B S hS p hp τ x).essImage =
      SheafOfModules.isQuasicoherentOnSite.{max v w, w, u, u}
        ((ringStructureSheafCore B S hS p hp τ).over x) :=
  SheafOfModules.essImage_eq_isQuasicoherentOnSite _
    (isQuasicoherentOnSite_localizationAssociatedModuleKind B S hS p hp τ x)
    (quasicoherentIsEssImageLocalizationAssociatedModuleKind B S hS p hp τ x)

/-- `𝓕 ↦ 𝓕^a` on the slice `𝒳_τ/x`, corestricted to the quasi-coherent modules there along
Stacks 03DV (1). -/
public noncomputable abbrev localizationAssociatedModuleQcohKind (τ : SiteKind) (x : 𝒳) :
    (SheafOfModules.isQuasicoherent (baseScheme' B S hS p x).ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{max v w, w, u, u}
        ((ringStructureSheafCore B S hS p hp τ).over x)).FullSubcategory :=
  ObjectProperty.lift _ (localizationAssociatedModuleKind B S hS p hp τ x)
    (isQuasicoherentOnSite_localizationAssociatedModuleKind B S hS p hp τ x)

/-- **`𝓕 ↦ 𝓕^a` on the slice is fully faithful**, which is Stacks 0GN7 for the big site of `U`
(`AlgebraicGeometry.BigFppfOver.full_baseAssociatedModuleQcoh` and its faithfulness companion)
composed with an equivalence of categories. -/
public noncomputable def fullyFaithfulLocalizationAssociatedModuleQcohKind (τ : SiteKind)
    (x : 𝒳) : (localizationAssociatedModuleQcohKind B S hS p hp τ x).FullyFaithful :=
  have := BigFppfOver.full_baseAssociatedModuleQcoh B (baseScheme' B S hS p x)
    (contains_baseScheme' B S hS p x) τ
  have := BigFppfOver.faithful_baseAssociatedModuleQcoh B (baseScheme' B S hS p x)
    (contains_baseScheme' B S hS p x) τ
  .ofFullyFaithful _

/-- `𝓕 ↦ 𝓕^a` on the slice is essentially surjective onto the quasi-coherent modules there: an
isomorphism in a full subcategory is an isomorphism of the underlying modules. -/
public theorem essSurj_localizationAssociatedModuleQcohKind (τ : SiteKind) (x : 𝒳) :
    (localizationAssociatedModuleQcohKind B S hS p hp τ x).EssSurj where
  mem_essImage N := by
    obtain ⟨𝓕, ⟨e⟩⟩ := quasicoherentIsEssImageLocalizationAssociatedModuleKind B S hS p hp τ x
      N.obj N.property
    exact ⟨𝓕, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **Descent, Proposition 03DX (1) on the slice `𝒳_τ/x`, with no hypothesis**: `𝓕 ↦ 𝓕^a` is an
equivalence from the quasi-coherent modules of the scheme `U = p(x)` to the quasi-coherent
modules of the slice.  Full faithfulness is Stacks 0GN7 and essential surjectivity is
`AlgebraicGeometry.FibredSite.quasicoherentIsEssImageLocalizationAssociatedModuleKind`. -/
public theorem isEquivalence_localizationAssociatedModuleQcohKind (τ : SiteKind) (x : 𝒳) :
    (localizationAssociatedModuleQcohKind B S hS p hp τ x).IsEquivalence :=
  have hff := fullyFaithfulLocalizationAssociatedModuleQcohKind B S hS p hp τ x
  have := hff.full
  have := hff.faithful
  have := essSurj_localizationAssociatedModuleQcohKind B S hS p hp τ x
  {}

/-- **The equivalence `QCoh(𝒪_U) ≌ QCoh(𝒳_τ/x, 𝒪_𝒳)` of Descent, Proposition 03DX (1) read on
the slice**, with `𝓕 ↦ 𝓕^a` as its functor and with no hypothesis. -/
public noncomputable def localizationAssociatedModuleEquivalenceKind (τ : SiteKind) (x : 𝒳) :
    (SheafOfModules.isQuasicoherent (baseScheme' B S hS p x).ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{max v w, w, u, u}
        ((ringStructureSheafCore B S hS p hp τ).over x)).FullSubcategory :=
  have := isEquivalence_localizationAssociatedModuleQcohKind B S hS p hp τ x
  (localizationAssociatedModuleQcohKind B S hS p hp τ x).asEquivalence

end AlgebraicGeometry.FibredSite

end
