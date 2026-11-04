module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EssentialImage
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.SmallEtaleAssociatedModuleColimits

/-!
# The essential image of the associated-module functor of the small étale site

A module on `S_étale` presented as a cokernel of free modules
`⊕_{i ∈ I₂} 𝒪 ⟶ ⊕_{i ∈ I₁} 𝒪 ⟶ 𝒢 ⟶ 0`
is `𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕`, namely the cokernel of the morphism of free
`𝒪_S`-modules presenting the first map.  Over that, the functor `𝓕 ↦ 𝓕^a` of Definition 03DU (4)
at `τ = étale` is an equivalence `QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)` as soon as it is essentially
surjective.

## Main definitions

* `AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`: essential surjectivity
  of `𝓕 ↦ 𝓕^a` onto the quasi-coherent modules of `S_étale`.
* `AlgebraicGeometry.SmallEtale.associatedModuleQcohOnSite`: the functor
  `QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)`, with no hypothesis.
* `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence`: the equivalence
  `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)`, over essential surjectivity alone.

## Main results

* `AlgebraicGeometry.SmallEtale.essImage_associatedModule_free`: a free module on `S_étale` is
  the associated module of the free `𝒪_S`-module on the same type.
* `AlgebraicGeometry.SmallEtale.exists_associatedModule_map_free`: every morphism between the
  associated modules of two free `𝒪_S`-modules comes from a morphism of free `𝒪_S`-modules.
* `AlgebraicGeometry.SmallEtale.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree` and
  `AlgebraicGeometry.SmallEtale.essImage_associatedModule_of_cokernelFree`: the local step of
  essential surjectivity, with no hypothesis.
* `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcohOnSite`: that functor is fully
  faithful, with no hypothesis.
* `AlgebraicGeometry.SmallEtale.essSurj_associatedModuleQcohOnSite` and
  `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite`: essential
  surjectivity and the equivalence, over `hsurj`.

## Implementation notes

The local step is the small étale counterpart of
`AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree`, and
it is unconditional where that one is not: the big-site statement carries
`AlgebraicGeometry.BigFppfOver.IsFullOnFree`, fullness of `𝓕 ↦ 𝓕^a` on free modules, as a
hypothesis, while on the small étale site that fullness is
`AlgebraicGeometry.SmallEtale.bijective_associatedModule_map_free`.

The corestriction of the functor into the quasi-coherent modules of the site is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`, and
full faithfulness is `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'`, so the
equivalence is reduced here to essential surjectivity.

### No `@[stacks 03DX]`

The equivalence here is stated over essential surjectivity, and a hypothesis is part of a
citation. Essential surjectivity is proved with no hypothesis as
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`, and clause (2) of
Stacks 03DX at `τ = étale` is registered, by `add_to_stacks`, on
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The local step of essential surjectivity -/

/-- **Stacks 03DX (2) at `τ = étale`, the direct sums.**  A free module on `S_étale` is the
associated module of the free `𝒪_S`-module on the same type. -/
public theorem essImage_associatedModule_free (I : Type u) :
    (associatedModule B S hS).essImage (SheafOfModules.free I) :=
  SheafOfModules.essImage_pullback_free (structureMap B S hS) I

/-- **Fullness of `𝓕 ↦ 𝓕^a` on free modules, on the small étale site.**  Every morphism between
the associated modules of two free `𝒪_S`-modules is the associated morphism of a morphism of free
`𝒪_S`-modules. -/
public theorem exists_associatedModule_map_free (I₁ I₂ : Type u)
    (α : (associatedModule B S hS).obj (SheafOfModules.free (R := S.ringCatSheaf) I₂) ⟶
      (associatedModule B S hS).obj (SheafOfModules.free (R := S.ringCatSheaf) I₁)) :
    ∃ β : SheafOfModules.free (R := S.ringCatSheaf) I₂ ⟶
        SheafOfModules.free (R := S.ringCatSheaf) I₁,
      (associatedModule B S hS).map β = α :=
  (bijective_associatedModule_map_free B S hS _ I₁).surjective α

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity, local step.**  A module on
`S_étale` presented as a cokernel `⊕_{i ∈ I₂} 𝒪 ⟶ ⊕_{i ∈ I₁} 𝒪 ⟶ 𝒢 ⟶ 0` is the associated module
`𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`, namely of the cokernel of the morphism of free
`𝒪_S`-modules that presents the first map. -/
public theorem exists_isQuasicoherent_iso_associatedModule_of_cokernelFree {I₁ I₂ : Type u}
    (α : SheafOfModules.free (R := structureSheaf B S hS) I₂ ⟶ SheafOfModules.free I₁)
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    {π : SheafOfModules.free (R := structureSheaf B S hS) I₁ ⟶ G} (hπ : α ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    ∃ G' : S.Modules, G'.IsQuasicoherent ∧
      Nonempty ((associatedModule B S hS).obj G' ≅ G) := by
  obtain ⟨β, hβ⟩ := exists_associatedModule_map_free B S hS I₁ I₂
    ((SheafOfModules.pullbackObjFreeIso (structureMap B S hS) I₂).hom ≫ α ≫
      (SheafOfModules.pullbackObjFreeIso (structureMap B S hS) I₁).inv)
  exact ⟨cokernel β, Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
    (X := S) (M := SheafOfModules.free I₂) (N := SheafOfModules.free I₁) β,
    SheafOfModules.nonempty_iso_pullbackObj_cokernel_free (structureMap B S hS) α β hβ hπ hc⟩

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity, local step**, in the form of a
membership in the essential image of `𝓕 ↦ 𝓕^a`. -/
public theorem essImage_associatedModule_of_cokernelFree {I₁ I₂ : Type u}
    (α : SheafOfModules.free (R := structureSheaf B S hS) I₂ ⟶ SheafOfModules.free I₁)
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    {π : SheafOfModules.free (R := structureSheaf B S hS) I₁ ⟶ G} (hπ : α ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    (associatedModule B S hS).essImage G := by
  obtain ⟨G', _, h⟩ :=
    exists_isQuasicoherent_iso_associatedModule_of_cokernelFree B S hS α hπ hc
  exact ⟨G', h⟩

/-! ### The equivalence, over essential surjectivity -/

/-- **Essential surjectivity of `𝓕 ↦ 𝓕^a` on the small étale site**, as a hypothesis: every
quasi-coherent module on `S_étale` is isomorphic to an `𝓕^a` for a quasi-coherent `𝒪_S`-module
`𝓕`. -/
public abbrev QuasicoherentIsEssImageAssociatedModule : Prop :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (structureSheaf B S hS) ≤
    (associatedModuleQcoh B S hS).essImage

/-- **The functor of Stacks 03DX (2) at `τ = étale`**: `𝓕 ↦ 𝓕^a` as a functor
`QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)`, with no hypothesis: the corestriction of
`AlgebraicGeometry.SmallEtale.associatedModuleQcoh` to the quasi-coherent modules on `S_étale`. -/
public noncomputable abbrev associatedModuleQcohOnSite :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  ObjectProperty.lift _ (associatedModuleQcoh B S hS) fun M =>
    isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS M.obj M.property

/-- **The corestricted functor `QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)` is fully faithful**, with no
hypothesis. -/
public noncomputable def fullyFaithfulAssociatedModuleQcohOnSite :
    (associatedModuleQcohOnSite B S hS).FullyFaithful :=
  .ofFullyFaithful _

/-- The corestricted functor `QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)` is essentially surjective, over
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`. -/
public theorem essSurj_associatedModuleQcohOnSite
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (associatedModuleQcohOnSite B S hS).EssSurj where
  mem_essImage G := by
    obtain ⟨𝓕, ⟨e⟩⟩ := hsurj G.obj G.property
    exact ⟨𝓕, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- `𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)`, over essential surjectivity
alone. -/
public theorem isEquivalence_associatedModuleQcohOnSite
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (associatedModuleQcohOnSite B S hS).IsEquivalence :=
  have hff := fullyFaithfulAssociatedModuleQcohOnSite B S hS
  have := hff.full
  have := hff.faithful
  have := essSurj_associatedModuleQcohOnSite B S hS hsurj
  {}

/-- The equivalence of categories `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)`, over essential surjectivity
alone, with `𝓕 ↦ 𝓕^a` as its functor. -/
public noncomputable def associatedModuleEquivalence
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  have := isEquivalence_associatedModuleQcohOnSite B S hS hsurj
  (associatedModuleQcohOnSite B S hS).asEquivalence

end AlgebraicGeometry.SmallEtale

end
