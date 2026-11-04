module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteLocalTypes
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSmallEtaleBigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Quasi-coherent modules on the small smooth, syntomic and fppf sites

Let `S` be a scheme of a big fppf site and `τ ∈ {smooth, syntomic, fppf}`.  Descent,
Proposition 03DX (2) asserts that `𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_S) ≌ QCoh(S_τ, 𝒪)` for
the small sites at `τ ∈ {Zariski, étale}`; this file proves the same statement for the small
smooth, syntomic and fppf sites `S_τ` of `AlgebraicGeometry.SmallFlatSite`, which extend the
source's small sites to the three remaining topologies.

The proof goes through the big site.  Let `ι : S_τ ⊆ (Sch/S)_τ` be the inclusion and `ι_!` its
lower shriek on sheaves of modules, which is fully faithful, carries `𝓕^a` on `S_τ` to `𝓕^a` on
`(Sch/S)_τ` (`AlgebraicGeometry.SmallFlatSite.associatedModuleCompLowerShriekIso`) and carries
quasi-coherent modules to quasi-coherent modules and only those
(`AlgebraicGeometry.SmallFlatSite.isQuasicoherentOnSite_lowerShriek_iff`).  Then:

* `𝓕 ↦ 𝓕^a|_{S_τ}` is fully faithful on `QCoh(𝒪_S)`, because its composite with the fully faithful
  `ι_!` is `𝓕 ↦ 𝓕^a|_{(Sch/S)_τ}`, which is fully faithful there (Stacks 0GN7);
* `𝓕^a|_{S_τ}` is quasi-coherent, because `ι_!` of it is `𝓕^a|_{(Sch/S)_τ}`, which is
  (Stacks 03DV);
* a quasi-coherent `𝓝` on `S_τ` is `𝓕^a|_{S_τ}`: `ι_! 𝓝` is quasi-coherent on `(Sch/S)_τ`, hence
  `𝓕^a|_{(Sch/S)_τ} = ι_!(𝓕^a|_{S_τ})` for a quasi-coherent `𝓕` by Proposition 03DX (1), and `ι_!`
  is fully faithful.

## Main definitions

* `AlgebraicGeometry.SmallFlatSite.associatedModuleQcoh`: `𝓕 ↦ 𝓕^a` on `QCoh(𝒪_S)`.
* `AlgebraicGeometry.SmallFlatSite.associatedModuleQcohOnSite`: the same, corestricted to
  `QCoh(S_τ, 𝒪)`.
* `AlgebraicGeometry.SmallFlatSite.associatedModuleEquivalence`: **the equivalence
  `QCoh(𝒪_S) ≌ QCoh(S_τ, 𝒪)`.**

## Main results

* `AlgebraicGeometry.SmallFlatSite.fullyFaithfulAssociatedModuleQcoh`: Stacks 0GN7 at `S_τ`.
* `AlgebraicGeometry.SmallFlatSite.isQuasicoherentOnSite_associatedModule`: Stacks 03DV at `S_τ`.
* `AlgebraicGeometry.SmallFlatSite.isEquivalence_associatedModuleQcohOnSite`: Stacks 03DX (2) at
  `τ ∈ {smooth, syntomic, fppf}`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallFlatSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-- The associated-module functor of the small `τ`-site, retyped so that its source carries the
category instance of `SheafOfModules.{u} S.ringCatSheaf`. -/
abbrev associatedModuleOfSheaf :
    SheafOfModules.{u} S.ringCatSheaf ⥤ SheafOfModules.{u} (ringStructureSheaf B S hS κ) :=
  associatedModule B S hS κ

/-- **The functor of Stacks 0GN7 for the small `τ`-site**: `𝓕 ↦ 𝓕^a` on the quasi-coherent
`𝒪_S`-modules. -/
abbrev associatedModuleQcoh :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (ringStructureSheaf B S hS κ) :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ associatedModuleOfSheaf B S hS κ

/-- The lower shriek of `𝓕^a` on the small `τ`-site is `𝓕^a` on the big site, on quasi-coherent
modules. -/
noncomputable def associatedModuleQcohCompLowerShriekIso :
    associatedModuleQcoh B S hS κ ⋙ lowerShriek B S hS κ ≅
      BigFppfOver.baseAssociatedModuleQcoh B S hS κ.toSiteKind :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (associatedModuleCompLowerShriekIso B S hS κ)

/-- **Stacks 0GN7 for the small `τ`-site.**  `𝓕 ↦ 𝓕^a` is fully faithful on the quasi-coherent
`𝒪_S`-modules: its composite with the fully faithful lower shriek is the corresponding functor of
the big site, which is fully faithful. -/
noncomputable def fullyFaithfulAssociatedModuleQcoh :
    (associatedModuleQcoh B S hS κ).FullyFaithful :=
  ((BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh B S hS κ.toSiteKind).ofIso
    (associatedModuleQcohCompLowerShriekIso B S hS κ).symm).ofCompFaithful

/-- **Stacks 03DV at the small `τ`-site.**  The associated module of a quasi-coherent
`𝒪_S`-module is a quasi-coherent `𝒪`-module on `S_τ`. -/
theorem isQuasicoherentOnSite_associatedModule (𝓕 : S.Modules)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕) :
    ((associatedModule B S hS κ).obj 𝓕).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_lowerShriek_iff B S hS κ _).2
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((associatedModuleCompLowerShriekIso B S hS κ).app 𝓕).symm
      (BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B S hS
        κ.toSiteKind 𝓕 h))

/-- **The functor of Stacks 03DX (2) at `τ ∈ {smooth, syntomic, fppf}`**: `𝓕 ↦ 𝓕^a` as a
functor `QCoh(𝒪_S) ⥤ QCoh(S_τ, 𝒪)`. -/
abbrev associatedModuleQcohOnSite :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheaf B S hS κ)).FullSubcategory :=
  ObjectProperty.lift _ (associatedModuleQcoh B S hS κ) fun M ↦
    isQuasicoherentOnSite_associatedModule B S hS κ M.obj M.property

/-- The corestricted functor `QCoh(𝒪_S) ⥤ QCoh(S_τ, 𝒪)` is fully faithful. -/
noncomputable def fullyFaithfulAssociatedModuleQcohOnSite :
    (associatedModuleQcohOnSite B S hS κ).FullyFaithful :=
  have := (fullyFaithfulAssociatedModuleQcoh B S hS κ).full
  have := (fullyFaithfulAssociatedModuleQcoh B S hS κ).faithful
  .ofFullyFaithful _

/-- **Essential surjectivity of `𝓕 ↦ 𝓕^a` onto the quasi-coherent modules of `S_τ`.**  The lower
shriek of a quasi-coherent module `𝓝` on `S_τ` is quasi-coherent on `(Sch/S)_τ`, hence is
`𝓕^a|_{(Sch/S)_τ} = ι_!(𝓕^a|_{S_τ})` for a quasi-coherent `𝓕` by Proposition 03DX (1); the lower
shriek is fully faithful, so `𝓝 ≅ 𝓕^a|_{S_τ}`. -/
theorem quasicoherentIsEssImageAssociatedModule :
    SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (ringStructureSheaf B S hS κ) ≤
      (associatedModuleQcoh B S hS κ).essImage := by
  intro 𝓝 h𝓝
  have h : ((lowerShriek B S hS κ).obj 𝓝).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_lowerShriek_iff B S hS κ 𝓝).1 h𝓝
  obtain ⟨𝓕, ⟨e⟩⟩ := BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule B S hS κ.toSiteKind
    _ h
  exact ⟨𝓕, ⟨(fullyFaithfulLowerShriek B S hS κ).preimageIso
    ((associatedModuleQcohCompLowerShriekIso B S hS κ).app 𝓕 ≪≫ e)⟩⟩

/-- The corestricted functor `QCoh(𝒪_S) ⥤ QCoh(S_τ, 𝒪)` is essentially surjective. -/
theorem essSurj_associatedModuleQcohOnSite : (associatedModuleQcohOnSite B S hS κ).EssSurj where
  mem_essImage G := by
    obtain ⟨𝓕, ⟨e⟩⟩ := quasicoherentIsEssImageAssociatedModule B S hS κ G.obj G.property
    exact ⟨𝓕, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **Descent, Proposition 03DX (2), extended to the small sites `S_τ` for
`τ ∈ {smooth, syntomic, fppf}`.**  `𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_S) ⥤ QCoh(S_τ, 𝒪)`. -/
theorem isEquivalence_associatedModuleQcohOnSite :
    (associatedModuleQcohOnSite B S hS κ).IsEquivalence :=
  have hff := fullyFaithfulAssociatedModuleQcohOnSite B S hS κ
  have := hff.full
  have := hff.faithful
  have := essSurj_associatedModuleQcohOnSite B S hS κ
  {}

/-- **The equivalence of categories `QCoh(𝒪_S) ≌ QCoh(S_τ, 𝒪)`** for the small sites at
`τ ∈ {smooth, syntomic, fppf}`, with `𝓕 ↦ 𝓕^a` as its functor: Descent, Proposition 03DX (2)
extended from `τ ∈ {Zariski, étale}` to the three remaining topologies. -/
noncomputable def associatedModuleEquivalence :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheaf B S hS κ)).FullSubcategory :=
  have := isEquivalence_associatedModuleQcohOnSite B S hS κ
  (associatedModuleQcohOnSite B S hS κ).asEquivalence

end AlgebraicGeometry.SmallFlatSite

end
