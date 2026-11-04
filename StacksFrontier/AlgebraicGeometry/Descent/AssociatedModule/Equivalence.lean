module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize

/-!
# The equivalence of Stacks 03DX (1), assembled from its three inputs

Stacks 03DX (1) says that `𝓕 ↦ 𝓕^a` defines an equivalence of categories
`QCoh(𝒪_S) ⟶ QCoh((Sch/S)_τ, 𝒪)`. This consists of three statements: the functor lands in the
quasi-coherent modules of the big site, it is fully faithful, and every quasi-coherent module on
the big site is isomorphic to some `𝓕^a`. This file assembles the equivalence for `τ = fppf`
from these three statements, taken as hypotheses:

* `AlgebraicGeometry.BigFppfOver.AssociatedModuleIsQuasicoherent`, Stacks 03DV, which is what
  corestricts the functor into `QCoh((Sch/S)_fppf, 𝒪)`;
* `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`, the input to Stacks 0GN7, which gives
  full faithfulness through `AlgebraicGeometry.BigFppfOver.fullyFaithfulAssociatedModuleQcoh`;
* `AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`, essential
  surjectivity: every quasi-coherent module on `(Sch/S)_fppf` lies in the essential image of
  `𝓕 ↦ 𝓕^a`.

The source category `QCoh(𝒪_S)` is cut out by `SheafOfModules.IsQuasicoherent` and the target
`QCoh((Sch/S)_fppf, 𝒪)` by `SheafOfModules.IsQuasicoherentOnSite`, the predicate of
Stacks 03DL (6).

## Main definitions

* `AlgebraicGeometry.BigFppfOver.associatedModuleQcohOnSite`: the functor
  `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)` of Stacks 03DX (1), namely
  `AlgebraicGeometry.BigFppfOver.associatedModuleQcoh` corestricted along Stacks 03DV.
* `AlgebraicGeometry.BigFppfOver.associatedModuleEquivalence`: the equivalence of Stacks
  03DX (1) for `τ = fppf`, over the three hypotheses above.

## Main results

* `AlgebraicGeometry.BigFppfOver.fullyFaithfulAssociatedModuleQcohOnSite`: the corestricted
  functor is fully faithful.
* `AlgebraicGeometry.BigFppfOver.essSurj_associatedModuleQcohOnSite`: it is essentially
  surjective.
* `AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite`: it is an
  equivalence.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The functor of Stacks 03DX (1)** for `τ = fppf`: `𝓕 ↦ 𝓕^a` as a functor
`QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)`, the corestriction of
`AlgebraicGeometry.BigFppfOver.associatedModuleQcoh` to the quasi-coherent modules on the big
fppf site along `hF`. -/
public noncomputable abbrev associatedModuleQcohOnSite
    (hF : AssociatedModuleIsQuasicoherent B S hS) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  ObjectProperty.lift _ (associatedModuleQcoh B S hS) hF

/-- Over Stacks 03DV and `AlgebraicGeometry.BigFppfOver.UnitIsoOnQuasicoherent`, the functor
`QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)` of Stacks 03DX (1) is fully faithful. -/
public noncomputable def fullyFaithfulAssociatedModuleQcohOnSite
    (hF : AssociatedModuleIsQuasicoherent B S hS) (hunit : UnitIsoOnQuasicoherent B S hS) :
    (associatedModuleQcohOnSite B S hS hF).FullyFaithful :=
  have := full_associatedModuleQcoh B S hS hunit
  have := faithful_associatedModuleQcoh B S hS hunit
  .ofFullyFaithful _

/-- **Essential surjectivity of the functor of Stacks 03DX (1)**, over Stacks 03DV and
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`. -/
public theorem essSurj_associatedModuleQcohOnSite
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (associatedModuleQcohOnSite B S hS hF).EssSurj where
  mem_essImage G := by
    obtain ⟨𝓕, ⟨e⟩⟩ := hsurj G.obj G.property
    exact ⟨𝓕, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **Stacks 03DX (1) for `τ = fppf`, over its three inputs**: `𝓕 ↦ 𝓕^a` is an equivalence
`QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)`. -/
public theorem isEquivalence_associatedModuleQcohOnSite
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS)
    (hunit : UnitIsoOnQuasicoherent B S hS) :
    (associatedModuleQcohOnSite B S hS hF).IsEquivalence :=
  have hff := fullyFaithfulAssociatedModuleQcohOnSite B S hS hF hunit
  have := hff.full
  have := hff.faithful
  have := essSurj_associatedModuleQcohOnSite B S hS hF hsurj
  {}

/-- **The equivalence of categories of Stacks 03DX (1) for `τ = fppf`, over its three
inputs**: `QCoh(𝒪_S) ≌ QCoh((Sch/S)_fppf, 𝒪)`, with
`AlgebraicGeometry.BigFppfOver.associatedModuleQcohOnSite` as its functor. -/
public noncomputable def associatedModuleEquivalence
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS)
    (hunit : UnitIsoOnQuasicoherent B S hS) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  have := isEquivalence_associatedModuleQcohOnSite B S hS hF hsurj hunit
  (associatedModuleQcohOnSite B S hS hF).asEquivalence

end AlgebraicGeometry.BigFppfOver

end
