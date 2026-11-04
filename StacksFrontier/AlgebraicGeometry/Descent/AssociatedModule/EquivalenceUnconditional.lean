module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Equivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithfulUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence

/-!
# The equivalence of Stacks 03DX (1) at `τ = fppf`, over essential surjectivity alone

Let `S` be a scheme in a big fppf site. The functor `𝓕 ↦ 𝓕^a` from quasi-coherent
`𝒪_S`-modules to quasi-coherent modules on `(Sch/S)_fppf` is defined with no hypothesis, since
`𝓕^a` is quasi-coherent on the site (Stacks 03DV,
`AlgebraicGeometry.BigFppfOver.associatedModuleIsQuasicoherent`), and it is fully faithful with
no hypothesis, since the unit of the associated-module adjunction is an isomorphism at the
quasi-coherent modules (`AlgebraicGeometry.BigFppfOver.unitIsoOnQuasicoherent`). It is therefore
an equivalence as soon as it is essentially surjective, that is, over
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.associatedModuleQcohOnSite'`: the functor of Stacks 03DX (1)
  for `τ = fppf`, `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)`.
* `AlgebraicGeometry.BigFppfOver.associatedModuleEquivalence'`: the equivalence of categories
  of Stacks 03DX (1) for `τ = fppf`, over essential surjectivity.

## Main results

* `AlgebraicGeometry.BigFppfOver.fullyFaithfulAssociatedModuleQcohOnSite'`: that functor is
  fully faithful.
* `AlgebraicGeometry.BigFppfOver.essSurj_associatedModuleQcohOnSite'` and
  `AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite'`: essential
  surjectivity and the equivalence, over `hsurj`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The functor of Stacks 03DX (1)** for `τ = fppf`: `𝓕 ↦ 𝓕^a` as a functor
`QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)`. -/
public noncomputable abbrev associatedModuleQcohOnSite' :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  associatedModuleQcohOnSite B S hS (associatedModuleIsQuasicoherent B S hS)

/-- The functor `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)`, `𝓕 ↦ 𝓕^a`, of Stacks 03DX (1) is fully
faithful. -/
public noncomputable def fullyFaithfulAssociatedModuleQcohOnSite' :
    (associatedModuleQcohOnSite' B S hS).FullyFaithful :=
  fullyFaithfulAssociatedModuleQcohOnSite B S hS (associatedModuleIsQuasicoherent B S hS)
    (unitIsoOnQuasicoherent B S hS)

/-- **Essential surjectivity of the functor of Stacks 03DX (1)** for `τ = fppf`, over
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`. -/
public theorem essSurj_associatedModuleQcohOnSite'
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (associatedModuleQcohOnSite' B S hS).EssSurj :=
  essSurj_associatedModuleQcohOnSite B S hS (associatedModuleIsQuasicoherent B S hS) hsurj

/-- **Stacks 03DX (1) for `τ = fppf`, over essential surjectivity alone**: `𝓕 ↦ 𝓕^a` is an
equivalence `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_fppf, 𝒪)`. -/
public theorem isEquivalence_associatedModuleQcohOnSite'
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (associatedModuleQcohOnSite' B S hS).IsEquivalence :=
  isEquivalence_associatedModuleQcohOnSite B S hS (associatedModuleIsQuasicoherent B S hS) hsurj
    (unitIsoOnQuasicoherent B S hS)

/-- **The equivalence of categories of Stacks 03DX (1) for `τ = fppf`, over essential
surjectivity alone**: `QCoh(𝒪_S) ≌ QCoh((Sch/S)_fppf, 𝒪)`, with `𝓕 ↦ 𝓕^a` as its functor. -/
public noncomputable def associatedModuleEquivalence'
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  associatedModuleEquivalence B S hS (associatedModuleIsQuasicoherent B S hS) hsurj
    (unitIsoOnQuasicoherent B S hS)

end BigFppfOver

end AlgebraicGeometry

end
