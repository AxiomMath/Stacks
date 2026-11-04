module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.DerivedModuleCorrespondence
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationEdge
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The morphism `ξ̃ : ⨁ Ω^•_{Y/S}[-n_i] ⟶ Rf_*Ω^•_{X/S}` of the Leray--Hirsch theorem

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes, and let `ξ_i ∈ H^{n_i}_{dR}(X/S)`.
Proposition 0FMR of the Stacks project considers, for each `i`, the morphism

`ξ'_i : Ω^•_{X/S} ⟶ Ω^•_{X/S}[n_i]`

of Remark 0FU7 in `D(X, (f ≫ g)⁻¹𝒪_S)`, and the composite

`ξ̃_i : Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S} ⟶ Rf_*Ω^•_{X/S}[n_i]`

of the canonical map with `Rf_*ξ'_i`, in `D(Y, g⁻¹𝒪_S)`; it then assembles the translates
`ξ̃_i[-n_i]` into

`ξ̃ = ⨁ ξ̃_i[-n_i] : ⨁ Ω^•_{Y/S}[-n_i] ⟶ Rf_*Ω^•_{X/S}`.

This file constructs these morphisms.

## Main definitions

* `AlgebraicGeometry.DeRhamLerayHirsch.relativeDirectImage`: the derived direct image
  `Rf_* : D(X, (f ≫ g)⁻¹𝒪_S) ⥤ D(Y, g⁻¹𝒪_S)`.
* `AlgebraicGeometry.DeRhamLerayHirsch.deRhamDirectImageMap`: the canonical map
  `Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}`, the canonical map of de Rham complexes `Ω^•_{Y/S} ⟶ f_*Ω^•_{X/S}`
  followed by the comparison `f_* ⟶ Rf_*`.
* `AlgebraicGeometry.DeRhamLerayHirsch.classDirectImageMorphism`: `ξ̃_i`.
* `AlgebraicGeometry.DeRhamLerayHirsch.lerayHirschMorphism`: `ξ̃`.

## Implementation notes

The direct image is taken along `Stacks.DeRhamBaseChange.inverseImageBaseMap` of the square
`(f, 𝟙 S)`, and the canonical map of de Rham complexes is
`Stacks.DeRhamBaseChange.deRhamPushforwardInt` of the same square: these are the data through
which the library identifies the pullback `f^* : H^*_{dR}(Y/S) ⟶ H^*_{dR}(X/S)` with the canonical
map followed by the Leray identification
(`Stacks.DeRhamBaseChange.deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback`).
The derived categories are the standard models, as for Remark 0FU7, and `Rf_*` commutes with the
shift through its structure of a right derived functor
(`CategoryTheory.Functor.IsRightDerivedFunctor.commShift`), as do the derived sections functors.

## References

* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The relative de Rham complex `Ω^•_{X/S}`, extended by zero, as an object of `D(X, p⁻¹𝒪_S)`. -/
abbrev deRhamObject (p : X ⟶ S) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase p))) :=
  DerivedCategory.Q.obj (deRhamCochainComplex p)

/-- The morphism of ringed spaces `(X, (f ≫ g)⁻¹𝒪_S) ⟶ (Y, g⁻¹𝒪_S)` underlying `f`. -/
abbrev baseMap : inverseImageBase (f ≫ g) ⟶ inverseImageBase g :=
  inverseImageBaseMap f (f ≫ g) g (𝟙 S) (Category.comp_id _).symm

/-- The derived direct image `Rf_* : D(X, (f ≫ g)⁻¹𝒪_S) ⥤ D(Y, g⁻¹𝒪_S)`. -/
abbrev relativeDirectImage :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase (f ≫ g)))) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase g))) :=
  derivedPushforward (baseMap f g)

/-- **The canonical map `Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}`** in `D(Y, g⁻¹𝒪_S)`: the canonical map of de
Rham complexes `Ω^•_{Y/S} ⟶ f_*Ω^•_{X/S}` followed by the comparison `f_* ⟶ Rf_*`. -/
def deRhamDirectImageMap :
    deRhamObject g ⟶ (relativeDirectImage f g).obj (deRhamObject (f ≫ g)) :=
  DerivedCategory.Q.map (deRhamPushforwardInt f (f ≫ g) g (𝟙 S) (Category.comp_id _).symm) ≫
    pushforwardComparisonQ (baseMap f g) (ProperSmoothDeRham.deRhamComplexInt (f ≫ g))

/-- The morphism `ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]` of Remark 0FU7 attached to `ξ ∈ H^n_{dR}(X/S)`. -/
abbrev classMorphism (p : X ⟶ S) (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n) :
    deRhamObject p ⟶ (deRhamObject p)⟦n⟧ :=
  SheafOfModules.deRhamClassMorphism (Scheme.Hom.deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n ξ

/-- `ξ̃ : Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}[n]`, the canonical map followed by `Rf_*ξ'`. -/
def classDirectImageMorphism (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) n) :
    deRhamObject g ⟶ ((relativeDirectImage f g).obj (deRhamObject (f ≫ g)))⟦n⟧ :=
  deRhamDirectImageMap f g ≫ (relativeDirectImage f g).map (classMorphism (f ≫ g) n ξ) ≫
    ((relativeDirectImage f g).commShiftIso n).hom.app _

/-- `ξ̃[-n] : Ω^•_{Y/S}[-n] ⟶ Rf_*Ω^•_{X/S}`. -/
def classDirectImageSummand (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) n) :
    (deRhamObject g)⟦-n⟧ ⟶ (relativeDirectImage f g).obj (deRhamObject (f ≫ g)) :=
  (classDirectImageMorphism f g n ξ)⟦-n⟧' ≫
    (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app _

/-- The Leray–Hirsch morphism of Proposition 0FMR,
`ξ̃ = ⨁ ξ̃_i[-n_i] : ⨁ Ω^•_{Y/S}[-n_i] ⟶ Rf_*Ω^•_{X/S}`. -/
def lerayHirschMorphism {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ)) :
    (⨁ fun i => (deRhamObject g)⟦-(n i : ℤ)⟧) ⟶
      (relativeDirectImage f g).obj (deRhamObject (f ≫ g)) :=
  biproduct.desc fun i => classDirectImageSummand f g (n i) (ξ i)

end AlgebraicGeometry.DeRhamLerayHirsch
