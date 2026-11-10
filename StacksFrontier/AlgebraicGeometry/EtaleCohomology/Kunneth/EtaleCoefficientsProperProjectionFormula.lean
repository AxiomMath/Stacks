module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsSmallModelBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionProjectionFormula
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection formula for a proper morphism on `D(-_étale, Λ)` of the Künneth section

The derived categories `D(X_étale, Λ)` of the Künneth section
(`Stacks.EtaleCohomology.EtaleCoefficients.DerivedModules`, on the small model
`SmallModel X.Etale`) and the derived categories of sheaves of `Λ`-modules
`D(Stacks.EtaleCohomology.EtaleModules Λ X)` on which [Stacks, Tag 0F0G] is proved are identified
by the composite equivalence

`D(EtaleModules Λ X) ≌ D(etaleRingedSite Λ X) ≌ D(X_étale, ULift Λ)`

of `Stacks.EtaleCohomology.etaleDerivedEquivalence` and the derived pullback along the comparison
of the two small models (`Stacks.EtaleCohomology.EtaleCoefficients.smallModelDerivedPullback`).
Under it the projection map of [Stacks, Tag 0943] on the first side
(`Stacks.EtaleCohomology.etalePushforwardProjectionMap`) and the projection map of the Künneth
section (`Stacks.EtaleCohomology.EtaleCoefficients.projectionMap`) are invertible at the same
objects. So [Stacks, Tag 0F0G] reads on `D(-_étale, Λ)`.

## Main definitions

* `Stacks.EtaleCohomology.EtaleCoefficients.etaleModulesDerivedComparison`: the composite
  equivalence `D(EtaleModules Λ X) ⥤ D(X_étale, ULift Λ)`.

## Main results

* `EtaleCoefficients.isIso_etalePushforwardProjectionMap_iff_isIso_projectionMap` and
  `isIso_etalePushforwardProjectionMap_iff_isIso_projectionFormulaMap`: the map of
  [Stacks, Tag 0943] on sheaves of `Λ`-modules against the two variants of the projection map on
  `D(-_étale, ULift Λ)`.
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_projectionMap_of_isProper`: the projection map
  `A ⊗^L Rf_*B ⟶ Rf_*(f⁻¹A ⊗^L B)` on `D(-_étale, ULift Λ)` is invertible for `f` proper and `Λ`
  torsion, at all unbounded `A` and `B` (the content of [Stacks, Tag 0F0G]).
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_projectionFormulaMap_of_isProper` and
  `isIso_projectionFormulaMap_zmod_of_isProper`: the same for the map
  `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L f⁻¹K)` of Stacks 0B56 of `ringedToposHom (ULift Λ) f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `Stacks.EtaleCohomology.etaleDerivedEquivalence` and
-- `Stacks.EtaleCohomology.etalePushforwardProjectionMap` are stated for the standard model of the
-- derived category.
attribute [local instance] HasDerivedCategory.standard

/-- Sheafification of presheaves of sets on the small model `AsSmall X.Etale`, at the universe of
its objects. -/
local instance (priority := high) hasSheafify_etaleRingedSite_type (Λ : Type) [CommRing Λ]
    (Z : Scheme.{u}) :
    HasSheafify (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (etaleRingedSite.{u, 0} Λ Z)).J
      (Type (u + 1)) :=
  instHasSheafifyType.{u + 1, u + 1} _

variable (Λ : Type) [CommRing Λ]

/-- **The comparison `D(EtaleModules Λ X) ⥤ D(X_étale, ULift Λ)`** of the derived category of
sheaves of `Λ`-modules on the small étale site with the derived category of the Künneth section:
`Stacks.EtaleCohomology.etaleDerivedEquivalence` followed by the derived pullback along the
comparison of the two small models. -/
abbrev etaleModulesDerivedComparison (X : Scheme.{u}) :
    DerivedCategory (EtaleModules.{u, 0} Λ X) ⥤ DerivedModules (ULift.{u + 1} Λ) X :=
  (etaleDerivedEquivalence.{u, 0} Λ X).functor ⋙ smallModelDerivedPullback Λ X

/-- The comparison is an equivalence. -/
instance isEquivalence_etaleModulesDerivedComparison (X : Scheme.{u}) :
    (etaleModulesDerivedComparison Λ X).IsEquivalence :=
  inferInstance

/-- The tensor product of sheaves of `Λ̲`-modules on `AsSmall X.Etale` is additive in the first
variable. -/
local instance sheafTensor_additive_smallModelTopos (X : Scheme.{u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (smallModelTopos Λ X).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive _

/-- The tensor product of sheaves of `Λ̲`-modules on `AsSmall X.Etale` is additive in the second
variable. -/
local instance sheafTensor_obj_additive_smallModelTopos (X : Scheme.{u})
    (M : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (smallModelTopos Λ X).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive _ M

/-- Total tensor complexes of complexes of sheaves of `Λ̲`-modules on `AsSmall X.Etale` exist. -/
local instance hasMapBifunctor_sheafTensor_smallModelTopos (X : Scheme.{u})
    (A B : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor (smallModelTopos Λ X).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor _ A B

variable {Λ}

/-- **The projection map of [Stacks, Tag 0943] on sheaves of `Λ`-modules and the projection map of
the Künneth section are invertible at the same objects.** For a morphism of schemes `f : X ⟶ Y`,
`E ∈ D(EtaleModules Λ X)` and `K ∈ D(EtaleModules Λ Y)`, the map
`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)` is invertible exactly when the projection map
`K' ⊗^L Rf_*E' ⟶ Rf_*(f⁻¹K' ⊗^L E')` on `D(-_étale, ULift Λ)` is, at the images `K'`, `E'` of `K`
and `E` under `etaleModulesDerivedComparison`. -/
theorem isIso_etalePushforwardProjectionMap_iff_isIso_projectionMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (E : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ Y)) :
    IsIso (etalePushforwardProjectionMap.{u, 0} Λ f E K) ↔
      IsIso (projectionMap (ULift.{u + 1} Λ) f ((etaleModulesDerivedComparison Λ Y).obj K)
        ((etaleModulesDerivedComparison Λ X).obj E)) := by
  rw [isIso_etalePushforwardProjectionMap_iff,
    ← Stacks.Cohomology.RingedSiteHomReadings.isIso_projectionMap_toRingedToposSiteHom_iff
      (etaleRingedSiteHom.{u, 0} Λ f)]
  exact isIso_projectionMap_smallModel_iff f _ _

/-- **[Stacks, Tag 0F0G] on `D(-_étale, Λ)` of the Künneth section.** Let `f : X ⟶ Y` be a proper
morphism of schemes and `Λ` a torsion ring. For all `A ∈ D(Y_étale, Λ)` and `B ∈ D(X_étale, Λ)`,
unbounded, the projection map

`A ⊗^L_Λ Rf_*B ⟶ Rf_*(f⁻¹A ⊗^L_Λ B)`

is an isomorphism. This is `Stacks.EtaleCohomology.isIso_etalePushforwardProjectionMap_of_isProper`
read through `isIso_etalePushforwardProjectionMap_iff_isIso_projectionMap`; the coefficient ring of
the Künneth section is `ULift Λ`, the copy of `Λ` in the universe of its sites. -/
theorem isIso_projectionMap_of_isProper (hΛ : IsAddTorsion Λ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (A : DerivedModules (ULift.{u + 1} Λ) Y)
    (B : DerivedModules (ULift.{u + 1} Λ) X) :
    IsIso (projectionMap (ULift.{u + 1} Λ) f A B) := by
  rw [projectionMap, Stacks.Cohomology.AbstractKunnethMap.isIso_projectionMap_iff_of_iso_objects
    _ _ _ _ ((etaleModulesDerivedComparison Λ Y).objObjPreimageIso A).symm
    ((etaleModulesDerivedComparison Λ X).objObjPreimageIso B).symm, ← projectionMap,
    ← isIso_etalePushforwardProjectionMap_iff_isIso_projectionMap]
  exact isIso_etalePushforwardProjectionMap_of_isProper Λ hΛ f _ _

/-- **The map of [Stacks, Tag 0943] on sheaves of `Λ`-modules and the map of Stacks 0B56 on
`D(-_étale, ULift Λ)` are invertible at the same objects.** For `f : X ⟶ Y`,
`E ∈ D(EtaleModules Λ X)` and `K ∈ D(EtaleModules Λ Y)`, the map
`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)` is invertible exactly when the map
`Rf_*E' ⊗^L K' ⟶ Rf_*(E' ⊗^L f⁻¹K')` of the morphism of ringed topoi `ringedToposHom (ULift Λ) f`
(`Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap`) is, at the images `E'`,
`K'` of `E` and `K` under `etaleModulesDerivedComparison`. -/
theorem isIso_etalePushforwardProjectionMap_iff_isIso_projectionFormulaMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (E : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ Y)) :
    IsIso (etalePushforwardProjectionMap.{u, 0} Λ f E K) ↔
      IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        (ringedToposHom (ULift.{u + 1} Λ) f) (isMorphismOfSites_ringedToposHom _ f)
        ((etaleModulesDerivedComparison Λ X).obj E)
        ((etaleModulesDerivedComparison Λ Y).obj K)) := by
  rw [isIso_etalePushforwardProjectionMap_iff,
    ← Stacks.Cohomology.RingedSiteHomReadings.isIso_projectionFormulaMap_toRingedToposSiteHom_iff
      (etaleRingedSiteHom.{u, 0} Λ f)]
  exact isIso_projectionFormulaMap_smallModel_iff f _ _

/-- **[Stacks, Tag 0F0G] on the derived categories `D(-_étale, Λ)` of the Künneth section, in the
form of Stacks 0B56.** Let `f : X ⟶ Y` be a proper morphism of schemes and `Λ` a torsion ring. For
all `E ∈ D(X_étale, Λ)` and `K ∈ D(Y_étale, Λ)`, unbounded, the map

`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)`

of the morphism of ringed topoi `ringedToposHom (ULift Λ) f` is an isomorphism. -/
@[sga "4 XVIII 2.13" "special case", sga "5 III 1.6" "special case"]
theorem isIso_projectionFormulaMap_of_isProper (hΛ : IsAddTorsion Λ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (E : DerivedModules (ULift.{u + 1} Λ) X)
    (K : DerivedModules (ULift.{u + 1} Λ) Y) :
    IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
      (ringedToposHom (ULift.{u + 1} Λ) f) (isMorphismOfSites_ringedToposHom _ f) E K) := by
  have h := Stacks.Cohomology.AbstractKunnethMap.isIso_adjunctionTensorMap_iff_of_iso_objects
    (TC := Functor.uncurry.obj (tensor (ULift.{u + 1} Λ) Y))
    (TD := Functor.uncurry.obj (tensor (ULift.{u + 1} Λ) X))
    (adjunction (ULift.{u + 1} Λ) f) (pullbackTensorIso (ULift.{u + 1} Λ) f).hom
    ((etaleModulesDerivedComparison Λ X).objObjPreimageIso E)
    ((etaleModulesDerivedComparison Λ Y).objObjPreimageIso K)
  exact h.1 ((isIso_etalePushforwardProjectionMap_iff_isIso_projectionFormulaMap f _ _).1
    (isIso_etalePushforwardProjectionMap_of_isProper Λ hΛ f _ _))

/-- **[Stacks, Tag 0F0G] on `D(-_étale, ℤ/m)` of the Künneth section**, for `m ≥ 1`: the map
`Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L f⁻¹K)` of `ringedToposHom (ULift (ZMod m)) f` is an isomorphism for
`f` proper. -/
theorem isIso_projectionFormulaMap_zmod_of_isProper (m : ℕ) [NeZero m] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (E : DerivedModules (ULift.{u + 1} (ZMod m)) X)
    (K : DerivedModules (ULift.{u + 1} (ZMod m)) Y) :
    IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
      (ringedToposHom (ULift.{u + 1} (ZMod m)) f) (isMorphismOfSites_ringedToposHom _ f) E K) :=
  isIso_projectionFormulaMap_of_isProper (fun x => isOfFinAddOrder_of_finite x) f E K

end Stacks.EtaleCohomology.EtaleCoefficients

end
