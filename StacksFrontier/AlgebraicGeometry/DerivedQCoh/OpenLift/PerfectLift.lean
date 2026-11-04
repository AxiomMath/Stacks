module

public import StacksFrontier.CategoryTheory.Monoidal.RigidLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.CategoryTheory.Monoidal.Reseat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedRestrictionMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.DerivedTensorDatumBridge
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.KoszulLift
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.PerfectSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCohomologyBijective
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict

/-!
# Lifting a morphism out of a perfect object over a quasi-compact open: the tools

Let `X` be an affine scheme, let `U ⊆ X` be a quasi-compact open and let `E, E'` be objects of
`D_QCoh(𝒪_X)` with `E` perfect. Every morphism `α : E|_U ⟶ E'|_U` is `γ|_U ∘ (β|_U)⁻¹` for a roof
`E ←β– E ⊗^L I –γ→ E'` with `I` perfect and `β` induced by a morphism `I ⟶ 𝒪_X` that is an
isomorphism on `U` ([Stacks, Tag 08EH]). This file provides the monoidal structure on
restriction to `U` and the comparison of the two models of restriction that this statement uses.

## Main results

* `Stacks.SheafOfModules.sliceRestrictionMonoidal`: restriction to an open, as a monoidal
  functor out of `D(𝒪_X)`.
* `Stacks.DerivedQCoh.OpenLift.derivedRestrictionIsoDerivedRestrictModules`: the two models of
  restriction to an open of `Spec A` agree on derived categories.

## References

* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
  Opposite AlgebraicGeometry
open Stacks.DerivedTensor.ExtensionByZero (restriction)

universe u

namespace Stacks.SheafOfModules

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- Restriction to the opens contained in `U`, as a strong monoidal functor from `D(O_X)` with
the derived tensor product `Stacks.SheafOfModules.derivedMonoidalStructure` to the derived
category of the slice site with its derived tensor product. -/
@[instance_reducible]
def sliceRestrictionMonoidal :
    letI := Stacks.DerivedTensor.ExtensionByZero.additive_restriction (ringedSite Rc) U
    letI := Stacks.DerivedTensor.ExtensionByZero.preservesFiniteLimits_restriction (ringedSite Rc) U
    letI := Stacks.DerivedTensor.ExtensionByZero.preservesFiniteColimits_restriction
      (ringedSite Rc) U
    letI := derivedMonoidalStructure Rc
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal ((ringedSite Rc).O.over U)
    (𝟭 (DerivedCategory (StructureSheafModules Rc)) ⋙
      (restriction (ringedSite Rc) U).mapDerivedCategory).Monoidal :=
  letI := Stacks.DerivedTensor.ExtensionByZero.additive_restriction (ringedSite Rc) U
  letI := Stacks.DerivedTensor.ExtensionByZero.preservesFiniteLimits_restriction (ringedSite Rc) U
  letI := Stacks.DerivedTensor.ExtensionByZero.preservesFiniteColimits_restriction
    (ringedSite Rc) U
  Functor.monoidalCompOf (derivedMonoidalStructure Rc)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Rc)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal ((ringedSite Rc).O.over U))
    (𝟭 _) (restriction (ringedSite Rc) U).mapDerivedCategory
    (@reseatMonoidal _ _ (DerivedMonoidal.derivedMonoidal Rc) _ _ (derivedTensorMonoidalIso Rc)
      (DerivedMonoidal.canonicalUnitIso Rc))
    (Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal (ringedSite Rc) U)

end Stacks.SheafOfModules

namespace CategoryTheory.Functor

variable {C D D' : Type*} [Category C] [Category D] [Category D']

/-- `Φ (F g)` is `R g` conjugated by a natural isomorphism `F ⋙ Φ ≅ R`. -/
theorem map_map_eq_of_natIso (F : C ⥤ D) (Φ : D ⥤ D') (R : C ⥤ D') (ri : F ⋙ Φ ≅ R) {P Q : C}
    (g : P ⟶ Q) : Φ.map (F.map g) = ri.hom.app P ≫ R.map g ≫ ri.inv.app Q := by
  rw [← ri.hom.naturality_assoc g, Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- A factorization after `R` is a factorization after `F`, for `R ≅ F ⋙ Φ` with `Φ`
faithful. -/
theorem map_comp_eq_map_of_natIso (F : C ⥤ D) (Φ : D ⥤ D') (hΦ : Φ.Faithful) (R : C ⥤ D')
    (ri : F ⋙ Φ ≅ R) {X Y Z : C} (b : X ⟶ Y) (a : F.obj Y ⟶ F.obj Z) (c : X ⟶ Z)
    (h : R.map b ≫ (ri.inv.app Y ≫ Φ.map a ≫ ri.hom.app Z) = R.map c) :
    F.map b ≫ a = F.map c := by
  apply Φ.map_injective
  rw [Φ.map_comp, map_map_eq_of_natIso F Φ R ri b, map_map_eq_of_natIso F Φ R ri c, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

/-- A factorization after `F` is a factorization after `R`, for `R ≅ F ⋙ Φ` with `Φ`
fully faithful. -/
theorem map_comp_eq_map_of_natIso' (F : C ⥤ D) (Φ : D ⥤ D') (hΦ : Φ.Full)
    (R : C ⥤ D') (ri : F ⋙ Φ ≅ R) {X Y Z : C} (b : X ⟶ Y) (α : R.obj Y ⟶ R.obj Z) (c : X ⟶ Z)
    (h : F.map b ≫ Φ.preimage (ri.hom.app Y ≫ α ≫ ri.inv.app Z) = F.map c) :
    R.map b ≫ α = R.map c := by
  have h' := congrArg Φ.map h
  rw [Φ.map_comp, Φ.map_preimage, map_map_eq_of_natIso F Φ R ri b,
    map_map_eq_of_natIso F Φ R ri c] at h'
  simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id,
    Iso.inv_hom_id_app_assoc] using congrArg (ri.inv.app X ≫ · ≫ ri.hom.app Z) h'

/-- A factorization is transported along a natural isomorphism. -/
theorem map_comp_eq_map_of_iso (R R' : C ⥤ D) (ψ : R ≅ R') {X Y Z : C} (β : X ⟶ Y)
    (a : R'.obj Y ⟶ R'.obj Z) (γ : X ⟶ Z)
    (h : R.map β ≫ ψ.hom.app Y ≫ a ≫ ψ.inv.app Z = R.map γ) : R'.map β ≫ a = R'.map γ := by
  have e : ∀ {P Q : C} (g : P ⟶ Q), R'.map g = ψ.inv.app P ≫ R.map g ≫ ψ.hom.app Q :=
    fun g => by simp
  rw [e β, e γ, ← h]
  simp

/-- An isomorphism after `R` is an isomorphism after `F`, for `R ≅ F ⋙ Φ` with `Φ` fully
faithful. -/
theorem isIso_map_of_natIso (F : C ⥤ D) (Φ : D ⥤ D') (hΦ : Φ.Full) (hΦ' : Φ.Faithful)
    (R : C ⥤ D') (ri : F ⋙ Φ ≅ R) {X Y : C} (g : X ⟶ Y) (h : IsIso (R.map g)) :
    IsIso (F.map g) := by
  have : IsIso (Φ.map (F.map g)) := (NatIso.isIso_map_iff ri g).mpr h
  exact (FullyFaithful.ofFullyFaithful Φ).isIso_of_isIso_map (F.map g)

/-- An isomorphism after `F` is an isomorphism after `R`, for `R ≅ F ⋙ Φ`. -/
theorem isIso_map_of_natIso' (F : C ⥤ D) (Φ : D ⥤ D') (R : C ⥤ D') (ri : F ⋙ Φ ≅ R) {X Y : C}
    (g : X ⟶ Y) (h : IsIso (F.map g)) : IsIso (R.map g) :=
  (NatIso.isIso_map_iff ri g).mp (Functor.map_isIso Φ (F.map g))

end CategoryTheory.Functor

namespace Stacks.DerivedQCoh.OpenLift

open Koszul.DerivedSystem Stacks.SheafOfModules Stacks.Cohomology.OpenSubspace

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- The derived restriction `Stacks.Cohomology.OpenSubspace.derivedRestriction` to an open of
`Spec A` is isomorphic to the functor `AlgebraicGeometry.RingedSpace.derivedRestrictModules`
induced by the exact restriction functor. -/
def derivedRestrictionIsoDerivedRestrictModules {A : CommRingCat.{u}} (U : (Spec A).Opens) :
    derivedRestriction (Spec A).ringCatSheaf U ≅
      AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace U :=
  Koszul.DerivedSystem.derivedRestrictionIsoMapDerivedCategory U ≪≫
    @Functor.mapDerivedCategoryCongr _ _ _ _ _ _ _ _ _ _
      (ExtensionByZeroModules.jStar_additive U (Spec A).ringCatSheaf)
      (Koszul.DerivedSystem.jStar_preservesFiniteLimits (Spec A).ringCatSheaf U)
      (Koszul.DerivedSystem.jStar_preservesFiniteColimits (Spec A).ringCatSheaf U)
      (AlgebraicGeometry.RingedSpace.restrictModules_additive (Spec A).toRingedSpace U)
      (AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits
        (Spec A).toRingedSpace U)
      (AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits
        (Spec A).toRingedSpace U)
      (Iso.refl _)

end Stacks.DerivedQCoh.OpenLift

end
