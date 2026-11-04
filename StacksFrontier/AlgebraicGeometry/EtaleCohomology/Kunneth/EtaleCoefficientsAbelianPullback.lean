module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackMonoidalModels
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Inverse images of sheaves of `ℤ/mℤ̲`-modules and of abelian sheaves

Let `f : X ⟶ Y` be a morphism of schemes and `m` a natural number. The inverse image
`f⁻¹ = (ringedToposHom ℤ/m f).pullbackTopos` of sheaves of `ℤ/mℤ̲`-modules on the small models
of the étale sites and the inverse image `smallEtalePullbackAb f` of abelian sheaves on the small
étale sites are both defined as left adjoints of direct images, and the direct images commute
with forgetting the module structure (`pushforwardEtaleToSheafIso`). This file proves that the
inverse images commute with it too:

`f⁻¹ ⋙ (underlying abelian sheaf) ≅ (underlying abelian sheaf) ⋙ f⁻¹`,

and so do the derived inverse images, on `D(-_étale, ℤ/m)` and on bounded below objects.

## The proof

For `ℤ/mℤ`-coefficients the underlying abelian sheaf is fully faithful with essential image the
abelian sheaves annihilated by `m` (`etaleToSheafZModFullyFaithful`,
`mem_essImage_etaleToSheaf_iff`), and the inverse image of abelian sheaves preserves
annihilation by `m`, being additive. So the abelian inverse image restricts to a functor
`liftedPullback` between sheaves of `ℤ/mℤ̲`-modules, and the abelian adjunction `f⁻¹ ⊣ f_*`
restricts to an adjunction `liftedPullback ⊣ f_*` (`Adjunction.restrictFullyFaithful`). By
uniqueness of left adjoints, `liftedPullback` is the inverse image of sheaves of modules.

The derived statement follows: the derived inverse image of `D(-_étale, ℤ/m)` is the inverse
image applied degreewise, it being exact (`EtaleCoefficientsExactness`).

## Main definitions

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `liftedPullback`, `liftedPullbackAdjunction` — the abelian inverse image restricted to sheaves
  of `ℤ/mℤ̲`-modules, and its adjunction with the direct image.
* `pullbackEtaleToSheafIso` — **`f⁻¹` commutes with the underlying abelian sheaf.**
* `pullbackForgetIso` — the same on `D(-_étale, ℤ/m)`.
* `pullbackForgetPlusIso` — the same on bounded below objects, with the abelian inverse image
  read as its right derived functor on `D⁺`, as in
  `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`.

## Implementation notes

The inverse image `pullback` of `D(-_étale, Λ)` is built on the standard model of the derived
category (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean:394`); that fixes the model in the derived section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.ProjectionFormulaConstant (etaleRing siteSheafEquiv)
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

variable (m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The underived inverse images -/

section Underived

/-- The abelian inverse image of the underlying abelian sheaf of a sheaf of `ℤ/mℤ̲`-modules is
annihilated by `m`, hence again such an underlying abelian sheaf. -/
theorem smallEtalePullbackAb_obj_mem_essImage
    (M : SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod m)) Y)) :
    (etaleToSheaf (ULift.{u + 1} (ZMod m)) X).essImage
      ((smallEtalePullbackAb f).obj ((etaleToSheaf (ULift.{u + 1} (ZMod m)) Y).obj M)) :=
  (mem_essImage_etaleToSheaf_iff m X _).2 (nsmul_id_map_eq_zero m _
    ((mem_essImage_etaleToSheaf_iff m Y _).1 ((etaleToSheaf _ Y).obj_mem_essImage M)))

/-- **The abelian inverse image, restricted to sheaves of `ℤ/mℤ̲`-modules**: it carries the
underlying abelian sheaves of sheaves of `ℤ/mℤ̲`-modules to such, and the underlying abelian
sheaf is fully faithful on them. -/
def liftedPullback :
    SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod m)) Y) ⥤
      SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod m)) X) :=
  (etaleToSheaf (ULift.{u + 1} (ZMod m)) X).essImage.lift
      (etaleToSheaf (ULift.{u + 1} (ZMod m)) Y ⋙ smallEtalePullbackAb f)
      (smallEtalePullbackAb_obj_mem_essImage m f) ⋙
    (etaleToSheaf (ULift.{u + 1} (ZMod m)) X).toEssImage.inv

/-- The underlying abelian sheaf of `liftedPullback` is the abelian inverse image. -/
def liftedPullbackCompIso :
    liftedPullback m f ⋙ etaleToSheaf (ULift.{u + 1} (ZMod m)) X ≅
      etaleToSheaf (ULift.{u + 1} (ZMod m)) Y ⋙ smallEtalePullbackAb f :=
  Functor.isoWhiskerLeft (liftedPullback m f)
      (etaleToSheaf (ULift.{u + 1} (ZMod m)) X).toEssImageCompι.symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (etaleToSheaf (ULift.{u + 1} (ZMod m)) X).toEssImage.asEquivalence.counitIso _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.leftUnitor _) ≪≫
    ObjectProperty.liftCompιIso _ _ _

/-- **The restricted abelian inverse image is left adjoint to the direct image of sheaves of
`ℤ/mℤ̲`-modules**: the restriction of the abelian adjunction `f⁻¹ ⊣ f_*` along the fully
faithful underlying abelian sheaves. -/
def liftedPullbackAdjunction :
    liftedPullback m f ⊣ (ringedToposHom (ULift.{u + 1} (ZMod m)) f).pushforwardTopos :=
  (smallEtaleAdjunctionAb f).restrictFullyFaithful (etaleToSheafZModFullyFaithful m Y)
    (etaleToSheafZModFullyFaithful m X) (liftedPullbackCompIso m f).symm
    (pushforwardEtaleToSheafIso (ULift.{u + 1} (ZMod m)) f).symm

/-- **The inverse image of sheaves of `ℤ/mℤ̲`-modules is the restricted abelian inverse image**,
both being left adjoint to the direct image. -/
def pullbackToposIsoLiftedPullback :
    (ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackTopos ≅ liftedPullback m f :=
  (ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackPushforwardAdjunctionTopos.leftAdjointUniq
    (liftedPullbackAdjunction m f)

/-- **The underlying abelian sheaf of the inverse image of a sheaf of `ℤ/mℤ̲`-modules is the
inverse image of its underlying abelian sheaf.** -/
def pullbackEtaleToSheafIso :
    (ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackTopos ⋙
        etaleToSheaf (ULift.{u + 1} (ZMod m)) X ≅
      etaleToSheaf (ULift.{u + 1} (ZMod m)) Y ⋙ smallEtalePullbackAb f :=
  Functor.isoWhiskerRight (pullbackToposIsoLiftedPullback m f) _ ≪≫ liftedPullbackCompIso m f

/-- **The underlying abelian sheaf carries the counit of `f⁻¹ ⊣ f_*` on sheaves of
`ℤ/mℤ̲`-modules to that on abelian sheaves**, through `pullbackEtaleToSheafIso` and
`pushforwardEtaleToSheafIso`. -/
theorem etaleToSheaf_map_counit
    (N : SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod m)) X)) :
    (etaleToSheaf (ULift.{u + 1} (ZMod m)) X).map
        ((ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackPushforwardAdjunctionTopos.counit.app
          N) =
      (pullbackEtaleToSheafIso m f).hom.app
          ((ringedToposHom (ULift.{u + 1} (ZMod m)) f).pushforwardTopos.obj N) ≫
        (smallEtalePullbackAb f).map
          ((pushforwardEtaleToSheafIso (ULift.{u + 1} (ZMod m)) f).hom.app N) ≫
        (smallEtaleAdjunctionAb f).counit.app
          ((etaleToSheaf (ULift.{u + 1} (ZMod m)) X).obj N) := by
  rw [← Adjunction.leftAdjointUniq_hom_app_counit
    (ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackPushforwardAdjunctionTopos
    (liftedPullbackAdjunction m f), Functor.map_comp, liftedPullbackAdjunction,
    Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [pullbackEtaleToSheafIso, pullbackToposIsoLiftedPullback, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_inv,
    Category.assoc]
  rfl

/-- **The underlying abelian sheaf carries the unit of `f⁻¹ ⊣ f_*` on sheaves of
`ℤ/mℤ̲`-modules to that on abelian sheaves**, through `pullbackEtaleToSheafIso` and
`pushforwardEtaleToSheafIso`. -/
theorem etaleToSheaf_map_unit
    (M : SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod m)) Y)) :
    (etaleToSheaf (ULift.{u + 1} (ZMod m)) Y).map
        ((ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackPushforwardAdjunctionTopos.unit.app
          M) ≫
      (pushforwardEtaleToSheafIso (ULift.{u + 1} (ZMod m)) f).hom.app
          ((ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackTopos.obj M) ≫
      (smallEtalePushforwardAb f).map ((pullbackEtaleToSheafIso m f).hom.app M) =
    (smallEtaleAdjunctionAb f).unit.app ((etaleToSheaf (ULift.{u + 1} (ZMod m)) Y).obj M) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackPushforwardAdjunctionTopos
    (liftedPullbackAdjunction m f) M
  have h' := congrArg (etaleToSheaf (ULift.{u + 1} (ZMod m)) Y).map h
  have hu : (etaleToSheaf (ULift.{u + 1} (ZMod m)) Y).map
      ((liftedPullbackAdjunction m f).unit.app M) =
      (smallEtaleAdjunctionAb f).unit.app ((etaleToSheaf (ULift.{u + 1} (ZMod m)) Y).obj M) ≫
        (smallEtalePushforwardAb f).map ((liftedPullbackCompIso m f).symm.hom.app M) ≫
        (pushforwardEtaleToSheafIso (ULift.{u + 1} (ZMod m)) f).symm.hom.app
          ((liftedPullback m f).obj M) :=
    Adjunction.map_restrictFullyFaithful_unit_app _ _ _ _ _ M
  rw [Functor.map_comp, hu] at h'
  have hn := (pushforwardEtaleToSheafIso (ULift.{u + 1} (ZMod m)) f).hom.naturality
    ((pullbackToposIsoLiftedPullback m f).hom.app M)
  simp only [pullbackEtaleToSheafIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.map_comp,
    Functor.comp_map, Iso.symm_hom] at h' hn ⊢
  rw [← reassoc_of% hn]
  simp only [pullbackToposIsoLiftedPullback] at h' ⊢
  rw [reassoc_of% h']
  simp

end Underived

/-! ### The derived inverse images -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The inverse image `f⁻¹` on sheaves of `ℤ/mℤ̲`-modules is additive, being a left adjoint. -/
instance pullbackTopos_uliftZMod_additive :
    (ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackTopos.Additive :=
  Adjunction.left_adjoint_additive
    (ringedToposHom (ULift.{u + 1} (ZMod m)) f).pullbackPushforwardAdjunctionTopos

/-- **The derived inverse image of `D(-_étale, ℤ/m)` commutes with the underlying complex of
abelian sheaves**, the abelian inverse image acting degreewise: the derived inverse image is the
inverse image applied degreewise, it being exact, and `pullbackEtaleToSheafIso` applied
degreewise. -/
def pullbackForgetIso :
    pullback (ULift.{u + 1} (ZMod m)) f ⋙ forgetDerived (ULift.{u + 1} (ZMod m)) X ≅
      forgetDerived (ULift.{u + 1} (ZMod m)) Y ⋙ (smallEtalePullbackAb f).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (Stacks.Sheaves.DerivedPullback.derivedPullbackIsoMapDerived
        (ringedToposHom (ULift.{u + 1} (ZMod m)) f)) _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (pullbackEtaleToSheafIso m f) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

/-- **On bounded below objects, the derived inverse image of `D(-_étale, ℤ/m)` commutes with the
underlying complex of abelian sheaves**, the abelian inverse image read as its right derived
functor on `D⁺`, as in `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`. -/
def pullbackForgetPlusIso :
    DerivedCategory.Plus.ι ⋙ pullback (ULift.{u + 1} (ZMod m)) f ⋙
        forgetDerived (ULift.{u + 1} (ZMod m)) X ≅
      forgetDerivedPlus (ULift.{u + 1} (ZMod m)) Y ⋙
        (smallEtalePullbackAb f).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι (pullbackForgetIso m f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl (DerivedCategory.Plus.ι ⋙
      forgetDerived (ULift.{u + 1} (ZMod m)) Y)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (forgetDerivedPlus (ULift.{u + 1} (ZMod m)) Y)
      (Functor.isoWhiskerRight (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso
        (smallEtalePullbackAb f)) DerivedCategory.Plus.ι)

end Derived

end Stacks.EtaleCohomology.EtaleCoefficients

end
