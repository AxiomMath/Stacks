module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
import all StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf

/-!
# Unitors of the derived tensor product on quasi-coherent objects

Declarations built on
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal`.

## Main results

* `curriedTensor_canonicalDerivedMonoidal_eq`
* `tensorUnit_canonicalDerivedMonoidal_eq`
* `isMonoidal_derivedQuasicoherent`
* `monoidalCategory_quasiCoherentDerivedCategory`
* `tensorUnit_quasiCoherentDerivedCategory`
* `derivedTensorIsoCurriedTensor`
* `quasiCoherentDerivedTensor_obj_map_hom`
* `quasiCoherentDerivedTensor_map_app_hom`
* `whiskerLeft_hom_quasiCoherentDerivedCategory`
* `whiskerRight_hom_quasiCoherentDerivedCategory`
* `quasiCoherentDerivedTensorIsoCurriedTensor`
* `quasiCoherentDerivedTensorRightUnitor`
* `eqToHom_flip_curriedTensor_app`
* `quasiCoherentDerivedTensorRightUnitor_hom_app`
* `quasiCoherentDerivedTensorLeftUnitor`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.Duality

variable (X : Scheme.{u})

/-- The tensor product of `canonicalDerivedMonoidal` at the locally small model is `⊗ᴸ_{𝒪_X}`. -/
theorem curriedTensor_canonicalDerivedMonoidal_eq :
    @curriedTensor (DerivedCategory X.Modules) _ (Scheme.Modules.canonicalDerivedMonoidal X) =
      derivedTensor X := by
  rw [Scheme.Modules.curriedTensor_canonicalDerivedMonoidal]
  rfl

/-- The unit of `canonicalDerivedMonoidal` is `𝒪_X` in degree zero. -/
theorem tensorUnit_canonicalDerivedMonoidal_eq :
    @tensorUnit (DerivedCategory X.Modules) _
        (Scheme.Modules.canonicalDerivedMonoidal X).toMonoidalCategoryStruct =
      (DerivedPushforward.derivedStructureSheaf X).obj :=
  Scheme.Modules.tensorUnit_canonicalDerivedMonoidal X

/-- `D_QCoh(𝒪_X)` contains the unit and is closed under `⊗ᴸ_{𝒪_X}`, the latter by
[Stacks, Tag 08DX] part (1). -/
instance isMonoidal_derivedQuasicoherent :
    @ObjectProperty.IsMonoidal (DerivedCategory X.Modules) _
      (Scheme.Modules.canonicalDerivedMonoidal X)
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)) :=
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  { prop_unit := by
      rw [tensorUnit_canonicalDerivedMonoidal_eq]
      exact (DerivedPushforward.derivedStructureSheaf X).property
    prop_tensor := fun K L hK hL => by
      have h : K ⊗ L = ((derivedTensor X).obj K).obj L := by
        rw [← curriedTensor_canonicalDerivedMonoidal_eq]
        rfl
      rw [h]
      exact isQuasicoherent_homology_derivedTensor X ⟨K, hK⟩ ⟨L, hL⟩ }

/-- **`D_QCoh(𝒪_X)` is a monoidal category** under the derived tensor product, as a full monoidal
subcategory of `D(𝒪_X)` with the structure
`AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal`. -/
instance monoidalCategory_quasiCoherentDerivedCategory :
    MonoidalCategory (quasiCoherentDerivedCategory X) :=
  @ObjectProperty.fullMonoidalSubcategory _ _ (Scheme.Modules.canonicalDerivedMonoidal X) _ _

/-- The unit of the monoidal structure on `D_QCoh(𝒪_X)` is `𝒪_X` in degree zero. -/
theorem tensorUnit_quasiCoherentDerivedCategory :
    𝟙_ (quasiCoherentDerivedCategory X) = DerivedPushforward.derivedStructureSheaf X :=
  ObjectProperty.FullSubcategory.ext (tensorUnit_canonicalDerivedMonoidal_eq X)

/-- The ambient derived tensor product, as the tensor product of `canonicalDerivedMonoidal`. -/
def derivedTensorIsoCurriedTensor :
    derivedTensor X ≅
      @curriedTensor (DerivedCategory X.Modules) _ (Scheme.Modules.canonicalDerivedMonoidal X) :=
  eqToIso (curriedTensor_canonicalDerivedMonoidal_eq X).symm

/-- Whiskering on the left in `D_QCoh(𝒪_X)` is whiskering in `D(𝒪_X)`. -/
theorem whiskerLeft_hom_quasiCoherentDerivedCategory (K : quasiCoherentDerivedCategory X)
    {L L' : quasiCoherentDerivedCategory X} (g : L ⟶ L') :
    (((curriedTensor (quasiCoherentDerivedCategory X)).obj K).map g).hom =
      ((@curriedTensor (DerivedCategory X.Modules) _
        (Scheme.Modules.canonicalDerivedMonoidal X)).obj K.obj).map g.hom :=
  rfl

/-- Whiskering on the right in `D_QCoh(𝒪_X)` is whiskering in `D(𝒪_X)`. -/
theorem whiskerRight_hom_quasiCoherentDerivedCategory {K K' : quasiCoherentDerivedCategory X}
    (g : K ⟶ K') (L : quasiCoherentDerivedCategory X) :
    (((curriedTensor (quasiCoherentDerivedCategory X)).map g).app L).hom =
      ((@curriedTensor (DerivedCategory X.Modules) _
        (Scheme.Modules.canonicalDerivedMonoidal X)).map g.hom).app L.obj :=
  rfl

/-- **The derived tensor product `Stacks.Duality.quasiCoherentDerivedTensor` is the tensor
product of the monoidal structure of `D_QCoh(𝒪_X)`.** -/
def quasiCoherentDerivedTensorIsoCurriedTensor :
    quasiCoherentDerivedTensor X ≅ curriedTensor (quasiCoherentDerivedCategory X) :=
  NatIso.ofComponents (fun K => NatIso.ofComponents
      (fun L => ObjectProperty.isoMk _ (((derivedTensorIsoCurriedTensor X).app K.obj).app L.obj))
      (fun {L L'} g => by
        apply ObjectProperty.hom_ext
        rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
          quasiCoherentDerivedTensor_obj_map_hom, whiskerLeft_hom_quasiCoherentDerivedCategory]
        exact ((derivedTensorIsoCurriedTensor X).hom.app K.obj).naturality g.hom))
    (fun {K K'} g => by
      ext L
      rw [NatTrans.comp_app, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.FullSubcategory.comp_hom, quasiCoherentDerivedTensor_map_app_hom,
        whiskerRight_hom_quasiCoherentDerivedCategory]
      exact congrArg (fun t => t.app L.obj)
        ((derivedTensorIsoCurriedTensor X).hom.naturality g.hom))

/-- **The right unitor** `K ⊗ᴸ 𝒪_X ≅ K` on `D_QCoh(𝒪_X)`, natural in `K`, in the shape of the
bifunctor `Stacks.Duality.quasiCoherentDerivedTensor`. -/
def quasiCoherentDerivedTensorRightUnitor :
    (quasiCoherentDerivedTensor X).flip.obj (DerivedPushforward.derivedStructureSheaf X) ≅ 𝟭 _ :=
  ((flipFunctor _ _ _).mapIso (quasiCoherentDerivedTensorIsoCurriedTensor X)).app _ ≪≫
    eqToIso (congrArg (fun U => (curriedTensor (quasiCoherentDerivedCategory X)).flip.obj U)
      (tensorUnit_quasiCoherentDerivedCategory X).symm) ≪≫
    rightUnitorNatIso (quasiCoherentDerivedCategory X)

/-- Transport of `(curriedTensor C).flip.obj U` along an equality of objects, at `K`, is `K`
whiskered with the transport. -/
private lemma eqToHom_flip_curriedTensor_app {C : Type*} [Category C] [MonoidalCategory C]
    {U V : C} (h : U = V) (K : C) :
    (eqToHom (congrArg (fun W => (curriedTensor C).flip.obj W) h)).app K = K ◁ eqToHom h := by
  subst h
  simp

/-- **The right unitor through the monoidal structure**: `K ⊗ᴸ 𝒪_X ≅ K` is the identification of
`⊗ᴸ` with the tensor product of `D_QCoh(𝒪_X)`, then `K` tensored with `𝒪_X = 𝟙`, then `ρ_K`. -/
theorem quasiCoherentDerivedTensorRightUnitor_hom_app (K : quasiCoherentDerivedCategory X) :
    (quasiCoherentDerivedTensorRightUnitor X).hom.app K =
      ((quasiCoherentDerivedTensorIsoCurriedTensor X).hom.app K).app
          (DerivedPushforward.derivedStructureSheaf X) ≫
        K ◁ eqToHom (tensorUnit_quasiCoherentDerivedCategory X).symm ≫ (ρ_ K).hom := by
  simp only [quasiCoherentDerivedTensorRightUnitor, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom]
  rw [eqToHom_flip_curriedTensor_app]
  rfl

/-- **The left unitor** `𝒪_X ⊗ᴸ K ≅ K` on `D_QCoh(𝒪_X)`, natural in `K`. -/
def quasiCoherentDerivedTensorLeftUnitor :
    (quasiCoherentDerivedTensor X).obj (DerivedPushforward.derivedStructureSheaf X) ≅ 𝟭 _ :=
  (quasiCoherentDerivedTensorIsoCurriedTensor X).app _ ≪≫
    eqToIso (congrArg (fun U => (curriedTensor (quasiCoherentDerivedCategory X)).obj U)
      (tensorUnit_quasiCoherentDerivedCategory X).symm) ≪≫
    leftUnitorNatIso (quasiCoherentDerivedCategory X)

end Stacks.Duality

end
