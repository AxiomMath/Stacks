module

public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse

/-!
# Scalars and the derived tensor product with a fixed object

Let `R` be a commutative ring and `M` an object of `D(R)`. The derived tensor product
`CochainComplex.DerivedTensor.derivedTensorProduct M` carries a scalar multiple `r • 𝟙` of the
identity of an object to `r • 𝟙`: it is computed by tensoring with a K-flat resolution, which is
termwise the tensor product of modules, and `(r • id) ⊗ id = r • id`. Consequently the functors
`N ↦ Hⁿ(N ⊗ᴸ M)` on `R`-modules carry multiplication by `r` to multiplication by `r`, which is
what makes the transformations of the dual notion of an obstruction theory (Stacks 07YX)
`R`-linear as soon as they are additive and natural.

## Main results

* `CochainComplex.DerivedTensor.trightCochain_map_smul_id`: on cochain complexes.
* `CochainComplex.DerivedTensor.derivedTensorProduct_map_smul_id`: in the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v w

namespace CategoryTheory.Localization

variable {R : Type*} [CommRing R] {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E] [Linear R C] [Linear R D] [Linear R E]
  {W : MorphismProperty C}

/-- A functor out of a localization, lifted from a functor carrying `r • 𝟙` to `r • 𝟙`, carries
`r • 𝟙` of a localized object to `r • 𝟙`, provided the localization functor does. -/
theorem lift_map_smul_id_obj (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D)
    [L.IsLocalization W] (r : R) (hL : ∀ Y : C, L.map (r • 𝟙 Y) = r • 𝟙 (L.obj Y))
    (hF' : ∀ Y : C, F.map (r • 𝟙 Y) = r • 𝟙 (F.obj Y)) (Y : C) :
    (lift F hF L).map (r • 𝟙 (L.obj Y)) = r • 𝟙 _ := by
  have hnat := (fac F hF L).hom.naturality (r • 𝟙 Y)
  rw [Functor.comp_map, hL, hF', Linear.comp_smul, Category.comp_id] at hnat
  rw [← cancel_mono ((fac F hF L).hom.app Y), Linear.smul_comp, Category.id_comp]
  exact hnat

end CategoryTheory.Localization

namespace CochainComplex.DerivedTensor

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

variable {R : Type u} [CommRing R]

/-- Tensoring with a fixed complex on the right carries `r • 𝟙` to `r • 𝟙`. -/
theorem trightCochain_map_smul_id (G X : CochainComplex (ModuleCat.{max u v} R) ℤ) (r : R) :
    (TrightCochain G).map (r • 𝟙 X) = r • 𝟙 _ := by
  change HomologicalComplex.mapBifunctorMap (r • 𝟙 X) (𝟙 G) (curriedTensor _)
    (ComplexShape.up ℤ) = r • 𝟙 (HomologicalComplex.mapBifunctor X G (curriedTensor _)
      (ComplexShape.up ℤ))
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, Linear.comp_smul,
    Category.comp_id]
  have h : ((curriedTensor (ModuleCat.{max u v} R)).map (r • 𝟙 (X.X i))).app (G.X j) =
      r • 𝟙 _ := by
    rw [curriedTensor_map_app]
    exact ModuleCat.hom_ext <| TensorProduct.ext' fun x y =>
      (TensorProduct.smul_tmul' r x y).symm
  rw [h, Linear.smul_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]

variable [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- The localized tensor functor `Tright K ⋙ Qh` carries `r • 𝟙` to `r • 𝟙`. -/
theorem tright_comp_Qh_map_smul_id (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (Y : HomotopyCategory (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) (r : R) :
    (Tright K ⋙ DerivedCategory.Qh).map (r • 𝟙 Y) = r • 𝟙 _ := by
  obtain ⟨Y'⟩ := Y
  have hY : r • 𝟙 ((HomotopyCategory.quotient (ModuleCat.{max u v} R)
      (ComplexShape.up ℤ)).obj Y') =
      (HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).map
        (r • 𝟙 Y') := by simp
  change (Tright K ⋙ DerivedCategory.Qh).map (r • 𝟙 ((HomotopyCategory.quotient
    (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).obj Y')) = _
  rw [hY]
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{max u v} R)
    (ComplexShape.up ℤ)).map ((TrightCochain K).map (r • 𝟙 Y'))) = _
  rw [trightCochain_map_smul_id]
  simp
  rfl

/-- **The derived tensor product with a fixed object carries `r • 𝟙` to `r • 𝟙`.** -/
theorem derivedTensorProduct_map_smul_id (M X : DerivedCategory (ModuleCat.{max u v} R))
    (r : R) : (derivedTensorProduct M).map (r • 𝟙 X) = r • 𝟙 _ := by
  -- reduce to an object in the image of `Qh`
  suffices h : ∀ Y : HomotopyCategory (ModuleCat.{max u v} R) (ComplexShape.up ℤ),
      (derivedTensorProduct M).map (r • 𝟙 (DerivedCategory.Qh.obj Y)) = r • 𝟙 _ by
    let e := DerivedCategory.Qh.objObjPreimageIso X
    rw [show r • 𝟙 X = e.inv ≫ (r • 𝟙 _) ≫ e.hom by simp, Functor.map_comp, Functor.map_comp, h]
    simp [← Functor.map_comp]
  exact fun Y => Localization.lift_map_smul_id_obj _ _ _ r
    (fun Y => by simp)
    (tright_comp_Qh_map_smul_id _ · r) Y

end CochainComplex.DerivedTensor
