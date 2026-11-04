module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# The monoidal structure on sheaves of modules whose tensor product is the tensor product sheaf

The monoidal structure `Stacks.SheafOfModules.monoidalCategory`, obtained by localizing the
objectwise monoidal structure on presheaves of modules along sheafification, has a tensor product
which is only isomorphic to the tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor`,
via `Stacks.SheafOfModules.tensorObjIso`. This file puts a second monoidal structure on sheaves of
`𝒪`-modules, `Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product is the tensor
product sheaf and whose unit is `SheafOfModules.unit`, on the nose, and whose structural morphisms
are those of the localized structure conjugated by `tensorObjIso`. The monoidal axioms are
transported from the localized structure along the identity functor with
`CategoryTheory.Monoidal.induced`.

## Main definitions

* `Stacks.SheafOfModules.Strict.monoidalCategoryStruct`: the tensor product sheaf, the unit
  `SheafOfModules.unit`, and the conjugates of the localized structural morphisms.
* `Stacks.SheafOfModules.Strict.toLocalizedMonoidal`: the identity functor, with target the type
  synonym `CategoryTheory.Monoidal.LocalizedMonoidal` carrying the localized monoidal structure.
* `Stacks.SheafOfModules.Strict.inducingFunctorData`: this functor carries
  `monoidalCategoryStruct` to the localized structure, with comparison isomorphism
  `tensorObjIso`.
* `Stacks.SheafOfModules.Strict.monoidalCategory`: the resulting monoidal structure.
* `Stacks.SheafOfModules.Strict.braiding`: the conjugate of the localized braiding;
  `Stacks.SheafOfModules.Strict.braidedCategory` and
  `Stacks.SheafOfModules.Strict.symmetricCategory` are the braided and symmetric structures it
  defines.

## Main results

* `Stacks.SheafOfModules.Strict.tensorObj_eq`: the tensor product of the strict structure is
  `Stacks.SheafOfModules.Tensor.sheafTensor`, by `rfl`.
* `Stacks.SheafOfModules.Strict.whiskerLeft_eq`,
  `Stacks.SheafOfModules.Strict.whiskerRight_eq`,
  `Stacks.SheafOfModules.Strict.tensorHom_eq`,
  `Stacks.SheafOfModules.Strict.associator_eq`,
  `Stacks.SheafOfModules.Strict.leftUnitor_eq` and
  `Stacks.SheafOfModules.Strict.rightUnitor_eq`: the structural morphisms are the conjugates by
  `tensorObjIso` of the localized ones.
* `Stacks.SheafOfModules.Strict.braiding_eq`: the braiding of `Strict.braidedCategory` is
  `Strict.braiding`, by `rfl`.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [The Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization

universe v u w

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

section Construction

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

/-- The data of a monoidal structure on sheaves of `𝒪`-modules whose tensor product is the
native tensor product sheaf defined by `𝒪` and `h𝒪` and whose unit is `SheafOfModules.unit`:
each structural morphism is the corresponding morphism of the localized monoidal structure
`Stacks.SheafOfModules.monoidalCategory`, conjugated by `Stacks.SheafOfModules.tensorObjIso`. -/
@[instance_reducible]
noncomputable def monoidalCategoryStruct :
    MonoidalCategoryStruct (SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) where
  tensorObj F G := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj (F)).obj (G))
  whiskerLeft X Y₁ Y₂ f :=
    (tensorObjIso 𝒪 h𝒪 X Y₁).inv ≫ X ◁ f ≫ (tensorObjIso 𝒪 h𝒪 X Y₂).hom
  whiskerRight f Y :=
    (tensorObjIso 𝒪 h𝒪 _ Y).inv ≫ f ▷ Y ≫ (tensorObjIso 𝒪 h𝒪 _ Y).hom
  tensorHom f g :=
    (tensorObjIso 𝒪 h𝒪 _ _).inv ≫ (f ⊗ₘ g) ≫ (tensorObjIso 𝒪 h𝒪 _ _).hom
  tensorUnit := SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)
  associator X Y Z :=
    ((tensorObjIso 𝒪 h𝒪 ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj (X)).obj (Y)))
          Z).symm ≪≫
        ((tensorObjIso 𝒪 h𝒪 X Y).symm ⊗ᵢ Iso.refl Z)) ≪≫ α_ X Y Z ≪≫
      ((Iso.refl X ⊗ᵢ tensorObjIso 𝒪 h𝒪 Y Z) ≪≫
        tensorObjIso 𝒪 h𝒪 X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj (Y)).obj
          (Z))))
  leftUnitor X :=
    (tensorObjIso 𝒪 h𝒪 (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) X).symm ≪≫ λ_ X
  rightUnitor X :=
    (tensorObjIso 𝒪 h𝒪 X (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))).symm ≪≫ ρ_ X

/-- Inserting `Iso.refl X ⊗ᵢ Iso.refl Y` after the inverse of an isomorphism `X ⊗ Y ≅ A` does not
change the composite with a further isomorphism. -/
private theorem symm_trans_refl_tensorIso_trans_hom {D : Type*} [Category D] [MonoidalCategory D]
    {A X Y Z : D} (e : X ⊗ Y ≅ A) (u : X ⊗ Y ≅ Z) :
    ((e.symm ≪≫ (Iso.refl X ⊗ᵢ Iso.refl Y)) ≪≫ u).hom = (e.symm ≪≫ u).hom := by
  simp

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Inserting `Iso.refl (𝟙_ _) ⊗ᵢ Iso.refl X` between the inverse of `tensorObjIso` and the left
unitor does not change the composite. -/
theorem leftUnitor_hom_aux
    (X : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (((tensorObjIso 𝒪 h𝒪 (𝟙_ (SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) X).symm ≪≫
          (Iso.refl (𝟙_ (SheafOfModules.{w}
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) ⊗ᵢ
            Iso.refl X)) ≪≫ λ_ X).hom =
      ((tensorObjIso 𝒪 h𝒪 (𝟙_ (SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) X).symm ≪≫
        λ_ X).hom := by
  exact symm_trans_refl_tensorIso_trans_hom _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Inserting `Iso.refl X ⊗ᵢ Iso.refl (𝟙_ _)` between the inverse of `tensorObjIso` and the right
unitor does not change the composite. -/
theorem rightUnitor_hom_aux
    (X : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (((tensorObjIso 𝒪 h𝒪 X (𝟙_ (SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))).symm ≪≫
          (Iso.refl X ⊗ᵢ
            Iso.refl (𝟙_ (SheafOfModules.{w}
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))))) ≪≫ ρ_ X).hom =
      ((tensorObjIso 𝒪 h𝒪 X (𝟙_ (SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))).symm ≪≫
        ρ_ X).hom := by
  exact symm_trans_refl_tensorIso_trans_hom _ _

section Braiding

attribute [local instance] Stacks.SheafOfModules.braidedCategory

/-- The braiding of the strict monoidal structure: the braiding of the localized one, conjugated
by `Stacks.SheafOfModules.tensorObjIso`. -/
noncomputable def braiding (X Y : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj (X)).obj (Y))
          ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj (Y)).obj (X))
          :=
  (tensorObjIso 𝒪 h𝒪 X Y).symm ≪≫ BraidedCategory.braiding
    (self := Stacks.SheafOfModules.braidedCategory 𝒪 h𝒪) X Y ≪≫ tensorObjIso 𝒪 h𝒪 Y X

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Strict.braiding` is carried to the localized braiding by `Strict.toLocalizedMonoidal`. -/
theorem braiding_aux (X Y : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (tensorObjIso 𝒪 h𝒪 X Y).hom ≫ (braiding 𝒪 h𝒪 X Y).hom =
      (BraidedCategory.braiding
    (self := Stacks.SheafOfModules.braidedCategory 𝒪 h𝒪) X Y).hom ≫ (tensorObjIso 𝒪 h𝒪 Y X).hom :=
  (tensorObjIso 𝒪 h𝒪 X Y).hom_inv_id_assoc _

end Braiding

end Construction

/-- The identity functor from sheaves of `𝒪`-modules to the type synonym
`CategoryTheory.Monoidal.LocalizedMonoidal` on which the localized monoidal structure of
`Stacks.SheafOfModules.monoidalCategory` is defined. -/
def toLocalizedMonoidal :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⥤
      LocalizedMonoidal (L := Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪)
        (W := Stacks.SheafOfModules.localIso (J := J) 𝒪) (sheafifyUnitIso 𝒪 h𝒪) :=
  𝟭 _

/-- `Strict.toLocalizedMonoidal` is faithful. -/
instance faithful_toLocalizedMonoidal : (toLocalizedMonoidal 𝒪 h𝒪).Faithful where
  map_injective h := h

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Strict.toLocalizedMonoidal` is the identity on objects, on the nose. -/
@[simp]
theorem toLocalizedMonoidal_obj (X : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (toLocalizedMonoidal 𝒪 h𝒪).obj X = X :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Strict.toLocalizedMonoidal` is the identity on morphisms, on the nose. -/
@[simp]
theorem toLocalizedMonoidal_map
    {X Y : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)} (f :
      X ⟶ Y) :
    (toLocalizedMonoidal 𝒪 h𝒪).map f = f :=
  rfl

/-- The identity functor of `Strict.toLocalizedMonoidal` carries `Strict.monoidalCategoryStruct`
to the localized monoidal structure, with comparison isomorphism
`Stacks.SheafOfModules.tensorObjIso` on tensor products and the identity on units. -/
noncomputable def inducingFunctorData :
    letI := monoidalCategoryStruct 𝒪 h𝒪
    CategoryTheory.Monoidal.InducingFunctorData (toLocalizedMonoidal 𝒪 h𝒪) :=
  letI := monoidalCategoryStruct 𝒪 h𝒪
  { μIso := fun X Y => tensorObjIso 𝒪 h𝒪 X Y
    εIso := Iso.refl _
    whiskerLeft_eq := fun _ _ _ _ => rfl
    whiskerRight_eq := fun _ _ => rfl
    tensorHom_eq := fun _ _ => rfl
    associator_eq := fun _ _ _ => rfl
    leftUnitor_eq := fun X => (leftUnitor_hom_aux 𝒪 h𝒪 X).symm
    rightUnitor_eq := fun X => (rightUnitor_hom_aux 𝒪 h𝒪 X).symm }

/-- The monoidal structure on sheaves of `𝒪`-modules whose tensor product is the tensor product
sheaf defined by `𝒪` and `h𝒪` on the nose, transported from
`Stacks.SheafOfModules.monoidalCategory` along the identity functor. -/
@[instance_reducible]
noncomputable def monoidalCategory :
    MonoidalCategory (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      𝒪 h𝒪)) :=
  letI := monoidalCategoryStruct 𝒪 h𝒪
  CategoryTheory.Monoidal.induced (toLocalizedMonoidal 𝒪 h𝒪) (inducingFunctorData 𝒪 h𝒪)

/-- The braiding of `Strict.monoidalCategory`, transported from
`Stacks.SheafOfModules.braidedCategory`. Its braiding is `Strict.braiding` on the nose. -/
@[instance_reducible]
noncomputable def braidedCategory :
    letI := monoidalCategory 𝒪 h𝒪
    BraidedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) :=
  letI := monoidalCategory 𝒪 h𝒪
  letI := monoidalCategoryStruct 𝒪 h𝒪
  letI : (toLocalizedMonoidal 𝒪 h𝒪).Monoidal :=
    (CategoryTheory.Monoidal.fromInducedCoreMonoidal (toLocalizedMonoidal 𝒪 h𝒪)
      (inducingFunctorData 𝒪 h𝒪)).toMonoidal
  BraidedCategory.ofFaithful (toLocalizedMonoidal 𝒪 h𝒪) (braiding 𝒪 h𝒪)
    (fun X Y => braiding_aux 𝒪 h𝒪 X Y)

/-- The braiding of `Strict.monoidalCategory` is a symmetry, transported from
`Stacks.SheafOfModules.symmetricCategory`. -/
@[instance_reducible]
noncomputable def symmetricCategory :
    letI := monoidalCategory 𝒪 h𝒪
    letI := braidedCategory 𝒪 h𝒪
    SymmetricCategory (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      𝒪 h𝒪)) :=
  letI := monoidalCategory 𝒪 h𝒪
  letI := monoidalCategoryStruct 𝒪 h𝒪
  letI := braidedCategory 𝒪 h𝒪
  letI : (toLocalizedMonoidal 𝒪 h𝒪).Monoidal :=
    (CategoryTheory.Monoidal.fromInducedCoreMonoidal (toLocalizedMonoidal 𝒪 h𝒪)
      (inducingFunctorData 𝒪 h𝒪)).toMonoidal
  letI : (toLocalizedMonoidal 𝒪 h𝒪).Braided :=
    { braided := fun X Y => braiding_aux 𝒪 h𝒪 X Y }
  SymmetricCategory.ofFaithful (toLocalizedMonoidal 𝒪 h𝒪)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The underlying data of `Strict.monoidalCategory` is `Strict.monoidalCategoryStruct`. -/
theorem monoidalCategory_toMonoidalCategoryStruct :
    (monoidalCategory 𝒪 h𝒪).toMonoidalCategoryStruct = monoidalCategoryStruct 𝒪 h𝒪 :=
  rfl

section Payoff

attribute [local instance] monoidalCategory

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The tensor product of the strict monoidal structure is the tensor product sheaf
`Stacks.SheafOfModules.Tensor.sheafTensor`, on the nose. -/
theorem tensorObj_eq (A B : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    A ⊗ B = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj (A)).obj (B))
          :=
  rfl

/-- The braiding of `Strict.braidedCategory` is `Strict.braiding`, on the nose. -/
theorem braiding_eq (X Y : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    BraidedCategory.braiding (self := braidedCategory 𝒪 h𝒪) X Y = braiding 𝒪 h𝒪 X Y :=
  rfl

end Payoff

section Conjugates

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Left whiskering in the strict monoidal structure is left whiskering in the localized one,
conjugated by `Stacks.SheafOfModules.tensorObjIso`. -/
theorem whiskerLeft_eq (X : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    {Y₁ Y₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)} (f
      : Y₁ ⟶ Y₂) :
    MonoidalCategoryStruct.whiskerLeft (self := monoidalCategoryStruct 𝒪 h𝒪) X f =
      (tensorObjIso 𝒪 h𝒪 X Y₁).inv ≫ X ◁ f ≫ (tensorObjIso 𝒪 h𝒪 X Y₂).hom :=
  rfl

/-- Right whiskering in the strict monoidal structure is right whiskering in the localized one,
conjugated by `Stacks.SheafOfModules.tensorObjIso`. -/
theorem whiskerRight_eq {X₁ X₂ : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (f : X₁ ⟶ X₂) (Y : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      𝒪 h𝒪)) :
    MonoidalCategoryStruct.whiskerRight (self := monoidalCategoryStruct 𝒪 h𝒪) f Y =
      (tensorObjIso 𝒪 h𝒪 X₁ Y).inv ≫ f ▷ Y ≫ (tensorObjIso 𝒪 h𝒪 X₂ Y).hom :=
  rfl

/-- The tensor product of two morphisms in the strict monoidal structure is their tensor
product in the localized one, conjugated by `Stacks.SheafOfModules.tensorObjIso`. -/
theorem tensorHom_eq {X₁ Y₁ X₂ Y₂ : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    MonoidalCategoryStruct.tensorHom (self := monoidalCategoryStruct 𝒪 h𝒪) f g =
      (tensorObjIso 𝒪 h𝒪 X₁ X₂).inv ≫ (f ⊗ₘ g) ≫ (tensorObjIso 𝒪 h𝒪 Y₁ Y₂).hom :=
  rfl

/-- The associator of the strict monoidal structure is the localized associator, conjugated by
`Stacks.SheafOfModules.tensorObjIso` on both sides. -/
theorem associator_eq (X Y Z : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    MonoidalCategoryStruct.associator (self := monoidalCategoryStruct 𝒪 h𝒪) X Y Z =
      ((tensorObjIso 𝒪 h𝒪 ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj (X)).obj (Y)))
          Z).symm
        ≪≫
          ((tensorObjIso 𝒪 h𝒪 X Y).symm ⊗ᵢ Iso.refl Z)) ≪≫ α_ X Y Z ≪≫
        ((Iso.refl X ⊗ᵢ tensorObjIso 𝒪 h𝒪 Y Z) ≪≫
          tensorObjIso 𝒪 h𝒪 X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj (Y)).obj
          (Z)))) :=
  rfl

/-- The left unitor of the strict monoidal structure is the localized left unitor, precomposed
with `Stacks.SheafOfModules.tensorObjIso`. -/
theorem leftUnitor_eq (X : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    MonoidalCategoryStruct.leftUnitor (self := monoidalCategoryStruct 𝒪 h𝒪) X =
      (tensorObjIso 𝒪 h𝒪 (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) X).symm ≪≫
        λ_ X :=
  rfl

/-- The right unitor of the strict monoidal structure is the localized right unitor,
precomposed with `Stacks.SheafOfModules.tensorObjIso`. -/
theorem rightUnitor_eq (X : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    MonoidalCategoryStruct.rightUnitor (self := monoidalCategoryStruct 𝒪 h𝒪) X =
      (tensorObjIso 𝒪 h𝒪 X (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))).symm ≪≫
        ρ_ X :=
  rfl

end Conjugates

end Stacks.SheafOfModules.Strict

end
