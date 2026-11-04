module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorUnitComparison

/-!
# The derived unit identification is the unit constraint of the derived tensor product

Let `S` be a simplicial-site situation and write `e` for the equivalence
`Stacks.DerivedTensor.AbelianSheaves.moduleEquivalence` of abelian sheaves on the total site with
modules over the constant sheaf of rings `ℤ`. This file compares the two identifications
`ℤ ⊗^L_ℤ K ≅ K` of Stacks 0D9K: the derived functor of the copower unit identification
`CategoryTheory.SimplicialSiteSituation.unitTensorIso`, read through
`CategoryTheory.SimplicialSiteSituation.unitIntegerTensorAbDerivedIso`, and the unit constraint
`Stacks.DerivedTensor.AbelianSheaves.constantSheafLeftUnitIso` of the derived tensor product of
abelian sheaves. They agree.

Read across `e`, the middle factor of the derived unit identification is the derived
transformation of the sheaf-level map `ℤ ⊗_ℤ - ⟶ 𝟭` obtained from the coefficient transport
`CategoryTheory.SimplicialSiteSituation.totalIntegerModuleIsoUnit` and the sheaf-level left unit
law `Stacks.SheafOfModules.unitSheafTensorNatIso`.

All names below are in the namespace `CategoryTheory.SimplicialSiteSituation`, except
`CategoryTheory.derivedNatTrans_whiskerRight_id`.

## Main results

* `CategoryTheory.derivedNatTrans_whiskerRight_id`: the compositor of derived functors is natural
  in the inner factor, at a transformation to the identity.
* `leftUnitTrans_intRingedSite_eq`: the left unit constraint of the derived tensor product on
  `Stacks.DerivedTensor.AbelianSheaves.intRingedSite`, in flat-single form.
* `tensorMap_inverseSingleTotalInteger_comp_flatSingleTensorIso`: the coefficient transport, read
  through the flat-single identifications.
* `unitIntegerTensorFlatIso_comp_leftUnitTrans` and
  `unitIntegerTensorFlatIso_comp_leftUnitIso_app`: the middle factor of the derived unit
  identification, as a transformation and at an object.
* `derivedNatTrans_unitTensorIso_app_eq_constantSheafLeftUnitIso`: the derived unit
  identification is the unit constraint of the derived tensor product of abelian sheaves.

## References

* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory

section WhiskerRightId

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The compositor of derived functors is natural in the inner factor, at a transformation to
the identity.** A transformation `α : F ⟶ 𝟭` of the inner factor of `F ⋙ G` induces, on the one
hand, the derived transformation of `G ∘ α`, whose target is the derived functor of `G` itself,
and on the other the derived transformation of `α` whiskered with the derived functor of `G`; the
compositor carries one to the other. -/
theorem derivedNatTrans_whiskerRight_id (α : F ⟶ 𝟭 A) :
    derivedNatTrans (F ⋙ G) G (Functor.whiskerRight α G) =
      (derivedCompIso F G (F ⋙ G) (Iso.refl _)).hom ≫
        Functor.whiskerRight
          (derivedNatTrans F (𝟭 A) α ≫ (derivedIdIso (A := A)).hom) G.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun X => ?_
  have hid : (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X ≫
        (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app X =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X :=
    HomologicalComplex.hom_ext _ _ fun _ => Category.comp_id _
  have hfac : G.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        G.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X)) =
      DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X)) ≫
        G.mapDerivedCategoryFactors.inv.app
          (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
    (G.mapDerivedCategoryFactors.inv.naturality
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X)).symm
  rw [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.comp_app, derivedNatTrans_app_Q',
    derivedNatTrans_app_Q', derivedIdIso_hom_app_Q, derivedCompIso_refl_hom_app_Q,
    mapHomologicalComplex_whiskerRight_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp G.mapDerivedCategory, Iso.inv_hom_id_app_assoc,
    ← CategoryTheory.Functor.map_comp DerivedCategory.Q, hid, hfac]
  rfl

end WhiskerRightId

section Rearrange

/-- Three successive images under a functor, fused, with a trailing morphism. -/
private theorem map_three_comp_assoc {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
    {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) {V : D} (k : F.obj W ⟶ V) :
    F.map f ≫ F.map g ≫ F.map h ≫ k = F.map (f ≫ g ≫ h) ≫ k := by
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]

/-- A rearrangement of composites. Given `a ≫ a' = 𝟙`, `f = a ≫ b₁`, `l = c ≫ n ≫ i`,
`b₁ ≫ b₂ ≫ b₃ ≫ c = a' ≫ m` and `d = m ≫ n`, the composite `f ≫ b₂ ≫ b₃ ≫ l` is `d ≫ i`. -/
private theorem middle_rearrange {D : Type*} [Category D]
    {P Q₁ Q₂ Q₃ Q₄ P' I₁ I₂ : D}
    (f : P ⟶ Q₂) (a : P ⟶ Q₁) (a' : Q₁ ⟶ P) (b₁ : Q₁ ⟶ Q₂) (b₂ : Q₂ ⟶ Q₃) (b₃ : Q₃ ⟶ Q₄)
    (l : Q₄ ⟶ I₁) (c : Q₄ ⟶ P') (n : P' ⟶ I₂) (i : I₂ ⟶ I₁) (m : P ⟶ P') (d : P ⟶ I₂)
    (ha : a ≫ a' = 𝟙 P) (hf : f = a ≫ b₁) (hl : l = c ≫ n ≫ i)
    (hkey : b₁ ≫ b₂ ≫ b₃ ≫ c = a' ≫ m) (hd : d = m ≫ n) :
    f ≫ b₂ ≫ b₃ ≫ l = d ≫ i := by
  rw [hf, hl, hd, Category.assoc, reassoc_of% hkey, ← Category.assoc, ha, Category.id_comp,
    Category.assoc]

/-- A rearrangement of composites across a functor. Given `b = d ≫ F(x ≫ y ≫ z)`, the composite
`a ≫ b ≫ c` is `(a ≫ d ≫ F x) ≫ F y ≫ F z ≫ c`. -/
private theorem final_rearrange {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
    {X₀ X₁ X₂ : D} {Y₀ Y₁ Y₂ Y₃ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ F.obj Y₃) (c : F.obj Y₃ ⟶ X₂) (d : X₁ ⟶ F.obj Y₀)
    (x : Y₀ ⟶ Y₁) (y : Y₁ ⟶ Y₂) (z : Y₂ ⟶ Y₃)
    (hb : b = d ≫ F.map (x ≫ y ≫ z)) :
    a ≫ b ≫ c = (a ≫ d ≫ F.map x) ≫ F.map y ≫ F.map z ≫ c := by
  rw [hb, F.map_comp, F.map_comp]
  simp only [Category.assoc]

end Rearrange

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves Stacks.SheafOfModules.Tensor
open Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

universe u

attribute [local instance] CategoryTheory.SimplicialSiteSituation.hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable (S : SimplicialSiteSituation.{u})

local instance sheafTensorObjAdditiveTotalInt
    (X : SheafOfModules.{u} (Stacks.DerivedTensor.AbelianSheaves.intRings S.totalTopology)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Stacks.DerivedTensor.AbelianSheaves.intRingSheaf S.totalTopology)).obj X).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    (Stacks.DerivedTensor.AbelianSheaves.intRingSheaf S.totalTopology) X

section Derived

attribute [local instance] HasDerivedCategory.standard

section FlatUnit

variable [PreservesFiniteLimits ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
    (SheafOfModules.unit (intRings S.totalTopology)))]
  [PreservesFiniteColimits ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
    (SheafOfModules.unit (intRings S.totalTopology)))]

/-- **The left unit constraint of the derived tensor product on `intRingedSite`, flat-single.**
The left unit constraint of the derived tensor product on
`Stacks.DerivedTensor.AbelianSheaves.intRingedSite` is the flat-single identification of
`𝒪[0] ⊗^L_𝒪 -` with the derived functor of `𝒪 ⊗_𝒪 -`, followed by the derived transformation of
the sheaf-level left unit law and `derivedIdIso`. -/
theorem leftUnitTrans_intRingedSite_eq :
    leftUnitTrans (intRingedSite S.totalTopology)
        (intDerivedTensorProduct S.totalTopology) =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
            (intDerivedTensorProduct S.totalTopology)
            (SheafOfModules.unit (intRings S.totalTopology))
            (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
              (Y := intRingedSite S.totalTopology))).hom ≫
        derivedNatTrans
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              (SheafOfModules.unit (intRings S.totalTopology)))
            (𝟭 (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)))
            (Stacks.SheafOfModules.unitSheafTensorNatIso
              (Y := intRingedSite S.totalTopology)).hom ≫
          (derivedIdIso
            (A := Stacks.DerivedTensor.RingedSite.Modules
              (intRingSheaf S.totalTopology))).hom := by
  rw [show leftUnitTrans (intRingedSite S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) =
        flatSingleLeftUnitTrans (intRingedSite S.totalTopology)
          (intDerivedTensorProduct S.totalTopology) from
      leftUnitFlatSingleAgree (intRingedSite S.totalTopology)
        (intDerivedTensorProduct S.totalTopology),
    flatSingleLeftUnitTrans_eq (intRingedSite S.totalTopology)
      (intDerivedTensorProduct S.totalTopology),
    CategoryTheory.mapDerivedCategoryIsoOfNatIso_hom_eq_derivedNatTrans
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        (SheafOfModules.unit (intRings S.totalTopology)))
      (𝟭 (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)))
      (Stacks.SheafOfModules.unitSheafTensorNatIso (Y := intRingedSite S.totalTopology)),
    ← CategoryTheory.derivedIdIso_eq_mapDerivedCategoryIdIso]

/-- **The coefficient transport, read through the flat-single identifications.** The three
coefficient factors — the inverse of the single-functor compositor of `e⁻¹`, the identification
of the constant integer sheaf with the abelian sheaf underlying the structure sheaf, and the unit
of the equivalence — followed by the flat-single identification of the unit, are the flat-single
identification of `e⁻¹ ℤ` followed by the derived transformation of the sheaf-level coefficient
map `CategoryTheory.SimplicialSiteSituation.totalIntegerModuleIsoUnit`. -/
theorem tensorMap_inverseSingleTotalInteger_comp_flatSingleTensorIso :
    (intDerivedTensorProduct S.totalTopology).tensor.map
          (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
            (totalIntegerSheaf S)).inv ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
            ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
              ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
                (intSheafIsoConstantSheaf S.totalTopology).hom)) ≫
          (intDerivedTensorProduct S.totalTopology).tensor.map
              (inverseUnitObjectIso S.totalTopology).hom ≫
            (flatSingleTensorIso (intRingSheaf S.totalTopology)
              (intDerivedTensorProduct S.totalTopology)
              (SheafOfModules.unit (intRings S.totalTopology))
              (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
                (Y := intRingedSite S.totalTopology))).hom =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
            (intDerivedTensorProduct S.totalTopology)
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
            (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)).hom ≫
        derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            (SheafOfModules.unit (intRings S.totalTopology)))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
            (totalIntegerModuleIsoUnit S).hom) := by
  refine Eq.trans (map_three_comp_assoc
    (intDerivedTensorProduct S.totalTopology).tensor _ _ _ _) ?_
  refine Eq.trans (congrArg
      (fun g => (intDerivedTensorProduct S.totalTopology).tensor.map g)
      (inverseSingleTotalInteger_comp_inverseUnitObjectIso S) =≫
    (flatSingleTensorIso (intRingSheaf S.totalTopology)
      (intDerivedTensorProduct S.totalTopology)
      (SheafOfModules.unit (intRings S.totalTopology))
      (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
        (Y := intRingedSite S.totalTopology))).hom) ?_
  exact flatSingleTensorIso_naturality (intRingSheaf S.totalTopology)
    (intDerivedTensorProduct S.totalTopology)
    (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
      (Y := intRingedSite S.totalTopology))
    (totalIntegerModuleIsoUnit S).hom

end FlatUnit

/-- **The middle factor of the derived unit identification.** The composite of
`unitIntegerTensorFlatIso`, the two coefficient identifications of `constantSheafLeftUnitIso` and
the left unit constraint of the derived tensor product on `intRingedSite` is the derived
transformation of the sheaf-level map `ℤ ⊗_ℤ - ⟶ 𝟭`: the coefficient transport followed by the
sheaf-level left unit law. -/
theorem unitIntegerTensorFlatIso_comp_leftUnitTrans :
    (unitIntegerTensorFlatIso S).hom ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
            ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
              ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
                (intSheafIsoConstantSheaf S.totalTopology).hom)) ≫
          ((intDerivedTensorProduct S.totalTopology).tensor.map
              (inverseUnitObjectIso S.totalTopology).hom ≫
            leftUnitTrans (intRingedSite S.totalTopology)
              (intDerivedTensorProduct S.totalTopology)) =
      derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
          (𝟭 (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
            (totalIntegerModuleIsoUnit S).hom ≫
            (Stacks.SheafOfModules.unitSheafTensorNatIso
              (Y := intRingedSite S.totalTopology)).hom) ≫
        (derivedIdIso
          (A := Stacks.DerivedTensor.RingedSite.Modules
            (intRingSheaf S.totalTopology))).hom := by
  let := preservesFiniteLimits_sheafTensorObj (intRingSheaf S.totalTopology)
    (SheafOfModules.unit (intRings S.totalTopology))
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
      (Y := intRingedSite S.totalTopology))
  let := preservesFiniteColimits_sheafTensorObj (intRingSheaf S.totalTopology)
    (SheafOfModules.unit (intRings S.totalTopology))
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
      (Y := intRingedSite S.totalTopology))
  have hflat : (unitIntegerTensorFlatIso S).hom =
      (flatSingleTensorIso (intRingSheaf S.totalTopology)
            (intDerivedTensorProduct S.totalTopology)
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S))
            (isFlat_moduleEquivalenceInverseTotalIntegerSheaf S)).inv ≫
        (intDerivedTensorProduct S.totalTopology).tensor.map
          (((moduleEquivalence S.totalTopology).inverse.mapDerivedCategorySingleFunctor 0).app
            (totalIntegerSheaf S)).inv := rfl
  exact middle_rearrange _ _ _ _ _ _ _ _ _ _ _ _ (Iso.inv_hom_id _) hflat
    (leftUnitTrans_intRingedSite_eq S)
    (tensorMap_inverseSingleTotalInteger_comp_flatSingleTensorIso S)
    (derivedNatTrans_comp
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
        (SheafOfModules.unit (intRings S.totalTopology)))
      (𝟭 (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)))
      ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
        (totalIntegerModuleIsoUnit S).hom)
      (Stacks.SheafOfModules.unitSheafTensorNatIso
        (Y := intRingedSite S.totalTopology)).hom)

/-- **The middle factor at an object**: `unitIntegerTensorFlatIso_comp_leftUnitTrans` at an object
`A`, with the left unit constraint spelled objectwise as
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso`. -/
theorem unitIntegerTensorFlatIso_comp_leftUnitIso_app
    (A : DerivedCategory (Stacks.DerivedTensor.RingedSite.Modules
      (intRingSheaf S.totalTopology))) :
    (unitIntegerTensorFlatIso S).hom.app A ≫
        ((intDerivedTensorProduct S.totalTopology).tensor.map
            ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.map
              ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
                (intSheafIsoConstantSheaf S.totalTopology).hom))).app A ≫
          (((intDerivedTensorProduct S.totalTopology).tensor.map
              (inverseUnitObjectIso S.totalTopology).hom).app A ≫
            (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso
              (intRingedSite S.totalTopology) (intDerivedTensorProduct S.totalTopology) A).hom) =
      (derivedNatTrans
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
            ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
          (𝟭 (Stacks.DerivedTensor.RingedSite.Modules (intRingSheaf S.totalTopology)))
          ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
            (totalIntegerModuleIsoUnit S).hom ≫
            (Stacks.SheafOfModules.unitSheafTensorNatIso
              (Y := intRingedSite S.totalTopology)).hom)).app A ≫
        (derivedIdIso
          (A := Stacks.DerivedTensor.RingedSite.Modules
            (intRingSheaf S.totalTopology))).hom.app A := by
  rw [← leftUnitTrans_app]
  exact NatTrans.congr_app (unitIntegerTensorFlatIso_comp_leftUnitTrans S) A

/-- **The derived unit identification is the unit constraint of the derived tensor product.** At
an object `K` of the unbounded derived category of abelian sheaves on the total site, the derived
functor of the copower unit identification `ℤ ⊗_ℤ - ≅ 𝟭` agrees, through the identification
`unitIntegerTensorAbDerivedIso` of the derived functor of `ℤ ⊗_ℤ -` with `ℤ ⊗^L_ℤ -`, with the
unit constraint `Stacks.DerivedTensor.AbelianSheaves.constantSheafLeftUnitIso` of the derived
tensor product of abelian sheaves. -/
theorem derivedNatTrans_unitTensorIso_app_eq_constantSheafLeftUnitIso
    (K : DerivedCategory (Sheaf S.totalTopology Ab.{u})) :
    (derivedNatTrans (unitIntegerTensorAb S) (𝟭 (Sheaf S.totalTopology Ab.{u}))
          (unitTensorIso S).hom).app K ≫
        (derivedIdIso (A := Sheaf S.totalTopology Ab.{u})).hom.app K =
      (unitIntegerTensorAbDerivedIso S).hom.app K ≫
        (constantSheafLeftUnitIso S.totalTopology K).hom := by
  have hb := (NatTrans.congr_app
      (derivedNatTrans_whiskerRight_id
        ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
          ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
        (moduleEquivalence S.totalTopology).functor
        ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).map
          (totalIntegerModuleIsoUnit S).hom ≫
          (Stacks.SheafOfModules.unitSheafTensorNatIso
            (Y := intRingedSite S.totalTopology)).hom))
      ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.obj K)).trans
    (congrArg
      (fun t => (derivedCompIso
            ((sheafTensor.{u, u, u, u, u} (intRingSheaf S.totalTopology)).obj
              ((moduleEquivalence S.totalTopology).inverse.obj (totalIntegerSheaf S)))
            (moduleEquivalence S.totalTopology).functor _ (Iso.refl _)).hom.app
          ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.obj K) ≫
        (moduleEquivalence S.totalTopology).functor.mapDerivedCategory.map t)
      (unitIntegerTensorFlatIso_comp_leftUnitIso_app S
        ((moduleEquivalence S.totalTopology).inverse.mapDerivedCategory.obj K)).symm)
  exact Eq.trans (NatTrans.congr_app (derivedNatTrans_unitTensorIso_eq S) K)
    (final_rearrange
      (moduleEquivalence S.totalTopology).functor.mapDerivedCategory _ _ _ _ _ _ _ hb)

end Derived

end CategoryTheory.SimplicialSiteSituation

end
