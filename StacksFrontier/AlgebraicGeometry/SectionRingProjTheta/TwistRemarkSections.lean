module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistRemarkAlgebra
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormula
public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Isomorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections

/-!
# Sections of the tensor products in the twist square of Stacks Tag 01QK

The category of `𝒪_X`-modules on a scheme `X` carries two tensor products: the monoidal product `⊗`
of `Stacks.SheafInternalHom.schemeMonoidalCategory` and the sheafified tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor`. This file relates their sections.

## Main results

* `Stacks.SectionRingProjTheta.tensorSheafIsoTensorObj_hom_tensorHom`: the identification
  `tensorSheafIsoTensorObj` of the two tensor products is natural in both variables.
* `Stacks.SectionRingProjTheta.toTensorSection_comp_tensorHom_val`: the comparison
  `toTensorSection` of the presheaf tensor product with the monoidal one is natural in both
  variables.
* `Stacks.SectionRingProjTheta.tensorSection_tensorHom`: the product of two sections is natural
  in both modules.
* `Stacks.SectionRingProjTheta.tensorSection_unitSec`: the product of the sections carried by two
  morphisms out of the unit is the section carried by their tensor product.
* `Stacks.SectionRingProjTheta.tensorSheafIsoTensorObj_hom_toTensorSheafSection`: the
  identification of the sheafified tensor product with the monoidal one sends the section of a
  pure tensor to the product of the two sections.
* `Stacks.SectionRingProjTheta.sheafTensor_hom_ext_of_isBasis`: a morphism out of a sheafified
  tensor product is determined by its values on pure tensors of sections over the opens of a
  basis.
* `Stacks.SectionRingProjTheta.monoidal_hom_ext_of_isBasis`: a morphism out of a monoidal tensor
  product is determined by its values on products of sections over the opens of a basis.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules (sheafifyValIso)
open Stacks.SectionTensorFormula (tensorSection tensorSheafIsoTensorObj schemeSheafCondition)
open scoped TensorProduct

universe u

namespace Stacks.SectionRingProjTheta

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Naturality of the product of sections -/

section General

universe w v u'

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The identification `tensorSheafIsoTensorObj` of the sheafified tensor product with the
monoidal one is natural in both variables. -/
theorem tensorSheafIsoTensorObj_hom_tensorHom
    {F F' G G' : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} (f : F ⟶ F') (g : G ⟶ G') :
    (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom ≫ (f ⊗ₘ g : F ⊗ G ⟶ F' ⊗ G') =
      ((sheafify 𝒪 h𝒪).map (f.val ⊗ₘ g.val) :
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
            (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F)).obj (G)) ⟶
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
            (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F')).obj (G'))) ≫
        (tensorSheafIsoTensorObj 𝒪 h𝒪 F' G').hom := by
  have hmid : ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) ≫ (f ⊗ₘ g) =
      ((sheafify 𝒪 h𝒪).map f.val ⊗ₘ (sheafify 𝒪 h𝒪).map g.val) ≫
        ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G').hom) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      Stacks.SectionTensorFormula.sheafifyCounit_naturality,
      Stacks.SectionTensorFormula.sheafifyCounit_naturality]
  calc Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
          ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) ≫ (f ⊗ₘ g)
      = Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
          ((sheafify 𝒪 h𝒪).map f.val ⊗ₘ (sheafify 𝒪 h𝒪).map g.val) ≫
            ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G').hom) :=
        whisker_eq (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val) hmid
    _ = (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
          ((sheafify 𝒪 h𝒪).map f.val ⊗ₘ (sheafify 𝒪 h𝒪).map g.val)) ≫
            ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G').hom) :=
        (Category.assoc _ _ _).symm
    _ = ((sheafify 𝒪 h𝒪).map (f.val ⊗ₘ g.val) ≫
          Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F'.val G'.val) ≫
            ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G').hom) :=
        eq_whisker (Functor.OplaxMonoidal.δ_natural (sheafify 𝒪 h𝒪) f.val g.val) _
    _ = (sheafify 𝒪 h𝒪).map (f.val ⊗ₘ g.val) ≫
          Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F'.val G'.val ≫
            ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G').hom) :=
        Category.assoc _ _ _

/-- The comparison `Stacks.SectionTensorFormula.toTensorSection` from the presheaf tensor product
to the underlying presheaf of the monoidal tensor product is natural in both variables. -/
theorem toTensorSection_comp_tensorHom_val
    {F F' G G' : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} (f : F ⟶ F') (g : G ⟶ G') :
    Stacks.SectionTensorFormula.toTensorSection 𝒪 h𝒪 F G ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ Stacks.SectionTensorFormula.toTensorSection 𝒪 h𝒪 F' G' :=
  have hunit : toSheafify 𝒪 h𝒪 (F.val ⊗ G.val) ≫ ((sheafify 𝒪 h𝒪).map (f.val ⊗ₘ g.val)).val =
      (f.val ⊗ₘ g.val) ≫ toSheafify 𝒪 h𝒪 (F'.val ⊗ G'.val) :=
    ((sheafifyAdjunction 𝒪 h𝒪).unit.naturality (f.val ⊗ₘ g.val)).symm
  have hstep := congrArg SheafOfModules.Hom.val (tensorSheafIsoTensorObj_hom_tensorHom 𝒪 h𝒪 f g)
  (whisker_eq (toSheafify 𝒪 h𝒪 (F.val ⊗ G.val)) hstep).trans
    (eq_whisker hunit (tensorSheafIsoTensorObj 𝒪 h𝒪 F' G').hom.val)

end General

variable {X : Scheme.{u}}

/-- The product `tensorSection` of two sections is natural in both modules. -/
theorem tensorSection_tensorHom {F F' G G' : X.Modules} (f : F ⟶ F') (g : G ⟶ G') {U : X.Opens}
    (m : Γ(F, U)) (n : Γ(G, U)) :
    (f ⊗ₘ g).app U (tensorSection F G m n) = tensorSection F' G' (f.app U m) (g.app U n) :=
  congrArg (fun φ => (φ.app (op U)).hom (m ⊗ₜ[Γ(X, U)] n))
    (toTensorSection_comp_tensorHom_val X.presheaf (schemeSheafCondition X) f g)

/-- The product of the sections carried by two morphisms `t`, `t'` out of the unit is the section
carried by `(λ_ (𝟙_ X.Modules)).inv ≫ (t ⊗ₘ t')`. -/
theorem tensorSection_unitSec {F G : X.Modules} (t : 𝟙_ X.Modules ⟶ F) (t' : 𝟙_ X.Modules ⟶ G)
    (U : X.Opens) :
    tensorSection F G (Stacks.SectionRingProjQuasicoherent.unitSec t U)
        (Stacks.SectionRingProjQuasicoherent.unitSec t' U) =
      Stacks.SectionRingProjQuasicoherent.unitSec ((λ_ (𝟙_ X.Modules)).inv ≫ (t ⊗ₘ t')) U := by
  refine (Stacks.SectionProduct.mulSec_eq_tensorSection F G t'
    (Stacks.SectionRingProjQuasicoherent.unitSec t U)).symm.trans ?_
  show ((Stacks.TensorSectionNonvanishing.mulRight F t').app U
      (Stacks.SectionRingProjQuasicoherent.unitSec t U)) = _
  rw [← Stacks.SectionRingProjQuasicoherent.unitSec_comp]
  congr 1
  rw [Stacks.TensorSectionNonvanishing.mulRight, ← Category.assoc, rightUnitor_inv_naturality,
    ← MonoidalCategory.unitors_inv_equal, Category.assoc, ← tensorHom_def]

/-- The identification `tensorSheafIsoTensorObj` of the sheafified tensor product with the
monoidal one sends the section of a pure tensor `a ⊗ₜ b` to the product `tensorSection A B a b`. -/
theorem tensorSheafIsoTensorObj_hom_toTensorSheafSection (A B : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) A B).hom.val.app (op U)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A B
          (op U) (a ⊗ₜ b)) = tensorSection A B a b :=
  rfl

/-- Two morphisms out of a sheafified tensor product are equal if they agree on the sections of
the pure tensors `a ⊗ₜ b` of sections over each open of a basis. -/
theorem sheafTensor_hom_ext_of_isBasis {A B G : X.Modules} {ι : Type*} (V : ι → X.Opens)
    (hV : Opens.IsBasis (Set.range V))
    {φ ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj A).obj B) ⟶ G}
    (h : ∀ (i : ι) (a : Γ(A, V i)) (b : Γ(B, V i)),
      Scheme.Modules.Hom.app φ (V i)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          X.toRingedSpace A B (op (V i)) (a ⊗ₜ b)) =
      Scheme.Modules.Hom.app ψ (V i)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          X.toRingedSpace A B (op (V i)) (a ⊗ₜ b))) : φ = ψ := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext X.toRingedSpace fun U a b => ?_
  obtain ⟨U⟩ := U
  have hcover : U ≤ iSup (fun p : {i : ι // V i ≤ U} => V p.1) := fun x hx => by
    obtain ⟨W, ⟨i, rfl⟩, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.mp hV hx
    exact Opens.mem_iSup.2 ⟨⟨i, hWU⟩, hxW⟩
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, G.isSheaf⟩
    (fun p : {i : ι // V i ≤ U} => V p.1) U (fun p => homOfLE p.2) hcover _ _ fun p => ?_
  obtain ⟨i, hle⟩ := p
  have hres := Stacks.Tag01VSPullbackTensor.toTensorSheafSection_presheaf_map A B (homOfLE hle)
    a b
  exact (Stacks.Tag01VSPullbackTensor.homApp_presheaf_map φ _ _).symm.trans
    ((congrArg (Scheme.Modules.Hom.app φ (V i)) hres).trans ((h i _ _).trans
    ((congrArg (Scheme.Modules.Hom.app ψ (V i)) hres).symm.trans
      (Stacks.Tag01VSPullbackTensor.homApp_presheaf_map ψ _ _))))

/-- Two morphisms out of a monoidal tensor product are equal if they agree on the products of
sections over each open of a basis. -/
theorem monoidal_hom_ext_of_isBasis {A B G : X.Modules} {ι : Type*} (V : ι → X.Opens)
    (hV : Opens.IsBasis (Set.range V)) {φ ψ : A ⊗ B ⟶ G}
    (h : ∀ (i : ι) (a : Γ(A, V i)) (b : Γ(B, V i)),
      φ.app (V i) (tensorSection A B a b) = ψ.app (V i) (tensorSection A B a b)) : φ = ψ :=
  (Iso.cancel_iso_hom_left (tensorSheafIsoTensorObj X.presheaf (schemeSheafCondition X) A B) _
    _).1 (sheafTensor_hom_ext_of_isBasis V hV h)

end Stacks.SectionRingProjTheta

end
