module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffineQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackEquivalenceOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel

/-!
# The coherator of an affine algebraic space

Let `X` be an affine algebraic space over a scheme `S`.  The inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`
has a right adjoint. The same holds for an affine scheme `T`, both on its Zariski site, at every
model of `D(𝒪_T)`, and on its small étale site.

## Main results

* `CategoryTheory.ObjectProperty.isLeftAdjoint_ι_of_isEquivalence` and
  `CategoryTheory.ObjectProperty.isLeftAdjoint_ι_of_equivalence`: transport of a coreflective
  subcategory along a left adjoint which restricts to an equivalence, and along an equivalence.
* `StacksDraft.DerivedModel.isLeftAdjoint_ι_derivedCategoryB_of_model`: the coreflectivity of
  `D_B(A)` does not depend on the model of the derived category.
* `AlgebraicGeometry.isLeftAdjoint_ι_derivedCategoryB_isQuasicoherent_of_isAffine`: the coherator
  of an affine scheme, at any model of its derived category.
* `AlgebraicGeometry.SmallEtale.isLeftAdjoint_ι_derivedCategoryB_qcohOnSite`: the coherator of the
  small étale site of an affine scheme.
* `AlgebraicGeometry.Space.isLeftAdjoint_ι_of_iso`: the coherator is transported along an
  isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.isLeftAdjoint_ι_of_isAffineSpace`: **the coherator of an affine
  algebraic space**.

## References

* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace CategoryTheory.ObjectProperty

variable {C C' D : Type*} [Category* C] [Category* C'] [Category* D]

/-- If a left adjoint `L : D ⥤ C` factors through the full subcategory cut out by `A` by an
equivalence, then the inclusion of that full subcategory has a right adjoint. -/
theorem isLeftAdjoint_ι_of_isEquivalence (A : ObjectProperty C) (L : D ⥤ C) [L.IsLeftAdjoint]
    (L' : D ⥤ A.FullSubcategory) [L'.IsEquivalence] (e : L' ⋙ A.ι ≅ L) : A.ι.IsLeftAdjoint := by
  have e' : L'.inv ⋙ L ≅ A.ι :=
    Functor.isoWhiskerLeft L'.inv e.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight L'.asEquivalence.counitIso A.ι ≪≫ Functor.leftUnitor _
  exact Functor.isLeftAdjoint_of_iso e'

/-- **Transport of a coreflective subcategory along an equivalence.**  If `E : C ≌ C'` matches the
object properties `A` and `A'` and the inclusion of `A` has a right adjoint, so does the
inclusion of `A'`. -/
theorem isLeftAdjoint_ι_of_equivalence (E : C ≌ C') (A : ObjectProperty C) (A' : ObjectProperty C')
    [A'.IsClosedUnderIsomorphisms] (h : ∀ X, A X ↔ A' (E.functor.obj X)) [A.ι.IsLeftAdjoint] :
    A'.ι.IsLeftAdjoint := by
  let L' : A.FullSubcategory ⥤ A'.FullSubcategory := A'.lift (A.ι ⋙ E.functor)
    (fun X => (h X.obj).1 X.property)
  have hff : L'.FullyFaithful := Functor.FullyFaithful.ofCompFaithful (G := A'.ι)
    ((A.fullyFaithfulι.comp E.fullyFaithfulFunctor).ofIso (A'.liftCompιIso _ _).symm)
  have : L'.Full := hff.full
  have : L'.Faithful := hff.faithful
  have : L'.EssSurj := ⟨fun Y => ⟨⟨E.inverse.obj Y.obj, (h _).2
    (A'.prop_of_iso (E.counitIso.app Y.obj).symm Y.property)⟩,
    ⟨A'.fullyFaithfulι.preimageIso (E.counitIso.app Y.obj)⟩⟩⟩
  have : L'.IsEquivalence := { }
  exact isLeftAdjoint_ι_of_isEquivalence A' (A.ι ⋙ E.functor) L' (A'.liftCompιIso _ _)

end CategoryTheory.ObjectProperty

namespace StacksDraft.DerivedModel

universe w z v u'

variable {A : Type u'} [Category.{v} A] [Abelian A]

/-- **The coreflectivity of `D_B(A)` does not depend on the chosen model of the derived
category.** -/
theorem isLeftAdjoint_ι_derivedCategoryB_of_model (B : ObjectProperty A)
    [B.IsClosedUnderIsomorphisms] (h₁ : HasDerivedCategory.{w} A) (h₂ : HasDerivedCategory.{z} A)
    (hι : (@DerivedCategoryB.derivedCategoryB A _ _ h₁ B).ι.IsLeftAdjoint) :
    (@DerivedCategoryB.derivedCategoryB A _ _ h₂ B).ι.IsLeftAdjoint := by
  have : (@DerivedCategoryB.derivedCategoryB A _ _ h₂ B).IsClosedUnderIsomorphisms :=
    ⟨fun {_ _} e hK n ↦ B.prop_of_iso
      ((@DerivedCategory.homologyFunctor A _ _ h₂ n).mapIso e) (hK n)⟩
  exact ObjectProperty.isLeftAdjoint_ι_of_equivalence (modelEquiv h₁ h₂)
    (@DerivedCategoryB.derivedCategoryB A _ _ h₁ B) (@DerivedCategoryB.derivedCategoryB A _ _ h₂ B)
    (fun K => (derivedCategoryB_modelEquiv_functor_obj_iff B h₁ h₂ K).symm)

end StacksDraft.DerivedModel

namespace AlgebraicGeometry

universe w

/-- **The coherator of an affine scheme, at any model of its derived category**:
`D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint for an affine scheme `X`. -/
theorem isLeftAdjoint_ι_derivedCategoryB_isQuasicoherent_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (h : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)) :
    (@DerivedCategoryB.derivedCategoryB _ _ _ h
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.IsLeftAdjoint :=
  have := Stacks.Duality.AffineGeneration.isLeftAdjoint_derivedQuasiCoherentι_of_isAffine X
  StacksDraft.DerivedModel.isLeftAdjoint_ι_derivedCategoryB_of_model _ _ h this

/-- **The coherator of the small étale site of an affine scheme.**  For an affine scheme `T`
the inclusion `D_QCoh(T_étale, 𝒪) ⥤ D(T_étale, 𝒪)` has a right adjoint. -/
theorem SmallEtale.isLeftAdjoint_ι_derivedCategoryB_qcohOnSite (BE : BigEtaleSite.{u})
    (T : Scheme.{u}) (hT : BE.Contains T) [_root_.AlgebraicGeometry.IsAffine T]
    (hZ : HasDerivedCategory.{w} (SheafOfModules.{u} T.ringCatSheaf))
    (hE : HasDerivedCategory.{w} (SheafOfModules.{u} (SmallEtale.structureSheaf BE T hT))) :
    (DerivedCategoryB.derivedCategoryB (SmallEtale.qcohOnSite BE T hT)).ι.IsLeftAdjoint := by
  have := isLeftAdjoint_ι_derivedCategoryB_isQuasicoherent_of_isAffine T hZ
  have := (SmallEtale.derivedAssociatedModuleAdjunction BE T hT).isLeftAdjoint
  have := SmallEtale.derivedAssociatedModule_isEquivalence.{w} BE T hT
  exact ObjectProperty.isLeftAdjoint_ι_of_isEquivalence _
    ((DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent T.ringCatSheaf)).ι ⋙
      (SmallEtale.associatedModuleOfSheaf BE T hT).mapDerivedCategory)
    (SmallEtale.derivedAssociatedModule.{w} BE T hT) (ObjectProperty.liftCompιIso _ _ _)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-! ### Transport along an isomorphism of algebraic spaces -/

section Iso

variable {X Y : AlgebraicSpaces B S hS}

/-- **The coherator is transported along an isomorphism of algebraic spaces.** If `X ≅ Y` and the
inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` has a right adjoint, then so does `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`. -/
theorem isLeftAdjoint_ι_of_iso (e : X ≅ Y)
    (hY : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι.IsLeftAdjoint) :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι.IsLeftAdjoint := by
  let E := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (etaleModulePullbackEquivalenceOfIso B S hS e)
  have := hY
  refine ObjectProperty.isLeftAdjoint_ι_of_equivalence E
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (fun M => ⟨fun hM => ?_, fun hM => ?_⟩)
  · exact derivedQuasicoherent_etaleModulePullback B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)
      M hM
  · exact ObjectProperty.prop_of_iso _ (E.unitIso.app M).symm
      (derivedQuasicoherent_etaleModulePullback B S hS e.inv (isEtale_hom_of_isIso B S hS e.inv)
        _ hM)

end Iso

/-! ### The represented affine algebraic space -/

section Represented

/-- **The coherator of the algebraic space represented by an affine scheme.** If the scheme
underlying `U` is affine, then the inclusion `D_QCoh ⥤ D` on the small étale site of the algebraic
space `yoneda.obj U` has a right adjoint. -/
theorem isLeftAdjoint_ι_yoneda_of_isAffine (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O))).ι.IsLeftAdjoint := by
  have := hU
  let hE : HasDerivedCategory (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :=
    HasDerivedCategory.standard _
  have := AlgebraicGeometry.SmallEtale.isLeftAdjoint_ι_derivedCategoryB_qcohOnSite
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    (HasDerivedCategory.standard _) hE
  let e := representedSmallEtaleModuleEquivalence B S hS U
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have hcl : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O))).IsClosedUnderIsomorphisms :=
    isClosedUnderIsomorphisms_derivedCategoryB_isQuasicoherentOnSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)
  refine @ObjectProperty.isLeftAdjoint_ι_of_equivalence _ _ _ _
    (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory e)
    (DerivedCategoryB.derivedCategoryB (AlgebraicGeometry.SmallEtale.qcohOnSite
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O))) hcl (fun M => forall_congr' fun n => ?_)
    inferInstance
  have h₁ := ObjectProperty.prop_iff_of_iso (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) ((e.functor.mapDerivedCategoryHomologyIso n).app M)
  have h₂ := isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U
    ((DerivedCategory.homologyFunctor _ n).obj M)
  exact h₂.symm.trans h₁.symm

/-- **The coherator of an affine algebraic space**: the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a
right adjoint when `X` is an affine algebraic space. -/
theorem isLeftAdjoint_ι_of_isAffineSpace (X : AlgebraicSpaces B S hS)
    (hX : IsAffineSpace B S hS X.1) :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι.IsLeftAdjoint := by
  obtain ⟨U, hU, ⟨e⟩⟩ := hX
  let Y' : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  exact isLeftAdjoint_ι_of_iso B S hS
    ((ObjectProperty.fullyFaithfulι _).preimageIso (X := X) (Y := Y') e)
    (isLeftAdjoint_ι_yoneda_of_isAffine B S hS U hU)

end Represented

end AlgebraicGeometry.Space

end
