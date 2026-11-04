module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensorComp

/-!
# Naturality of the tensor comparison of Stacks 03DX (2) on a representable

For quasi-coherent modules `M`, `N` on the scheme underlying `U`, the module attached to `M ⊗ N`
on the small étale site of `yoneda.obj U` is identified with the tensor product of the attached
modules by `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso`.  This file proves
that the identification is natural in both factors.

## Main results

* `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence_functor_map_hom`: the
  morphism of attached modules is the image of the associated module under Stacks 04M0.
* `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso_eq`: the identification
  written out as a composite of isomorphisms, with every morphism of ringed topoi explicit.
* `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso_hom_naturality`: **the
  identification `(M ⊗ N)_{yoneda U} ≅ M_{yoneda U} ⊗ N_{yoneda U}` is natural in `M` and `N`.**

## Implementation notes

The identification is a composite of three isomorphisms, each natural: the two comparisons of
Stacks 03EL read through identifications of pullbacks
(`Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality`) and the reading of the
monoidal product as the tensor product sheaf
(`AlgebraicGeometry.Space.modulesTensorObjIso_hom_naturality`).  The three squares are pasted by
an abstract lemma at variables, instantiated once.  Three obstacles shape it.  The
identification is compared with its written-out form only as an isomorphism
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso_eq`, by `rfl`): the same
equation between the underlying morphisms, written with `≫`, exhausts the heartbeat budget.  The
source objects of the abstract lemma are given explicitly as associated modules: inferred from
the goal they are read off `(e.functor.obj M).obj` by unfolding the equivalence of Stacks 03DX (2),
and the result no longer matches the comparisons.  And the tensor product sheaf and the comparison
of Stacks 03EL are made locally irreducible, so that the spellings of the three tensor product
sheaves involved are compared argument by argument instead of by unfolding sheafification.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

/-- The abstract shape of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso_hom_naturality`, at variables:
three natural squares pasted along a functor, with the first and the middle morphisms and the
two composites each given in two spellings. -/
private theorem mapIso_trans_trans_symm_naturality {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (E : 𝒞 ⥤ 𝒟) {x x' y y' : 𝒞} {z z' w w' : 𝒟} (I₁ : x ≅ y) (I₁' : x' ≅ y')
    (I₂ : E.obj y ≅ z) (I₂' : E.obj y' ≅ z') (I₃ : w ≅ z) (I₃' : w' ≅ z') (e : x ⟶ x')
    (e₀ : E.obj x ⟶ E.obj x') (he : e₀ = E.map e) (F₁ F₁' : E.obj y ⟶ E.obj y')
    (hF₁ : F₁ = F₁') (f₂ f₂' : z ⟶ z') (hf₂ : f₂ = f₂') (g : w ⟶ w')
    (h₁ : E.map e ≫ E.map I₁'.hom = E.map I₁.hom ≫ F₁) (h₂ : F₁' ≫ I₂'.hom = I₂.hom ≫ f₂)
    (h₃ : g ≫ I₃'.hom = I₃.hom ≫ f₂') (J : E.obj x ≅ w) (J' : E.obj x' ≅ w')
    (hJ : J = E.mapIso I₁ ≪≫ I₂ ≪≫ I₃.symm) (hJ' : J' = E.mapIso I₁' ≪≫ I₂' ≪≫ I₃'.symm) :
    e₀ ≫ J'.hom = J.hom ≫ g := by
  subst hF₁ hf₂ he hJ hJ'
  have h₃' : I₃.inv ≫ g = f₂ ≫ I₃'.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% h₃, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃']

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The tensor product of two morphisms of quasi-coherent modules on the scheme underlying `U`,
as a morphism of the quasi-coherent tensor products
`AlgebraicGeometry.Space.quasicoherentTensorObj`. -/
abbrev quasicoherentTensorHom
    {M M' N N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (a : M ⟶ M') (b : N ⟶ N') :
    quasicoherentTensorObj B S hS U M N ⟶ quasicoherentTensorObj B S hS U M' N' :=
  ObjectProperty.homMk
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).map a.hom).app
        N.obj ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).obj M'.obj).map
        b.hom)

/-- The morphism of attached modules of a morphism of quasi-coherent modules on the scheme
underlying `U` is the image of its associated module under the comparison of Stacks 04M0. -/
theorem representedQuasicoherentSchemeEquivalence_functor_map_hom
    {M M' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (x : M ⟶ M') :
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map x).hom =
      (representedSmallEtaleModuleEquivalence B S hS U).functor.map
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map x.hom) :=
  rfl

attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor
  Stacks.SheafOfModules.pullbackTensorIso

/-- `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso` written out as a composite
of isomorphisms, with the morphism of ringed topoi of the reindexing of Stacks 04M0 explicit. -/
theorem representedQuasicoherentSchemeTensorIso_eq
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    representedQuasicoherentSchemeTensorIso B S hS U M N =
      (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
          (Stacks.SheafOfModules.pullbackTensorIsoTransport
            (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
              (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
            (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
              (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
            M.obj N.obj) ≪≫
        Stacks.SheafOfModules.pullbackTensorIsoTransport
          (Stacks.SheafOfModules.reindexRingedToposModulesHom
            (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
            (representedSchemeCommRingStructureSheaf B S hS U))
          (Stacks.SheafOfModules.pullbackModulesReindexIso
            (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
            (representedSchemeCommRingStructureSheaf B S hS U))
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M.obj)
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj N.obj) ≪≫
        (modulesTensorObjIso B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).symm :=
  rfl

/-- **The identification `(M ⊗ N)_{yoneda U} ≅ M_{yoneda U} ⊗ N_{yoneda U}` of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso` is natural in `M` and `N`.** -/
theorem representedQuasicoherentSchemeTensorIso_hom_naturality
    {M M' N N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (a : M ⟶ M') (b : N ⟶ N') :
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map
        (quasicoherentTensorHom B S hS U a b)).hom ≫
        (representedQuasicoherentSchemeTensorIso B S hS U M' N').hom =
      (representedQuasicoherentSchemeTensorIso B S hS U M N).hom ≫
        MonoidalCategoryStruct.tensorHom (C := Modules.{u, u} B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map a).hom
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map b).hom := by
  have n₁ := Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
    (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    a.hom b.hom
  have h₁ := ((representedSmallEtaleModuleEquivalence B S hS U).functor.map_comp _ _).symm.trans
    ((congrArg (representedSmallEtaleModuleEquivalence B S hS U).functor.map n₁).trans
      ((representedSmallEtaleModuleEquivalence B S hS U).functor.map_comp _ _))
  have h₂ := Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
    (Stacks.SheafOfModules.reindexRingedToposModulesHom
      (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U))
    (Stacks.SheafOfModules.pullbackModulesReindexIso
      (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U))
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map a.hom)
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map b.hom)
  have h₃ := modulesTensorObjIso_hom_naturality B S hS
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map a).hom
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map b).hom
  exact mapIso_trans_trans_symm_naturality (representedSmallEtaleModuleEquivalence B S hS U).functor
    (x := (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        (quasicoherentTensorObj B S hS U M N).obj)
    (x' := (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
        (quasicoherentTensorObj B S hS U M' N').obj)
    _ _ _ _ _ _ _ _ (representedQuasicoherentSchemeEquivalence_functor_map_hom B S hS U _) _ _ rfl
    _ _ rfl _ h₁ h₂ h₃ _ _ (representedQuasicoherentSchemeTensorIso_eq B S hS U M N)
    (representedQuasicoherentSchemeTensorIso_eq B S hS U M' N')

end AlgebraicGeometry.Space

end
