module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-!
# The module attached to a quasi-coherent module on a scheme chart is monoidal

Let `U` be an object of the big fppf site over `S`.  Stacks 03DX (2) attaches to a quasi-coherent
module `M` on the scheme underlying `U` an `𝒪`-module `M_{yoneda U}` on the representable algebraic
space `yoneda.obj U`, `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.  This
file identifies the module attached to a tensor product:

`(M ⊗ N)_{yoneda U} ≅ M_{yoneda U} ⊗ N_{yoneda U}`,

naturally in `M` and `N`.  The passage is the associated module `𝓕 ↦ 𝓕^a` of the small Zariski
site followed by the comparison of Stacks 04M0, and each factor is a comparison of Stacks 03EL:
`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso` and
`AlgebraicGeometry.Space.representedSmallEtaleModuleTensorIso`.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentTensorObj`: the tensor product of two quasi-coherent
  modules on the scheme underlying `U`, as a quasi-coherent module (Stacks 01CE).
* `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso`: **the module attached to a
  tensor product is the tensor product of the attached modules.**

## Main results

* `Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality`: a comparison of Stacks 03EL
  read through an identification of the pullback of modules with another functor is natural in
  both factors.  Both factors of the comparison above have this shape.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace Stacks.SheafOfModules

universe w w' v u₁ v' u'

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  {L : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  (α : f.pullbackModules ≅ L)

/-- The comparison of Stacks 03EL for `f`, read through an identification `α` of the pullback of
modules along `f` with a functor `L`: `L(M ⊗ N) ≅ L M ⊗ L N`.

`AlgebraicGeometry.SmallEtale.associatedModuleTensorIso` and
`Stacks.SheafOfModules.reindexTensorIso` are this composite, written out. -/
def pullbackTensorIsoTransport (M N : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    L.obj (((Tensor.sheafTensor Y.O).obj M).obj N) ≅
      ((Tensor.sheafTensor X.O).obj (L.obj M)).obj (L.obj N) :=
  α.symm.app _ ≪≫ (pullbackTensorIso f).app (M, N) ≪≫
    ((Tensor.sheafTensor X.O).mapIso (α.app M)).app _ ≪≫
      ((Tensor.sheafTensor X.O).obj _).mapIso (α.app N)

/-- **A comparison of Stacks 03EL read through an identification of the pullback is natural in
both factors.** -/
theorem pullbackTensorIsoTransport_hom_naturality
    {M M' N N' : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)} (a : M ⟶ M') (b : N ⟶ N') :
    L.map (((Tensor.sheafTensor Y.O).map a).app N ≫ ((Tensor.sheafTensor Y.O).obj M').map b) ≫
        (pullbackTensorIsoTransport f α M' N').hom =
      (pullbackTensorIsoTransport f α M N).hom ≫
        ((Tensor.sheafTensor X.O).map (L.map a)).app (L.obj N) ≫
          ((Tensor.sheafTensor X.O).obj (L.obj M')).map (L.map b) := by
  have h1 := α.inv.naturality
    (((Tensor.sheafTensor Y.O).map a).app N ≫ ((Tensor.sheafTensor Y.O).obj M').map b)
  have h2 := pullbackTensorIso_hom_naturality_map f a b
  have h3 : ((Tensor.sheafTensor X.O).map (f.pullbackModules.map a)).app (f.pullbackModules.obj N) ≫
        ((Tensor.sheafTensor X.O).obj (f.pullbackModules.obj M')).map (f.pullbackModules.map b) ≫
        ((Tensor.sheafTensor X.O).map (α.hom.app M')).app (f.pullbackModules.obj N') ≫
          ((Tensor.sheafTensor X.O).obj (L.obj M')).map (α.hom.app N') =
      ((Tensor.sheafTensor X.O).map (α.hom.app M)).app (f.pullbackModules.obj N) ≫
        ((Tensor.sheafTensor X.O).obj (L.obj M)).map (α.hom.app N) ≫
        ((Tensor.sheafTensor X.O).map (L.map a)).app (L.obj N) ≫
          ((Tensor.sheafTensor X.O).obj (L.obj M')).map (L.map b) := by
    have n1 := ((Tensor.sheafTensor X.O).map (α.hom.app M')).naturality (f.pullbackModules.map b)
    have n2 := ((Tensor.sheafTensor X.O).map (L.map a)).naturality (α.hom.app N)
    rw [reassoc_of% n1, ← NatTrans.comp_app_assoc, ← Functor.map_comp, ← Functor.map_comp,
      α.hom.naturality a, α.hom.naturality b, Functor.map_comp, NatTrans.comp_app,
      Functor.map_comp, Category.assoc, ← reassoc_of% n2]
  simp only [pullbackTensorIsoTransport, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2]
  exact congrArg (fun k => α.inv.app _ ≫ (pullbackTensorIso f).hom.app (M, N) ≫ k) h3

end Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **Stacks 01CE on the scheme underlying `U`**: the tensor product of two quasi-coherent modules,
as a quasi-coherent module. -/
abbrev quasicoherentTensorObj
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory :=
  ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).obj M.obj).obj N.obj,
    _root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_tensorSheaf_of_isQuasicoherent _ _ _
      M.property N.property⟩

/-- **The module attached to a tensor product of quasi-coherent modules is the tensor product of
the attached modules.**  For quasi-coherent modules `M` and `N` on the scheme underlying `U`,

`(M ⊗ N)_{yoneda U} ≅ M_{yoneda U} ⊗ N_{yoneda U}`

on the small étale site of `yoneda.obj U`, where `(-)_{yoneda U}` is Stacks 03DX (2),
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`.  Its first factor is
Stacks 03EL at `ε` read through `AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso` (the
composite `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso` writes out), carried by the
comparison of Stacks 04M0; its second is Stacks 03EL at the inverse of that comparison read
through `Stacks.SheafOfModules.pullbackModulesReindexIso` (the composite
`AlgebraicGeometry.Space.representedSmallEtaleModuleTensorIso` writes out); and the monoidal
product is read as the tensor product sheaf by `AlgebraicGeometry.Space.modulesTensorObjIso`.
Both factors are formed with `Stacks.SheafOfModules.pullbackTensorIsoTransport`, whose
naturality is `Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality`. -/
def representedQuasicoherentSchemeTensorIso
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
        (quasicoherentTensorObj B S hS U M N)).obj ≅
      MonoidalCategoryStruct.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj :=
  (representedSmallEtaleModuleEquivalence B S hS U).functor.mapIso
      (Stacks.SheafOfModules.pullbackTensorIsoTransport
        (_root_.AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (_root_.AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) M.obj N.obj) ≪≫
    Stacks.SheafOfModules.pullbackTensorIsoTransport _
      (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U)) _ _ ≪≫
    (modulesTensorObjIso B S hS (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).symm

end AlgebraicGeometry.Space

end
