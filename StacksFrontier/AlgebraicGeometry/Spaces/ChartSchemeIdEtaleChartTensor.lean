module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleTensor

/-!
# The identity-chart restriction of a tensor product of quasi-coherent modules

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`.  An `𝒪`-module on
the small étale site of the algebraic space `yoneda.obj U` restricts to an
`AlgebraicGeometry.Scheme.Modules` on `T` along the identity chart, and
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` factors that restriction as the
comparison of Stacks 04M0 followed by the Zariski restriction
`AlgebraicGeometry.SmallEtale.restrictModule` of Descent, Proposition 03DX (2).  Each of the two
factors is compatible with the tensor product, so the restriction itself is:

`(𝓟 ⊗_𝒪 𝓠)|_T ≅ 𝓟|_T ⊗_{𝒪_T} 𝓠|_T` for *quasi-coherent* `𝓟` and `𝓠`.

The two factors are
`AlgebraicGeometry.Space.representedSmallEtaleModuleTensorIso`, Stacks 03EL at the morphism of
ringed sites presented by the inverse of the 04M0 comparison, and
`AlgebraicGeometry.SmallEtale.restrictModuleTensorIso`, the monoidality of the Zariski
restriction on quasi-coherent modules.  The first is stated for the *functor* of the comparison
equivalence and what is needed is its inverse, which is
`AlgebraicGeometry.Space.representedSmallEtaleModuleInverseTensorIso` below: an equivalence whose
functor is monoidal has monoidal inverse, and the two counits and the unit do it at one pair of
objects.

## Main definitions

* `AlgebraicGeometry.Space.representedSmallEtaleModuleInverseTensorIso`: the inverse of the
  comparison of Stacks 04M0 carries the tensor product sheaf to the tensor product sheaf.
* `AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartTensorIso`: **the identity-chart
  restriction of a tensor product of quasi-coherent `𝒪`-modules is the tensor product of the
  restrictions.**

## Implementation notes

Quasi-coherence of the two modules is needed, and only for
`AlgebraicGeometry.SmallEtale.restrictModuleTensorIso`: the Zariski restriction is a right
adjoint and so only lax monoidal in general, and it is on quasi-coherent modules that it is the
inverse of an equivalence.  The 04M0 comparison needs no hypothesis.  Quasi-coherence of the
modules read across that comparison is not a further hypothesis — it is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModule_iff`, Stacks 03DM for
clause (6) of Stacks 03DL.

Both the étale and Zariski tensor products are the curried
`Stacks.SheafOfModules.Tensor.sheafTensor`.
`AlgebraicGeometry.Space.modulesTensorObjIso` compares the monoidal product of
`AlgebraicGeometry.Space.Modules` with that tensor product. The tensor of the two restriction
comparisons is assembled separately from the full composite to keep elaboration bounded.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The inverse of the comparison of Stacks 04M0 carries the tensor product sheaf to the tensor
product sheaf.**

An equivalence whose functor is monoidal has monoidal inverse, and this is that argument unfolded
at one pair of objects, so that no monoidal structure has to be transported: the two counits
rewrite `𝓟` and `𝓠` as the images of their inverse images,
`AlgebraicGeometry.Space.representedSmallEtaleModuleTensorIso` splits the image of the tensor
product, and the unit cancels the round trip. -/
def representedSmallEtaleModuleInverseTensorIso
    (P Q : SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :
    (representedSmallEtaleModuleEquivalence B S hS U).inverse.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).obj Q) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (representedSchemeCommRingStructureSheaf B S hS U)).obj
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)).obj
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q) :=
  (representedSmallEtaleModuleEquivalence B S hS U).inverse.mapIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).mapIso (X := P)
          (Y := (representedSmallEtaleModuleEquivalence B S hS U).functor.obj
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P))
          ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app P).symm).app Q ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
            (structureSheaf B S hS (yoneda.obj U)
              (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj
            ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
              ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P))).mapIso
          (X := Q)
          (Y := (representedSmallEtaleModuleEquivalence B S hS U).functor.obj
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q))
          ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app Q).symm ≪≫
        (representedSmallEtaleModuleTensorIso B S hS U
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q)).symm) ≪≫
    ((representedSmallEtaleModuleEquivalence B S hS U).unitIso.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (representedSchemeCommRingStructureSheaf B S hS U)).obj
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)).obj
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q))).symm

/-- **The identity-chart restriction of a tensor product of quasi-coherent `𝒪`-modules is the
tensor product of the restrictions.**  For quasi-coherent `𝒪`-modules `𝓟` and `𝓠` on the small
étale site of the algebraic space `yoneda.obj U`,

`(𝓟 ⊗_𝒪 𝓠)|_T ≅ 𝓟|_T ⊗_{𝒪_T} 𝓠|_T`

on the Zariski site of the scheme `T` underlying `U`.

`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` factors the restriction as the
inverse of the comparison of Stacks 04M0 followed by the Zariski restriction of Descent,
Proposition 03DX (2); the first factor is compatible with the tensor product by
`AlgebraicGeometry.Space.representedSmallEtaleModuleInverseTensorIso` and the second by
`AlgebraicGeometry.SmallEtale.restrictModuleTensorIso`, whose quasi-coherence hypotheses are the
two given ones read across the comparison. -/
def restrictToChartSchemeIdEtaleChartTensorIso
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    restrictToChartScheme B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) (P ⊗ Q)
        (idEtaleChart B S hS U) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).obj
          (restrictToChartScheme B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) P (idEtaleChart B S hS U))).obj
          (restrictToChartScheme B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) Q (idEtaleChart B S hS U)) := by
  set E := representedSmallEtaleModuleEquivalence B S hS U with hE
  -- the two modules read on the small étale site of the scheme, and their quasi-coherence
  have hP' : (E.inverse.obj P).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U (E.inverse.obj P)).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (E.counitIso.app P).symm hP)
  have hQ' : (E.inverse.obj Q).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U (E.inverse.obj Q)).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (E.counitIso.app Q).symm hQ)
  -- the monoidal product of `Space.Modules` at the bifunctor spelling
  have hten : (P ⊗ Q : Modules.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).obj Q :=
    modulesTensorObjIso B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) P Q
  let tensorRestrictionIso :=
    (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)).mapIso
      (Iso.prod (restrictToChartSchemeIdEtaleChartIso B S hS U P).symm
        (restrictToChartSchemeIdEtaleChartIso B S hS U Q).symm)
  refine restrictToChartSchemeIdEtaleChartIso B S hS U (P ⊗ Q) ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
      (E.inverse.mapIso hten ≪≫ representedSmallEtaleModuleInverseTensorIso B S hS U P Q) ≪≫
    _root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property
        (E.inverse.obj P) (E.inverse.obj Q) hP' hQ' ≪≫
    tensorRestrictionIso

end AlgebraicGeometry.Space

end
