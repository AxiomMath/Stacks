module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative

/-!
# The derived pullback of the structure sheaf along a morphism of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi.  The structure sheaf `O_D`
placed in degree `0` is a K-flat complex with flat terms, so its derived pullback is its pullback
of modules (Stacks 06YY), and the pullback of `O_D` is `O_C`:

`Lf^*(O_D[0]) ≅ O_C[0]`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral`:
  `Lf^*(O_D[0]) ≅ O_C[0]`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe u c c'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

omit [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasSheafify Y.J (Type u)] in
/-- The structure sheaf placed in degree `0`, as a complex, has flat terms. -/
theorem isFlat_single_unit_X (j : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O)
      (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).X j) := by
  by_cases hj : j = 0
  · subst hj
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
      (HomologicalComplex.singleObjXSelf _ _ _).symm
      (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := Y.toRingedSite))
  · exact Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero (Y := Y.toRingedSite) _
      (HomologicalComplex.isZero_single_obj_X _ 0 _ j hj)

/-- The derived pullback of the structure sheaf is the structure sheaf:
`Lf^*(O_D[0]) ≅ O_C[0]`. -/
def derivedPullbackUnitIsoGeneral :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (derivedPullback f).mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
    flatPullbackIso f _ (Stacks.SheafOfModules.isKFlat_single_unit Y.O) (isFlat_single_unit_X) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (f.toModulesHom.pullbackModules)
        (ComplexShape.up ℤ) 0).app _) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).symm

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
