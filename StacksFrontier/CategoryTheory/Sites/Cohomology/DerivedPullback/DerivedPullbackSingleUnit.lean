module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceShiftedUnit

/-!
# The derived pullback of the structure sheaf placed in any degree

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `q : ℤ`. The complex
`O_D[q]` (the structure sheaf placed in degree `q`) is K-flat with flat terms, so its derived
pullback is computed termwise (Stacks 06YY), and `f^*O_D ≅ O_C`: `Lf^*(O_D[q]) ≅ O_C[q]`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackSingleUnitIso`.

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
/-- The structure sheaf placed in degree `q`, as a complex, has flat terms. -/
theorem isFlat_singleUnitComplex_X (q j : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O)
      ((Stacks.SheafOfModules.singleUnitComplex Y.O q).X j) := by
  by_cases hj : j = q
  · subst hj
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
      (HomologicalComplex.singleObjXSelf _ _ _).symm
      (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := Y.toRingedSite))
  · exact Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero (Y := Y.toRingedSite) _
      (HomologicalComplex.isZero_single_obj_X _ q _ j hj)

/-- **`Lf^*(O_D[q]) ≅ O_C[q]`**: the K-flat model `O_D[q]` computes the derived pullback, the
degreewise pullback of a complex concentrated in degree `q` is concentrated in degree `q`, and
`f^*O_D ≅ O_C`. -/
def derivedPullbackSingleUnitIso (q : ℤ) :
    (derivedPullback f).obj
        (DerivedCategory.Q.obj (Stacks.SheafOfModules.singleUnitComplex Y.O q)) ≅
      DerivedCategory.Q.obj (Stacks.SheafOfModules.singleUnitComplex X.O q) :=
  flatPullbackIso f _ (Stacks.SheafOfModules.isKFlat_singleUnitComplex Y.O q)
      (isFlat_singleUnitComplex_X q) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (f.toModulesHom.pullbackModules)
        (ComplexShape.up ℤ) q).app _ ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) q).mapIso
        (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso f.toModulesHom).symm)

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
