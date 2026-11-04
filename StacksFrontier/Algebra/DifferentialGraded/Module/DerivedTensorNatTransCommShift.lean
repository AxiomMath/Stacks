module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBimoduleMap
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.CategoryTheory.Functor.Derived.LeftDerivedNatTransCommShift
public import StacksFrontier.CategoryTheory.Shift.QuotientNatTransCommShift

/-! # The transformation `1 ⊗ f` of the derived tensor products commutes with the translation

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let
`f : N ⟶ N'` be a homomorphism of differential graded `(A, B)`-bimodules. The transformation
`1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'` of Stacks Tag 09S3 commutes with the translation.

The compatibility is proved where the transformation is defined and then carried along its
construction: on differential graded modules it is the statement that the sign-free comparison
`(M ⊗_A N)[n] ≅ M[n] ⊗_A N` of Tag 0FQN is natural in the bimodule, which holds because both
sides are the identity on pure tensors; it descends to the homotopy categories because the
comparison of Tag 09LM with the quotient by homotopy commutes with the translation; and it passes
to the derived functors because a transformation of total left derived functors induced by one
that commutes with the translation again does.

## Main results

* `DifferentialGraded.Bimodule.tensorModuleNatTrans_commShift`
* `DifferentialGraded.Bimodule.tensorHomotopyNatTrans_commShift`
* `DifferentialGraded.Bimodule.derivedTensorNatTrans_commShift`

## References

* [Stacks Project, Tag 09S3](https://stacks.math.columbia.edu/tag/09S3); the tensor functors are
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) and
  [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS), and the shift comparison is
  [Tag 0FQN](https://stacks.math.columbia.edu/tag/0FQN).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- The commutation of the ordinary tensor functor with the shift, at an object: the component
of the comparison is the inverse of the sign-free isomorphism `(M ⊗_A N)[n] ≅ M[n] ⊗_A N` of
Stacks 0FQN. -/
theorem commShiftIso_tensorCompFunctor_hom_app (N : Bimodule A B) (n : ℤ)
    (M : DifferentialGradedModule.{u, u, u} A) :
    ((tensorCompFunctor N).commShiftIso n).hom.app M = (tensorShiftIso N M n).1.inv := rfl

/-- **The transformation `1 ⊗ f` of Stacks 09S3 commutes with the shift.** Both sides are
homomorphisms out of `M[n] ⊗_A N` sending the pure tensor `x ⊗ y` to `x ⊗ f(y)`. -/
instance tensorModuleNatTrans_commShift {N N' : Bimodule A B} (f : N ⟶ N') :
    NatTrans.CommShift (tensorModuleNatTrans f) ℤ := by
  refine ⟨fun n => ?_⟩
  ext M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  refine tensorObj_hom_ext' N (DifferentialGradedModule.shift M n) _ _ fun x y => ?_
  have hL : (((tensorCompFunctor N).commShiftIso n).hom.app M).toFun
        (((tensorDGFunctor N).pure (DifferentialGradedModule.shift M n)).toLinearMap x y) =
      ((tensorDGFunctor N).pure M).toLinearMap x y :=
    tensorShiftIso_inv_pure N M n x y
  have hR : (((tensorCompFunctor N').commShiftIso n).hom.app M).toFun
        (((tensorDGFunctor N').pure (DifferentialGradedModule.shift M n)).toLinearMap x
          (f.rightHom.toFun y)) =
      ((tensorDGFunctor N').pure M).toLinearMap x (f.rightHom.toFun y) :=
    tensorShiftIso_inv_pure N' M n x (f.rightHom.toFun y)
  have eL : ((CategoryTheory.shiftFunctor (DifferentialGradedModule B) n).map
        ((tensorModuleNatTrans f).app M)).toFun
        ((((tensorCompFunctor N).commShiftIso n).hom.app M).toFun
          (((tensorDGFunctor N).pure (DifferentialGradedModule.shift M n)).toLinearMap x y)) =
      ((tensorDGFunctor N').pure M).toLinearMap x (f.rightHom.toFun y) := by
    rw [hL]
    exact tensorHomOfBimoduleHom_pure f M x y
  have eR : (((tensorCompFunctor N').commShiftIso n).hom.app M).toFun
        (((tensorModuleNatTrans f).app (DifferentialGradedModule.shift M n)).toFun
          (((tensorDGFunctor N).pure (DifferentialGradedModule.shift M n)).toLinearMap x y)) =
      ((tensorDGFunctor N').pure M).toLinearMap x (f.rightHom.toFun y) := by
    rw [show ((tensorModuleNatTrans f).app (DifferentialGradedModule.shift M n)).toFun
          (((tensorDGFunctor N).pure (DifferentialGradedModule.shift M n)).toLinearMap x y) =
        ((tensorDGFunctor N').pure (DifferentialGradedModule.shift M n)).toLinearMap x
          (f.rightHom.toFun y) from tensorHomOfBimoduleHom_pure f _ x y]
    exact hR
  exact eL.trans eR.symm

/-- **The comparison of Stacks 09LM with the quotient commutes with the translation**: it is one
of the two isomorphisms exhibiting the tensor functor on homotopy categories as a lift of
ordinary tensoring along the quotient by homotopy. -/
instance tensorCompFunctor_quotient_commShift (N : Bimodule A B) :
    NatTrans.CommShift (tensorCompFunctor_quotient N).hom ℤ := by
  have hlift : NatTrans.CommShift (tensorHomotopyLiftIso N).hom ℤ :=
    Functor.CommShift.ofIso_compatibility (tensorHomotopyLiftIso N) ℤ
  have hw : Functor.whiskerLeft (toHomotopyCategory A) (tensorHomotopyLiftIso N).hom =
      (CategoryTheory.Quotient.lift.isLift (homotopyRel A)
            (tensorCompFunctor N ⋙ toHomotopyCategory B)
            (tensorComp_quotient_respects_homotopy N)).hom ≫
        (tensorCompFunctor_quotient N).hom :=
    NatTrans.ext (funext fun _ => rfl)
  have h1 : NatTrans.CommShift
      ((CategoryTheory.Quotient.lift.isLift (homotopyRel A)
            (tensorCompFunctor N ⋙ toHomotopyCategory B)
            (tensorComp_quotient_respects_homotopy N)).hom ≫
        (tensorCompFunctor_quotient N).hom) ℤ := by
    rw [← hw]; infer_instance
  have h2 : (tensorCompFunctor_quotient N).hom =
      (CategoryTheory.Quotient.lift.isLift (homotopyRel A)
            (tensorCompFunctor N ⋙ toHomotopyCategory B)
            (tensorComp_quotient_respects_homotopy N)).inv ≫
        ((CategoryTheory.Quotient.lift.isLift (homotopyRel A)
              (tensorCompFunctor N ⋙ toHomotopyCategory B)
              (tensorComp_quotient_respects_homotopy N)).hom ≫
          (tensorCompFunctor_quotient N).hom) := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hhom : NatTrans.CommShift
      (CategoryTheory.Quotient.lift.isLift (homotopyRel A)
          (tensorCompFunctor N ⋙ toHomotopyCategory B)
          (tensorComp_quotient_respects_homotopy N)).hom ℤ :=
    CategoryTheory.Quotient.liftCommShift_compatibility
      (tensorCompFunctor N ⋙ toHomotopyCategory B) (homotopyRel A) ℤ
      (tensorComp_quotient_respects_homotopy N)
  have hinv : NatTrans.CommShift
      (CategoryTheory.Quotient.lift.isLift (homotopyRel A)
          (tensorCompFunctor N ⋙ toHomotopyCategory B)
          (tensorComp_quotient_respects_homotopy N)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  rw [h2]
  exact NatTrans.CommShift.comp _ _ ℤ

/-- **The transformation `1 ⊗ f` on the homotopy categories commutes with the translation.** Its
restriction along the quotient by homotopy is the transformation on differential graded modules,
read through the comparison of Tag 09LM. -/
instance tensorHomotopyNatTrans_commShift {N N' : Bimodule A B} (f : N ⟶ N') :
    NatTrans.CommShift (tensorHomotopyNatTrans f) ℤ := by
  have hw : Functor.whiskerLeft (toHomotopyCategory A) (tensorHomotopyNatTrans f) =
      (tensorCompFunctor_quotient N).inv ≫
        Functor.whiskerRight (tensorModuleNatTrans f) (toHomotopyCategory B) ≫
          (tensorCompFunctor_quotient N').hom :=
    NatTrans.ext (funext fun M => tensorHomotopyNatTrans_app f M)
  have h : NatTrans.CommShift
      (Functor.whiskerLeft (toHomotopyCategory A) (tensorHomotopyNatTrans f)) ℤ := by
    rw [hw]; infer_instance
  exact NatTrans.commShift_of_whiskerLeft_quotientFunctor ℤ (tensorHomotopyNatTrans f)

/-- **The transformation `1 ⊗ f` with localized target commutes with the translation.** -/
instance ordinaryTensorNatTrans_commShift {N N' : Bimodule A B} (f : N ⟶ N') :
    NatTrans.CommShift (ordinaryTensorNatTrans f) ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Functor.whiskerRight (tensorHomotopyNatTrans f) (quasiIsomorphisms' B).Q) ℤ)

/-- **The transformation `1 ⊗ f` of Stacks 09S3 between the derived tensor functors commutes with
the translation.** Both functors are total left derived functors, their comparisons of Tag 09LS
commute with the translation, and `1 ⊗ f` on the homotopy categories does. -/
instance derivedTensorNatTrans_commShift {N N' : Bimodule A B} (f : N ⟶ N') :
    NatTrans.CommShift (derivedTensorNatTrans f) ℤ :=
  Functor.leftDerivedNatTrans_commShift (derivedTensorFunctor N) (derivedTensorFunctor N')
    (derivedTensorFunctorCounit N) (derivedTensorFunctorCounit N') (quasiIsomorphisms' A) ℤ
    (ordinaryTensorNatTrans f)

end DifferentialGraded.Bimodule

end
