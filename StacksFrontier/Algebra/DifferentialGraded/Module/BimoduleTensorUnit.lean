module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCohomology

/-!
# The regular module is a unit for the relative tensor product

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Tensoring the regular module `A` with `N` over `A`
gives back `N`: there is a canonical isomorphism `A ⊗_A N ≅ N` of right differential graded
`B`-modules, sending the pure tensor `a ⊗ y` to `a y`. Passing to derived categories, the derived
tensor product of the class of the regular module with `N` is the class of `N`, and the same holds
after shifting: `A[k] ⊗_A^𝐋 N ≅ N[k]`.

## Main definitions

* `DifferentialGraded.Bimodule.tensorObj'`: the relative tensor product `M ⊗_A N` of Tag 09LM of
  a right differential graded `A`-module `M`, as an object of the category of right differential
  graded `B`-modules.
* `DifferentialGraded.Bimodule.tensorRegularIso`: the isomorphism `A ⊗_A N ≅ N` of right
  differential graded `B`-modules, bundled with its action on pure tensors.
* `DifferentialGraded.Bimodule.tensorShiftRegularIso`: the shifted form `A[k] ⊗_A N ≅ N[k]`.
* `DifferentialGraded.Bimodule.derivedTensorRegularIso`: the isomorphism `A ⊗_A^𝐋 N ≅ N` in
  `D(B, d)`.
* `DifferentialGraded.Bimodule.derivedTensorShiftRegularIso`: the shifted derived form
  `A[k] ⊗_A^𝐋 N ≅ N[k]`.

## Main results

* `DifferentialGraded.Bimodule.tensorShiftRegularIso_hom_pure`: the shifted isomorphism sends the
  pure tensor `a ⊗ y` to `a y`, with no sign.

## Implementation notes

The sign-free shift comparison of Tag 0FQN is `DifferentialGraded.Bimodule.tensorShiftIso`, and
the unit isomorphism `A ⊗_A N = N` is used without being stated in the Stacks source, so no
declaration here carries a `stacks` attribute.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) for the relative tensor
  product and its universal property, [Tag 0FQN](https://stacks.math.columbia.edu/tag/0FQN) for
  the sign-free shift comparison, [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1) for the
  left orthogonality of the regular module, and
  [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) for the derived tensor product.
-/

@[expose] public section

open CategoryTheory

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGraded.Bimodule

universe u

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

open DifferentialGradedModule

/-- The relative tensor product `M ⊗_A N` of Tag 09LM, named as an object of the category of
right differential graded `B`-modules. -/
noncomputable abbrev tensorObj' (N : Bimodule A B) (M : DifferentialGradedModule A) :
    DifferentialGradedModule B :=
  (tensorDGFunctor N).functor.obj M

/-! ### The differential graded isomorphism -/

/-- The left action of a homogeneous element of `A` on a homogeneous element of the bimodule,
read off the total action. -/
private theorem leftActionTotal_coe (N : Bimodule A B) {n q : ℤ} (a : A.grading n)
    (y : N.rightModule.grading q) :
    leftActionTotal A B N.rightModule N.leftAction.1 (a : A.A) (y : N.rightModule.M) =
      ((show N.rightModule.grading (q + n) from
        (N.leftAction.1.action n a).v q (q + n) (by omega) y) : N.rightModule.M) := by
  rw [leftActionTotal_apply A B N.rightModule N.leftAction.1 n a,
    totalizeCochain_apply_of_eq B N.rightModule n q (q + n) rfl
      (N.leftAction.1.action n a) y]
  rfl

/-- The total left action is right `B`-linear in the second variable, for an arbitrary scalar of
`A` and an arbitrary scalar of `B`. -/
private theorem leftActionTotal_op_smul (N : Bimodule A B) (a : A.A) (b : B.A)
    (y : N.rightModule.M) :
    leftActionTotal A B N.rightModule N.leftAction.1 a (MulOpposite.op b • y) =
      MulOpposite.op b • leftActionTotal A B N.rightModule N.leftAction.1 a y := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha', smul_add]
  | @homogeneous n a =>
    induction b using DirectSum.Decomposition.inductionOn B.grading with
    | zero => simp
    | add b b' hb hb' => simp only [MulOpposite.op_add, add_smul, map_add, hb, hb']
    | @homogeneous q b =>
      exact leftActionTotal_commutes A B N.rightModule N.leftAction.1 N.leftAction.2 a b y

/-- In the regular module, the right action of `a` on `x` is the product `x * a`. -/
private theorem regularModule_op_smul (x a : A.A) :
    MulOpposite.op a • (x : (regularModule A).M) = x * a :=
  MulOpposite.smul_eq_mul_unop ..

/-- The left action of `A` on the bimodule `N`, as a balanced bilinear map out of the regular
module. -/
private noncomputable def regularBilinear (N : Bimodule A B) :
    BalancedBilinearMap (regularModule A) N N.rightModule where
  toLinearMap := leftActionTotal A B N.rightModule N.leftAction.1
  map_grading p q x y := by
    rw [add_comm p q]
    exact leftActionTotal_apply_mem A B N.rightModule N.leftAction.1 x y
  map_d p x y := leftActionTotal_leibniz A B N.rightModule N.leftAction.1 x y
  balance p q n x y a := by
    rw [regularModule_op_smul, leftActionTotal_mul A B N.rightModule N.leftAction.1 x a,
      Module.End.mul_apply, ← leftActionTotal_apply A B N.rightModule N.leftAction.1 n a,
      ← leftActionTotal_apply A B N.rightModule N.leftAction.1 p x, leftActionTotal_coe N a y]
  map_right x y b := leftActionTotal_op_smul N x b y

/-- The inclusion `y ↦ 1 ⊗ y` of the bimodule into `A ⊗_A N`. -/
private noncomputable def regularTensorInv (N : Bimodule A B) :
    DifferentialGradedModule.Hom N.rightModule (tensorObj' N (regularModule A)) where
  toFun := ((tensorDGFunctor N).pure (regularModule A)).toLinearMap (1 : A.A)
  map_smul y b := ((tensorDGFunctor N).pure (regularModule A)).map_right (1 : A.A) y b
  map_grading n y hy := by
    have h := ((tensorDGFunctor N).pure (regularModule A)).map_grading 0 n
      ⟨(1 : A.A), SetLike.one_mem_graded A.grading⟩ ⟨y, hy⟩
    rwa [zero_add] at h
  map_d := by
    refine LinearMap.ext fun y => ?_
    have h := ((tensorDGFunctor N).pure (regularModule A)).map_d 0
      ⟨(1 : A.A), SetLike.one_mem_graded A.grading⟩ y
    rw [show (regularModule A).d
        ((⟨(1 : A.A), SetLike.one_mem_graded A.grading⟩ : (regularModule A).grading 0) :
          (regularModule A).M) = 0 from DifferentialGradedAlgebra.d_one A,
      map_zero, LinearMap.zero_apply, zero_add] at h
    simpa using h.symm

/-- In `A ⊗_A N` the pure tensor `1 ⊗ a y` equals `a ⊗ y`. -/
private theorem pure_one_leftActionTotal (N : Bimodule A B) (a : A.A)
    (y : N.rightModule.M) :
    ((tensorDGFunctor N).pure (regularModule A)).toLinearMap (1 : A.A)
        (leftActionTotal A B N.rightModule N.leftAction.1 a y) =
      ((tensorDGFunctor N).pure (regularModule A)).toLinearMap a y := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | @homogeneous n a =>
    induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | @homogeneous q y =>
      have hb := ((tensorDGFunctor N).pure (regularModule A)).balance 0 q n
        ⟨(1 : A.A), SetLike.one_mem_graded A.grading⟩ y a
      rw [regularModule_op_smul, one_mul] at hb
      rw [leftActionTotal_coe N a y]
      exact hb.symm

/-- The homomorphism `A ⊗_A N → N` with `a ⊗ y ↦ a y`, from the universal property of the
relative tensor product. -/
private noncomputable def regularTensorHom (N : Bimodule A B) :
    DifferentialGradedModule.Hom (tensorObj' N (regularModule A)) N.rightModule :=
  ((tensorDGFunctor N).universal (regularModule A) N.rightModule (regularBilinear N)).choose

/-- The homomorphism `A ⊗_A N → N` sends the pure tensor `a ⊗ y` to `a y`. -/
private theorem regularTensorHom_pure (N : Bimodule A B) (a : A.A) (y : N.rightModule.M) :
    (regularTensorHom N).toFun
        (((tensorDGFunctor N).pure (regularModule A)).toLinearMap a y) =
      leftActionTotal A B N.rightModule N.leftAction.1 a y :=
  ((tensorDGFunctor N).universal (regularModule A) N.rightModule
    (regularBilinear N)).choose_spec.1 a y

/-- **The regular module is a unit for the relative tensor product.** Tensoring the regular
module `A` with a differential graded `(A, B)`-bimodule `N` over `A` gives back `N`: there is an
isomorphism `A ⊗_A N ≅ N` of right differential graded `B`-modules carrying the pure tensor
`a ⊗ y` to `a y`. -/
@[no_expose]
noncomputable def tensorRegularIso (N : Bimodule A B) :
    { e : tensorObj' N (regularModule A) ≅ N.rightModule //
      ∀ (a : A.A) (y : N.rightModule.M),
        e.hom.toFun (((tensorDGFunctor N).pure (regularModule A)).toLinearMap a y) =
          leftActionTotal A B N.rightModule N.leftAction.1 a y } := by
  refine ⟨{ hom := regularTensorHom N
            inv := regularTensorInv N
            hom_inv_id := ?_
            inv_hom_id := ?_ }, regularTensorHom_pure N⟩
  · refine tensorObj_hom_ext' N (regularModule A) _ (DifferentialGradedModule.Hom.id _)
      fun a y => ?_
    change (regularTensorInv N).toFun ((regularTensorHom N).toFun _) = _
    rw [regularTensorHom_pure N a y]
    exact pure_one_leftActionTotal N a y
  · refine DifferentialGradedModule.Hom.ext (LinearMap.ext fun y => ?_)
    change (regularTensorHom N).toFun
      (((tensorDGFunctor N).pure (regularModule A)).toLinearMap (1 : A.A) y) = y
    rw [regularTensorHom_pure N (1 : A.A) y,
      leftActionTotal_one A B N.rightModule N.leftAction.1]
    rfl

/-! ### The shifted differential graded isomorphism -/

/-- **The shifted unit isomorphism.** For every `k : ℤ`, the isomorphism `A[k] ⊗_A N ≅ N[k]` of
right differential graded `B`-modules obtained from the unit isomorphism `A ⊗_A N ≅ N` and the
sign-free comparison `(M ⊗_A N)[k] ≅ M[k] ⊗_A N` of Tag 0FQN. -/
@[no_expose]
noncomputable def tensorShiftRegularIso (N : Bimodule A B) (k : ℤ) :
    tensorObj' N (shift (regularModule A) k) ≅ shift N.rightModule k :=
  (tensorShiftIso N (regularModule A) k).1.symm ≪≫
    (DifferentialGradedModule.shiftFunctor B k).mapIso (tensorRegularIso N).1

/-- The shifted unit isomorphism `A[k] ⊗_A N ≅ N[k]` sends the pure tensor `a ⊗ y` to `a y`, with
no sign. -/
theorem tensorShiftRegularIso_hom_pure (N : Bimodule A B) (k : ℤ)
    (a : (shift (regularModule A) k).M) (y : N.rightModule.M) :
    (tensorShiftRegularIso N k).hom.toFun
        (((tensorDGFunctor N).pure (shift (regularModule A) k)).toLinearMap a y) =
      leftActionTotal A B N.rightModule N.leftAction.1 a y := by
  show ((DifferentialGradedModule.shiftFunctor B k).map (tensorRegularIso N).1.hom).toFun
    ((tensorShiftIso N (regularModule A) k).1.inv.toFun _) = _
  rw [tensorShiftIso_inv_pure N (regularModule A) k a y,
    DifferentialGradedModule.shiftFunctor_map_toFun]
  exact (tensorRegularIso N).2 a y

/-! ### The derived isomorphism -/

/-- **The derived unit isomorphism.** In `D(B, d)` the derived tensor product of the class of the
regular module `A` with the bimodule `N` is the class of `N`. -/
@[no_expose]
noncomputable def derivedTensorRegularIso (N : Bimodule A B) :
    (derivedTensorFunctor N).obj
        ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≅
      (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule := by
  have := isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N
    ((toHomotopyCategory A).obj (regularModule A))
    (leftOrthogonal_acyclic_toHomotopyCategory_regularModule A)
  exact asIso ((derivedTensorFunctorCounit N).app
      ((toHomotopyCategory A).obj (regularModule A))) ≪≫
    (quasiIsomorphisms' B).Q.mapIso
      ((Iso.app (tensorCompFunctor_quotient N) (regularModule A)).symm ≪≫
        (toHomotopyCategory B).mapIso (tensorRegularIso N).1)

/-- **The shifted derived unit isomorphism.** For every `k : ℤ` the derived tensor product of the
class of `A[k]` with the bimodule `N` is the class of `N[k]`. This is the base case of the
dévissage of Tag 0FQE, whose hypothesis (3) is a property of the shifts of the class of the
regular module. -/
@[no_expose]
noncomputable def derivedTensorShiftRegularIso (N : Bimodule A B) (k : ℤ) :
    (derivedTensorFunctor N).obj
        (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦k⟧) ≅
      ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)⟦k⟧ :=
  ((derivedTensorFunctor N).commShiftIso k).app
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A)) ≪≫
    (CategoryTheory.shiftFunctor (derivedCategory' B) k).mapIso (derivedTensorRegularIso N)

end DifferentialGraded.Bimodule

end
