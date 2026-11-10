module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.ShiftCancel

/-!
# Shifts commute with tensoring by a differential graded bimodule

For a right differential graded `A`-module `M` and a differential graded `(A, B)`-bimodule `N`,
shifting the relative tensor product `M ⊗_A N` agrees with tensoring the shift: there is a
canonical isomorphism `(M ⊗_A N)[k] ≅ M[k] ⊗_A N` of right differential graded `B`-modules, and
on pure tensors it is the identity, with no intervening sign.

## Main results

* `DifferentialGraded.Bimodule.tensorShiftIso`: the isomorphism, specified by its sign-free
  action on pure tensors.

## Implementation notes

*Both directions come from the universal property.* The underlying module of a shift is the
module itself, so the universal balanced bilinear map of `M ⊗_A N` is also one into the shift
once its degrees and its Leibniz sign are corrected; the two comparison morphisms are therefore
obtained by lifting such maps along the universal property of Tag 09LM, and they are mutually
inverse because each composite agrees with the identity on pure tensors, which the uniqueness
half of that property turns into an equality of morphisms.

*The sign bookkeeping is where the content is.* The Leibniz rule of the shift carries the factor
`(-1)^k`, so the balanced bilinear map into `(M ⊗_A N)[k]` has to have its own sign rewritten
from `(-1)^{p + k}` to `(-1)^p`; that is `negOnePow_mul_add_self`. The backward direction instead
lands in a double shift, which `DifferentialGradedModule.shiftShiftNegIso` cancels, and
`DifferentialGradedModule.Hom.unshift` divides out the leftover unit.

## References

* [Stacks Project, Tag 0FQN](https://stacks.math.columbia.edu/tag/0FQN)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace DifferentialGraded.Bimodule

universe u

variable {R : Type u} [CommRing R]
variable {A B : DifferentialGradedAlgebra R}

open DifferentialGradedModule

private lemma negOnePow_mul_add_self (p k : ℤ) :
    (k.negOnePow : ℤ) * (p + k).negOnePow = p.negOnePow := by
  have h : k.negOnePow * (p + k).negOnePow = p.negOnePow := by
    rw [Int.negOnePow_add]
    calc
      k.negOnePow * (p.negOnePow * k.negOnePow) =
          p.negOnePow * (k.negOnePow * k.negOnePow) := by ac_rfl
      _ = p.negOnePow := by rw [Int.units_mul_self, mul_one]
  simpa only [Units.val_mul] using congrArg (fun x : Units ℤ => (x : ℤ)) h

/-- The universal balanced bilinear map of `M ⊗_A N`, read as one out of `M[k]` into the shift
`(M ⊗_A N)[k]`. -/
private noncomputable def tensorShiftBackwardBilinear (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ) :
    BalancedBilinearMap (shift M k) N (shift ((tensorDGFunctor N).functor.obj M) k) :=
  let T := tensorDGFunctor N
  { toLinearMap := (T.pure M).toLinearMap
    map_grading := by
      intro p q x y
      have h := (T.pure M).map_grading (p + k) q ⟨x.val, by simp⟩ y
      change (T.pure M).toLinearMap x.val y ∈ (T.functor.obj M).grading (p + q + k)
      change (T.pure M).toLinearMap x.val y ∈ (T.functor.obj M).grading (p + k + q) at h
      rw [show p + q + k = p + k + q by omega]
      exact h
    map_d := by
      intro p x y
      change (shift (T.functor.obj M) k).d ((T.pure M).toLinearMap x.val y) =
        (T.pure M).toLinearMap ((shift M k).d x.val) y +
          (p.negOnePow : ℤ) • (T.pure M).toLinearMap x.val (N.rightModule.d y)
      have hd := (T.pure M).map_d (p + k) ⟨x.val, by simp⟩ y
      change (T.functor.obj M).d ((T.pure M).toLinearMap x.val y) =
        (T.pure M).toLinearMap (M.d x.val) y +
          ((p + k).negOnePow : ℤ) •
            (T.pure M).toLinearMap x.val (N.rightModule.d y) at hd
      simp only [LinearMap.smul_apply, shift_d]
      rw [hd]
      simp only [map_zsmul, Units.smul_def]
      rw [smul_add, smul_smul, negOnePow_mul_add_self]
      rfl
    balance := by
      intro p q n x y a
      exact (T.pure M).balance (p + k) q n ⟨x.val, by simp⟩ y a
    map_right := by
      intro x y b
      exact (T.pure M).map_right (x : M.M) y b }

/-- The comparison morphism `M[k] ⊗_A N ⟶ (M ⊗_A N)[k]`. -/
private noncomputable def tensorShiftBackward (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ) :
    DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj (shift M k))
      (shift ((tensorDGFunctor N).functor.obj M) k) :=
  ((tensorDGFunctor N).universal (shift M k) (shift ((tensorDGFunctor N).functor.obj M) k)
    (tensorShiftBackwardBilinear N M k)).choose

private theorem tensorShiftBackward_pure (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ) (x : (shift M k).M) (y : N.rightModule.M) :
    (tensorShiftBackward N M k).toFun
      (((tensorDGFunctor N).pure (shift M k)).toLinearMap x y) =
      ((tensorDGFunctor N).pure M).toLinearMap x y :=
  ((tensorDGFunctor N).universal (shift M k) (shift ((tensorDGFunctor N).functor.obj M) k)
    (tensorShiftBackwardBilinear N M k)).choose_spec.1 x y

/-- The universal balanced bilinear map of `M[k] ⊗_A N`, read as one out of `M` into the shift of
that tensor product by `-k`. -/
private noncomputable def tensorShiftForwardBilinear (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ) :
    BalancedBilinearMap M N (shift ((tensorDGFunctor N).functor.obj (shift M k)) (-k)) :=
  let T := tensorDGFunctor N
  { toLinearMap := (T.pure (shift M k)).toLinearMap
    map_grading := by
      intro p q x y
      have hx : x.val ∈ (shift M k).grading (p - k) := by
        simp [shift_grading]
      have hy := (T.pure (shift M k)).map_grading (p - k) q ⟨x.val, hx⟩ y
      change (T.pure (shift M k)).toLinearMap x.val y ∈
        (T.functor.obj (shift M k)).grading (p - k + q) at hy
      change (T.pure (shift M k)).toLinearMap x.val y ∈
        (T.functor.obj (shift M k)).grading (p + q - k)
      rw [show p + q - k = p - k + q by omega]
      exact hy
    map_d := by
      intro p x y
      change (shift (T.functor.obj (shift M k)) (-k)).d
          ((T.pure (shift M k)).toLinearMap x.val y) =
        (T.pure (shift M k)).toLinearMap (M.d x.val) y +
          (p.negOnePow : ℤ) • (T.pure (shift M k)).toLinearMap x.val (N.rightModule.d y)
      have hd := (T.pure (shift M k)).map_d (p - k)
        ⟨x.val, by simp [shift_grading]⟩ y
      change (T.functor.obj (shift M k)).d ((T.pure (shift M k)).toLinearMap x.val y) =
        (T.pure (shift M k)).toLinearMap ((shift M k).d x.val) y +
          ((p - k).negOnePow : ℤ) •
            (T.pure (shift M k)).toLinearMap x.val (N.rightModule.d y) at hd
      simp only [LinearMap.smul_apply, shift_d]
      rw [hd]
      simp only [shift_d, LinearMap.smul_apply, map_zsmul, Units.smul_def]
      simp only [smul_add, smul_smul]
      congr 1
      · norm_cast
        rw [← Int.negOnePow_add, show -k + k = 0 by omega]
        simp
      · norm_cast
        rw [← Int.negOnePow_add, show -k + (p - k) = p + 2 * (-k) by omega,
          Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
    balance := by
      intro p q n x y a
      have hx : x.val ∈ (shift M k).grading (p - k) := by
        simp [shift_grading]
      have hy := (T.pure (shift M k)).balance (p - k) q n ⟨x.val, hx⟩ y a
      convert hy using 1
    map_right := by
      intro x y b
      exact (T.pure (shift M k)).map_right (x : M.M) y b }

private noncomputable def tensorShiftForwardAux (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ) :
    DifferentialGradedModule.Hom ((tensorDGFunctor N).functor.obj M)
      (shift ((tensorDGFunctor N).functor.obj (shift M k)) (-k)) :=
  ((tensorDGFunctor N).universal M
    (shift ((tensorDGFunctor N).functor.obj (shift M k)) (-k))
    (tensorShiftForwardBilinear N M k)).choose

private theorem tensorShiftForwardAux_pure (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ) (x : M.M) (y : N.rightModule.M) :
    (tensorShiftForwardAux N M k).toFun
      (((tensorDGFunctor N).pure M).toLinearMap x y) =
      ((tensorDGFunctor N).pure (shift M k)).toLinearMap x y :=
  ((tensorDGFunctor N).universal M
    (shift ((tensorDGFunctor N).functor.obj (shift M k)) (-k))
    (tensorShiftForwardBilinear N M k)).choose_spec.1 x y

/-- The comparison morphism `(M ⊗_A N)[k] ⟶ M[k] ⊗_A N`. -/
private noncomputable def tensorShiftForward (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ) :
    DifferentialGradedModule.Hom (shift ((tensorDGFunctor N).functor.obj M) k)
      ((tensorDGFunctor N).functor.obj (shift M k)) :=
  DifferentialGradedModule.Hom.comp
    (shiftShiftNegIso ((tensorDGFunctor N).functor.obj (shift M k)) k).hom
    (shiftMap (tensorShiftForwardAux N M k) k)

private theorem tensorShiftForward_pure (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ) (x : M.M) (y : N.rightModule.M) :
    (tensorShiftForward N M k).toFun
      (((tensorDGFunctor N).pure M).toLinearMap x y) =
      ((tensorDGFunctor N).pure (shift M k)).toLinearMap x y := by
  change (tensorShiftForwardAux N M k).toFun
    (((tensorDGFunctor N).pure M).toLinearMap x y) = _
  exact tensorShiftForwardAux_pure N M k x y

private theorem tensorShiftForwardBackward_id (N : Bimodule A B)
    (M : DifferentialGradedModule A) (k : ℤ) :
    DifferentialGradedModule.Hom.comp (tensorShiftBackward N M k)
        (tensorShiftForward N M k) =
      DifferentialGradedModule.Hom.id (shift ((tensorDGFunctor N).functor.obj M) k) := by
  let T := tensorDGFunctor N
  let X := T.functor.obj M
  let c := DifferentialGradedModule.Hom.comp (tensorShiftBackward N M k)
    (tensorShiftForward N M k)
  let c' := DifferentialGradedModule.Hom.unshift k c
  obtain ⟨u, hu, huniq⟩ := T.universal M X (T.pure M)
  have hc : ∀ (x : M.M) (y : N.rightModule.M),
      c'.toFun ((T.pure M).toLinearMap x y) = (T.pure M).toLinearMap x y := by
    intro x y
    change (tensorShiftBackward N M k).toFun
      ((tensorShiftForward N M k).toFun ((T.pure M).toLinearMap x y)) = _
    rw [tensorShiftForward_pure, tensorShiftBackward_pure]
  have hid : ∀ (x : M.M) (y : N.rightModule.M),
      (DifferentialGradedModule.Hom.id X).toFun ((T.pure M).toLinearMap x y) =
        (T.pure M).toLinearMap x y := fun _ _ => rfl
  have hfun : c'.toFun = (DifferentialGradedModule.Hom.id X).toFun :=
    congrArg DifferentialGradedModule.Hom.toFun ((huniq c' hc).trans (huniq _ hid).symm)
  exact DifferentialGradedModule.Hom.ext hfun

/-- **Stacks 0FQN.** The canonical, sign-free identification `(M ⊗_A N)[k] ≅ M[k] ⊗_A N`: it
sends each pure tensor to the same pure tensor. -/
@[stacks 0FQN, no_expose]
noncomputable def tensorShiftIso (N : Bimodule A B) (M : DifferentialGradedModule A) (k : ℤ) :
    { e : shift ((tensorDGFunctor N).functor.obj M) k ≅
        (tensorDGFunctor N).functor.obj (shift M k) //
      ∀ (x : M.M) (y : N.rightModule.M),
        e.hom.toFun (((tensorDGFunctor N).pure M).toLinearMap x y) =
          ((tensorDGFunctor N).pure (shift M k)).toLinearMap x y } := by
  let T := tensorDGFunctor N
  let f := tensorShiftForward N M k
  let g := tensorShiftBackward N M k
  refine ⟨{ hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }, ?_⟩
  · exact tensorShiftForwardBackward_id N M k
  · let X := T.functor.obj (shift M k)
    let c := DifferentialGradedModule.Hom.comp f g
    obtain ⟨u, hu, huniq⟩ := T.universal (shift M k) X (T.pure (shift M k))
    have hc : ∀ (x : (shift M k).M) (y : N.rightModule.M),
        c.toFun ((T.pure (shift M k)).toLinearMap x y) =
          (T.pure (shift M k)).toLinearMap x y := by
      intro x y
      change f.toFun (g.toFun ((T.pure (shift M k)).toLinearMap x y)) = _
      rw [tensorShiftBackward_pure]
      exact tensorShiftForward_pure N M k x y
    have hid : ∀ (x : (shift M k).M) (y : N.rightModule.M),
        (DifferentialGradedModule.Hom.id X).toFun
            ((T.pure (shift M k)).toLinearMap x y) =
          (T.pure (shift M k)).toLinearMap x y := fun _ _ => rfl
    exact (huniq c hc).trans (huniq _ hid).symm
  · intro x y
    change f.toFun ((T.pure M).toLinearMap x y) = _
    exact tensorShiftForward_pure N M k x y

end DifferentialGraded.Bimodule
