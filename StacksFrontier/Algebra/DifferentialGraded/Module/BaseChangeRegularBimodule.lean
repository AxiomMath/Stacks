module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorBimoduleVariable

/-! # The regular module of `Bᵒᵖ ⊗_R C` as a differential graded bimodule

Let `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`. A
differential graded `(B, C)`-bimodule is the same thing as a right differential graded module
over `Bᵒᵖ ⊗_R C` (Tag 0FQJ), and `DifferentialGraded.Bimodule.baseChangeRegularIso` identifies
the right `C`-module underlying the regular module of `Bᵒᵖ ⊗_R C` with the base-change module
`(B ⊗_R C)_C` of Tag 0BZ4. This file upgrades that identification to an isomorphism of
differential graded `(B, C)`-bimodules: the regular module of `Bᵒᵖ ⊗_R C`, read as a bimodule,
is `{}_B(B ⊗_R C)_C`.

## Main definitions

* `DifferentialGraded.Bimodule.oppGradingElem`: a homogeneous element of `B`, read as a
  homogeneous element of the graded opposite of `B`.
* `DifferentialGraded.Bimodule.baseChangeRegularBimoduleIso`: the regular module of `Bᵒᵖ ⊗_R C`,
  read as a differential graded `(B, C)`-bimodule, is `{}_B(B ⊗_R C)_C`.

## Main results

* `DifferentialGraded.Bimodule.oppGradingElem_equiv`: the canonical identification carries
  `DifferentialGraded.Bimodule.oppGradingElem` back to the element it came from.
* `DifferentialGraded.Bimodule.oppTensorEquiv_tmul_mul_oppIncludeLeft` and
  `DifferentialGraded.Bimodule.oppTensorEquiv_mul_oppIncludeLeft`: the comparison of carriers
  turns right multiplication by `bᵒᵖ ⊗ 1` into left multiplication by `b ⊗ 1`, up to the Koszul
  sign, first on a pure tensor and then on an arbitrary homogeneous element.
* `DifferentialGraded.Bimodule.baseChangeBimodule_leftActionTotal`: the totalized left
  `B`-action on `{}_B(B ⊗_R C)_C` is left multiplication by `b ⊗ 1`.
* `DifferentialGraded.Bimodule.oppTensorEquiv_leftActionTotal_homogeneous` and
  `DifferentialGraded.Bimodule.oppTensorEquiv_leftActionTotal`: the comparison of carriers
  intertwines the two totalized left `B`-actions.

## Implementation notes

*Why the signs cancel.* On the pure tensor `βᵒᵖ ⊗ c` with `β` of degree `p` and `c` of degree
`r`, right multiplication by `bᵒᵖ ⊗ 1` with `b` of degree `n` produces the Koszul sign `(-1)^{rn}`
from the graded tensor product and a further `(-1)^{pn}` from the graded opposite, for a total
`(-1)^{(p+r)n}`. The left action of `b` on the bimodule attached to a right module over
`Bᵒᵖ ⊗_R C` carries the prefactor `(-1)^{n(p+r)}`, which cancels it; and on the other side
`(1 : C.A)` has degree zero, so left multiplication by `b ⊗ 1` in `B ⊗_R C` contributes no sign
at all.

*Why only the left action has content.* The comparison of underlying right `C`-modules is
already `DifferentialGraded.Bimodule.baseChangeRegularIso`, so by
`DifferentialGraded.Bimodule.isoOfRightIso` the only thing left to check is compatibility with
the left `B`-actions.

*Why so many type ascriptions.* The carrier of the differential graded algebra `X ⊗_R Y` and the
graded tensor product `X.grading ᵍ⊗[R] Y.grading` of its gradings are the same type but not the
same expression, and the multiplication is only found by instance search for the second spelling;
`show ... from ...` moves between them.

## References

* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ), bimodules as modules over
  the graded tensor product.
* [Stacks Project, Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the base-change module.
* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W), the graded tensor product
  of differential graded algebras.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (B C : DifferentialGradedAlgebra.{u, u} R)

/-! ### Homogeneous elements of the graded opposite -/

/-- A homogeneous element of `B` of degree `n`, read as a homogeneous element of degree `n` of the
graded opposite of `B` through the canonical identification of carriers. -/
def oppGradingElem {n : ℤ} (b : B.grading n) : (oppAlgebra B).grading n :=
  ⟨(DifferentialGradedAlgebra.opposite R B).equiv.symm (b : B.A),
    ((DifferentialGradedAlgebra.opposite R B).mem_grading_iff n _).mpr (by
      rw [LinearEquiv.apply_symm_apply]
      exact b.property)⟩

/-- The canonical identification of carriers carries `DifferentialGraded.Bimodule.oppGradingElem`
back to the element it came from. -/
theorem oppGradingElem_equiv {n : ℤ} (b : B.grading n) :
    (DifferentialGradedAlgebra.opposite R B).equiv (oppGradingElem B b : (oppAlgebra B).A) =
      (b : B.A) :=
  (DifferentialGradedAlgebra.opposite R B).equiv.apply_symm_apply (b : B.A)

/-! ### The comparison of carriers and the left action -/

/-- **On a pure tensor, the comparison of the carriers of `Bᵒᵖ ⊗_R C` and `B ⊗_R C` turns right
multiplication by `bᵒᵖ ⊗ 1` into left multiplication by `b ⊗ 1`, up to the Koszul sign.** -/
theorem oppTensorEquiv_tmul_mul_oppIncludeLeft {n p r : ℤ} (b : B.grading n)
    (β : (oppAlgebra B).grading p) (c : C.grading r) :
    oppTensorEquiv B C
        (((β : (oppAlgebra B).A) ᵍ⊗ₜ[R] (c : C.A) : (oppAlgebra B).grading ᵍ⊗[R] C.grading) *
          ((oppGradingElem B b : (oppAlgebra B).A) ᵍ⊗ₜ[R] (1 : C.A))) =
      (n * (p + r)).negOnePow •
        (((b : B.A) ᵍ⊗ₜ[R] (1 : C.A) : B.grading ᵍ⊗[R] C.grading) *
          (show B.grading ᵍ⊗[R] C.grading from
            oppTensorEquiv B C
              ((β : (oppAlgebra B).A) ᵍ⊗ₜ[R] (c : C.A) :
                (oppAlgebra B).grading ᵍ⊗[R] C.grading))) := by
  have harith : r * n + p * n = n * (p + r) := by ring
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul (oppAlgebra B).grading C.grading
      (β : (oppAlgebra B).A) c (oppGradingElem B b) (1 : C.A),
    ← Int.negOnePow_def, mul_one, Units.smul_def, map_zsmul, oppTensorEquiv_tmul,
    oppTensorEquiv_tmul,
    (DifferentialGradedAlgebra.opposite R B).map_mul_of_mem p n (β : (oppAlgebra B).A)
      (oppGradingElem B b : (oppAlgebra B).A) β.property (oppGradingElem B b).property,
    oppGradingElem_equiv, Units.smul_def, DifferentialGraded.zsmul_tmul_left,
    tmul_one_mul_tmul B C (b : B.A) _ (c : C.A), smul_smul, Units.smul_def, ← Units.val_mul,
    ← Int.negOnePow_add, harith]

/-- **On a homogeneous element, the comparison of the carriers of `Bᵒᵖ ⊗_R C` and `B ⊗_R C` turns
right multiplication by `bᵒᵖ ⊗ 1` into left multiplication by `b ⊗ 1`, up to the Koszul sign.** -/
theorem oppTensorEquiv_mul_oppIncludeLeft {n q : ℤ} (b : B.grading n) (x : (tensorAlgebra B C).A)
    (hx : x ∈ (tensorAlgebra B C).grading q) :
    oppTensorEquiv B C
        ((show (oppAlgebra B).grading ᵍ⊗[R] C.grading from x) *
          ((oppGradingElem B b : (oppAlgebra B).A) ᵍ⊗ₜ[R] (1 : C.A))) =
      (n * q).negOnePow •
        (((b : B.A) ᵍ⊗ₜ[R] (1 : C.A) : B.grading ᵍ⊗[R] C.grading) *
          (show B.grading ᵍ⊗[R] C.grading from oppTensorEquiv B C x)) := by
  refine tensorProductGrading_induction (oppAlgebra B) C q
    (motive := fun z => oppTensorEquiv B C
        (z * ((oppGradingElem B b : (oppAlgebra B).A) ᵍ⊗ₜ[R] (1 : C.A))) =
      (n * q).negOnePow •
        (((b : B.A) ᵍ⊗ₜ[R] (1 : C.A) : B.grading ᵍ⊗[R] C.grading) *
          (show B.grading ᵍ⊗[R] C.grading from oppTensorEquiv B C z)))
    ?_ ?_ ?_ ?_ x hx
  · simp
  · intro z w hz hw
    rw [add_mul, map_add, hz, hw, map_add, mul_add, smul_add]
  · intro s z hz
    rw [smul_mul_assoc, map_smul, hz, map_smul, mul_smul_comm]
    exact smul_comm s (n * q).negOnePow _
  · intro p r a c ha hc hpr
    rw [← hpr]
    exact oppTensorEquiv_tmul_mul_oppIncludeLeft B C b ⟨a, ha⟩ ⟨c, hc⟩

/-- **The totalized left `B`-action on `{}_B(B ⊗_R C)_C` is left multiplication by `b ⊗ 1`.**
This is `DifferentialGraded.baseChangeBimodule_leftAction`, read through
`DifferentialGraded.Bimodule.leftAction_val`. -/
theorem baseChangeBimodule_leftActionTotal {n q : ℤ} (b : B.grading n)
    (y : (baseChangeBimodule B C).rightModule.grading q) :
    leftActionTotal B C (baseChangeBimodule B C).rightModule
        (baseChangeBimodule B C).leftAction.1 (b : B.A)
        (y : (baseChangeBimodule B C).rightModule.M) =
      ((b : B.A) ᵍ⊗ₜ[R] (1 : C.A) : B.grading ᵍ⊗[R] C.grading) *
        (show B.grading ᵍ⊗[R] C.grading from (y : (baseChangeBimodule B C).rightModule.M)) :=
  (leftAction_val B C (baseChangeBimodule B C) n q b y).symm.trans
    (baseChangeBimodule_leftAction B C n q b y)

/-- **On homogeneous elements, the comparison of carriers intertwines the two totalized left
`B`-actions**: the one on the bimodule attached to the regular module of `Bᵒᵖ ⊗_R C`, and the one
on `{}_B(B ⊗_R C)_C`. -/
theorem oppTensorEquiv_leftActionTotal_homogeneous {n q : ℤ} (b : B.grading n)
    (y : (tensorAlgebra B C).A) (hy : y ∈ (tensorAlgebra B C).grading q) :
    oppTensorEquiv B C
        (leftActionTotal B C
          (ofTensorModule B C (regularModule (tensorAlgebra B C))).rightModule
          (ofTensorModule B C (regularModule (tensorAlgebra B C))).leftAction.1 (b : B.A) y) =
      leftActionTotal B C (baseChangeBimodule B C).rightModule
        (baseChangeBimodule B C).leftAction.1 (b : B.A) (oppTensorEquiv B C y) := by
  have hleft : leftActionTotal B C
        (ofTensorModule B C (regularModule (tensorAlgebra B C))).rightModule
        (ofTensorModule B C (regularModule (tensorAlgebra B C))).leftAction.1 (b : B.A) y =
      (n * q).negOnePow •
        ((show (oppAlgebra B).grading ᵍ⊗[R] C.grading from y) *
          ((oppGradingElem B b : (oppAlgebra B).A) ᵍ⊗ₜ[R] (1 : C.A))) :=
    ofTensorModule_leftActionTotal_apply B C (regularModule (tensorAlgebra B C)) b ⟨y, hy⟩
  have hright : leftActionTotal B C (baseChangeBimodule B C).rightModule
        (baseChangeBimodule B C).leftAction.1 (b : B.A) (oppTensorEquiv B C y) =
      ((b : B.A) ᵍ⊗ₜ[R] (1 : C.A) : B.grading ᵍ⊗[R] C.grading) *
        (show B.grading ᵍ⊗[R] C.grading from oppTensorEquiv B C y) :=
    baseChangeBimodule_leftActionTotal B C b
      ⟨oppTensorEquiv B C y, oppTensorEquiv_mem_grading B C q y hy⟩
  rw [hleft, hright, Units.smul_def, map_zsmul,
    oppTensorEquiv_mul_oppIncludeLeft B C b y hy, Units.smul_def, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul]

/-- **The comparison of carriers intertwines the two totalized left `B`-actions**, for an
arbitrary element of `B` and an arbitrary element of the carrier. -/
theorem oppTensorEquiv_leftActionTotal (b : B.A)
    (y : (ofTensorModule B C (regularModule (tensorAlgebra B C))).rightModule.M) :
    oppTensorEquiv B C
        (leftActionTotal B C
          (ofTensorModule B C (regularModule (tensorAlgebra B C))).rightModule
          (ofTensorModule B C (regularModule (tensorAlgebra B C))).leftAction.1 b y) =
      leftActionTotal B C (baseChangeBimodule B C).rightModule
        (baseChangeBimodule B C).leftAction.1 b (oppTensorEquiv B C y) := by
  induction b using DirectSum.Decomposition.inductionOn B.grading with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply]
    rfl
  | add b b' hb hb' =>
    simp only [map_add, LinearMap.add_apply, hb, hb']
    rfl
  | @homogeneous n b =>
    induction y using DirectSum.Decomposition.inductionOn
        (ofTensorModule B C (regularModule (tensorAlgebra B C))).rightModule.grading with
    | zero =>
      simp only [map_zero]
      exact (map_zero _).symm
    | add y y' hy hy' =>
      simp only [map_add, hy, hy']
      exact (map_add _ _ _).symm
    | @homogeneous q y =>
      exact oppTensorEquiv_leftActionTotal_homogeneous B C b
        (y : (ofTensorModule B C (regularModule (tensorAlgebra B C))).rightModule.M) y.property

/-! ### The base-change bimodule -/

/-- **The regular module of `Bᵒᵖ ⊗_R C`, read as a differential graded `(B, C)`-bimodule, is
`{}_B(B ⊗_R C)_C`.** -/
def baseChangeRegularBimoduleIso :
    ofTensorModule B C (DifferentialGradedModule.regularModule (tensorAlgebra B C)) ≅
      baseChangeBimodule B C :=
  isoOfRightIso B C (baseChangeRegularIso B C) (oppTensorEquiv_leftActionTotal B C)

end DifferentialGraded.Bimodule

end
