module

public import StacksFrontier.Algebra.Module.Projective.Determinant.BaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Base change of the degreewise annihilator, inside the exterior power

Let `R` be a commutative ring, `A` a commutative `R`-algebra and `M` an `R`-module. The
degree-`n` part of the annihilator of the degree-one elements of `⋀_R M` commutes with base
change along the degreewise comparison of exterior powers
`ExteriorAlgebra.exteriorPowerBaseChange`: one inclusion holds for every `M`, and for `M` finite
projective the two sides agree. Both sides are compared inside the exterior **algebra** of the
base change, along `ProjectiveDeterminant.exteriorAlgebraBaseChange`, for which the
corresponding statement is `ProjectiveDeterminant.annihilatorPart_baseChange_map`.

## Main results

* `ProjectiveDeterminant.exteriorAlgebraBaseChange_exteriorPowerBaseChangeMap`: the degreewise
  comparison of exterior powers, read inside the exterior algebra of the base change and then
  carried along the comparison of exterior algebras, is `x ↦ 1 ⊗ x`.
* `ProjectiveDeterminant.mul_exteriorPowerBaseChange_eq_zero`: **the image of `A ⊗_R partₙ` is
  annihilated by every degree-one element of `⋀_A(A ⊗_R M)`**, with no finiteness or
  projectivity hypothesis.
* `ProjectiveDeterminant.map_baseChange_annihilatorPart_le`: the submodule form of that, with
  elementwise readings `mul_coe_exteriorPowerBaseChange_eq_zero` and
  `mul_coe_intPieceBaseChange_eq_zero`, the latter in the `ℤ`-graded spelling
  `ExteriorAlgebra.intPiece`, whose pure-tensor case is
  `mul_coe_intPieceBaseChange_tmul_eq_zero`.
* `ProjectiveDeterminant.annihilatorPart_exteriorPowerBaseChange_map`: **the degreewise
  comparison of exterior powers carries the base change of the degree-`n` part of the
  annihilator onto the degree-`n` part of the annihilator of the base change.** Both sides are
  written at the spelling `Stacks.ExteriorAnnihilator.part` is defined at — the comap of the
  annihilator of the degree-one elements along the inclusion of the degree-`n` exterior power.

## References

* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
* [Stacks Project, Tag 0C6F](https://stacks.math.columbia.edu/tag/0C6F)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ProjectiveDeterminant

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (M : Type*) [AddCommGroup M] [Module R M]

/-! ### The two base-change comparisons agree -/

/-- **The degreewise comparison of exterior powers agrees with the comparison of exterior
algebras.** Read inside `ExteriorAlgebra A (A ⊗_R M)` and then carried along
`ProjectiveDeterminant.exteriorAlgebraBaseChange`, the map
`ExteriorAlgebra.exteriorPowerBaseChangeMap` is `x ↦ 1 ⊗ x`. -/
theorem exteriorAlgebraBaseChange_exteriorPowerBaseChangeMap (n : ℕ) (x : ↥(⋀[R]^n M)) :
    exteriorAlgebraBaseChange R A M
        ((ExteriorAlgebra.exteriorPowerBaseChangeMap R A M n x :
          ExteriorAlgebra A (A ⊗[R] M))) =
      1 ⊗ₜ[R] (x : ExteriorAlgebra R M) := by
  let f : ↥(⋀[R]^n M) →ₗ[R] A ⊗[R] ExteriorAlgebra R M :=
    { toFun := fun y => exteriorAlgebraBaseChange R A M
        ((ExteriorAlgebra.exteriorPowerBaseChangeMap R A M n y :
          ExteriorAlgebra A (A ⊗[R] M)))
      map_add' := fun y z => by simp only [map_add, Submodule.coe_add]
      map_smul' := fun r y => by
        simp only [map_smul, RingHom.id_apply]
        rw [← algebraMap_smul A r (ExteriorAlgebra.exteriorPowerBaseChangeMap R A M n y),
          SetLike.val_smul, map_smul, algebraMap_smul] }
  let g : ↥(⋀[R]^n M) →ₗ[R] A ⊗[R] ExteriorAlgebra R M :=
    { toFun := fun y => 1 ⊗ₜ[R] (y : ExteriorAlgebra R M)
      map_add' := fun y z => by simp only [Submodule.coe_add, TensorProduct.tmul_add]
      map_smul' := fun r y => by
        simp only [SetLike.val_smul, RingHom.id_apply, TensorProduct.tmul_smul] }
  have hfg : f = g := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
    change exteriorAlgebraBaseChange R A M
        ((ExteriorAlgebra.exteriorPowerBaseChangeMap R A M n (exteriorPower.ιMulti R n v) :
          ExteriorAlgebra A (A ⊗[R] M))) =
      1 ⊗ₜ[R] ((exteriorPower.ιMulti R n v : ↥(⋀[R]^n M)) : ExteriorAlgebra R M)
    rw [ExteriorAlgebra.exteriorPowerBaseChangeMap_ιMulti]
    exact exteriorAlgebraBaseChange_ιMulti R A M n v
  exact DFunLike.congr_fun hfg x

/-- The composite `A ⊗_R ⋀ⁿ_R M → ⋀ⁿ_A(A ⊗_R M) ⊆ ⋀_A(A ⊗_R M) ≅ A ⊗_R ⋀_R M`, which
`ProjectiveDeterminant.exteriorPowerBaseChangeIntoAlgebra_tmul` identifies with
`a ⊗ y ↦ a ⊗ y`. -/
private def exteriorPowerBaseChangeIntoAlgebra (n : ℕ) :
    A ⊗[R] ↥(⋀[R]^n M) →ₗ[A] A ⊗[R] ExteriorAlgebra R M :=
  (exteriorAlgebraBaseChange R A M).toLinearMap ∘ₗ
    ((⋀[A]^n (A ⊗[R] M)).subtype ∘ₗ
      (ExteriorAlgebra.exteriorPowerBaseChange R A M n : _ →ₗ[A] _))

private theorem exteriorPowerBaseChangeIntoAlgebra_tmul (n : ℕ) (a : A) (y : ↥(⋀[R]^n M)) :
    exteriorPowerBaseChangeIntoAlgebra R A M n (a ⊗ₜ[R] y) =
      a ⊗ₜ[R] (y : ExteriorAlgebra R M) := by
  change exteriorAlgebraBaseChange R A M
      ((ExteriorAlgebra.exteriorPowerBaseChange R A M n (a ⊗ₜ[R] y) :
        ExteriorAlgebra A (A ⊗[R] M))) = _
  rw [ExteriorAlgebra.exteriorPowerBaseChange_tmul, Submodule.coe_smul, map_smul,
    exteriorAlgebraBaseChange_exteriorPowerBaseChangeMap, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

/-! ### The annihilator of the base change -/

/-- Membership in the comap of the annihilator of the degree-one elements along `S.subtype`. -/
private theorem mem_comap_iInf_ker_mulLeft_iff {K N : Type*} [CommRing K] [AddCommGroup N]
    [Module K N] (S : Submodule K (ExteriorAlgebra K N)) (x : S) :
    x ∈ (⨅ m : N, LinearMap.ker (LinearMap.mulLeft K (ExteriorAlgebra.ι K m))).comap S.subtype ↔
      ∀ m : N, ExteriorAlgebra.ι K m * (x : ExteriorAlgebra K N) = 0 := by
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.mulLeft_apply]

/-- **The image of the base change of the degreewise annihilator is annihilated.** If `y` is a
degree-`n` element of `⋀_R M` killed by every degree-one element over `R`, then its image under
the degreewise base-change comparison is killed by every degree-one element of
`⋀_A(A ⊗_R M)`. -/
theorem mul_exteriorPowerBaseChange_eq_zero (n : ℕ) (x : ↥(⋀[R]^n M))
    (hx : ∀ m : M, ExteriorAlgebra.ι R m * (x : ExteriorAlgebra R M) = 0)
    (a : A) (w : A ⊗[R] M) :
    ExteriorAlgebra.ι A w *
        (ExteriorAlgebra.exteriorPowerBaseChange R A M n (a ⊗ₜ[R] x) :
          ExteriorAlgebra A (A ⊗[R] M)) = 0 := by
  rw [ExteriorAlgebra.exteriorPowerBaseChange_tmul, Submodule.coe_smul, mul_smul_comm]
  refine Eq.trans (congrArg (fun z => a • z) ?_) (smul_zero a)
  refine (EquivLike.injective (exteriorAlgebraBaseChange R A M)) ?_
  rw [map_mul, map_zero, exteriorAlgebraBaseChange_exteriorPowerBaseChangeMap]
  induction w using TensorProduct.inductionOn with
  | tmul b m =>
      rw [show (b ⊗ₜ[R] m : A ⊗[R] M) = b • ((1 : A) ⊗ₜ[R] m) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, map_smul, exteriorAlgebraBaseChange_ι, smul_mul_assoc,
        Algebra.TensorProduct.tmul_mul_tmul, hx m, TensorProduct.tmul_zero, smul_zero]
  | add u v hu hv => rw [map_add, map_add, add_mul, hu, hv, add_zero]

/-- **The image of the base change of the degreewise annihilator lies in the annihilator of the
base change.** This is the inclusion of
`ProjectiveDeterminant.annihilatorPart_exteriorPowerBaseChange_map` that needs no hypothesis on
`M`. -/
theorem map_baseChange_annihilatorPart_le (n : ℕ) :
    Submodule.map (ExteriorAlgebra.exteriorPowerBaseChange R A M n).toLinearMap
        (Submodule.baseChange A
          ((⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))).comap
            (⋀[R]^n M).subtype)) ≤
      (⨅ w : A ⊗[R] M, LinearMap.ker (LinearMap.mulLeft A (ExteriorAlgebra.ι A w))).comap
        (⋀[A]^n (A ⊗[R] M)).subtype := by
  rw [Submodule.map_le_iff_le_comap, Submodule.baseChange_eq_span, Submodule.span_le]
  rintro t ⟨y, hy, rfl⟩
  have hy := (mem_comap_iInf_ker_mulLeft_iff _ y).1 hy
  exact (mem_comap_iInf_ker_mulLeft_iff _ _).2 fun w =>
    mul_exteriorPowerBaseChange_eq_zero R A M n y hy 1 w

/-- `ProjectiveDeterminant.mul_exteriorPowerBaseChange_eq_zero` in the `ℤ`-graded spelling
`ExteriorAlgebra.intPiece`, for a single pure tensor. -/
theorem mul_coe_intPieceBaseChange_tmul_eq_zero (n : ℕ) (a : A)
    (x : ↥(ExteriorAlgebra.intPiece R M (n : ℤ)))
    (hx : ∀ m : M, ExteriorAlgebra.ι R m * (x : ExteriorAlgebra R M) = 0) (w : A ⊗[R] M) :
    ExteriorAlgebra.ι A w *
        (ExteriorAlgebra.intPieceBaseChange R A M n (a ⊗ₜ[R] x) :
          ExteriorAlgebra A (A ⊗[R] M)) = 0 :=
  mul_exteriorPowerBaseChange_eq_zero R A M n x hx a w

/-- `ProjectiveDeterminant.map_baseChange_annihilatorPart_le` read on an element: an element of
the base change of the degree-`n` part of the annihilator is carried by the degreewise
comparison to an element killed by every degree-one element of `⋀_A(A ⊗_R M)`. -/
theorem mul_coe_exteriorPowerBaseChange_eq_zero (n : ℕ) (t : A ⊗[R] ↥(⋀[R]^n M))
    (ht : t ∈ Submodule.baseChange A
      ((⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))).comap
        (⋀[R]^n M).subtype))
    (w : A ⊗[R] M) :
    ExteriorAlgebra.ι A w *
        (ExteriorAlgebra.exteriorPowerBaseChange R A M n t : ExteriorAlgebra A (A ⊗[R] M)) = 0 := by
  have h := map_baseChange_annihilatorPart_le R A M n (Submodule.mem_map_of_mem ht)
  exact (mem_comap_iInf_ker_mulLeft_iff _ _).1 h w

/-- `ProjectiveDeterminant.mul_coe_exteriorPowerBaseChange_eq_zero` in the `ℤ`-graded spelling
`ExteriorAlgebra.intPiece`. -/
theorem mul_coe_intPieceBaseChange_eq_zero (n : ℕ)
    (t : A ⊗[R] ↥(ExteriorAlgebra.intPiece R M (n : ℤ)))
    (ht : t ∈ Submodule.baseChange A
      ((⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))).comap
        (ExteriorAlgebra.intPiece R M (n : ℤ)).subtype))
    (w : A ⊗[R] M) :
    ExteriorAlgebra.ι A w *
        (ExteriorAlgebra.intPieceBaseChange R A M n t : ExteriorAlgebra A (A ⊗[R] M)) = 0 :=
  mul_coe_exteriorPowerBaseChange_eq_zero R A M n t ht w

variable [Module.Finite R M] [Module.Projective R M]

/-- **The degreewise annihilator commutes with base change, inside the exterior power.** The
degreewise base-change comparison `A ⊗_R ⋀ⁿ_R M ≃ ⋀ⁿ_A(A ⊗_R M)` carries the base change of the
degree-`n` part of the annihilator of the degree-one elements of `⋀_R M` onto the degree-`n`
part of the annihilator of the degree-one elements of `⋀_A(A ⊗_R M)`.

The submodules on the two sides are the ones `Stacks.ExteriorAnnihilator.part` is defined to be,
so this applies to those submodules with no transport. -/
theorem annihilatorPart_exteriorPowerBaseChange_map (n : ℕ) :
    Submodule.map (ExteriorAlgebra.exteriorPowerBaseChange R A M n).toLinearMap
        (Submodule.baseChange A
          ((⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))).comap
            (⋀[R]^n M).subtype)) =
      (⨅ w : A ⊗[R] M, LinearMap.ker (LinearMap.mulLeft A (ExteriorAlgebra.ι A w))).comap
        (⋀[A]^n (A ⊗[R] M)).subtype := by
  refine le_antisymm (map_baseChange_annihilatorPart_le R A M n) ?_
  · intro z hz
    replace hz := (mem_comap_iInf_ker_mulLeft_iff _ z).1 hz
    have hmemA : ((⋀[A]^n (A ⊗[R] M)).subtype z) ∈ component (R := A) (M := A ⊗[R] M) n := by
      rw [← map_annihilatorPart_eq_component (R := A) (M := A ⊗[R] M) n]
      exact Submodule.mem_map_of_mem ((mem_comap_iInf_ker_mulLeft_iff _ z).2 hz)
    have hEz : exteriorAlgebraBaseChange R A M ((z : ExteriorAlgebra A (A ⊗[R] M))) ∈
        Submodule.baseChange A (component (R := R) (M := M) n) := by
      rw [← component_baseChange_map R A M n]
      exact Submodule.mem_map_of_mem hmemA
    have hle : Submodule.baseChange A (component (R := R) (M := M) n) ≤
        Submodule.map (exteriorPowerBaseChangeIntoAlgebra R A M n) (Submodule.baseChange A
          ((⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))).comap
            (⋀[R]^n M).subtype)) := by
      rw [← map_annihilatorPart_eq_component (R := R) (M := M) n,
        Submodule.baseChange_eq_span, Submodule.span_le]
      rintro t ⟨c, hc, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hc
      exact ⟨(1 : A) ⊗ₜ[R] y, Submodule.tmul_mem_baseChange_of_mem 1 hy,
        (exteriorPowerBaseChangeIntoAlgebra_tmul R A M n 1 y).trans rfl⟩
    obtain ⟨w, hw, hwe⟩ := hle hEz
    exact ⟨w, hw,
      Subtype.ext ((EquivLike.injective (exteriorAlgebraBaseChange R A M)) hwe)⟩

end ProjectiveDeterminant

end
