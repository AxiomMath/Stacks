module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClopen
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.Associativity

/-!
# The unit constraints of the tensor product of correspondences

For `P ≅ Spec k`, transporting `[Δ_P] ⊗ c` and `c ⊗ [Δ_P]` along the projections gives `c`
(Stacks 0FG7).

## Main results

* `Stacks.WeilCohomology.corrEquivOfIso_tensor_diagonalCorr_left` and
  `Stacks.WeilCohomology.corrEquivOfIso_tensor_diagonalCorr_right`: the unit laws.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

local notation "pf[" sA ", " sB ", " v ", " hv ", " n "]" =>
  properChowPushforward (fieldChowSituation k) sA sB v hv n
    (properPushforwardDescends _ _ _ _ _ _)

/-! ### The unit -/

section Unit

variable {A B P : Scheme.{u}} (sA : A ⟶ (fieldChowSituation k).S)
  (sB : B ⟶ (fieldChowSituation k).S) (sP : P ⟶ (fieldChowSituation k).S)
  [Smooth sA] [IsSeparated sA] [IsProper sA] [Smooth sB] [IsSeparated sB] [IsProper sB]
  [Smooth sP] [IsSeparated sP] [IsProper sP] [IsIso sP]

omit [Smooth sP] [IsSeparated sP] [IsProper sP] in
/-- An isomorphism has relative dimension `0`. -/
theorem relativeDimension_zero_of_isIso : RelativeDimension sP 0 :=
  (locallyQuasiFinite_iff_relativeDimension_zero sP).mp inferInstance

omit [IsProper sP] in
/-- For `P ≅ Spec k`, the diagonal class `[Δ_P]` is its block of dimension `0`. -/
theorem diagonalCorr_eq_diagonalBlock_zero : diagonalCorr k sP = diagonalBlock k sP 0 := by
  rw [diagonalCorr_eq_sum k sP (D := {0}) fun d hd ↦ ?_, Finset.sum_singleton]
  rw [Finset.mem_singleton]
  by_contra h
  rw [dimPart_eq_bot_of_ne_zero sP (relativeDimension_zero_of_isIso k sP) h] at hd
  simp at hd

omit [IsSeparated sA] [IsProper sA] [IsSeparated sB] [IsProper sB] [IsSeparated sP] [IsProper sP] in
/-- The unit constraint on a block, read in the product. -/
theorem tensorBlockHom_unit_left (d e : ℕ) :
    ((tensorBlockHom k sP sA sP sB 0 d 0 e) ≫ (prodHom (partBase sA (0 + d)) (partBase sB (0 + e))
        (partBase (prodBase sP sA) (0 + d)) (partBase (prodBase sP sB) (0 + e))
          (partMap sA (prodBase sP sA) (Limits.pullback.snd sP sA) Limits.pullback.condition.symm
              (0 + d)) (partMap sB (prodBase sP sB)
                  (Limits.pullback.snd sP sB) Limits.pullback.condition.symm (0 + e))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))) ≫ (prodHom sA sB
              (partBase sA (0 + d)) (partBase sB (0 + e)) (dimPart sA (0 + d)).ι (dimPart sB
                  (0 + e)).ι rfl rfl) =
      (prodHom (partBase sA d) (partBase sB e) (prodBase (partBase sP 0) (partBase sA d)) (prodBase
          (partBase sP 0) (partBase sB e))
          (Limits.pullback.snd (partBase sP 0) (partBase sA d)) (Limits.pullback.snd
              (partBase sP 0) (partBase sB e))
          Limits.pullback.condition.symm Limits.pullback.condition.symm) ≫ (prodHom sA sB
              (partBase sA d) (partBase sB e) (dimPart sA d).ι (dimPart sB e).ι rfl rfl) := by
  apply Limits.pullback.hom_ext <;> simp [tensorBlockHom, -Nat.add_zero, -add_zero, -zero_add,
    -Nat.zero_add]

/-- `[Δ_P]` is a left unit on a block, on integral Chow groups. -/
theorem unit_left_parts_heq (r : ℤ) (d e : ℕ)
    (α : chowGroup (fieldChowSituation k) (prodBase (partBase sA d) (partBase sB e))
        ((e : ℤ) - r)) :
    pf[(tensorBase (partBase sP 0) (partBase sA d) (partBase sP 0) (partBase sB e)), (prodBase
        (partBase sA (0 + d)) (partBase sB (0 + e))), (tensorBlockHom k sP sA sP sB 0 d 0 e) ≫
            (prodHom (partBase sA (0 + d)) (partBase sB (0 + e)) (partBase (prodBase sP sA)
                (0 + d)) (partBase (prodBase sP sB) (0 + e))
          (partMap sA (prodBase sP sA) (Limits.pullback.snd sP sA) Limits.pullback.condition.symm
              (0 + d)) (partMap sB (prodBase sP sB)
                  (Limits.pullback.snd sP sB) Limits.pullback.condition.symm (0 + e))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _)),
        by rw [Category.assoc, prodHom_comp_prodBase, tensorBlockHom_comp_prodBase],
            (((0 + e : ℕ) : ℤ) - (0 + r))] (tensorInt k (partBase sP 0) (partBase sA d)
                (partBase sP 0) (partBase sB e) (canonicalDiagonalClassFamily k)
          (relativeDimension_partBase sP 0) (relativeDimension_partBase sA d)
          (relativeDimension_partBase sP 0) (relativeDimension_partBase sB e) 0 r
          (diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0)) α) ≍ α := by
  have := isIso_dimPart_self_ι sP (relativeDimension_zero_of_isIso k sP)
  have h₂ := tensorInt_leftUnit k (partBase sP 0) (partBase sA d) (partBase sB e)
      (relativeDimension_partBase sA d) (relativeDimension_partBase sB e)
          (relativeDimension_partBase sP 0) r α
  exact (properChowPushforward_parts_heq k sA sB _ (Nat.zero_add d) (Nat.zero_add e) _ _ (prodHom
      (partBase sA d) (partBase sB e) (prodBase (partBase sP 0) (partBase sA d)) (prodBase
          (partBase sP 0) (partBase sB e))
          (Limits.pullback.snd (partBase sP 0) (partBase sA d)) (Limits.pullback.snd
              (partBase sP 0) (partBase sB e))
          Limits.pullback.condition.symm Limits.pullback.condition.symm)
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (tensorBlockHom_unit_left k sA sB sP d e) rfl _ _
    HEq.rfl).trans h₂

/-- `[Δ_P]` is a left unit on pure blocks. -/
theorem corrEquivOfIso_tensor_diagonal_left_tmul (r : ℤ) (d e : ℕ) (q : ℚ)
    (α : chowGroup (fieldChowSituation k) (prodBase (partBase sA d) (partBase sB e))
        ((e : ℤ) - r)) :
    corrEquivOfIso k sA (prodBase sP sA) sB (prodBase sP sB) (Limits.pullback.snd sP sA)
        (Limits.pullback.snd sP sB) Limits.pullback.condition.symm Limits.pullback.condition.symm
            (0 + r)
        (tensor k sP sA sP sB (canonicalDiagonalClassFamily k) 0 r
          (DirectSum.lof ℚ ℕ _ 0 (DirectSum.lof ℚ ℕ _ 0
            ((1 : ℚ) ⊗ₜ[ℤ] diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0))))
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))) =
      corrCongr k sA sB (zero_add r).symm (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
          (q ⊗ₜ[ℤ] α))) := by
  have hc := properChowPushforward_comp_apply (fieldChowSituation k) _ _ _
      (tensorBlockHom k sP sA sP sB 0 d 0 e) (prodHom (partBase sA (0 + d)) (partBase sB (0 + e))
          (partBase (prodBase sP sA) (0 + d)) (partBase (prodBase sP sB) (0 + e))
          (partMap sA (prodBase sP sA) (Limits.pullback.snd sP sA) Limits.pullback.condition.symm
              (0 + d)) (partMap sB (prodBase sP sB)
                  (Limits.pullback.snd sP sB) Limits.pullback.condition.symm (0 + e))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _)) _ rfl
    (tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
    (by rw [Category.assoc, prodHom_comp_prodBase, tensorBlockHom_comp_prodBase])
        (((0 + e : ℕ) : ℤ) - (0 + r))
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
        (properPushforwardDescends _ _ _ _ _ _) (tensorInt k (partBase sP 0) (partBase sA d)
            (partBase sP 0) (partBase sB e) (canonicalDiagonalClassFamily k)
          (relativeDimension_partBase sP 0) (relativeDimension_partBase sA d)
          (relativeDimension_partBase sP 0) (relativeDimension_partBase sB e) 0 r
          (diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0)) α)
  refine (congrArg (corrEquivOfIso k sA (prodBase sP sA) sB (prodBase sP sB)
      (Limits.pullback.snd sP sA)
          (Limits.pullback.snd sP sB) Limits.pullback.condition.symm Limits.pullback.condition.symm
              (0 + r))
    (tensor_lof_lof_tmul k sP sA sP sB (canonicalDiagonalClassFamily k) 0 r 0 0 d e 1 q
      (diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0)) α)).trans ?_
  refine (corrEquivOfIso_lof_lof _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
  refine lof_lof_eq_corrCongr k sA sB (zero_add r).symm (Nat.zero_add d)
      (Nat.zero_add e) q _ _ _ _ ?_ rfl
    (unit_left_parts_heq k sA sB sP r d e α)
  rw [correspondenceEquivOfIso_tmul, one_mul]
  exact congrArg (TensorProduct.tmul ℤ q) hc.symm

omit [IsSeparated sA] [IsProper sA] [IsSeparated sB] [IsProper sB] [IsSeparated sP] [IsProper sP] in
/-- The unit constraint on a block, read in the product. -/
theorem tensorBlockHom_unit_right (d e : ℕ) :
    ((tensorBlockHom k sA sP sB sP d 0 e 0) ≫ (prodHom (partBase sA (d + 0)) (partBase sB (e + 0))
        (partBase (prodBase sA sP) (d + 0)) (partBase (prodBase sB sP) (e + 0))
          (partMap sA (prodBase sA sP) (Limits.pullback.fst sA sP) rfl (d + 0)) (partMap sB
              (prodBase sB sP) (Limits.pullback.fst sB sP) rfl (e + 0))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))) ≫ (prodHom sA sB
              (partBase sA (d + 0)) (partBase sB (e + 0)) (dimPart sA (d + 0)).ι (dimPart sB
                  (e + 0)).ι rfl rfl) =
      (prodHom (partBase sA d) (partBase sB e) (prodBase (partBase sA d) (partBase sP 0)) (prodBase
          (partBase sB e) (partBase sP 0))
          (Limits.pullback.fst (partBase sA d) (partBase sP 0)) (Limits.pullback.fst
              (partBase sB e) (partBase sP 0)) rfl rfl) ≫ (prodHom sA sB (partBase sA d)
                  (partBase sB e) (dimPart sA d).ι (dimPart sB e).ι rfl rfl) := by
  apply Limits.pullback.hom_ext <;> simp [tensorBlockHom, -Nat.add_zero, -add_zero, -zero_add,
    -Nat.zero_add]

/-- `[Δ_P]` is a right unit on a block, on integral Chow groups. -/
theorem unit_right_parts_heq (r : ℤ) (d e : ℕ)
    (α : chowGroup (fieldChowSituation k) (prodBase (partBase sA d) (partBase sB e))
        ((e : ℤ) - r)) :
    pf[(tensorBase (partBase sA d) (partBase sP 0) (partBase sB e) (partBase sP 0)), (prodBase
        (partBase sA (d + 0)) (partBase sB (e + 0))), (tensorBlockHom k sA sP sB sP d 0 e 0) ≫
            (prodHom (partBase sA (d + 0)) (partBase sB (e + 0)) (partBase (prodBase sA sP)
                (d + 0)) (partBase (prodBase sB sP) (e + 0))
          (partMap sA (prodBase sA sP) (Limits.pullback.fst sA sP) rfl (d + 0)) (partMap sB
              (prodBase sB sP) (Limits.pullback.fst sB sP) rfl (e + 0))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _)),
        by rw [Category.assoc, prodHom_comp_prodBase, tensorBlockHom_comp_prodBase],
            (((e + 0 : ℕ) : ℤ) - (r + 0))] (tensorInt k (partBase sA d) (partBase sP 0)
                (partBase sB e) (partBase sP 0) (canonicalDiagonalClassFamily k)
          (relativeDimension_partBase sA d) (relativeDimension_partBase sP 0)
          (relativeDimension_partBase sB e) (relativeDimension_partBase sP 0) r 0 α
          (diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0))) ≍ α := by
  have := isIso_dimPart_self_ι sP (relativeDimension_zero_of_isIso k sP)
  have h₂ := tensorInt_rightUnit k (partBase sP 0) (partBase sA d) (partBase sB e)
      (relativeDimension_partBase sA d) (relativeDimension_partBase sB e)
          (relativeDimension_partBase sP 0) r α
  exact (properChowPushforward_parts_heq k sA sB _ (Nat.add_zero d) (Nat.add_zero e) _ _ (prodHom
      (partBase sA d) (partBase sB e) (prodBase (partBase sA d) (partBase sP 0)) (prodBase
          (partBase sB e) (partBase sP 0))
          (Limits.pullback.fst (partBase sA d) (partBase sP 0)) (Limits.pullback.fst
              (partBase sB e) (partBase sP 0)) rfl rfl)
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (tensorBlockHom_unit_right k sA sB sP d e) rfl _ _
    HEq.rfl).trans h₂

/-- `[Δ_P]` is a right unit on pure blocks. -/
theorem corrEquivOfIso_tensor_diagonal_right_tmul (r : ℤ) (d e : ℕ) (q : ℚ)
    (α : chowGroup (fieldChowSituation k) (prodBase (partBase sA d) (partBase sB e))
        ((e : ℤ) - r)) :
    corrEquivOfIso k sA (prodBase sA sP) sB (prodBase sB sP) (Limits.pullback.fst sA sP)
        (Limits.pullback.fst sB sP) rfl rfl (r + 0)
        (tensor k sA sP sB sP (canonicalDiagonalClassFamily k) r 0
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (q ⊗ₜ[ℤ] α)))
          (DirectSum.lof ℚ ℕ _ 0 (DirectSum.lof ℚ ℕ _ 0
            ((1 : ℚ) ⊗ₜ[ℤ] diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0))))) =
      corrCongr k sA sB (add_zero r).symm (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
          (q ⊗ₜ[ℤ] α))) := by
  have hc := properChowPushforward_comp_apply (fieldChowSituation k) _ _ _
      (tensorBlockHom k sA sP sB sP d 0 e 0) (prodHom (partBase sA (d + 0)) (partBase sB (e + 0))
          (partBase (prodBase sA sP) (d + 0)) (partBase (prodBase sB sP) (e + 0))
          (partMap sA (prodBase sA sP) (Limits.pullback.fst sA sP) rfl (d + 0)) (partMap sB
              (prodBase sB sP) (Limits.pullback.fst sB sP) rfl (e + 0))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _)) _ rfl
    (tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
    (by rw [Category.assoc, prodHom_comp_prodBase, tensorBlockHom_comp_prodBase])
        (((e + 0 : ℕ) : ℤ) - (r + 0))
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
        (properPushforwardDescends _ _ _ _ _ _) (tensorInt k (partBase sA d) (partBase sP 0)
            (partBase sB e) (partBase sP 0) (canonicalDiagonalClassFamily k)
          (relativeDimension_partBase sA d) (relativeDimension_partBase sP 0)
          (relativeDimension_partBase sB e) (relativeDimension_partBase sP 0) r 0 α
          (diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0)))
  refine (congrArg (corrEquivOfIso k sA (prodBase sA sP) sB (prodBase sB sP)
      (Limits.pullback.fst sA sP) (Limits.pullback.fst sB sP) rfl rfl (r + 0))
    (tensor_lof_lof_tmul k sA sP sB sP (canonicalDiagonalClassFamily k) r 0 d e 0 0 q 1 α
      (diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0)))).trans ?_
  refine (corrEquivOfIso_lof_lof _ _ _ _ _ _ _ _ _ _ _ _ _).trans ?_
  refine lof_lof_eq_corrCongr k sA sB (add_zero r).symm (Nat.add_zero d)
      (Nat.add_zero e) q _ _ _ _ ?_ rfl
    (unit_right_parts_heq k sA sB sP r d e α)
  rw [correspondenceEquivOfIso_tmul, mul_one]
  exact congrArg (TensorProduct.tmul ℤ q) hc.symm

/-- For `P ≅ Spec k`, the diagonal class `[Δ_P]` as a pure tensor of a pure block. -/
theorem diagonalCorr_eq_lof_lof_tmul :
    diagonalCorr k sP = DirectSum.lof ℚ ℕ _ 0 (DirectSum.lof ℚ ℕ _ 0
      ((1 : ℚ) ⊗ₜ[ℤ] diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0))) :=
  diagonalCorr_eq_diagonalBlock_zero k sP

/-- **`[Δ_P]` is a left unit for the tensor product of correspondences** (Stacks 0FG7), for
`P ≅ Spec k`: transporting `[Δ_P] ⊗ c` along the projections `P × A ≅ A` and `P × B ≅ B` gives
`c`, for the canonical diagonal classes. -/
theorem corrEquivOfIso_tensor_diagonalCorr_left (r : ℤ) (a : Corr k sA sB r) :
    corrEquivOfIso k sA (prodBase sP sA) sB (prodBase sP sB) (Limits.pullback.snd sP sA)
        (Limits.pullback.snd sP sB) Limits.pullback.condition.symm Limits.pullback.condition.symm
        (0 + r) (tensor k sP sA sP sB (canonicalDiagonalClassFamily k) 0 r (diagonalCorr k sP) a) =
      corrCongr k sA sB (zero_add r).symm a := by
  rw [diagonalCorr_eq_lof_lof_tmul k sP]
  refine LinearMap.congr_fun (corr_linear_ext k sA sB
    ((corrEquivOfIso k sA (prodBase sP sA) sB (prodBase sP sB) (Limits.pullback.snd sP sA)
        (Limits.pullback.snd sP sB) Limits.pullback.condition.symm Limits.pullback.condition.symm
        (0 + r)).toLinearMap ∘ₗ
      tensor k sP sA sP sB (canonicalDiagonalClassFamily k) 0 r
        (DirectSum.lof ℚ ℕ _ 0 (DirectSum.lof ℚ ℕ _ 0
          ((1 : ℚ) ⊗ₜ[ℤ] diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0)))))
    (corrCongr k sA sB (zero_add r).symm).toLinearMap fun d e q α ↦ ?_) a
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
  exact corrEquivOfIso_tensor_diagonal_left_tmul k sA sB sP r d e q α

/-- **`[Δ_P]` is a right unit for the tensor product of correspondences** (Stacks 0FG7), for
`P ≅ Spec k`: transporting `c ⊗ [Δ_P]` along the projections `A × P ≅ A` and `B × P ≅ B` gives
`c`, for the canonical diagonal classes. -/
theorem corrEquivOfIso_tensor_diagonalCorr_right (r : ℤ) (a : Corr k sA sB r) :
    corrEquivOfIso k sA (prodBase sA sP) sB (prodBase sB sP) (Limits.pullback.fst sA sP)
        (Limits.pullback.fst sB sP) rfl rfl (r + 0)
        (tensor k sA sP sB sP (canonicalDiagonalClassFamily k) r 0 a (diagonalCorr k sP)) =
      corrCongr k sA sB (add_zero r).symm a := by
  rw [diagonalCorr_eq_lof_lof_tmul k sP]
  refine LinearMap.congr_fun (corr_linear_ext k sA sB
    ((corrEquivOfIso k sA (prodBase sA sP) sB (prodBase sB sP) (Limits.pullback.fst sA sP)
        (Limits.pullback.fst sB sP) rfl rfl (r + 0)).toLinearMap ∘ₗ
      (tensor k sA sP sB sP (canonicalDiagonalClassFamily k) r 0).flip
        (DirectSum.lof ℚ ℕ _ 0 (DirectSum.lof ℚ ℕ _ 0
          ((1 : ℚ) ⊗ₜ[ℤ] diagonalChowClass k (partBase sP 0) (((0 : ℕ) : ℤ) - 0)))))
    (corrCongr k sA sB (add_zero r).symm).toLinearMap fun d e q α ↦ ?_) a
  rw [LinearMap.comp_apply, LinearMap.flip_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
  exact corrEquivOfIso_tensor_diagonal_right_tmul k sA sB sP r d e q α

end Unit

end Stacks.WeilCohomology

end
