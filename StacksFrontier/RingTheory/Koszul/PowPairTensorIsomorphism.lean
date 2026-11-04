module

public import StacksFrontier.Algebra.DifferentialGraded.TensorProductLift
public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebraPowPair

/-!
# The Koszul algebra of a pair of powers is a tensor product of Koszul algebras

Let `f` be an element of a commutative ring `R` and let `n, t` be natural numbers. The Koszul
algebra `K_{n,t} = R⟨y, x⟩` of the pair `(f ^ n, f ^ t)` receives the tensor product
`K_n ⊗_R K_t` of the two one-variable Koszul algebras by `Koszul.powPairFromTensor`, which sends
`a ⊗ b` to the product of the images of `a` and `b`. That homomorphism is an isomorphism of
differential graded algebras; its inverse sends the generator `y` to `ξ ⊗ 1` and the generator
`x` to `1 ⊗ ξ`.

The inverse comes from the universal property of the exterior algebra. The two elements `ξ ⊗ 1`
and `1 ⊗ ξ` of `K_n ⊗_R K_t` have square zero and anticommute — the latter because the Koszul
sign of two elements of degree `-1` is `-1` — so the linear map taking the two basis vectors of
`R²` to them extends to an algebra homomorphism out of `R⟨y, x⟩`. It preserves the grading
because `ξ ⊗ 1` and `1 ⊗ ξ` have degree `-1`, and it commutes with the differentials because the
differential of `K_n ⊗_R K_t` takes the values `f ^ n` and `f ^ t` on them.

## Main definitions

* `Koszul.powOne`: the one-variable Koszul algebra `K_m` of `f ^ m`, and `Koszul.powOneGen` its
  generator `ξ`.
* `Koszul.powTensorAlgebra`: the tensor product `K_n ⊗_R K_t`.
* `Koszul.powTensorY`, `Koszul.powTensorX` and `Koszul.powTensorYX`: the pure tensors `ξ ⊗ 1`,
  `1 ⊗ ξ` and `ξ ⊗ ξ`.
* `Koszul.powPairToTensor`: the homomorphism `K_{n,t} → K_n ⊗_R K_t` inverse to
  `Koszul.powPairFromTensor`.

## Main results

* `Koszul.d_powTensorY` and `Koszul.d_powTensorX`: the differential of `K_n ⊗_R K_t` sends
  `ξ ⊗ 1` to `f ^ n` and `1 ⊗ ξ` to `f ^ t`.
* `Koszul.powTensorX_mul_powTensorY`: the two pure tensors anticommute.
* `Koszul.powPairToTensor_powPairFromTensor` and
  `Koszul.powPairFromTensor_powPairToTensor`: the two composites are the identity.
* `Koszul.powPairFromTensor_bijective`: `Koszul.powPairFromTensor` is bijective, so it is an
  isomorphism of differential graded algebras with inverse `Koszul.powPairToTensor`.

## Implementation notes

Every element of `K_n`, of `K_t` and of their tensor product is named at the carrier type of the
differential graded algebra it belongs to, rather than at the exterior algebra that carrier
unfolds to. The graded tensor product needs the graded-algebra instance of each factor, and that
instance is found only when the submodule family and the element live over the same carrier; a
term of the exterior algebra placed in the tensor product directly makes the instance search
fail.

The grading of the inverse is checked on the wedge products `ξ_{i₁} ⋯ ξ_{i_k}`, which span the
`k`-th exterior power, by induction on `k` through the recurrence `Koszul.ιMulti_succ_apply`.
Compatibility with the differentials is checked by the left induction principle of a Clifford
algebra: the inductive step multiplies on the left by a generator, where the Koszul differential
is the contraction formula and the differential of the tensor product is the Leibniz rule in
degree `-1`, whose sign is `-1`.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
* [Stacks Project, Tag 0664](https://stacks.math.columbia.edu/tag/0664)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open scoped ExteriorAlgebra TensorProduct

open DifferentialGradedAlgebra DividedPowers.TateResolution

variable {R : Type u} [CommRing R]

section Setup

/-- The one-variable Koszul algebra `K_m = R⟨ξ⟩` with `d ξ = f ^ m`. -/
abbrev powOne (f : R) (m : ℕ) : DifferentialGradedAlgebra.{u, u} R :=
  powAlgebra (fun _ : Fin 1 => f) m

/-- The tensor product `K_n ⊗_R K_t` of the two one-variable Koszul algebras. -/
abbrev powTensorAlgebra (f : R) (n t : ℕ) : DifferentialGradedAlgebra.{u, u} R :=
  tensorProduct (powOne f n) (powOne f t)

/-- The generator `ξ` of the one-variable Koszul algebra `K_m`. -/
abbrev powOneGen (f : R) (m : ℕ) : (powOne f m).A :=
  ExteriorAlgebra.ι R (Pi.single 0 1)

/-- The generator `ξ` of `K_m` has degree `-1`. -/
theorem powOneGen_mem_grading (f : R) (m : ℕ) :
    powOneGen f m ∈ (powOne f m).grading (-1) :=
  ι_mem_powAlgebra_grading (fun _ : Fin 1 => f) m (Pi.single 0 1)

/-- The differential of `K_m` sends the generator `ξ` to `f ^ m`. -/
theorem powOne_d_powOneGen (f : R) (m : ℕ) :
    (powOne f m).d (powOneGen f m) = algebraMap R (powOne f m).A (f ^ m) :=
  powAlgebra_d_ι (fun _ : Fin 1 => f) m 0

/-- The generator `ξ` of `K_m` has square zero. -/
theorem powOneGen_mul_self (f : R) (m : ℕ) :
    powOneGen f m * powOneGen f m = 0 :=
  ExteriorAlgebra.ι_sq_zero _

/-- A vector of `R¹` is its only coordinate times the basis vector. -/
theorem eq_smul_single (v : Fin 1 → R) : v = v 0 • (Pi.single 0 1 : Fin 1 → R) := by
  refine funext fun i => ?_
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp

/-- In `K_m`, the image of a vector `v` of `R¹` is `v 0 • ξ`. -/
theorem ι_eq_smul_powOneGen (f : R) (m : ℕ) (v : Fin 1 → R) :
    (ExteriorAlgebra.ι R v : (powOne f m).A) = v 0 • powOneGen f m := by
  have h : (ExteriorAlgebra.ι R v : (powOne f m).A) =
      ExteriorAlgebra.ι R (v 0 • (Pi.single 0 1 : Fin 1 → R)) := by
    rw [← eq_smul_single]
  rw [h, map_smul]
  rfl

/-- The pure tensor `ξ ⊗ 1` of `K_n ⊗_R K_t`. -/
abbrev powTensorY (f : R) (n t : ℕ) : (powOne f n).grading ᵍ⊗[R] (powOne f t).grading :=
  powOneGen f n ᵍ⊗ₜ[R] (1 : (powOne f t).A)

/-- The pure tensor `1 ⊗ ξ` of `K_n ⊗_R K_t`. -/
abbrev powTensorX (f : R) (n t : ℕ) : (powOne f n).grading ᵍ⊗[R] (powOne f t).grading :=
  (1 : (powOne f n).A) ᵍ⊗ₜ[R] powOneGen f t

/-- The pure tensor `ξ ⊗ ξ` of `K_n ⊗_R K_t`. -/
abbrev powTensorYX (f : R) (n t : ℕ) : (powOne f n).grading ᵍ⊗[R] (powOne f t).grading :=
  powOneGen f n ᵍ⊗ₜ[R] powOneGen f t

/-- The pure tensor `ξ ⊗ 1` has degree `-1` in `K_n ⊗_R K_t`. -/
theorem powTensorY_mem_grading (f : R) (n t : ℕ) :
    powTensorY f n t ∈ (powTensorAlgebra f n t).grading (-1) := by
  have h := tmul_mem_grading (powOne f n) (powOne f t) (-1) 0
    (powOneGen f n) (1 : (powOne f t).A)
    (powOneGen_mem_grading f n) (SetLike.one_mem_graded (powOne f t).grading)
  rw [show (-1 : ℤ) + 0 = -1 from by ring] at h
  exact h

/-- The pure tensor `1 ⊗ ξ` has degree `-1` in `K_n ⊗_R K_t`. -/
theorem powTensorX_mem_grading (f : R) (n t : ℕ) :
    powTensorX f n t ∈ (powTensorAlgebra f n t).grading (-1) := by
  have h := tmul_mem_grading (powOne f n) (powOne f t) 0 (-1)
    (1 : (powOne f n).A) (powOneGen f t)
    (SetLike.one_mem_graded (powOne f n).grading) (powOneGen_mem_grading f t)
  rw [show (0 : ℤ) + -1 = -1 from by ring] at h
  exact h

/-- In `K_n ⊗_R K_t`, the pure tensor `a ⊗ 0` is zero. -/
theorem tmul_zero_right (f : R) (n t : ℕ) (a : (powOne f n).A) :
    (a ᵍ⊗ₜ[R] (0 : (powOne f t).A) : (powOne f n).grading ᵍ⊗[R] (powOne f t).grading) = 0 := by
  rw [GradedTensorProduct.tmul, TensorProduct.tmul_zero, map_zero]

/-- In `K_n ⊗_R K_t`, the pure tensor `0 ⊗ b` is zero. -/
theorem tmul_zero_left (f : R) (n t : ℕ) (b : (powOne f t).A) :
    ((0 : (powOne f n).A) ᵍ⊗ₜ[R] b : (powOne f n).grading ᵍ⊗[R] (powOne f t).grading) = 0 := by
  rw [GradedTensorProduct.tmul, TensorProduct.zero_tmul, map_zero]

/-- The differential of `K_n ⊗_R K_t` sends `ξ ⊗ 1` to `f ^ n`. -/
theorem d_powTensorY (f : R) (n t : ℕ) :
    (powTensorAlgebra f n t).d (powTensorY f n t) =
      algebraMap R (powTensorAlgebra f n t).A (f ^ n) := by
  have h : (powTensorAlgebra f n t).d (powTensorY f n t) =
      (((powOne f n).d (powOneGen f n) ᵍ⊗ₜ[R] (1 : (powOne f t).A)) +
        (((-1 : ℤ).negOnePow : ℤ)) •
          (powOneGen f n ᵍ⊗ₜ[R] (powOne f t).d (1 : (powOne f t).A)) :
        (powOne f n).grading ᵍ⊗[R] (powOne f t).grading) :=
    tensorProductDifferential_tmul (powOne f n) (powOne f t) (-1)
      ⟨powOneGen f n, powOneGen_mem_grading f n⟩ (1 : (powOne f t).A)
  rw [h, d_one (powOne f t), powOne_d_powOneGen, tmul_zero_right, smul_zero, add_zero]
  exact (GradedTensorProduct.includeLeft (powOne f n).grading
    (powOne f t).grading).commutes (f ^ n)

/-- The differential of `K_n ⊗_R K_t` sends `1 ⊗ ξ` to `f ^ t`. -/
theorem d_powTensorX (f : R) (n t : ℕ) :
    (powTensorAlgebra f n t).d (powTensorX f n t) =
      algebraMap R (powTensorAlgebra f n t).A (f ^ t) := by
  have h : (powTensorAlgebra f n t).d (powTensorX f n t) =
      (((powOne f n).d (1 : (powOne f n).A) ᵍ⊗ₜ[R] powOneGen f t) +
        (((0 : ℤ).negOnePow : ℤ)) •
          ((1 : (powOne f n).A) ᵍ⊗ₜ[R] (powOne f t).d (powOneGen f t)) :
        (powOne f n).grading ᵍ⊗[R] (powOne f t).grading) :=
    tensorProductDifferential_tmul (powOne f n) (powOne f t) 0
      ⟨(1 : (powOne f n).A), SetLike.one_mem_graded (powOne f n).grading⟩ (powOneGen f t)
  rw [h, d_one (powOne f n), powOne_d_powOneGen, tmul_zero_left, zero_add, Int.negOnePow_zero,
    Units.val_one, one_smul]
  exact (GradedTensorProduct.includeRight (powOne f n).grading
    (powOne f t).grading).commutes (f ^ t)

end Setup

section Anticommute

/-- The product `(ξ ⊗ 1) (1 ⊗ ξ)` is the pure tensor `ξ ⊗ ξ`. -/
theorem powTensorY_mul_powTensorX (f : R) (n t : ℕ) :
    powTensorY f n t * powTensorX f n t = powTensorYX f n t :=
  GradedTensorProduct.tmul_one_mul_one_tmul _ _ _ _

/-- The pure tensors `ξ ⊗ 1` and `1 ⊗ ξ` anticommute: the Koszul sign of two elements of degree
`-1` is `-1`. -/
theorem powTensorX_mul_powTensorY (f : R) (n t : ℕ) :
    powTensorX f n t * powTensorY f n t = -(powTensorY f n t * powTensorX f n t) := by
  have h : powTensorX f n t * powTensorY f n t =
      ((-1 : ℤˣ) ^ ((-1 : ℤ) * (-1 : ℤ))) •
        ((((1 : (powOne f n).A) * powOneGen f n) ᵍ⊗ₜ[R]
          (powOneGen f t * (1 : (powOne f t).A))) :
            (powOne f n).grading ᵍ⊗[R] (powOne f t).grading) :=
    GradedTensorProduct.tmul_coe_mul_coe_tmul (powOne f n).grading (powOne f t).grading
      (1 : (powOne f n).A) ⟨powOneGen f t, powOneGen_mem_grading f t⟩
      ⟨powOneGen f n, powOneGen_mem_grading f n⟩ (1 : (powOne f t).A)
  rw [h, one_mul, mul_one, show (-1 : ℤ) * (-1 : ℤ) = 1 from by ring, zpow_one,
    powTensorY_mul_powTensorX, Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]

/-- The pure tensor `ξ ⊗ 1` has square zero. -/
theorem powTensorY_mul_self (f : R) (n t : ℕ) :
    powTensorY f n t * powTensorY f n t = 0 := by
  have h : powTensorY f n t * powTensorY f n t =
      (((powOneGen f n * powOneGen f n) ᵍ⊗ₜ[R] (1 : (powOne f t).A)) :
        (powOne f n).grading ᵍ⊗[R] (powOne f t).grading) :=
    GradedTensorProduct.tmul_one_mul_coe_tmul (powOne f n).grading (powOne f t).grading
      (powOneGen f n) ⟨powOneGen f n, powOneGen_mem_grading f n⟩ (1 : (powOne f t).A)
  rw [h, powOneGen_mul_self, tmul_zero_left]

/-- The pure tensor `1 ⊗ ξ` has square zero. -/
theorem powTensorX_mul_self (f : R) (n t : ℕ) :
    powTensorX f n t * powTensorX f n t = 0 := by
  have h : powTensorX f n t * powTensorX f n t =
      (((1 : (powOne f n).A) ᵍ⊗ₜ[R] (powOneGen f t * powOneGen f t)) :
        (powOne f n).grading ᵍ⊗[R] (powOne f t).grading) :=
    GradedTensorProduct.tmul_coe_mul_one_tmul (powOne f n).grading (powOne f t).grading
      (1 : (powOne f n).A) ⟨powOneGen f t, powOneGen_mem_grading f t⟩ (powOneGen f t)
  rw [h, powOneGen_mul_self, tmul_zero_right]

end Anticommute

section Inverse

/-- The linear map `R² → K_n ⊗_R K_t` taking the first basis vector to `ξ ⊗ 1` and the second
to `1 ⊗ ξ`. -/
def powPairToTensorMap (f : R) (n t : ℕ) :
    (Fin 2 → R) →ₗ[R] (powTensorAlgebra f n t).A where
  toFun v := v 0 • powTensorY f n t + v 1 • powTensorX f n t
  map_add' v w := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, smul_add]

/-- `Koszul.powPairToTensorMap` sends `v` to `v 0 • (ξ ⊗ 1) + v 1 • (1 ⊗ ξ)`. -/
@[simp] theorem powPairToTensorMap_apply (f : R) (n t : ℕ) (v : Fin 2 → R) :
    powPairToTensorMap f n t v = v 0 • powTensorY f n t + v 1 • powTensorX f n t := rfl

/-- Every value of `Koszul.powPairToTensorMap` has square zero. -/
theorem powPairToTensorMap_mul_self (f : R) (n t : ℕ) (v : Fin 2 → R) :
    powPairToTensorMap f n t v * powPairToTensorMap f n t v = 0 := by
  have hexp : powPairToTensorMap f n t v * powPairToTensorMap f n t v =
      (v 0 * v 0) • (powTensorY f n t * powTensorY f n t) +
        ((v 0 * v 1) • (powTensorX f n t * powTensorY f n t) +
          (v 1 * v 0) • (powTensorY f n t * powTensorX f n t)) +
        (v 1 * v 1) • (powTensorX f n t * powTensorX f n t) := by
    simp only [powPairToTensorMap_apply, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_add, smul_smul]
    abel
  rw [hexp, powTensorY_mul_self, powTensorX_mul_self, smul_zero, smul_zero, zero_add, add_zero,
    powTensorX_mul_powTensorY, smul_neg, show v 1 * v 0 = v 0 * v 1 from by ring]
  abel

/-- The underlying algebra homomorphism `K_{n,t} → K_n ⊗_R K_t`. -/
def powPairToTensorAlgHom (f : R) (n t : ℕ) :
    ExteriorAlgebra R (Fin 2 → R) →ₐ[R] (powTensorAlgebra f n t).A :=
  ExteriorAlgebra.lift R ⟨powPairToTensorMap f n t, powPairToTensorMap_mul_self f n t⟩

/-- `Koszul.powPairToTensorAlgHom` sends `ι v` to `v 0 • (ξ ⊗ 1) + v 1 • (1 ⊗ ξ)`. -/
@[simp] theorem powPairToTensorAlgHom_ι (f : R) (n t : ℕ) (v : Fin 2 → R) :
    powPairToTensorAlgHom f n t (ExteriorAlgebra.ι R v) =
      v 0 • powTensorY f n t + v 1 • powTensorX f n t :=
  ExteriorAlgebra.lift_ι_apply R _ _ v

/-- `Koszul.powPairToTensorAlgHom` sends the image `ι v` of a vector to an element of degree `-1`.
-/
theorem powPairToTensorAlgHom_ι_mem (f : R) (n t : ℕ) (v : Fin 2 → R) :
    powPairToTensorAlgHom f n t (ExteriorAlgebra.ι R v) ∈
      (powTensorAlgebra f n t).grading (-1) := by
  rw [powPairToTensorAlgHom_ι]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (powTensorY_mem_grading f n t))
    (Submodule.smul_mem _ _ (powTensorX_mem_grading f n t))

/-- `Koszul.powPairToTensorAlgHom` sends a wedge product of `k` vectors to an element of degree
`-k`. -/
theorem powPairToTensorAlgHom_ιMulti_mem (f : R) (n t : ℕ) (k : ℕ) :
    ∀ w : Fin k → (Fin 2 → R),
      powPairToTensorAlgHom f n t (ExteriorAlgebra.ιMulti R k w) ∈
        (powTensorAlgebra f n t).grading (-(k : ℤ)) := by
  induction k with
  | zero =>
      intro w
      rw [ExteriorAlgebra.ιMulti_zero_apply, map_one, show -((0 : ℕ) : ℤ) = 0 from by norm_num]
      exact SetLike.one_mem_graded (powTensorAlgebra f n t).grading
  | succ j ih =>
      intro w
      rw [ιMulti_succ_apply, map_mul]
      have hmul := SetLike.mul_mem_graded (powPairToTensorAlgHom_ι_mem f n t (w 0))
        (ih (Fin.tail w))
      rw [show (-1 : ℤ) + -(j : ℤ) = -((j + 1 : ℕ) : ℤ) from by push_cast; ring] at hmul
      exact hmul

/-- `Koszul.powPairToTensorAlgHom` sends the `k`-th exterior power into degree `-k`. -/
theorem powPairToTensorAlgHom_mem (f : R) (n t k : ℕ)
    {a : ExteriorAlgebra R (Fin 2 → R)} (ha : a ∈ exteriorGrade R (Fin 2 → R) k) :
    powPairToTensorAlgHom f n t a ∈ (powTensorAlgebra f n t).grading (-(k : ℤ)) := by
  rw [← (Submodule.ext_iff.mp (exteriorPower.ιMulti_span_fixedDegree R k (Fin 2 → R)))] at ha
  induction ha using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      exact powPairToTensorAlgHom_ιMulti_mem f n t k w
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul r x _ ihx =>
      rw [map_smul]
      exact Submodule.smul_mem _ r ihx

/-- `Koszul.powPairToTensorAlgHom` preserves the grading: it sends the degree `m` part of `K_{n,t}`
into the degree `m` part of `K_n ⊗_R K_t`. -/
theorem powPairToTensorAlgHom_mem_grading (f : R) (n t : ℕ) (m : ℤ)
    {a : ExteriorAlgebra R (Fin 2 → R)} (ha : a ∈ (powPairAlgebra f n t).grading m) :
    powPairToTensorAlgHom f n t a ∈ (powTensorAlgebra f n t).grading m := by
  rw [powPairAlgebra_grading] at ha
  by_cases hm : m ≤ 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
    rw [cohomologicalExteriorGrade_neg_natCast] at ha
    exact powPairToTensorAlgHom_mem f n t k ha
  · have h0 : a = 0 := eq_zero_of_mem_cohomologicalExteriorGrade_of_pos R _ (by omega) ha
    rw [h0, map_zero]
    exact Submodule.zero_mem _

/-- The differential of `K_n ⊗_R K_t` takes the value `v₀ f^n + v₁ f^t` on the image of a
vector. -/
theorem d_powPairToTensorAlgHom_ι (f : R) (n t : ℕ) (v : Fin 2 → R) :
    (powTensorAlgebra f n t).d (powPairToTensorAlgHom f n t (ExteriorAlgebra.ι R v)) =
      algebraMap R (powTensorAlgebra f n t).A (seqDual (powPairSeq f n t) v) := by
  rw [powPairToTensorAlgHom_ι, map_add, map_smul, map_smul, d_powTensorY, d_powTensorX,
    seqDual_apply, Fin.sum_univ_two, powPairSeq_zero, powPairSeq_one, map_add, Algebra.smul_def,
    Algebra.smul_def, map_mul, map_mul]

/-- `Koszul.powPairToTensorAlgHom` intertwines contraction against `(f ^ n, f ^ t)` with the
differential of `K_n ⊗_R K_t`. -/
theorem powPairToTensorAlgHom_map_contraction (f : R) (n t : ℕ)
    (a : ExteriorAlgebra R (Fin 2 → R)) :
    powPairToTensorAlgHom f n t (contraction (seqDual (powPairSeq f n t)) a) =
      (powTensorAlgebra f n t).d (powPairToTensorAlgHom f n t a) := by
  have hsign : (((-1 : ℤ).negOnePow : ℤ)) = -1 := by
    rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, Int.negOnePow_neg, Int.negOnePow_one]
    rfl
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      have hL : powPairToTensorAlgHom f n t
          (contraction (seqDual (powPairSeq f n t))
            (algebraMap R (ExteriorAlgebra R (Fin 2 → R)) r)) = 0 := by
        rw [CliffordAlgebra.contractLeft_algebraMap]
        exact map_zero _
      have hR : (powTensorAlgebra f n t).d (powPairToTensorAlgHom f n t
          (algebraMap R (ExteriorAlgebra R (Fin 2 → R)) r)) = 0 := by
        rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul,
          d_one (powTensorAlgebra f n t), smul_zero]
      exact hL.trans hR.symm
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, map_add]
  | ι_mul x m hx =>
      have hdx : contraction (seqDual (powPairSeq f n t)) (ExteriorAlgebra.ι R m * x) =
          seqDual (powPairSeq f n t) m • x -
            ExteriorAlgebra.ι R m * contraction (seqDual (powPairSeq f n t)) x :=
        CliffordAlgebra.contractLeft_ι_mul _ _ _
      have hleib := d_mul_of_mem (powTensorAlgebra f n t)
        (powPairToTensorAlgHom_ι_mem f n t m) (powPairToTensorAlgHom f n t x)
      rw [hsign] at hleib
      rw [hdx, map_sub, map_smul,
        map_mul (powPairToTensorAlgHom f n t) (ExteriorAlgebra.ι R m)
          (contraction (seqDual (powPairSeq f n t)) x), hx,
        map_mul (powPairToTensorAlgHom f n t) (ExteriorAlgebra.ι R m) x, hleib,
        d_powPairToTensorAlgHom_ι, Algebra.smul_def, neg_smul, one_smul]
      abel

/-- `Koszul.powPairToTensorAlgHom` commutes with the differentials of `K_{n,t}` and `K_n ⊗_R K_t`.
-/
theorem powPairToTensorAlgHom_map_d (f : R) (n t : ℕ) (a : ExteriorAlgebra R (Fin 2 → R)) :
    powPairToTensorAlgHom f n t ((powPairAlgebra f n t).d a) =
      (powTensorAlgebra f n t).d (powPairToTensorAlgHom f n t a) :=
  powPairToTensorAlgHom_map_contraction f n t a

/-- **The inverse of `Koszul.powPairFromTensor`.** The homomorphism `K_{n,t} → K_n ⊗_R K_t` of
differential graded algebras taking the generator `y` to `ξ ⊗ 1` and the generator `x` to
`1 ⊗ ξ`. -/
def powPairToTensor (f : R) (n t : ℕ) :
    (powPairAlgebra f n t).Hom (powTensorAlgebra f n t) where
  toAlgebraHom := powPairToTensorAlgHom f n t
  map_grading m _ ha := powPairToTensorAlgHom_mem_grading f n t m ha
  map_d := powPairToTensorAlgHom_map_d f n t

/-- The underlying algebra homomorphism of `Koszul.powPairToTensor` is
`Koszul.powPairToTensorAlgHom`. -/
@[simp] theorem powPairToTensor_toAlgebraHom (f : R) (n t : ℕ) :
    (powPairToTensor f n t).toAlgebraHom = powPairToTensorAlgHom f n t := rfl

end Inverse

section Composites

/-- `Koszul.powPairFromTensor` sends `a ⊗ 1` to the image of `a` under
`Koszul.koszulToPowPairLeft`. -/
theorem powPairFromTensor_includeLeft (f : R) (n t : ℕ) (a : (powOne f n).A) :
    (powPairFromTensor f n t).toAlgebraHom
        (GradedTensorProduct.includeLeft (powOne f n).grading (powOne f t).grading a) =
      (koszulToPowPairLeft f n t).toAlgebraHom a := by
  have h : (powPairFromTensor f n t).toAlgebraHom
      (GradedTensorProduct.includeLeft (powOne f n).grading (powOne f t).grading a) =
      (koszulToPowPairLeft f n t).toAlgebraHom a *
        (koszulToPowPairRight f n t).toAlgebraHom (1 : (powOne f t).A) := rfl
  rw [h, map_one, mul_one]

/-- `Koszul.powPairFromTensor` sends `1 ⊗ b` to the image of `b` under
`Koszul.koszulToPowPairRight`. -/
theorem powPairFromTensor_includeRight (f : R) (n t : ℕ) (b : (powOne f t).A) :
    (powPairFromTensor f n t).toAlgebraHom
        (GradedTensorProduct.includeRight (powOne f n).grading (powOne f t).grading b) =
      (koszulToPowPairRight f n t).toAlgebraHom b := by
  have h : (powPairFromTensor f n t).toAlgebraHom
      (GradedTensorProduct.includeRight (powOne f n).grading (powOne f t).grading b) =
      (koszulToPowPairLeft f n t).toAlgebraHom (1 : (powOne f n).A) *
        (koszulToPowPairRight f n t).toAlgebraHom b := rfl
  rw [h, map_one, one_mul]

/-- `Koszul.powPairFromTensor` sends `ξ ⊗ 1` to the generator `y` of `K_{n,t}`. -/
theorem powPairFromTensor_powTensorY (f : R) (n t : ℕ) :
    (powPairFromTensor f n t).toAlgebraHom (powTensorY f n t) = powPairY R := by
  have h0 : (powPairFromTensor f n t).toAlgebraHom (powTensorY f n t) =
      (powPairFromTensor f n t).toAlgebraHom
        (GradedTensorProduct.includeLeft (powOne f n).grading (powOne f t).grading
          (powOneGen f n)) := rfl
  rw [h0, powPairFromTensor_includeLeft]
  have h : (koszulToPowPairLeft f n t).toAlgebraHom (powOneGen f n) =
      ExteriorAlgebra.map (powPairCoord R 0) (ExteriorAlgebra.ι R (Pi.single 0 1)) := rfl
  rw [h, ExteriorAlgebra.map_apply_ι, powPairY]
  congr 1

/-- `Koszul.powPairFromTensor` sends `1 ⊗ ξ` to the generator `x` of `K_{n,t}`. -/
theorem powPairFromTensor_powTensorX (f : R) (n t : ℕ) :
    (powPairFromTensor f n t).toAlgebraHom (powTensorX f n t) = powPairX R := by
  have h0 : (powPairFromTensor f n t).toAlgebraHom (powTensorX f n t) =
      (powPairFromTensor f n t).toAlgebraHom
        (GradedTensorProduct.includeRight (powOne f n).grading (powOne f t).grading
          (powOneGen f t)) := rfl
  rw [h0, powPairFromTensor_includeRight]
  have h : (koszulToPowPairRight f n t).toAlgebraHom (powOneGen f t) =
      ExteriorAlgebra.map (powPairCoord R 1) (ExteriorAlgebra.ι R (Pi.single 0 1)) := rfl
  rw [h, ExteriorAlgebra.map_apply_ι, powPairX]
  congr 1

/-- The inverse `Koszul.powPairToTensorAlgHom` sends the generator `y` back to `ξ ⊗ 1`. -/
private theorem powPairToTensorAlgHom_powPairFromTensor_powTensorY (f : R) (n t : ℕ) :
    powPairToTensorAlgHom f n t ((powPairFromTensor f n t).toAlgebraHom (powTensorY f n t)) =
      powTensorY f n t := by
  rw [powPairFromTensor_powTensorY, powPairY, powPairToTensorAlgHom_ι]
  simp

/-- The inverse `Koszul.powPairToTensorAlgHom` sends the generator `x` back to `1 ⊗ ξ`. -/
private theorem powPairToTensorAlgHom_powPairFromTensor_powTensorX (f : R) (n t : ℕ) :
    powPairToTensorAlgHom f n t ((powPairFromTensor f n t).toAlgebraHom (powTensorX f n t)) =
      powTensorX f n t := by
  rw [powPairFromTensor_powTensorX, powPairX, powPairToTensorAlgHom_ι]
  simp

/-- **`K_n ⊗_R K_t → K_{n,t} → K_n ⊗_R K_t` is the identity.** -/
theorem powPairToTensor_powPairFromTensor (f : R) (n t : ℕ) :
    (powPairToTensorAlgHom f n t).comp (powPairFromTensor f n t).toAlgebraHom =
      AlgHom.id R (powTensorAlgebra f n t).A := by
  refine GradedTensorProduct.algHom_ext (powOne f n).grading (powOne f t).grading ?_ ?_
  · refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    change powPairToTensorAlgHom f n t ((powPairFromTensor f n t).toAlgebraHom
        (GradedTensorProduct.includeLeft (powOne f n).grading (powOne f t).grading
          (ExteriorAlgebra.ι R v))) =
      GradedTensorProduct.includeLeft (powOne f n).grading (powOne f t).grading
        (ExteriorAlgebra.ι R v)
    rw [ι_eq_smul_powOneGen f n v, map_smul, map_smul]
    exact (map_smul (powPairToTensorAlgHom f n t) (v 0) _).trans
      (congrArg (v 0 • ·) (powPairToTensorAlgHom_powPairFromTensor_powTensorY f n t))
  · refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    change powPairToTensorAlgHom f n t ((powPairFromTensor f n t).toAlgebraHom
        (GradedTensorProduct.includeRight (powOne f n).grading (powOne f t).grading
          (ExteriorAlgebra.ι R v))) =
      GradedTensorProduct.includeRight (powOne f n).grading (powOne f t).grading
        (ExteriorAlgebra.ι R v)
    rw [ι_eq_smul_powOneGen f t v, map_smul, map_smul]
    exact (map_smul (powPairToTensorAlgHom f n t) (v 0) _).trans
      (congrArg (v 0 • ·) (powPairToTensorAlgHom_powPairFromTensor_powTensorX f n t))

/-- **`K_{n,t} → K_n ⊗_R K_t → K_{n,t}` is the identity.** -/
theorem powPairFromTensor_powPairToTensor (f : R) (n t : ℕ) :
    (powPairFromTensor f n t).toAlgebraHom.comp (powPairToTensorAlgHom f n t) =
      AlgHom.id R (ExteriorAlgebra R (Fin 2 → R)) := by
  refine ExteriorAlgebra.hom_ext (LinearMap.ext fun m => ?_)
  change (powPairFromTensor f n t).toAlgebraHom
      (powPairToTensorAlgHom f n t (ExteriorAlgebra.ι R m)) = ExteriorAlgebra.ι R m
  rw [powPairToTensorAlgHom_ι, map_add, map_smul, map_smul, powPairFromTensor_powTensorY,
    powPairFromTensor_powTensorX, powPairY, powPairX]
  have hm : (ExteriorAlgebra.ι R m : ExteriorAlgebra R (Fin 2 → R)) =
      m 0 • ExteriorAlgebra.ι R (Pi.single 0 1) +
        m 1 • ExteriorAlgebra.ι R (Pi.single 1 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hm]
  rfl

/-- **The Koszul algebra of a pair of powers is the tensor product of the two one-variable
Koszul algebras.** The homomorphism `Koszul.powPairFromTensor : K_n ⊗_R K_t → K_{n,t}` is
bijective, with inverse the homomorphism `Koszul.powPairToTensor` of differential graded
algebras. -/
theorem powPairFromTensor_bijective (f : R) (n t : ℕ) :
    Function.Bijective (powPairFromTensor f n t).toAlgebraHom :=
  ⟨Function.LeftInverse.injective (g := powPairToTensorAlgHom f n t) fun x =>
      AlgHom.congr_fun (powPairToTensor_powPairFromTensor f n t) x,
    Function.RightInverse.surjective (g := powPairToTensorAlgHom f n t) fun z =>
      AlgHom.congr_fun (powPairFromTensor_powPairToTensor f n t) z⟩

end Composites

end Koszul
