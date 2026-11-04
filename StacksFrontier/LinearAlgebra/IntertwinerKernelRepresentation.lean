module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix

/-!
# The kernel of a surjective intertwiner of matrix representations

Let `ρ₁ : G → GL_a(K)` and `ρ₂ : G → GL_b(K)` be representations of a group over a field and let
`T : K^a → K^b` be a surjective linear map with `T ρ₁(g) = ρ₂(g) T` for every `g`. The kernel of
`T` is stable under `ρ₁`. In a basis it is a representation `κ : G → GL_c(K)` with
`c = a - b`, continuous when `ρ₁` is, and the trace of `ρ₁` is the sum of those of `ρ₂` and `κ`:
`tr ρ₁(g)ⁿ = tr ρ₂(g)ⁿ + tr κ(g)ⁿ` for every `g` and `n`. This is the representation-theoretic
input to the kernel of a surjection of lisse sheaves on a connected scheme.

The proof is matrix algebra. A right inverse `S` of `T` makes `E = 1 - S T` an idempotent with
image `ker T`. Factor it as `E = P Q` with `Q P = 1`. Then `κ(g) = Q ρ₁(g) P` is multiplicative
because `T P = 0`, and the trace splits along `1 = P Q + S T`.

## Main results

* `Stacks.LinearAlgebra.exists_mul_eq_one_and_mul_eq_of_mul_self_eq`: an idempotent matrix
  over a field factors through the identity of its rank.
* `Stacks.LinearAlgebra.exists_kernelRepresentation_trace_pow_eq_add`: the kernel
  representation of a surjective intertwiner, and the additivity of traces.
-/

@[expose] public section

open Matrix

namespace Stacks.LinearAlgebra

variable {K : Type*} [Field K]

/-- **An idempotent matrix over a field factors through the identity of its rank**: `E = P Q`
with `Q P = 1`, `P` being a basis of the image of `E` and `Q` the coordinates in it of `E v`. -/
theorem exists_mul_eq_one_and_mul_eq_of_mul_self_eq {a : ℕ} (E : Matrix (Fin a) (Fin a) K)
    (hE : E * E = E) :
    ∃ (c : ℕ) (P : Matrix (Fin a) (Fin c) K) (Q : Matrix (Fin c) (Fin a) K),
      Q * P = 1 ∧ P * Q = E := by
  classical
  set e := Matrix.toLin' E
  set W := LinearMap.range e
  let b := Module.finBasis K W
  have hfix : ∀ v : W, e v = v := by
    rintro ⟨v, u, rfl⟩
    show Matrix.toLin' E (Matrix.toLin' E u) = Matrix.toLin' E u
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hE]
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ e.rangeRestrict), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro w
    have h : e.rangeRestrict (W.subtype (b.equivFun.symm w)) = b.equivFun.symm w :=
      Subtype.ext (hfix _)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h, LinearEquiv.apply_symm_apply,
      LinearMap.id_apply]
  · rw [← LinearMap.toMatrix'_comp]
    conv_rhs => rw [← LinearMap.toMatrix'_toLin' E]
    congr 1
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Submodule.coe_subtype, LinearMap.codRestrict_apply]
    rfl

/-- If `P Q + S T = 1`, the trace of `R` splits as `tr (T R S) + tr (Q R P)`. -/
theorem trace_eq_trace_add_trace_of_mul_add_mul_eq_one {m n k : ℕ}
    (R : Matrix (Fin m) (Fin m) K) (P : Matrix (Fin m) (Fin k) K) (Q : Matrix (Fin k) (Fin m) K)
    (S : Matrix (Fin m) (Fin n) K) (T : Matrix (Fin n) (Fin m) K) (h : P * Q + S * T = 1) :
    R.trace = (T * R * S).trace + (Q * R * P).trace := by
  conv_lhs => rw [← Matrix.mul_one R, ← h, Matrix.mul_add, Matrix.trace_add, add_comm,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm (R * S) T,
    Matrix.trace_mul_comm (R * P) Q]
  simp only [Matrix.mul_assoc]

variable {G : Type*} [Group G] {a b : ℕ}

/-- **The kernel of a surjective intertwiner of matrix representations.** If `T : K^a → K^b`
is surjective and intertwines `ρ₁ : G → GL_a(K)` with `ρ₂ : G → GL_b(K)`, then the action of
`ρ₁` on the kernel of `T` is a representation `κ : G → GL_c(K)`, continuous when `ρ₁` is, and
`tr ρ₁(g)ⁿ = tr ρ₂(g)ⁿ + tr κ(g)ⁿ` for every `g ∈ G` and `n`. -/
theorem exists_kernelRepresentation_trace_pow_eq_add [TopologicalSpace G] [TopologicalSpace K]
    [IsTopologicalRing K] (ρ₁ : G →* GL (Fin a) K) (ρ₂ : G →* GL (Fin b) K)
    (hρ₁ : Continuous ρ₁) (T : Matrix (Fin b) (Fin a) K)
    (hT : ∀ g, T * (ρ₁ g).val = (ρ₂ g).val * T) (hsurj : Function.Surjective T.mulVec) :
    ∃ (c : ℕ) (κ : G →* GL (Fin c) K), Continuous κ ∧ ∀ (g : G) (n : ℕ),
      ((ρ₁ g).val ^ n).trace = ((ρ₂ g).val ^ n).trace + ((κ g).val ^ n).trace := by
  classical
  obtain ⟨s, hs⟩ := (Matrix.toLin' T).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 fun w => (hsurj w).imp fun _ hv => by rwa [Matrix.toLin'_apply])
  set S := LinearMap.toMatrix' s
  have hTS : T * S = 1 := by
    rw [← LinearMap.toMatrix'_toLin' T, ← LinearMap.toMatrix'_comp, hs,
      LinearMap.toMatrix'_id]
  set E : Matrix (Fin a) (Fin a) K := 1 - S * T
  have hE : E * E = E := by
    simp only [E, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, ← Matrix.mul_assoc T S T, hTS]
    abel
  obtain ⟨c, P, Q, hQP, hPQ⟩ := exists_mul_eq_one_and_mul_eq_of_mul_self_eq E hE
  have hTE : T * E = 0 := by
    simp only [E, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hTS, Matrix.one_mul,
      sub_self]
  have hTP : T * P = 0 :=
    calc T * P = T * P * (Q * P) := by rw [hQP, Matrix.mul_one]
      _ = T * (P * Q) * P := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPQ, hTE, Matrix.zero_mul]
  have hEρP : ∀ h, E * (ρ₁ h).val * P = (ρ₁ h).val * P := fun h => by
    simp only [E, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc S T, hT h,
      Matrix.mul_assoc, hTP, Matrix.mul_zero, sub_zero]
  let κM : G →* Matrix (Fin c) (Fin c) K :=
    { toFun := fun g => Q * (ρ₁ g).val * P
      map_one' := by rw [map_one, Units.val_one, Matrix.mul_one, hQP]
      map_mul' := fun g h => by
        rw [show Q * (ρ₁ g).val * P * (Q * (ρ₁ h).val * P) =
            Q * (ρ₁ g).val * (E * (ρ₁ h).val * P) by rw [← hPQ]; simp only [Matrix.mul_assoc],
          hEρP h, map_mul, Units.val_mul]
        simp only [Matrix.mul_assoc] }
  have hκM : ∀ g, κM g = Q * (ρ₁ g).val * P := fun _ => rfl
  refine ⟨c, κM.toHomUnits, ?_, fun g n => ?_⟩
  · have hc : ∀ (f : G → Matrix (Fin a) (Fin a) K), Continuous f →
        Continuous fun g => Q * f g * P := fun f hf =>
      (continuous_const.matrix_mul hf).matrix_mul continuous_const
    refine Units.continuous_iff.2 ⟨hc _ (Units.continuous_val.comp hρ₁), ?_⟩
    have : (fun g => ((κM.toHomUnits g)⁻¹ : (Matrix (Fin c) (Fin c) K)ˣ).val) =
        fun g => Q * ((ρ₁ g)⁻¹ : GL (Fin a) K).val * P := by
      funext g
      rw [← map_inv, MonoidHom.coe_toHomUnits, hκM, map_inv]
    rw [this]
    exact hc _ (Units.continuous_coe_inv.comp hρ₁)
  · rw [MonoidHom.coe_toHomUnits, ← map_pow, hκM, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← map_pow ρ₁, ← map_pow ρ₂,
      trace_eq_trace_add_trace_of_mul_add_mul_eq_one (ρ₁ (g ^ n)).val P Q S T
        (by simp [hPQ, E]), hT, Matrix.mul_assoc, hTS, Matrix.mul_one]

end Stacks.LinearAlgebra

end
