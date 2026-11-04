module

public import StacksFrontier.NumberTheory.Padics.LAdicOuterAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalMonodromyGroupTheory

/-!
# Integral congruence subgroups land in the `ℓ`-adic disc

The units of `M_n(K)` in the disc `‖g - 1‖ < ℓ⁻¹` form a subgroup
(`Stacks.LAdic.matrixDiscSubgroup`), and the congruence subgroup `Γ(ℓ²) ⊆ GL_r(ℤ_ℓ)`
(`Stacks.EtaleCohomology.congruenceSubgroup`) maps into it under any normed `ℚ_ℓ`-algebra `K`.
This is how a continuous `ℓ`-adic representation, through its integral model, enters the
hypotheses of `Stacks.LAdic.exists_pow_eq_exp_mul_exp_of_normalizes`: the preimage of `Γ(ℓ²)` is
an open normal subgroup on which the representation takes values in the disc.

## Main results

* `Stacks.LAdic.matrixDiscSubgroup`
* `Stacks.LAdic.toUnitsMatrix`: `GL_r(ℤ_ℓ) → GL_r(K)`.
* `Stacks.LAdic.toUnitsMatrix_mem_matrixDiscSubgroup`
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.LAdic

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K]
  {n : Type*} [Fintype n] [DecidableEq n]

variable (ℓ K n) in
/-- The units of `M_n(K)` in the disc `‖g - 1‖ < ℓ⁻¹`. -/
def matrixDiscSubgroup : Subgroup (Matrix n n K)ˣ where
  carrier := {g | ‖(g : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹}
  one_mem' := by
    change ‖((1 : (Matrix n n K)ˣ) : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹
    rw [Units.val_one, sub_self, norm_zero]
    have : (0 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    positivity
  mul_mem' {a b} ha hb := by
    change ‖((a * b : (Matrix n n K)ˣ) : Matrix n n K) - 1‖ < (ℓ : ℝ)⁻¹
    have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    have hb1 : ‖(b : Matrix n n K) - 1‖ ≤ 1 := hb.le.trans (inv_le_one_of_one_le₀ hℓ.le)
    have e : ((a * b : (Matrix n n K)ˣ) : Matrix n n K) - 1 =
        ((a : Matrix n n K) - 1) * ((b : Matrix n n K) - 1) + ((a : Matrix n n K) - 1) +
          ((b : Matrix n n K) - 1) := by rw [Units.val_mul]; noncomm_ring
    rw [e]
    have hX : ‖((a : Matrix n n K) - 1) * ((b : Matrix n n K) - 1)‖ ≤ ‖(a : Matrix n n K) - 1‖ :=
      (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hb1)
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hX le_rfl)) le_rfl)) (max_lt ha hb)
  inv_mem' {a} ha := by
    have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    exact (norm_inv_sub_one_le (ha.trans (inv_lt_one_of_one_lt₀ hℓ))).trans_lt ha

variable (K) in
/-- The image of an integral invertible matrix in `GL_n(K)`. -/
def toUnitsMatrix : GL n ℤ_[ℓ] →* (Matrix n n K)ˣ :=
  Units.map ((algebraMap ℚ_[ℓ] K).comp (PadicInt.Coe.ringHom (p := ℓ))).mapMatrix.toMonoidHom

omit [IsUltrametricDist K] in
/-- The underlying matrix of `toUnitsMatrix K g` is the entrywise image of `g` in `K`. -/
theorem coe_toUnitsMatrix (g : GL n ℤ_[ℓ]) :
    ((toUnitsMatrix K g : (Matrix n n K)ˣ) : Matrix n n K) =
      (g : Matrix n n ℤ_[ℓ]).map fun x => algebraMap ℚ_[ℓ] K x := rfl

/-- The image in `GL_r(K)` of an element of the congruence subgroup `Γ(ℓ²)` lies in the disc
`matrixDiscSubgroup ℓ K (Fin r)`. -/
theorem toUnitsMatrix_mem_matrixDiscSubgroup {r : ℕ} {g : GL (Fin r) ℤ_[ℓ]}
    (hg : g ∈ Stacks.EtaleCohomology.congruenceSubgroup ℓ r 2) :
    toUnitsMatrix K g ∈ matrixDiscSubgroup ℓ K (Fin r) := by
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  show ‖((toUnitsMatrix K g : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) - 1‖ <
    (ℓ : ℝ)⁻¹
  have hlt : ((ℓ : ℝ)⁻¹) ^ 2 < (ℓ : ℝ)⁻¹ := by
    rw [sq]; exact mul_lt_of_lt_one_left (by positivity) (inv_lt_one_of_one_lt₀ hℓ)
  refine lt_of_le_of_lt ?_ hlt
  rw [norm_le_iff (by positivity)]
  intro i j
  obtain ⟨c, hc⟩ := hg i j
  have hentry : (((toUnitsMatrix K g : (Matrix (Fin r) (Fin r) K)ˣ) : Matrix (Fin r) (Fin r) K) -
      1) i j = algebraMap ℚ_[ℓ] K (((g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) i j : ℤ_[ℓ]) := by
    rw [coe_toUnitsMatrix, Matrix.sub_apply, Matrix.map_apply, Matrix.sub_apply, PadicInt.coe_sub,
      map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hentry, norm_algebraMap', hc, PadicInt.coe_mul, norm_mul, PadicInt.coe_pow, norm_pow,
    PadicInt.coe_natCast, Padic.norm_p]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one c)

end Stacks.LAdic
