module

public import StacksFrontier.NumberTheory.Padics.LAdicOuterAction
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Characters of finite order on the geometric fundamental group

Let `Γ` be a compact group (the arithmetic fundamental group `π₁(X₀)` of a variety over a finite
field), `H ⊆ Γ` a subgroup (the geometric fundamental group `π₁(X̄)`) and `φ ∈ Γ` (a Frobenius
element).  A continuous character `χ : Γ → Kˣ` with values in a complete ultrametric field over
`ℚ_ℓ` has finite order on `H` as soon as `H` has no nonzero continuous homomorphism to `K`
invariant under conjugation by `φ`.

This is the group-theoretic half of Deligne's theorem that the determinant of a lisse sheaf has
finite order on the geometric fundamental group (Weil II, 1.3.4): a power `χᵐ` takes values in
the disc `‖x - 1‖ < ℓ⁻¹`, and `ψ = log ∘ χᵐ` is a continuous homomorphism `H → K`, invariant under
conjugation by `φ` because `K` is commutative.  The remaining input, that a Frobenius-invariant
homomorphism `π₁(X̄) → ℚ_ℓ` vanishes, is the statement that `1` is not an eigenvalue of Frobenius
on `H¹(X̄, ℚ_ℓ)`.

## Main results

* `Stacks.LAdic.discSubgroup`: the units in the disc `‖x - 1‖ < ℓ⁻¹`.
* `Stacks.LAdic.norm_ladicLog_sub_ladicLog_le`: the logarithm is `1`-Lipschitz on that disc.
* `Stacks.LAdic.exists_pow_eq_one_of_forall_conj_invariant`: the finiteness criterion.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.3.4.
-/

@[expose] public noncomputable section

open Filter Topology

namespace Stacks.LAdic

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NormedAlgebra ℚ_[ℓ] K]

omit [Fact ℓ.Prime] [NormedAlgebra ℚ_[ℓ] K] in
/-- An element of the disc `‖x - 1‖ < 1` has norm `1`. -/
theorem norm_eq_one_of_norm_sub_one_lt {x : K} (hx : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h : ‖x - 1‖ ≠ ‖(1 : K)‖ := hx.ne.trans_eq norm_one.symm
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h
  rw [sub_add_cancel, norm_one] at this
  rw [this, max_eq_right hx.le]

variable (ℓ K) in
/-- The units of `K` in the disc `‖x - 1‖ < ℓ⁻¹`. -/
def discSubgroup : Subgroup Kˣ where
  carrier := {x | ‖(x : K) - 1‖ < (ℓ : ℝ)⁻¹}
  one_mem' := by
    change ‖((1 : Kˣ) : K) - 1‖ < (ℓ : ℝ)⁻¹
    rw [Units.val_one, sub_self, norm_zero]
    exact inv_pos.mpr (by exact_mod_cast (Fact.out : ℓ.Prime).pos)
  mul_mem' {a b} ha hb := by
    change ‖((a * b : Kˣ) : K) - 1‖ < (ℓ : ℝ)⁻¹
    have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    have e : ((a * b : Kˣ) : K) - 1 = ((a : K) - 1) * ((b : K) - 1) + ((a : K) - 1) +
        ((b : K) - 1) := by rw [Units.val_mul]; ring
    rw [e]
    have hb1 : ‖(b : K) - 1‖ ≤ 1 := hb.le.trans (inv_le_one_of_one_le₀ hℓ.le)
    have hX : ‖((a : K) - 1) * ((b : K) - 1)‖ ≤ ‖(a : K) - 1‖ :=
      (norm_mul _ _).trans_le (mul_le_of_le_one_right (norm_nonneg _) hb1)
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hX le_rfl)) le_rfl)) (max_lt ha hb)
  inv_mem' {a} ha := by
    have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    exact (norm_inv_sub_one_le (ha.trans (inv_lt_one_of_one_lt₀ hℓ))).trans_lt ha

variable [CompleteSpace K]

/-- The logarithm is `1`-Lipschitz on the disc `‖x - 1‖ < ℓ⁻¹` of `K`. -/
theorem norm_ladicLog_sub_ladicLog_le {x y : K} (hx : ‖x - 1‖ < (ℓ : ℝ)⁻¹)
    (hy : ‖y - 1‖ < (ℓ : ℝ)⁻¹) : ‖ladicLog ℓ x - ladicLog ℓ y‖ ≤ ‖x - y‖ := by
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hy1 : ‖y‖ = 1 := norm_eq_one_of_norm_sub_one_lt (hy.trans (inv_lt_one_of_one_lt₀ hℓ))
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  have hxy : ‖x / y - 1‖ = ‖x - y‖ := by
    rw [div_sub_one hy0, norm_div, hy1, div_one]
  have hxy' : ‖x - y‖ < (ℓ : ℝ)⁻¹ := by
    rw [← sub_sub_sub_cancel_right x y 1]
    exact lt_of_le_of_lt (by
      rw [sub_eq_add_neg, ← norm_neg (y - 1)]
      exact IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
  have hsplit : ladicLog ℓ x = ladicLog ℓ (x / y) + ladicLog ℓ y := by
    rw [← ladicLog_mul_of_commute (Commute.all _ _) (hxy ▸ hxy'.le) hy.le, div_mul_cancel₀ _ hy0]
  rw [hsplit, add_sub_cancel_right, ← hxy]
  exact norm_ladicLog_le (hxy ▸ hxy'.le)

/-- The logarithm is continuous on the disc `‖x - 1‖ < ℓ⁻¹` of `K`. -/
theorem continuousOn_ladicLog :
    ContinuousOn (ladicLog ℓ : K → K) {x | ‖x - 1‖ < (ℓ : ℝ)⁻¹} := by
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx y hy => ?_).continuousOn
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact norm_ladicLog_sub_ladicLog_le hx hy

variable (ℓ) in
include ℓ in
/-- **Finite order on the geometric fundamental group** (the group-theoretic half of Weil II,
1.3.4).  Let `Γ` be a compact group, `H ⊆ Γ` a subgroup and `φ ∈ Γ`.  If every continuous
homomorphism `H → K` invariant under conjugation by `φ` vanishes, then every continuous character
`χ : Γ → Kˣ` has finite order on `H`. -/
theorem exists_pow_eq_one_of_forall_conj_invariant {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (H : Subgroup Γ) (φ : Γ)
    (hH : ∀ ψ : H → K, (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
      (∀ a b : H, (b : Γ) = φ * a * φ⁻¹ → ψ b = ψ a) → ψ = 0)
    (χ : Γ →* Kˣ) (hχ : Continuous fun g => (χ g : K)) :
    ∃ m : ℕ, 0 < m ∧ ∀ h ∈ H, χ h ^ m = 1 := by
  set U : Subgroup Γ := (discSubgroup ℓ K).comap χ
  have hUopen : IsOpen (U : Set Γ) := by
    show IsOpen {g : Γ | ‖(χ g : K) - 1‖ < (ℓ : ℝ)⁻¹}
    exact isOpen_lt (continuous_norm.comp (hχ.sub continuous_const)) continuous_const
  have : (discSubgroup ℓ K).Normal := Subgroup.normal_of_comm _
  have : U.Normal := Subgroup.Normal.comap inferInstance χ
  have : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUopen
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set m := U.index
  have hm : 0 < m := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hdisc : ∀ g : Γ, ‖((χ g : K)) ^ m - 1‖ < (ℓ : ℝ)⁻¹ := fun g => by
    have := U.pow_index_mem g
    rw [Subgroup.mem_comap] at this
    change ‖((χ (g ^ m) : Kˣ) : K) - 1‖ < _ at this
    rwa [map_pow, Units.val_pow_eq_pow_val] at this
  let ψ : H → K := fun h => ladicLog ℓ ((χ h : K) ^ m)
  have hadd : ∀ a b, ψ (a * b) = ψ a + ψ b := fun a b => by
    simp only [ψ, Subgroup.coe_mul, map_mul, Units.val_mul, mul_pow]
    exact ladicLog_mul_of_commute (Commute.all _ _) (hdisc a).le (hdisc b).le
  have hcont : Continuous ψ :=
    continuousOn_ladicLog.comp_continuous ((hχ.comp continuous_subtype_val).pow m) fun h => hdisc h
  have hinv : ∀ a b : H, (b : Γ) = φ * a * φ⁻¹ → ψ b = ψ a := fun a b hab => by
    have e : χ (φ * a * φ⁻¹) = χ a := by
      rw [map_mul, map_mul, map_inv, mul_comm (χ φ), mul_assoc, mul_inv_cancel, mul_one]
    simp only [ψ, hab, e]
  refine ⟨m, hm, fun h hh => Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact eq_one_of_ladicLog_eq_zero (hdisc h) (congrFun (hH ψ hadd hcont hinv) ⟨h, hh⟩)

end Stacks.LAdic
