module

public import Mathlib.Data.Nat.ChineseRemainder
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.ProcyclicGroupAlgebra
public import StacksFrontier.NumberTheory.TraceFormula.CommutativeExample

/-!
# `Ẑ^{(q)}` is procyclic

The natural numbers are dense in `Ẑ^{(q)} = ∏_{ℓ ∤ q} ℤ_ℓ`: a basic open neighbourhood restricts
only finitely many coordinates, each to a coset of `ℓ^e ℤ_ℓ`, and the Chinese remainder theorem
produces a natural number in all of them. Consequently, for a topological group `G` isomorphic to
`Ẑ^{(q)}` (written multiplicatively) the element `σ` corresponding to `1` generates every finite
quotient of `G`, and for every prime `ℓ ∤ q` the reductions `Ẑ^{(q)} → ℤ_ℓ → ℤ/ℓ^e` give quotients
of `G` with open kernels sending `σ` to `1`. These are the hypotheses of
`Stacks.GroupHomology.Procyclic`.

## Main results

* `Stacks.TraceFormula.denseRange_natCast_restrictedProfiniteIntegers`: `ℕ` is dense in
  `Ẑ^{(q)}`.
* `Stacks.TraceFormula.generatesQuotients_of_continuousMulEquiv` and
  `Stacks.TraceFormula.hasPrimePowerQuotients_of_continuousMulEquiv`: the hypotheses of
  `Stacks.GroupHomology.Procyclic` for a group isomorphic to `Ẑ^{(q)}`.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
-/

@[expose] public noncomputable section

namespace Stacks.TraceFormula

open Topology

attribute [local instance] isUltrametricDist_padicInt

/-- `y ∈ ℤ_p` maps to `0` in `ℤ/p^e` iff `‖y‖ ≤ p^(-e)`. -/
private theorem toZModPow_eq_zero_iff_norm_le (p : ℕ) [Fact p.Prime] (e : ℕ) (y : ℤ_[p]) :
    PadicInt.toZModPow e y = 0 ↔ ‖y‖ ≤ (p : ℝ) ^ (-e : ℤ) := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, PadicInt.norm_le_pow_iff_mem_span_pow]

/-- The kernel of `ℤ_p → ℤ/p^e` is open. -/
public theorem isOpen_ker_toZModPow (p : ℕ) [Fact p.Prime] (e : ℕ) :
    IsOpen {y : ℤ_[p] | PadicInt.toZModPow e y = 0} := by
  have : {y : ℤ_[p] | PadicInt.toZModPow e y = 0} =
      Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-e : ℤ)) := by
    ext y
    rw [Set.mem_setOf_eq, toZModPow_eq_zero_iff_norm_le, Metric.mem_closedBall, dist_zero_right]
  rw [this]
  exact IsUltrametricDist.isOpen_closedBall _
    (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _).ne'

/-- `y` and `z` with the same image in `ℤ/p^e` are close: the fibres of `ℤ_p → ℤ/p^e` are open. -/
public theorem isOpen_fiber_toZModPow (p : ℕ) [Fact p.Prime] (e : ℕ) (x : ℤ_[p]) :
    IsOpen {y : ℤ_[p] | PadicInt.toZModPow e y = PadicInt.toZModPow e x} := by
  have : {y : ℤ_[p] | PadicInt.toZModPow e y = PadicInt.toZModPow e x} =
      (fun y => y - x) ⁻¹' {y : ℤ_[p] | PadicInt.toZModPow e y = 0} := by
    ext y
    simp [sub_eq_zero]
  rw [this]
  exact (isOpen_ker_toZModPow p e).preimage (continuous_id.sub continuous_const)

/-- Every neighbourhood of `x ∈ ℤ_p` contains a fibre of `ℤ_p → ℤ/p^e`. -/
public theorem exists_fiber_subset (p : ℕ) [Fact p.Prime] {x : ℤ_[p]} {s : Set ℤ_[p]}
    (hs : s ∈ 𝓝 x) :
    ∃ e : ℕ, {y : ℤ_[p] | PadicInt.toZModPow e y = PadicInt.toZModPow e x} ⊆ s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨e, he⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp)
  refine ⟨e, fun y hy => hball ?_⟩
  have hmem := (toZModPow_eq_zero_iff_norm_le p e (y - x)).1
    (by rw [map_sub, sub_eq_zero]; exact hy)
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖y - x‖ ≤ (p : ℝ) ^ (-e : ℤ) := hmem
    _ = (p : ℝ)⁻¹ ^ e := by rw [zpow_neg, zpow_natCast, inv_pow]
    _ < ε := he

/-- **The natural numbers are dense in `Ẑ^{(q)} = ∏_{ℓ ∤ q} ℤ_ℓ`.** -/
public theorem denseRange_natCast_restrictedProfiniteIntegers (q : ℕ) :
    DenseRange (Nat.cast : ℕ → RestrictedProfiniteIntegers q) := by
  classical
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro x
  rw [mem_closure_iff_nhds]
  intro W hW
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  choose e he using fun i : CoprimePrimes q => exists_fiber_subset i.1 (ht i)
  let a : CoprimePrimes q → ℕ := fun i => (PadicInt.toZModPow (e i) (x i)).val
  let s : CoprimePrimes q → ℕ := fun i => i.1 ^ e i
  have hs : ∀ i ∈ I, s i ≠ 0 := fun i _ => pow_ne_zero _ i.2.1.ne_zero
  have pp : Set.Pairwise (I : Set (CoprimePrimes q)) (Function.onFun Nat.Coprime s) := by
    intro i _ j _ hij
    exact Nat.coprime_pow_primes _ _ i.2.1 j.2.1 fun h => hij (Subtype.ext h)
  obtain ⟨n, hn⟩ := Nat.chineseRemainderOfFinset a s I hs pp
  refine ⟨(n : RestrictedProfiniteIntegers q), hsub fun i hi => he i ?_, n, rfl⟩
  simp only [Set.mem_setOf_eq, Pi.natCast_apply, map_natCast]
  have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (hn i hi)
  rw [this]
  exact ZMod.natCast_zmod_val _

section Transfer

open Stacks.GroupHomology.Procyclic

variable {q : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (e : Multiplicative (RestrictedProfiniteIntegers q) ≃ₜ* G)

/-- The element of `G` corresponding to `1 ∈ Ẑ^{(q)}`. -/
public def generatorOf : G := e (Multiplicative.ofAdd 1)

omit [IsTopologicalGroup G] in
/-- The `n`-th power of the generator corresponds to `n ∈ Ẑ^{(q)}`. -/
public theorem generatorOf_pow (n : ℕ) :
    generatorOf e ^ n = e (Multiplicative.ofAdd (n : RestrictedProfiniteIntegers q)) := by
  rw [generatorOf, ← map_pow, ← ofAdd_nsmul, nsmul_one]

/-- **The element corresponding to `1` generates every finite quotient of `G ≅ Ẑ^{(q)}`.** -/
public theorem generatesQuotients_of_continuousMulEquiv :
    GeneratesQuotients (generatorOf e) := by
  intro U g
  -- the open neighbourhood `g U` of `g`, pulled back to `Ẑ^{(q)}`
  let W : Set (RestrictedProfiniteIntegers q) :=
    {x | g⁻¹ * e (Multiplicative.ofAdd x) ∈ (U : Subgroup G)}
  have hW : IsOpen W :=
    U.isOpen'.preimage (continuous_const.mul (e.continuous.comp continuous_ofAdd))
  have hx : Multiplicative.toAdd (e.symm g) ∈ W := by
    simp [W]
  obtain ⟨n, hn⟩ := (denseRange_natCast_restrictedProfiniteIntegers q).exists_mem_open hW
    ⟨_, hx⟩
  refine ⟨n, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq, generatorOf_pow]
  exact hn

/-- The reduction `G ≅ Ẑ^{(q)} → ℤ_ℓ → ℤ/ℓ^e` at a prime `ℓ ∤ q`. -/
public def primePowerQuotient (ℓ : CoprimePrimes q) (k : ℕ) :
    G →* Multiplicative (ZMod (ℓ.1 ^ k)) where
  toFun g := Multiplicative.ofAdd (PadicInt.toZModPow k (Multiplicative.toAdd (e.symm g) ℓ))
  map_one' := by simp
  map_mul' g h := by simp [← ofAdd_add]

omit [IsTopologicalGroup G] in
/-- On `e x`, the reduction is the image of the `ℓ`-coordinate of `x` in `ℤ/ℓ^k`. -/
public theorem primePowerQuotient_apply (ℓ : CoprimePrimes q) (k : ℕ)
    (x : RestrictedProfiniteIntegers q) :
    primePowerQuotient e ℓ k (e (Multiplicative.ofAdd x)) =
      Multiplicative.ofAdd (PadicInt.toZModPow k (x ℓ)) := by
  simp [primePowerQuotient]

omit [IsTopologicalGroup G] in
/-- The reduction sends the generator to `1 ∈ ℤ/ℓ^k`. -/
public theorem primePowerQuotient_generatorOf (ℓ : CoprimePrimes q) (k : ℕ) :
    primePowerQuotient e ℓ k (generatorOf e) = Multiplicative.ofAdd 1 := by
  rw [generatorOf, primePowerQuotient_apply]
  simp

omit [IsTopologicalGroup G] in
/-- The kernel of `G ≅ Ẑ^{(q)} → ℤ/ℓ^e` is open. -/
public theorem isOpen_ker_primePowerQuotient (ℓ : CoprimePrimes q) (k : ℕ) :
    IsOpen ((primePowerQuotient e ℓ k).ker : Set G) := by
  have : ((primePowerQuotient e ℓ k).ker : Set G) =
      (fun g => Multiplicative.toAdd (e.symm g) ℓ) ⁻¹'
        {y : ℤ_[ℓ.1] | PadicInt.toZModPow k y = 0} := by
    ext g
    simp [primePowerQuotient, MonoidHom.mem_ker]
  rw [this]
  exact (isOpen_ker_toZModPow ℓ.1 k).preimage
    ((continuous_apply ℓ).comp (continuous_toAdd.comp e.symm.continuous))

omit [IsTopologicalGroup G] in
/-- **The prime power quotients of `G ≅ Ẑ^{(q)}` at a prime `ℓ ∤ q`.** -/
public theorem hasPrimePowerQuotients_of_continuousMulEquiv (ℓ : CoprimePrimes q) :
    HasPrimePowerQuotients (generatorOf e) ℓ.1 := by
  intro k
  exact ⟨primePowerQuotient e ℓ k, isOpen_ker_primePowerQuotient e ℓ k,
    primePowerQuotient_generatorOf e ℓ k⟩

end Transfer

end Stacks.TraceFormula

end
