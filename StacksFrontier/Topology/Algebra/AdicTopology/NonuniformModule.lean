module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.ScalarContinuity

@[expose] public section

/-!
# A linearly topologized module whose topology is not uniformly adic

Stacks Project, Chapter 87 "Formal Spaces", Tag 0AMR.

Tag 0AMR observes that for a linearly topologized module `M` over a linearly topologized ring
`R`, continuity of the scalar multiplication only gives the *pointwise* statement that for every
`x : M` and every open submodule `M μ` there is an open ideal `I λ` with `I λ • x ⊆ M μ`; it does
*not* give an open ideal `I λ` with `I λ • M ⊆ M μ`. The counterexample given there is
`R = k[[t]]` with the `t`-adic topology and `M = ⨁_{n ∈ ℕ} R` with the fundamental system of
open submodules
`M m = ⨁_{n ∈ ℕ} t ^ (n * m) R`.

This file constructs that example and proves both halves: `M` really is a linearly topologized
`R`-module (so the pointwise condition holds, by every element having finite support), and the
uniform condition fails for every `m ≥ 1`.

## Main definitions

* `TopologicalModule.Nonuniform.tIdeal`: the ideal `(t)` of `k[[t]]`, whose adic topology is the
  `t`-adic one.
* `TopologicalModule.Nonuniform.coordinateSubmodule`: the submodule
  `M m = ⨁_{n ∈ ℕ} t ^ (n * m) k[[t]]` of `⨁_{n ∈ ℕ} k[[t]]`.

## Main results

* `TopologicalModule.Nonuniform.exists_pow_X_smul_mem`: the pointwise condition, that for every
  `m` and every `x` there is a `j` with `t ^ j • x ∈ M m`.
* `TopologicalModule.Nonuniform.isTopologicalAddGroup`,
  `TopologicalModule.Nonuniform.continuousSMul` and
  `TopologicalModule.Nonuniform.isLinearTopology`: the submodules `coordinateSubmodule` are a
  fundamental system of open submodules for a linear topology on `⨁_{n ∈ ℕ} k[[t]]`. Continuity
  of the scalar multiplication is obtained from the pointwise condition through the criterion
  `TopologicalModule.continuousSMul_iff_forall_exists_smul_mem`.
* `TopologicalModule.Nonuniform.not_exists_forall_pow_X_smul_mem` and
  `TopologicalModule.Nonuniform.not_exists_isOpen_ideal_smul_mem`: the uniform condition fails,
  both for the basic open ideals `(t ^ j)` and for an arbitrary open ideal.
* `TopologicalModule.Nonuniform.exists_isLinearTopology_not_exists_isOpen_ideal_smul_mem`: the
  two halves packaged as the existence statement asserted by the source.

## References

* [Stacks Project, Tag 0AMR](https://stacks.math.columbia.edu/tag/0AMR)
-/

namespace TopologicalModule.Nonuniform

open Filter PowerSeries
open scoped Pointwise Topology

variable (k : Type*) [Field k]

/-- The ideal `(t)` of the power series ring `k[[t]]`; its adic topology is the `t`-adic one. -/
noncomputable def tIdeal : Ideal (PowerSeries k) := Ideal.span {(X : PowerSeries k)}

/-- Membership in a power of `(t)` is divisibility by a power of `t`. -/
lemma mem_tIdeal_pow_iff {j : ℕ} {f : PowerSeries k} :
    f ∈ tIdeal k ^ j ↔ (X : PowerSeries k) ^ j ∣ f := by
  rw [tIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- `k[[t]]` carries the `t`-adic topology throughout this file. -/
noncomputable local instance instTopologicalSpacePowerSeries : TopologicalSpace (PowerSeries k) :=
  (tIdeal k).adicTopology

/-- `k[[t]]` with the `t`-adic topology is a nonarchimedean ring. -/
local instance instNonarchimedeanRingPowerSeries : NonarchimedeanRing (PowerSeries k) :=
  (tIdeal k).nonarchimedean

/-- For the `t`-adic topology on `k[[t]]` the powers of `(t)` are a basis of neighbourhoods
of zero. -/
lemma hasBasis_nhds_zero_powerSeries :
    (𝓝 (0 : PowerSeries k)).HasBasis (fun _ : ℕ ↦ True)
      fun j ↦ ((tIdeal k ^ j : Ideal (PowerSeries k)) : Set (PowerSeries k)) :=
  (tIdeal k).hasBasis_nhds_zero_adic

/-- The submodule `M m = ⨁_{n ∈ ℕ} t ^ (n * m) k[[t]]` of `M = ⨁_{n ∈ ℕ} k[[t]]`: the
elements whose `n`-th coordinate is divisible by `t ^ (n * m)`. -/
def coordinateSubmodule (m : ℕ) : Submodule (PowerSeries k) (ℕ →₀ PowerSeries k) where
  carrier := {x | ∀ n : ℕ, (X : PowerSeries k) ^ (n * m) ∣ x n}
  add_mem' hx hy n := by simpa using dvd_add (hx n) (hy n)
  zero_mem' n := by simp
  smul_mem' c x hx n := by simpa using (hx n).mul_left c

/-- An element `x` lies in `M m` if and only if its `n`-th coordinate is divisible by
`t ^ (n * m)` for every `n`. -/
@[simp]
lemma mem_coordinateSubmodule {m : ℕ} {x : ℕ →₀ PowerSeries k} :
    x ∈ coordinateSubmodule k m ↔ ∀ n : ℕ, (X : PowerSeries k) ^ (n * m) ∣ x n :=
  Iff.rfl

/-- The family `M m` is decreasing in `m`. -/
lemma coordinateSubmodule_mono {m m' : ℕ} (h : m ≤ m') :
    coordinateSubmodule k m' ≤ coordinateSubmodule k m :=
  fun _ hx n ↦ dvd_trans (pow_dvd_pow _ (Nat.mul_le_mul_left n h)) (hx n)

/-- If `f` is divisible by `t ^ j` and `j ≥ n * m` for every `n` in the support of `x`, then
`f • x` lies in `M m`. This is the finite-support argument of the source. -/
lemma smul_mem_coordinateSubmodule {m j : ℕ} {f : PowerSeries k} (hf : (X : PowerSeries k) ^ j ∣ f)
    {x : ℕ →₀ PowerSeries k} (hx : ∀ n ∈ x.support, n * m ≤ j) :
    f • x ∈ coordinateSubmodule k m := by
  intro n
  rw [Finsupp.smul_apply, smul_eq_mul]
  by_cases hxn : x n = 0
  · simp [hxn]
  · exact dvd_mul_of_dvd_left ((pow_dvd_pow _ (hx n (by simpa))).trans hf) _

/-- For every `m` and `x` there is a `j` such that every multiple of `t ^ j` sends `x` into
`M m`, because `x` has finite support. -/
private lemma exists_forall_pow_X_dvd_smul_mem (m : ℕ) (x : ℕ →₀ PowerSeries k) :
    ∃ j : ℕ, ∀ f : PowerSeries k, (X : PowerSeries k) ^ j ∣ f → f • x ∈ coordinateSubmodule k m :=
  ⟨x.support.sup id * m, fun _ hf ↦ smul_mem_coordinateSubmodule k hf
    fun _ hn ↦ Nat.mul_le_mul_right m (Finset.le_sup (f := id) hn)⟩

/-- The pointwise condition of the source: for every `m` and every `x ∈ ⨁_{n ∈ ℕ} k[[t]]` there
is a `j` with `t ^ j • x ∈ M m`. It holds because `x` has only finitely many nonzero
coordinates. -/
@[stacks 0AMR "nonuniform_module_example"]
theorem exists_pow_X_smul_mem (m : ℕ) (x : ℕ →₀ PowerSeries k) :
    ∃ j : ℕ, (X : PowerSeries k) ^ j • x ∈ coordinateSubmodule k m :=
  (exists_forall_pow_X_dvd_smul_mem k m x).imp fun _ h ↦ h _ dvd_rfl

/-- The pointwise condition of `TopologicalModule.continuousSMul_iff_forall_exists_smul_mem` for
this example: `(t ^ j) • x ⊆ M m` for `j` large enough, again by finiteness of the support. -/
lemma exists_forall_mem_smul_mem (m : ℕ) (x : ℕ →₀ PowerSeries k) :
    ∃ j : ℕ, ∀ f ∈ tIdeal k ^ j, f • x ∈ coordinateSubmodule k m :=
  (exists_forall_pow_X_dvd_smul_mem k m x).imp fun _ h _ hf ↦ h _ ((mem_tIdeal_pow_iff k).mp hf)

/-- The submodules `M m` form a basis of neighbourhoods of zero for a module topology on
`⨁_{n ∈ ℕ} k[[t]]`. -/
lemma submodulesBasis_coordinateSubmodule : SubmodulesBasis (coordinateSubmodule k) where
  inter m m' := ⟨max m m', le_inf (coordinateSubmodule_mono k (le_max_left m m'))
    (coordinateSubmodule_mono k (le_max_right m m'))⟩
  smul x m := by
    obtain ⟨j, hj⟩ := exists_forall_mem_smul_mem k m x
    exact mem_of_superset ((hasBasis_nhds_zero_powerSeries k).mem_of_mem (i := j) trivial) hj

/-- The topology on `⨁_{n ∈ ℕ} k[[t]]` defined by the fundamental system `M m`. -/
noncomputable local instance instTopologicalSpaceNonuniform :
    TopologicalSpace (ℕ →₀ PowerSeries k) :=
  (submodulesBasis_coordinateSubmodule k).topology

/-- The submodules `M m` are a fundamental system of neighbourhoods of zero. -/
theorem hasBasis_nhds_zero_coordinateSubmodule :
    (𝓝 (0 : ℕ →₀ PowerSeries k)).HasBasis (fun _ : ℕ ↦ True)
      fun m ↦ (coordinateSubmodule k m : Set (ℕ →₀ PowerSeries k)) := by
  refine ⟨fun U ↦ ?_⟩
  rw [(submodulesBasis_coordinateSubmodule k).toModuleFilterBasis.toAddGroupFilterBasis
    |>.nhds_zero_hasBasis.mem_iff]
  constructor
  · rintro ⟨-, ⟨i, rfl⟩, h⟩
    exact ⟨i, trivial, h⟩
  · rintro ⟨i, -, h⟩
    exact ⟨_, ⟨i, rfl⟩, h⟩

/-- Addition on `⨁_{n ∈ ℕ} k[[t]]` is continuous: this is the half of the tag that is
automatic. -/
theorem isTopologicalAddGroup : IsTopologicalAddGroup (ℕ →₀ PowerSeries k) :=
  (submodulesBasis_coordinateSubmodule k).toModuleFilterBasis.toAddGroupFilterBasis
    |>.isTopologicalAddGroup

attribute [local instance] isTopologicalAddGroup

/-- Scalar multiplication `k[[t]] × M → M` is continuous: this is the criterion
`TopologicalModule.continuousSMul_iff_forall_exists_smul_mem` applied to the pointwise condition
`TopologicalModule.Nonuniform.exists_forall_mem_smul_mem`. -/
theorem continuousSMul : ContinuousSMul (PowerSeries k) (ℕ →₀ PowerSeries k) :=
  (TopologicalModule.continuousSMul_iff_forall_exists_smul_mem (fun j ↦ tIdeal k ^ j)
      (coordinateSubmodule k) (hasBasis_nhds_zero_powerSeries k)
      (hasBasis_nhds_zero_coordinateSubmodule k)).mpr fun x m ↦ exists_forall_mem_smul_mem k m x

/-- `M = ⨁_{n ∈ ℕ} k[[t]]` with this topology is a linearly topologized
`k[[t]]`-module. -/
theorem isLinearTopology : IsLinearTopology (PowerSeries k) (ℕ →₀ PowerSeries k) :=
  IsLinearTopology.mk_of_hasBasis _ (hasBasis_nhds_zero_coordinateSubmodule k)

/-- `t ^ j` is not divisible by `t ^ i` when `j < i`. -/
lemma not_pow_X_dvd_pow_X {i j : ℕ} (h : j < i) :
    ¬ (X : PowerSeries k) ^ i ∣ (X : PowerSeries k) ^ j := by
  rw [X_pow_dvd_iff]
  exact fun hdvd ↦ one_ne_zero (α := k) (by simpa using hdvd j h)

/-- The uniform condition fails: for `m ≥ 1` there is no `j` with `t ^ j • M ⊆ M m`. -/
@[stacks 0AMR "nonuniform_module_example"]
theorem not_exists_forall_pow_X_smul_mem {m : ℕ} (hm : 1 ≤ m) :
    ¬ ∃ j : ℕ, ∀ x : ℕ →₀ PowerSeries k,
      (X : PowerSeries k) ^ j • x ∈ coordinateSubmodule k m := by
  rintro ⟨j, hj⟩
  have h := hj (Finsupp.single (j + 1) 1) (j + 1)
  rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h
  exact not_pow_X_dvd_pow_X k (by nlinarith) h

/-- The uniform condition fails for an arbitrary open ideal of `k[[t]]`, not just for the basic
ones: for `m ≥ 1` there is no open ideal `I` with `I • M ⊆ M m`. -/
theorem not_exists_isOpen_ideal_smul_mem {m : ℕ} (hm : 1 ≤ m) :
    ¬ ∃ I : Ideal (PowerSeries k), IsOpen (I : Set (PowerSeries k)) ∧
      ∀ f ∈ I, ∀ x : ℕ →₀ PowerSeries k, f • x ∈ coordinateSubmodule k m := by
  rintro ⟨I, hIopen, hI⟩
  obtain ⟨j, -, hj⟩ :=
    (hasBasis_nhds_zero_powerSeries k).mem_iff.mp (hIopen.mem_nhds I.zero_mem)
  refine not_exists_forall_pow_X_smul_mem k hm ⟨j, fun x ↦ hI _ (hj ?_) x⟩
  exact (mem_tIdeal_pow_iff k).mpr dvd_rfl

/-- The source's example, as an existence statement: over `R = k[[t]]` with the `t`-adic
topology there is a linearly topologized `R`-module `M`, with a fundamental system `N` of open
submodules, for which no open ideal `I` of `R` satisfies `I • M ⊆ N 1`. -/
@[stacks 0AMR "nonuniform_module_example"]
theorem exists_isLinearTopology_not_exists_isOpen_ideal_smul_mem :
    ∃ (τ : TopologicalSpace (ℕ →₀ PowerSeries k))
      (N : ℕ → Submodule (PowerSeries k) (ℕ →₀ PowerSeries k)),
      (@nhds _ τ 0).HasBasis (fun _ : ℕ ↦ True) (fun m ↦ (N m : Set (ℕ →₀ PowerSeries k))) ∧
      @IsTopologicalAddGroup _ τ _ ∧
      @ContinuousSMul (PowerSeries k) _ _ _ τ ∧
      @IsLinearTopology (PowerSeries k) _ _ _ _ τ ∧
      ¬ ∃ I : Ideal (PowerSeries k), IsOpen (I : Set (PowerSeries k)) ∧
          ∀ f ∈ I, ∀ x : ℕ →₀ PowerSeries k, f • x ∈ N 1 :=
  ⟨instTopologicalSpaceNonuniform k, coordinateSubmodule k,
    hasBasis_nhds_zero_coordinateSubmodule k, isTopologicalAddGroup k, continuousSMul k,
    isLinearTopology k, not_exists_isOpen_ideal_smul_mem k le_rfl⟩

end TopologicalModule.Nonuniform

end
