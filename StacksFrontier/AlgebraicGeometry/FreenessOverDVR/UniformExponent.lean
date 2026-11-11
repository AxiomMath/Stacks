module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# Uniform exponents behind freeness of vector bundles over a discrete valuation ring

Two exponents govern the proof of [Stacks, Tag 0EXF]: an exponent `k` past which the
`π`-power torsion of a finite module no longer meets `π ^ n M`, and an exponent `e + 1` past
which surjectivity modulo `π ^ (e + 1)` already implies surjectivity. Both depend only on the
ambient module, not on the vector bundle being tested, which is why the integer `n` of that
lemma can be chosen before the bundle is.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `exists_forall_pow_smul_top_inf_torsion_eq_bot`: for a finite module `M` over a Noetherian
  ring and `π` in the ring, the `π`-power torsion submodule meets `π ^ n M` in `0` for all
  large `n`. This is the Artin-Rees exponent `k`, and
  `exists_forall_pow_smul_top_inf_eq_bot` is the version for an arbitrary submodule whose
  elements are `π`-power torsion.
* `exists_pow_smul_eq_bot_of_forall_pow_smul_eq_zero`: a submodule all of whose elements are
  `π`-power torsion is annihilated by a single power of `π` when the module is Noetherian.
* `le_span_singleton_smul_top_of_pow_smul_le`: in a torsion-free module over a domain, a
  submodule `T` with `π ^ e T ⊆ π ^ (e + 1) P` is contained in `π P`.
* `eq_top_of_sup_sup_pow_smul_top_eq_top`: over a local domain, a submodule `S` of a
  torsion-free finite module `P` is everything as soon as `S`, a submodule `T` with
  `π ^ e T ⊆ π ^ (e + 1) P`, and `π ^ (e + 1) P` together generate `P`. This is the
  Nakayama step that turns surjectivity modulo `π ^ (e + 1)` into surjectivity.

## Implementation notes

**No `@[stacks 0EXF]` attribute is attached to anything here**, and nothing below states any
part of that tag. Tag 0EXF asserts that for `f : X → S` proper with geometrically connected
fibres over the spectrum of a discrete valuation ring there is an integer `n` such that every
finite locally free `𝒪_X`-module free on `X_η` and on `X_n` is free. The results here are the
two module-theoretic mechanisms that produce that integer; the geometric statement needs in
addition the reduction to the case of a section (Krull-Akizuki together with the valuative
criterion of properness), the identification of `R Γ(X, ℰ)` with a direct sum of its
cohomology modules over a discrete valuation ring, and finiteness of those cohomology modules.
None of that is proved here. The tag itself is carried by `exists_thickening_exponent_free` in
`StacksFrontier/AlgebraicGeometry/FreenessOverDVR/FreenessCriterion.lean`; the section-based route,
from `TrivialityInput`, is `Triviality.lean`, which assembles the exponents built below with the
summand counting of `InvariantFactorCount.lean` and the endgame of `CyclicSummands.lean`.

In the source proof the `k` of `exists_forall_pow_smul_top_inf_torsion_eq_bot` is the exponent
with `(𝒪_X)_tors ∩ π ^ k 𝒪_X = 0`, and the `e` of `eq_top_of_sup_sup_pow_smul_top_eq_top` is
the largest exponent with `A / π ^ e A` a cyclic summand of some `H ^ i(X, 𝒪_X)`. When `f`
admits a section the integer of Tag 0EXF is `k + e + 1`; both depend only on `X`.

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public section

open scoped Pointwise

universe u v

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A submodule annihilated by `I ^ e` meets `I ^ n M` in `0` for every large `n`: Artin-Rees
applied to the pair `(M, N)` bounds the interaction away. -/
theorem exists_forall_pow_smul_inf_eq_bot [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M) {e : ℕ} (hN : I ^ e • N = ⊥) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → I ^ n • (⊤ : Submodule R M) ⊓ N = ⊥ := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul N
  refine ⟨c + e, fun n hn => le_antisymm ?_ bot_le⟩
  have hcn : c ≤ n := (Nat.le_add_right c e).trans hn
  rw [hc n hcn, ← hN]
  exact Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) inf_le_right

/-- A submodule whose every element is killed by some power of `π` is killed by a single power
of `π`, when the ambient module is Noetherian. -/
theorem exists_pow_smul_eq_bot_of_forall_pow_smul_eq_zero [IsNoetherian R M]
    (π : R) (N : Submodule R M) (hN : ∀ x ∈ N, ∃ m : ℕ, π ^ m • x = 0) :
    ∃ e : ℕ, Ideal.span {π} ^ e • N = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian N
  have hchoice : ∀ x : M, ∃ m : ℕ, x ∈ N → π ^ m • x = 0 := by
    intro x
    by_cases hx : x ∈ N
    · obtain ⟨m, hm⟩ := hN x hx
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose m hm using hchoice
  have hle : N ≤ Submodule.torsionBy R M (π ^ s.sup m) := by
    rw [← hs]
    refine Submodule.span_le.2 fun y hy => ?_
    have hys : y ∈ s := Finset.mem_coe.1 hy
    have hyN : y ∈ N := hs ▸ Submodule.subset_span hy
    have hzero : π ^ m y • y = 0 := hm y hyN
    have hsup : m y ≤ s.sup m := Finset.le_sup hys
    rw [SetLike.mem_coe, Submodule.mem_torsionBy_iff, ← Nat.sub_add_cancel hsup, pow_add,
      mul_smul, hzero, smul_zero]
  refine ⟨s.sup m, ?_⟩
  rw [eq_bot_iff]
  refine Submodule.smul_le.2 ?_
  intro r hr x hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hr
  obtain ⟨c, rfl⟩ := hr
  have hzero : π ^ s.sup m • x = 0 := (Submodule.mem_torsionBy_iff _ x).1 (hle hx)
  rw [mul_smul, hzero, smul_zero]
  exact Submodule.zero_mem _

/-- The Artin-Rees exponent: the `π`-power torsion of a finite module over a Noetherian ring
meets `π ^ n M` in `0` for every large `n`. -/
theorem exists_forall_pow_smul_top_inf_eq_bot [IsNoetherianRing R] [Module.Finite R M]
    (π : R) (N : Submodule R M) (hN : ∀ x ∈ N, ∃ m : ℕ, π ^ m • x = 0) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Ideal.span {π} ^ n • (⊤ : Submodule R M) ⊓ N = ⊥ := by
  obtain ⟨e, he⟩ := exists_pow_smul_eq_bot_of_forall_pow_smul_eq_zero π N hN
  exact exists_forall_pow_smul_inf_eq_bot (Ideal.span {π}) N he

/-- The `π`-power torsion submodule of a finite module over a Noetherian ring meets `π ^ n M`
in `0` for every large `n`. -/
theorem exists_forall_pow_smul_top_inf_torsion_eq_bot [IsNoetherianRing R] [Module.Finite R M]
    (π : R) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Ideal.span {π} ^ n • (⊤ : Submodule R M) ⊓
      Submodule.torsion' R M (Submonoid.powers π) = ⊥ := by
  refine exists_forall_pow_smul_top_inf_eq_bot π _ fun x hx => ?_
  obtain ⟨⟨a, m, rfl⟩, ha⟩ := hx
  exact ⟨m, ha⟩

variable {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]

/-- A submodule `T` of a torsion-free module with `π ^ e T ⊆ π ^ (e + 1) P` is contained in
`π P`, for `π` a nonzero element of a domain. -/
theorem le_span_singleton_smul_top_of_pow_smul_le [IsDomain A] [NoZeroSMulDivisors A P]
    {π : A} (hπ : π ≠ 0) {e : ℕ} (T : Submodule A P)
    (hT : Ideal.span {π} ^ e • T ≤ Ideal.span {π} ^ (e + 1) • (⊤ : Submodule A P)) :
    T ≤ Ideal.span {π} • (⊤ : Submodule A P) := by
  intro x hx
  have h1 : π ^ e • x ∈ Ideal.span {π} ^ (e + 1) • (⊤ : Submodule A P) := by
    refine hT (Submodule.smul_mem_smul ?_ hx)
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨y, -, hy⟩ := h1
  have hxy : π ^ e • (π • y) = π ^ e • x := by rw [← mul_smul, ← pow_succ]; exact hy
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨y, Submodule.mem_top, smul_right_injective P (pow_ne_zero e hπ) hxy⟩

/-- Over a local domain, a submodule `S` of a torsion-free finite module `P` is everything as
soon as `S`, a submodule `T` with `π ^ e T ⊆ π ^ (e + 1) P`, and `π ^ (e + 1) P` generate `P`.
This upgrades surjectivity modulo `π ^ (e + 1)` to surjectivity. -/
theorem eq_top_of_sup_sup_pow_smul_top_eq_top [IsDomain A] [IsLocalRing A] [Module.Finite A P]
    [NoZeroSMulDivisors A P] {π : A} (hπ : π ≠ 0) (hmem : π ∈ IsLocalRing.maximalIdeal A)
    {e : ℕ} (S T : Submodule A P)
    (hT : Ideal.span {π} ^ e • T ≤ Ideal.span {π} ^ (e + 1) • (⊤ : Submodule A P))
    (hST : S ⊔ T ⊔ Ideal.span {π} ^ (e + 1) • (⊤ : Submodule A P) = ⊤) :
    S = ⊤ := by
  have hspan : Ideal.span {π} ≤ IsLocalRing.maximalIdeal A := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  have hpow : Ideal.span {π} ^ (e + 1) ≤ Ideal.span {π} := by
    simpa using Ideal.pow_le_pow_right (I := Ideal.span {π}) (Nat.le_add_left 1 e)
  have hsup : (⊤ : Submodule A P) ≤ S ⊔ Ideal.span {π} • (⊤ : Submodule A P) :=
    hST.ge.trans (sup_le (sup_le le_sup_left
      ((le_span_singleton_smul_top_of_pow_smul_le hπ T hT).trans le_sup_right))
      ((Submodule.smul_mono_left hpow).trans le_sup_right))
  exact top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (hspan.trans (IsLocalRing.maximalIdeal_le_jacobson ⊥)) hsup)

end Stacks.AlgebraicGeometry.FreenessOverDVR
