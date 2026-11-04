module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Recovering an element from its `p`-th power along a purely inseparable extension

Let `A` be a domain of characteristic `p` and `B` a finite torsion free `A`-algebra which is a
domain and whose `p`-th powers lie in `A`, as happens for the integral closure of a normal domain
`A` in a purely inseparable extension of exponent one of its fraction field. Write `ρ : B → A`
for the `p`-th power map. Let `θ : A → A` be additive and `p⁻¹`-linear, `θ(aᵖ z) = a θ(z)`, with
`θ(1) ≠ 0`. Then there are a nonzero `c ∈ A` and finitely many `bᵢ, βᵢ ∈ B` such that every
`s ∈ B` satisfies

`c s = ∑ᵢ θ(ρ(bᵢ) ρ(s)) βᵢ`.

So multiplication by `c` on `B` factors as the `p`-th power map `B → A`, followed by the
additive maps `z ↦ θ(ρ(bᵢ) z)` of `A`, followed by the `A`-linear map `Aⁿ → B` given by the
`βᵢ`.

## Main results

* `Stacks.ResolutionOfSurfaces.exists_linearIndependent_forall_smul_mem_span`: a finite module
  over a domain has a linearly independent family of which every element has a nonzero multiple
  in the span.
* `Stacks.ResolutionOfSurfaces.exists_smul_eq_sum_frobenius`: the identity above.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public section

open Submodule Matrix

namespace Stacks.ResolutionOfSurfaces

section LinearIndependent

variable {A M : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]
  [Module.Finite A M]

/-- A finite module `M` over a domain contains a linearly independent family `b : Fin n → M`
such that every element of `M` has a nonzero multiple in the span of `b`. -/
theorem exists_linearIndependent_forall_smul_mem_span :
    ∃ (n : ℕ) (b : Fin n → M), LinearIndependent A b ∧
      ∀ x : M, ∃ a : A, a ≠ 0 ∧ a • x ∈ span A (Set.range b) := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := M)
  let P : ℕ → Prop := fun m => ∃ v : Fin m → M, LinearIndependent A v
  have hbound : ∀ m, P m → m ≤ S.card := by
    rintro m ⟨v, hv⟩
    simpa using linearIndependent_le_span' v hv (S : Set M) (by rw [hS]; exact le_top)
  have hP0 : P 0 := ⟨Fin.elim0, linearIndependent_empty_type⟩
  set n := Nat.findGreatest P S.card with hn
  obtain ⟨b, hb⟩ : P n := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hnot : ¬ P (n + 1) := by
    intro h
    by_cases hle : n + 1 ≤ S.card
    · exact absurd (Nat.le_findGreatest hle h) (by omega)
    · exact hle (hbound _ h)
  refine ⟨n, b, hb, fun x => ?_⟩
  have hdep : ¬ LinearIndependent A (Fin.snoc b x : Fin (n + 1) → M) := fun h => hnot ⟨_, h⟩
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  rw [Fin.sum_univ_castSucc] at hg
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
  have hlast : g (Fin.last n) ≠ 0 := by
    intro h0
    rw [h0, zero_smul, add_zero] at hg
    have hzero := Fintype.linearIndependent_iff.mp hb _ hg
    refine hi ?_
    induction i using Fin.lastCases with
    | last => exact h0
    | cast j => exact hzero j
  refine ⟨g (Fin.last n), hlast, ?_⟩
  rw [eq_neg_of_add_eq_zero_right hg]
  exact neg_mem (sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩))

end LinearIndependent

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {A B : Type*} [CommRing A] [IsDomain A]
  [CommRing B] [IsDomain B] [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]

/-- **Multiplication by a nonzero `c` factors through the `p`-th power map.** Let `B` be a
finite torsion free algebra over a domain `A`, itself a domain, with a map `ρ : B → A` lifting
`s ↦ sᵖ`, and let `θ : A → A` be additive with `θ(aᵖ z) = a θ(z)` and `θ(1) ≠ 0`. Then for some
nonzero `c ∈ A` and some `bᵢ, βᵢ ∈ B`, every `s ∈ B` satisfies `c s = ∑ᵢ θ(ρ(bᵢ) ρ(s)) βᵢ`. -/
theorem exists_smul_eq_sum_frobenius [CharP A p] (ρ : B → A)
    (hρ : ∀ s, algebraMap A B (ρ s) = s ^ p)
    (θ : A →+ A) (hθ : ∀ a z, θ (a ^ p * z) = a * θ z) (hθ1 : θ 1 ≠ 0) :
    ∃ (c : A) (n : ℕ) (b β : Fin n → B), c ≠ 0 ∧
      ∀ s : B, c • s = ∑ i, θ (ρ (b i) * ρ s) • β i := by
  classical
  have hinj : Function.Injective (algebraMap A B) := by
    intro a a' h
    rw [← sub_eq_zero]
    have h1 : (a - a') • (1 : B) = 0 := by
      rw [Algebra.smul_def, mul_one, map_sub, h, sub_self]
    exact (smul_eq_zero.mp h1).resolve_right one_ne_zero
  have : CharP B p := charP_of_injective_algebraMap hinj p
  have ρmul : ∀ s t, ρ (s * t) = ρ s * ρ t := fun s t =>
    hinj (by rw [hρ, map_mul, hρ, hρ, mul_pow])
  have ρadd : ∀ s t, ρ (s + t) = ρ s + ρ t := fun s t =>
    hinj (by rw [hρ, map_add, hρ, hρ, add_pow_char])
  have ρsmul : ∀ (a : A) s, ρ (a • s) = a ^ p * ρ s := fun a s =>
    hinj (by rw [hρ, map_mul, hρ, map_pow, Algebra.smul_def, mul_pow])
  let φ : B →ₗ[A] A :=
    { toFun := fun s => θ (ρ s)
      map_add' := fun s t => by rw [ρadd, map_add]
      map_smul' := fun a s => by rw [ρsmul, hθ, smul_eq_mul, RingHom.id_apply] }
  have hφ : ∀ s, φ s = θ (ρ s) := fun _ => rfl
  obtain ⟨n, b, hb, hspan⟩ := exists_linearIndependent_forall_smul_mem_span (A := A) (M := B)
  have hcoord : ∀ s : B, ∃ a : A, a ≠ 0 ∧ ∃ y : Fin n → A, a • s = ∑ k, y k • b k := by
    intro s
    obtain ⟨a, ha, hs⟩ := hspan s
    obtain ⟨y, hy⟩ := (mem_span_range_iff_exists_fun A).mp hs
    exact ⟨a, ha, y, hy.symm⟩
  let G : Matrix (Fin n) (Fin n) A := Matrix.of fun i k => φ (b i * b k)
  have hGapply : ∀ (y : Fin n → A) i, φ (b i * ∑ k, y k • b k) = (G *ᵥ y) i := by
    intro y i
    simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul, G, mulVec,
      dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hu0 : (∑ k, y k • b k) ≠ 0 := fun h =>
      hy0 (funext fun k => Fintype.linearIndependent_iff.mp hb y h k)
    set u : B := ∑ k, y k • b k with hu
    have hbu : ∀ i, φ (b i * u) = 0 := fun i => by
      rw [hu, hGapply, hy, Pi.zero_apply]
    have hsu : ∀ s, φ (s * u) = 0 := by
      intro s
      obtain ⟨a, ha, z, hz⟩ := hcoord s
      have h1 : a • φ (s * u) = 0 := by
        rw [← map_smul, ← smul_mul_assoc, hz, Finset.sum_mul, map_sum]
        exact Finset.sum_eq_zero fun k _ => by rw [smul_mul_assoc, map_smul, hbu, smul_zero]
      exact (smul_eq_zero.mp h1).resolve_left ha
    have h2 := hsu (u ^ (p - 1))
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, hφ] at h2
    have h3 : ρ (u ^ p) = ρ u ^ p * 1 := by
      rw [mul_one]
      exact hinj (by rw [hρ, map_pow, hρ])
    rw [h3, hθ] at h2
    have hρu : ρ u ≠ 0 := by
      intro h
      apply hu0
      have : u ^ p = 0 := by rw [← hρ, h, map_zero]
      exact (pow_eq_zero_iff hp.out.ne_zero).mp this
    exact (mul_eq_zero.mp h2).elim hρu hθ1
  let β : Fin n → B := fun i => ∑ k, G.adjugate k i • b k
  refine ⟨G.det, n, b, β, hdet, fun s => ?_⟩
  obtain ⟨a, ha, y, hy⟩ := hcoord s
  set w : Fin n → A := fun i => θ (ρ (b i) * ρ s) with hw
  have hwG : a • w = G *ᵥ y := by
    funext i
    rw [Pi.smul_apply, hw, smul_eq_mul, ← hGapply, ← hy, mul_smul_comm, map_smul, smul_eq_mul,
      hφ, ρmul]
  have hcr : a • (G.adjugate *ᵥ w) = G.det • y := by
    rw [← mulVec_smul, hwG, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  have key : a • (G.det • s) = a • ∑ i, w i • β i := by
    rw [smul_comm, hy, Finset.smul_sum, Finset.smul_sum]
    have hk : ∀ k, G.det • y k • b k = (a * (G.adjugate *ᵥ w) k) • b k := by
      intro k
      rw [smul_smul, ← smul_eq_mul a, ← Pi.smul_apply a, hcr, Pi.smul_apply, smul_eq_mul]
    simp_rw [hk, β, Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.mul_sum,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring_nf
  exact smul_right_injective B ha key

end Frobenius

end Stacks.ResolutionOfSurfaces

end
