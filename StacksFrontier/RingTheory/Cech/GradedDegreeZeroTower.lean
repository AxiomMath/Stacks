module

public import StacksFrontier.RingTheory.Cech.DegreeZeroTowerComparison
public import StacksFrontier.RingTheory.Cech.GradedSubcomplex
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The degree-zero tower of the Čech complex of a graded module

Let `R = ⨁_{i ≥ 0} 𝒜 i` be a graded ring, `M = ⨁_{j ∈ ℤ} 𝒨 j` a Noetherian graded module
concentrated in nonnegative degrees, `g₁, …, g_r` homogeneous elements and `f ∈ 𝒜 1`. This file
specializes `StacksFrontier/RingTheory/Cech/DegreeZeroTowerComparison.lean` to the degree-`m` parts
of the Čech complex `C^{•+1}(g₁, …, g_r; M)` — the Čech complex, without its augmentation term,
of the standard covering of the punctured spectrum — and verifies its three inputs:

* the graded lift of coboundaries is `Cech.exists_eq_cechD_mem_gradedCechTerm`;
* the torsion bound comes from the stabilization of the chain `M[fⁿ]` of a Noetherian module;
* the annihilation comes from an annihilation of the cohomology of the *extended* Čech complex
  `C^•(g; M)` — that is, of the local cohomology `H^j_{(g)}(M)` — by a power of `f` in degrees
  `j ≤ σ + 1`, together with the vanishing of `M` in negative degrees, which is what makes the
  augmentation term `M` invisible in negative degrees.

## Main results

* `Stacks.GradedDegreeZeroTower.exists_cechD_eq_smul_of_homology`: an annihilation of the
  cohomology of a complex of modules, read on cocycles.
* `Stacks.GradedDegreeZeroTower.mem_bd_of_sub_pow_smul_mem_bd` and
  `Stacks.GradedDegreeZeroTower.exists_cocycle_sub_eq_pow_smul`: the two halves of the
  degree-zero comparison of [Stacks, Tag 0EL1], for the Čech complex of a graded module.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EKM](https://stacks.math.columbia.edu/tag/0EKM)
-/

@[expose] public section

open CategoryTheory

universe u v w t

attribute [local instance] instVAddNatIntGradedLocalizedModule

namespace Stacks.GradedDegreeZeroTower

/-! ### An annihilation of cohomology, read on cocycles -/

/-- **An annihilation of cohomology, read on cocycles.** If `a` kills the degree-`q + 1`
cohomology of a cochain complex of modules, then `a` times a cocycle of degree `q + 1` is a
coboundary. -/
theorem exists_cechD_eq_smul_of_homology {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (q : ℕ) (a : R)
    (h : ∀ x : K.homology (q + 1), a • x = 0) (z : K.X (q + 1))
    (hz : K.d (q + 1) (q + 2) z = 0) : ∃ y : K.X q, K.d q (q + 1) y = a • z := by
  obtain ⟨c, hc⟩ : ∃ c : K.cycles (q + 1), K.iCycles (q + 1) c = z :=
    ⟨_, K.i_cyclesMk z (q + 2) (by simp) hz⟩
  let S := ShortComplex.mk (K.toCycles q (q + 1)) (K.homologyπ (q + 1))
    (K.toCycles_comp_homologyπ q (q + 1))
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff S).mp
    (S.exact_of_g_is_cokernel (K.homologyIsCokernel q (q + 1) (by simp))) (a • c)
    ((map_smul _ a c).trans (h _))
  refine ⟨y, ?_⟩
  have hh := congrArg (K.iCycles (q + 1)) hy
  rw [map_smul, hc] at hh
  exact (congrArg (fun k : K.X q ⟶ K.X (q + 1) => k y) (K.toCycles_i q (q + 1))).symm.trans hh

section Cech

variable {R : Type u} [CommRing R] {r : ℕ} {σ' : Type w} {τ : Type t}
  [SetLike σ' R] [AddSubgroupClass σ' R] (𝒜 : ℕ → σ') [GradedRing 𝒜]
  {M : Type v} [AddCommGroup M] [Module R M]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]
  (g : Fin r → R) {c : Fin r → ℕ} (hc : ∀ i, g i ∈ 𝒜 (c i)) {f : R} (hf : f ∈ 𝒜 1)

/-- The degree-`m` part of the Čech complex without its augmentation term, in Čech degree `p`. -/
abbrev degreePart (p : ℕ) (m : ℤ) : AddSubgroup (Cech.cechTerm g M (p + 1)) :=
  Cech.gradedCechTerm 𝒜 𝒨 g m (p + 1)

/-- The differential of the Čech complex without its augmentation term. -/
noncomputable abbrev cechDiff (p : ℕ) : Cech.cechTerm g M (p + 1) →ₗ[R] Cech.cechTerm g M (p + 2) :=
  Cech.cechD g M (p + 1)

omit [DirectSum.Decomposition 𝒨] in
include hc hf in
/-- Multiplication by `f` raises the degree of a Čech cochain by one. -/
theorem smul_mem_gradedCechTerm {p : ℕ} {m : ℤ} {z : Cech.cechTerm g M p}
    (hz : z ∈ Cech.gradedCechTerm 𝒜 𝒨 g m p) :
    f • z ∈ Cech.gradedCechTerm 𝒜 𝒨 g (m + 1) p := by
  classical
  refine Cech.mem_gradedCechTerm.2 fun s => ?_
  rw [DFinsupp.smul_apply]
  have hprod : (∏ i ∈ s.1, g i) ∈ 𝒜 (∑ i ∈ s.1, c i) := SetLike.prod_mem_graded 𝒜 c g
    (fun i _ => hc i)
  obtain ⟨n, x, hx, hzx⟩ := (Stacks.GradedLocalization.mem_gradedPiece_iff 𝒜 𝒨 hprod m _).1
    (Cech.mem_gradedCechTerm.1 hz s)
  rw [hzx, LocalizedModule.smul'_mk]
  refine Stacks.GradedLocalization.mk_mem_gradedPiece 𝒜 𝒨 hprod ?_
  convert SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒨) hf hx using 2
  change m + 1 + n • ((∑ i ∈ s.1, c i : ℕ) : ℤ) = ((1 : ℕ) : ℤ) + (m + n • _)
  push_cast
  ring

/-! ### The torsion bound -/

omit [SetLike σ' R] [AddSubgroupClass σ' R] [GradedRing 𝒜] [SetLike τ M] [AddSubgroupClass τ M]
  [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒜 𝒨] in
/-- **The `f`-power torsion of a Noetherian module is bounded**: the chain of kernels of
multiplication by `fⁿ` stabilizes. -/
theorem exists_pow_smul_torsion_bound [IsNoetherian R M] (f : R) :
    ∃ t : ℕ, ∀ (x : M) (n : ℕ), f ^ (t + n) • x = 0 → f ^ t • x = 0 := by
  let K : ℕ →o Submodule R M :=
    ⟨fun n => LinearMap.ker ((f ^ n) • LinearMap.id), fun a b hab x hx => by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [pow_add, mul_comm, mul_smul, hx, smul_zero]⟩
  obtain ⟨t, ht⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  refine ⟨t, fun x n hx => ?_⟩
  have hmem : x ∈ K (t + n) := by
    change x ∈ LinearMap.ker ((f ^ (t + n)) • LinearMap.id)
    simpa using hx
  rw [← ht (t + n) (Nat.le_add_right t n)] at hmem
  change x ∈ LinearMap.ker ((f ^ t) • LinearMap.id) at hmem
  simpa using hmem

omit [SetLike σ' R] [AddSubgroupClass σ' R] [GradedRing 𝒜] [SetLike τ M] [AddSubgroupClass τ M]
  [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒜 𝒨] in
/-- The torsion bound passes to a localization. -/
theorem localized_torsion_bound (f : R) {t : ℕ}
    (ht : ∀ (x : M) (n : ℕ), f ^ (t + n) • x = 0 → f ^ t • x = 0) (S : Submonoid R)
    (y : LocalizedModule S M) (n : ℕ) (hy : f ^ (t + n) • y = 0) : f ^ t • y = 0 := by
  induction y using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk (1 : S)] at hy ⊢
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 hy
    refine LocalizedModule.mk_eq.2 ⟨u, ?_⟩
    simp only [one_smul, smul_zero, Submonoid.smul_def] at hu ⊢
    rw [smul_comm (u : R) (f ^ (t + n)) m] at hu
    rw [smul_comm (u : R) (f ^ t) m]
    exact ht _ n hu

omit [SetLike σ' R] [AddSubgroupClass σ' R] [GradedRing 𝒜] [SetLike τ M] [AddSubgroupClass τ M]
  [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒜 𝒨] in
/-- The torsion bound passes to the terms of the Čech complex. -/
theorem cechTerm_torsion_bound (f : R) {t : ℕ}
    (ht : ∀ (x : M) (n : ℕ), f ^ (t + n) • x = 0 → f ^ t • x = 0) (p : ℕ)
    (z : Cech.cechTerm g M p) (n : ℕ) (hz : f ^ (t + n) • z = 0) : f ^ t • z = 0 := by
  classical
  refine DFinsupp.ext fun s => ?_
  rw [DFinsupp.smul_apply, DFinsupp.zero_apply]
  refine localized_torsion_bound f ht _ _ n ?_
  rw [← DFinsupp.smul_apply, hz, DFinsupp.zero_apply]

/-! ### The annihilation -/

omit [DirectSum.Decomposition 𝒨] in
include hc hf in
/-- Multiplication by `f ^ n` raises the degree of a Čech cochain by `n`. -/
theorem pow_smul_mem_gradedCechTerm {p : ℕ} {m : ℤ} {z : Cech.cechTerm g M p}
    (hz : z ∈ Cech.gradedCechTerm 𝒜 𝒨 g m p) (n : ℕ) :
    f ^ n • z ∈ Cech.gradedCechTerm 𝒜 𝒨 g (m + n) p :=
  DegreeZeroTower.pow_smul_mem (D := fun p m => Cech.gradedCechTerm 𝒜 𝒨 g m p) f
    (fun _ _ _ hx => smul_mem_gradedCechTerm 𝒜 𝒨 g hc hf hx) p hz n

include hc hf in
/-- **The annihilation, in the Čech complex without its augmentation term.** Suppose `f ^ c'`
kills the cohomology of the extended Čech complex `C^•(g; M)` in degrees `j ≤ σ + 1`, and `M`
vanishes in negative degrees. Then `f ^ c'` carries every degree-`m` cocycle in Čech degree
`p ≤ σ` to a degree-`(m + c')` coboundary, where in Čech degree `0` the condition `m + c' < 0`
makes that coboundary zero: the would-be preimage lives in the augmentation term `M`, in the
negative degree `m + c'`. -/
theorem annihilation (hneg : ∀ j : ℤ, j < 0 → ∀ x ∈ 𝒨 j, x = 0) {c' σ : ℕ}
    (hH : ∀ j : ℕ, j ≤ σ + 1 → ∀ x : (Cech.cechComplex g M).homology j, f ^ c' • x = 0) :
    ∀ p, p ≤ σ → ∀ m (z : Cech.cechTerm g M (p + 1)), z ∈ degreePart 𝒜 𝒨 g p m →
      cechDiff g p z = 0 → (1 ≤ p ∨ m + c' < 0) →
        f ^ c' • z ∈ DegreeZeroTower.bd (cechDiff g) (degreePart 𝒜 𝒨 g) p (m + c') := by
  classical
  intro p hp m z hz hdz hcases
  obtain ⟨y, hy⟩ := exists_cechD_eq_smul_of_homology (Cech.cechComplex g M) p (f ^ c')
    (hH (p + 1) (by omega)) z (by rwa [Cech.cechComplex_d])
  rw [Cech.cechComplex_d] at hy
  obtain ⟨w, hw, hdw⟩ := Cech.exists_eq_cechD_mem_gradedCechTerm 𝒜 𝒨 g hc (m + c') p
    (pow_smul_mem_gradedCechTerm 𝒜 𝒨 g hc hf hz c') hy
  cases p with
  | zero =>
    have hneg' : m + c' < 0 := by omega
    have hw0 : w = 0 := by
      refine DFinsupp.ext fun s => ?_
      have hprod : (∏ i ∈ s.1, g i) ∈ 𝒜 (∑ i ∈ s.1, c i) :=
        SetLike.prod_mem_graded 𝒜 c g (fun i _ => hc i)
      obtain ⟨n, x, hx, hwx⟩ := (Stacks.GradedLocalization.mem_gradedPiece_iff 𝒜 𝒨 hprod
        (m + c') _).1 (Cech.mem_gradedCechTerm.1 hw s)
      rw [Finset.card_eq_zero.1 s.2, Finset.sum_empty] at hx
      have hx0 : x = 0 := hneg _ (by simpa using hneg') x (by simpa using hx)
      rw [DFinsupp.zero_apply, hwx, hx0, LocalizedModule.zero_mk]
    rw [← hdw, hw0, map_zero]
    exact zero_mem _
  | succ q =>
    exact (DegreeZeroTower.mem_bd_succ (cechDiff g) (degreePart 𝒜 𝒨 g)).2 ⟨w, hw, hdw⟩

/-! ### The two halves of the degree-zero comparison -/

include hc hf in
/-- **The injectivity half, for the Čech complex of a graded module.** -/
theorem mem_bd_of_sub_pow_smul_mem_bd [IsNoetherian R M]
    (hneg : ∀ j : ℤ, j < 0 → ∀ x ∈ 𝒨 j, x = 0) {c' σ : ℕ}
    (hH : ∀ j : ℕ, j ≤ σ + 1 → ∀ x : (Cech.cechComplex g M).homology j, f ^ c' • x = 0) :
    ∃ N₀ : ℕ, ∀ p, p ≤ σ → ∀ N, N₀ ≤ N → ∀ z u : Cech.cechTerm g M (p + 1),
      z ∈ degreePart 𝒜 𝒨 g p 0 → cechDiff g p z = 0 → u ∈ degreePart 𝒜 𝒨 g p (-N) →
      z - f ^ N • u ∈ DegreeZeroTower.bd (cechDiff g) (degreePart 𝒜 𝒨 g) p 0 →
      z ∈ DegreeZeroTower.bd (cechDiff g) (degreePart 𝒜 𝒨 g) p 0 := by
  obtain ⟨t, ht⟩ := exists_pow_smul_torsion_bound (M := M) f
  refine ⟨t + c' + 1, fun p hp N hN z u hz hdz hu hzu => ?_⟩
  exact DegreeZeroTower.mem_bd_of_sub_pow_smul_mem_bd
    (C := fun p => Cech.cechTerm g M (p + 1)) (d := cechDiff g) (D := degreePart 𝒜 𝒨 g) f
    (fun p x => LinearMap.congr_fun (Cech.cechD_comp_cechD g M (p + 1)) x)
    (fun p m x hx => smul_mem_gradedCechTerm 𝒜 𝒨 g hc hf hx)
    (fun p x n hx => cechTerm_torsion_bound g f ht (p + 1) x n hx)
    (annihilation 𝒜 𝒨 g hc hf hneg hH) hp hN hz hdz hu hzu

include hc hf in
/-- **The surjectivity half, for the Čech complex of a graded module.** -/
theorem exists_cocycle_sub_eq_pow_smul [IsNoetherian R M]
    (hneg : ∀ j : ℤ, j < 0 → ∀ x ∈ 𝒨 j, x = 0) {c' σ : ℕ}
    (hH : ∀ j : ℕ, j ≤ σ + 1 → ∀ x : (Cech.cechComplex g M).homology j, f ^ c' • x = 0) :
    ∃ e : ℕ, ∀ p, p + 1 ≤ σ → ∀ n (y : Cech.cechTerm g M (p + 1)) (u : Cech.cechTerm g M (p + 2)),
      y ∈ degreePart 𝒜 𝒨 g p 0 → u ∈ degreePart 𝒜 𝒨 g (p + 1) (-(n + e : ℕ)) →
      cechDiff g p y = f ^ (n + e) • u →
      ∃ x ∈ degreePart 𝒜 𝒨 g p 0, cechDiff g p x = 0 ∧
        ∃ w ∈ degreePart 𝒜 𝒨 g p (-n), y - x = f ^ n • w := by
  obtain ⟨t, ht⟩ := exists_pow_smul_torsion_bound (M := M) f
  refine ⟨t + c', fun p hp n y u hy hu hyu => ?_⟩
  have hu' : u ∈ degreePart 𝒜 𝒨 g (p + 1) (-(n + t + c' : ℕ)) := by
    rwa [show n + t + c' = n + (t + c') by omega]
  exact DegreeZeroTower.exists_cocycle_sub_eq_pow_smul
    (C := fun p => Cech.cechTerm g M (p + 1)) (d := cechDiff g) (D := degreePart 𝒜 𝒨 g) f
    (fun p x => LinearMap.congr_fun (Cech.cechD_comp_cechD g M (p + 1)) x)
    (fun p m x hx => smul_mem_gradedCechTerm 𝒜 𝒨 g hc hf hx)
    (fun p x n hx => cechTerm_torsion_bound g f ht (p + 1) x n hx)
    (annihilation 𝒜 𝒨 g hc hf hneg hH) hp n hy hu'
    (hyu.trans (by rw [show n + (t + c') = n + t + c' by omega]))

end Cech

end Stacks.GradedDegreeZeroTower

end
