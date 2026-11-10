module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Tactic.Abel

/-!
# Formal functions in one degree of a graded complex

Let `R` be a ring, `f ∈ R`, and let `C⁰ → C¹ → ⋯` be a complex of `R`-modules each of whose terms
carries a family of additive subgroups `Dₘ ⊆ Cᵖ` indexed by `m ∈ ℤ` — the elements "of degree
`m`" — such that the differential preserves degrees and multiplication by `f` raises the degree by
one. The motivating example is the degree-`m` part of the Čech complex of a graded module over a
graded ring with respect to homogeneous elements, `f` homogeneous of degree one; there, the
degree-`0` part computes the cohomology of a coherent sheaf on a projective scheme and the
degree-`0` part of the complex reduced modulo `fⁿ` computes the cohomology of its restriction to
the `n`-th infinitesimal neighbourhood of the zero scheme of `f`. This is the situation of
[Stacks, Tag 0EL1].

This file proves the algebraic heart of the comparison `Hᵖ ⟶ lim Hᵖ(mod fⁿ)` in degree zero,
elementwise, from three inputs:

* the **graded lift**: a coboundary of degree `m` is the coboundary of an element of degree `m`;
* the **torsion bound**: there is `t` with `f^(t+n) x = 0 ⟹ f^t x = 0` for every element `x`;
* the **annihilation**: some power `f ^ c` carries every degree-`m` cocycle in degree `≤ σ` to a
  coboundary, except in degree `0`, where it is asked only for `m + c < 0` and then means that
  `f ^ c` kills the cocycle.

The two conclusions are the two halves of the bijectivity of the comparison map in every degree
`p < σ`: a degree-zero cocycle which is a coboundary modulo `f ^ N` for `N` large is a coboundary
(`mem_bd_of_sub_pow_smul_mem_bd`), and a degree-zero cochain whose coboundary vanishes modulo
`f ^ m` for `m` large differs from a genuine cocycle by a multiple of `f ^ n`
(`exists_cocycle_sub_eq_pow_smul`).

The argument is the one of [Stacks, Tag 0EKM], run in a single degree of the grading, where the
completeness of the degree-zero part is automatic: the elements of the kernel of the comparison
are of the form `fᴺ · w` with `w` of degree `-N`, and those are killed by the annihilation once
`N` is large.

## Main definitions

* `Stacks.DegreeZeroTower.bd`: the degree-`m` coboundaries in degree `p`.

## Main results

* `Stacks.DegreeZeroTower.mem_bd_of_sub_pow_smul_mem_bd`: the injectivity half.
* `Stacks.DegreeZeroTower.exists_cocycle_sub_eq_pow_smul`: the surjectivity half.
* `Stacks.DegreeZeroTower.bijective_toCompatible`: the passage from the two halves to the
  bijectivity of a map into compatible families.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EKM](https://stacks.math.columbia.edu/tag/0EKM)
-/

@[expose] public section

namespace Stacks.DegreeZeroTower

universe u v

section Complex

variable {R : Type u} [CommRing R] {C : ℕ → Type v} [∀ p, AddCommGroup (C p)]
  [∀ p, Module R (C p)] (d : ∀ p, C p →ₗ[R] C (p + 1)) (D : ∀ p, ℤ → AddSubgroup (C p))

/-- The degree-`m` coboundaries in degree `p`: nothing in degree `0`, and the image of the
degree-`m` part of the previous term in degree `p + 1`. -/
def bd : ∀ p, ℤ → AddSubgroup (C p)
  | 0, _ => ⊥
  | p + 1, m => (D p m).map (d p).toAddMonoidHom

/-- There are no coboundaries in degree `0`. -/
theorem bd_zero (m : ℤ) : bd d D 0 m = ⊥ := rfl

/-- An element of degree `p + 1` is a degree-`m` coboundary if and only if it is the image under
`d p` of an element of degree `m`. -/
theorem mem_bd_succ {p : ℕ} {m : ℤ} {z : C (p + 1)} :
    z ∈ bd d D (p + 1) m ↔ ∃ w ∈ D p m, d p w = z := by
  simp [bd]

variable {d D} (f : R)

section Laws

variable (hdd : ∀ p (x : C p), d (p + 1) (d p x) = 0)
  (hdD : ∀ p m (x : C p), x ∈ D p m → d p x ∈ D (p + 1) m)
  (hfD : ∀ p m (x : C p), x ∈ D p m → f • x ∈ D p (m + 1))

include hfD in
/-- Multiplication by `f ^ n` raises the degree by `n`. -/
theorem pow_smul_mem (p : ℕ) {m : ℤ} {x : C p} (hx : x ∈ D p m) (n : ℕ) :
    f ^ n • x ∈ D p (m + n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', mul_smul, Nat.cast_succ, ← add_assoc]
    exact hfD p _ _ ih

include hdd in
/-- A coboundary is a cocycle. -/
theorem d_eq_zero_of_mem_bd {p : ℕ} {m : ℤ} {z : C p} (hz : z ∈ bd d D p m) : d p z = 0 := by
  cases p with
  | zero =>
    rw [bd_zero, AddSubgroup.mem_bot] at hz
    simp [hz]
  | succ p =>
    obtain ⟨w, -, rfl⟩ := (mem_bd_succ d D).1 hz
    exact hdd p w

include hfD in
/-- Multiplication by `f ^ n` carries degree-`m` coboundaries to degree-`(m + n)` ones. -/
theorem pow_smul_mem_bd {p : ℕ} {m : ℤ} {z : C p} (hz : z ∈ bd d D p m) (n : ℕ) :
    f ^ n • z ∈ bd d D p (m + n) := by
  cases p with
  | zero =>
    rw [bd_zero, AddSubgroup.mem_bot] at hz ⊢
    simp [hz]
  | succ p =>
    obtain ⟨w, hw, rfl⟩ := (mem_bd_succ d D).1 hz
    exact (mem_bd_succ d D).2 ⟨f ^ n • w, pow_smul_mem f hfD p hw n, map_smul _ _ _⟩

end Laws

variable (hdd : ∀ p (x : C p), d (p + 1) (d p x) = 0)
  (hdD : ∀ p m (x : C p), x ∈ D p m → d p x ∈ D (p + 1) m)
  (hfD : ∀ p m (x : C p), x ∈ D p m → f • x ∈ D p (m + 1))
  {t : ℕ} (htors : ∀ p (x : C p) (n : ℕ), f ^ (t + n) • x = 0 → f ^ t • x = 0)
  {c σ : ℕ} (hann : ∀ p, p ≤ σ → ∀ m (z : C p), z ∈ D p m → d p z = 0 →
    (1 ≤ p ∨ m + c < 0) → f ^ c • z ∈ bd d D p (m + c))

/-- If `f ^ (t + n)` kills `d p u`, then `f ^ c • f ^ t • u` is a coboundary. -/
private theorem pow_smul_pow_smul_mem_bd (hfD : ∀ p m (x : C p), x ∈ D p m → f • x ∈ D p (m + 1))
    (htors : ∀ p (x : C p) (n : ℕ), f ^ (t + n) • x = 0 → f ^ t • x = 0)
    (hann : ∀ p, p ≤ σ → ∀ m (z : C p), z ∈ D p m → d p z = 0 →
      (1 ≤ p ∨ m + c < 0) → f ^ c • z ∈ bd d D p (m + c))
    {p : ℕ} (hp : p ≤ σ) {m : ℤ} {u : C p} {n : ℕ}
    (hu : u ∈ D p m) (hdu : f ^ (t + n) • d p u = 0) (hm : 1 ≤ p ∨ m + t + c < 0) :
    f ^ c • (f ^ t • u) ∈ bd d D p (m + t + c) :=
  hann p hp _ (f ^ t • u) (pow_smul_mem f hfD p hu t)
    (by rw [map_smul]; exact htors (p + 1) _ _ hdu) hm

include hdd hfD htors hann in
/-- **The injectivity half.** Let `p ≤ σ` and `N ≥ t + c + 1`. A degree-zero cocycle `z` which,
up to a degree-zero coboundary, is `f ^ N` times an element of degree `-N`, is a coboundary. -/
theorem mem_bd_of_sub_pow_smul_mem_bd {p : ℕ} (hp : p ≤ σ) {N : ℕ} (hN : t + c + 1 ≤ N)
    {z u : C p} (_hz : z ∈ D p 0) (hdz : d p z = 0) (hu : u ∈ D p (-N))
    (hzu : z - f ^ N • u ∈ bd d D p 0) : z ∈ bd d D p 0 := by
  have hdb : d p (z - f ^ N • u) = 0 := d_eq_zero_of_mem_bd hdd hzu
  have hdu : f ^ N • d p u = 0 := by
    rw [map_sub, hdz, zero_sub, neg_eq_zero, map_smul] at hdb
    exact hdb
  obtain ⟨k, rfl⟩ : ∃ k, N = t + (c + 1 + k) := ⟨N - (t + c + 1), by omega⟩
  have hcv := pow_smul_pow_smul_mem_bd f hfD htors hann hp hu hdu (Or.inr (by push_cast; omega))
  have hfu : f ^ (t + (c + 1 + k)) • u = f ^ (k + 1) • (f ^ c • (f ^ t • u)) := by
    rw [smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
  have hmem := pow_smul_mem_bd f hfD hcv (k + 1)
  rw [← hfu] at hmem
  have h0 : -(↑(t + (c + 1 + k)) : ℤ) + ↑t + ↑c + ↑(k + 1) = 0 := by push_cast; omega
  rw [h0] at hmem
  have := add_mem hzu hmem
  rwa [sub_add_cancel] at this

include hdd hfD htors hann in
/-- **The surjectivity half.** Let `p + 1 ≤ σ`. A degree-zero cochain `y` whose coboundary is
`f ^ (n + t + c)` times an element of degree `-(n + t + c)` differs from a degree-zero cocycle by
`f ^ n` times an element of degree `-n`. -/
theorem exists_cocycle_sub_eq_pow_smul {p : ℕ} (hp : p + 1 ≤ σ) (n : ℕ) {y : C p}
    {u : C (p + 1)} (hy : y ∈ D p 0) (hu : u ∈ D (p + 1) (-(n + t + c : ℕ)))
    (hyu : d p y = f ^ (n + t + c) • u) :
    ∃ x ∈ D p 0, d p x = 0 ∧ ∃ w ∈ D p (-n), y - x = f ^ n • w := by
  have hdu : f ^ (t + (n + c)) • d (p + 1) u = 0 := by
    have h := congrArg (d (p + 1)) hyu
    rw [hdd, map_smul] at h
    rw [show t + (n + c) = n + t + c by omega]
    exact h.symm
  have hcv := pow_smul_pow_smul_mem_bd f hfD htors hann hp hu hdu (Or.inl (Nat.le_add_left 1 p))
  obtain ⟨w, hw, hdw⟩ := (mem_bd_succ d D).1 hcv
  have hdeg : -(↑(n + t + c) : ℤ) + ↑t + ↑c = -n := by push_cast; omega
  rw [hdeg] at hw
  refine ⟨y - f ^ n • w, ?_, ?_, w, hw, by abel⟩
  · have h := pow_smul_mem f hfD p hw n
    rw [neg_add_cancel] at h
    exact sub_mem hy h
  · rw [map_sub, map_smul, hdw, hyu, smul_smul, smul_smul, ← pow_add, ← pow_add]
    rw [sub_eq_zero]
    congr 2
    omega

end Complex

/-! ### From the two halves to a bijection onto compatible families -/

section Tower

variable {H : Type u} {G : ℕ → Type v} [AddCommGroup H] [∀ n, AddCommGroup (G n)]
  (φ : ∀ n, H →+ G n) (τ : ∀ n, G (n + 1) →+ G n) (hφτ : ∀ n x, τ n (φ (n + 1) x) = φ n x)

/-- The composite of the transition maps from level `n + k` down to level `n`. -/
def descend : ∀ (n k : ℕ), G (n + k) →+ G n
  | _, 0 => AddMonoidHom.id _
  | n, k + 1 => (descend n k).comp (τ (n + k))

/-- A compatible family is compatible along every composite of transition maps. -/
private theorem descend_eq_of_compat {y : ∀ n, G n} (hy : ∀ n, τ n (y (n + 1)) = y n) (n k : ℕ) :
    descend τ n k (y (n + k)) = y n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change descend τ n k (τ (n + k) (y (n + k + 1))) = y n
    rw [hy, ih]

include hφτ in
/-- Descending `φ (n + k) x` along the transition maps gives `φ n x`. -/
theorem descend_comp (n k : ℕ) (x : H) : descend τ n k (φ (n + k) x) = φ n x := by
  exact descend_eq_of_compat τ (y := fun m => φ m x) (fun m => hφτ m x) n k

/-- A compatible family is compatible along every composite of transition maps. -/
theorem descend_family {y : ∀ n, G n} (hy : ∀ n, τ n (y (n + 1)) = y n) (n k : ℕ) :
    descend τ n k (y (n + k)) = y n :=
  descend_eq_of_compat τ hy n k

include hφτ in
/-- **A map into a tower which is injective at all large levels and whose cokernels descend
into its image is a bijection onto the compatible families.** -/
theorem bijective_toCompatible (N₀ : ℕ) (hinj : ∀ N, N₀ ≤ N → Function.Injective (φ N))
    (hsurj : ∀ n, ∃ k, ∀ y : G (n + k), ∃ x : H, φ n x = descend τ n k y) :
    Function.Injective (fun x : H => fun n => φ n x) ∧
      ∀ y : ∀ n, G n, (∀ n, τ n (y (n + 1)) = y n) → ∃ x : H, ∀ n, φ n x = y n := by
  refine ⟨fun x x' h => hinj N₀ le_rfl (congrFun h N₀), fun y hy => ?_⟩
  have hlift : ∀ M, ∃ x : H, φ M x = y M := fun M => by
    obtain ⟨k, hk⟩ := hsurj M
    obtain ⟨x, hx⟩ := hk (y (M + k))
    exact ⟨x, hx.trans (descend_family τ hy M k)⟩
  obtain ⟨x, hx⟩ := hlift N₀
  have hup : ∀ M, N₀ ≤ M → φ M x = y M := fun M hM => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
    obtain ⟨x', hx'⟩ := hlift (N₀ + k)
    have : x' = x := hinj N₀ le_rfl (by
      rw [hx, ← descend_comp φ τ hφτ N₀ k x', hx', descend_family τ hy])
    rw [← this, hx']
  refine ⟨x, fun n => ?_⟩
  rw [← descend_comp φ τ hφτ n N₀ x, hup (n + N₀) (Nat.le_add_left _ _), descend_family τ hy]

end Tower

end Stacks.DegreeZeroTower

end
