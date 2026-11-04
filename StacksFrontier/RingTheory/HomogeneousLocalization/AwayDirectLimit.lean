module

public import Mathlib.Algebra.Colimit.Module
public import StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra

/-!
# The degree-zero localization at a homogeneous element as a direct limit

Let `A` be a graded ring with grading `𝒜 : ι → σ` and let `a ∈ 𝒜 d` be homogeneous. Mathlib's
`HomogeneousLocalization.Away 𝒜 a` is the degree-zero part of `A[1/a]`, whose elements are the
fractions `x / aⁿ` with `x ∈ 𝒜 (n • d)` (`HomogeneousLocalization.Away.mk`). This file identifies
it with the direct limit of the system

`𝒜 0 → 𝒜 d → 𝒜 (2 • d) → ⋯`,

the map `𝒜 (n • d) → 𝒜 ((n + 1) • d)` being multiplication by `a`, the fraction `x / aⁿ`
corresponding to `x` in the `n`-th term.

Concretely this is the pair of statements that a fraction may always be rewritten over a larger
power of `a`, so that finitely many fractions can be put over a common denominator, and that a
fraction vanishes exactly when a power of `a` annihilates its numerator.

## Main definitions

* `HomogeneousLocalization.Away.mulPow` is the transition map of the system, multiplication by
  `a ^ (m - n)` from `𝒜 (n • d)` to `𝒜 (m • d)`.
* `HomogeneousLocalization.Away.mkLinearMap` is `x ↦ x / aⁿ` as a map out of the `n`-th term.
* `HomogeneousLocalization.Away.directLimitEquiv` is the resulting isomorphism from the direct
  limit.

## Main results

* `HomogeneousLocalization.Away.mk_eq_mk_iff` and
  `HomogeneousLocalization.Away.mk_eq_zero_iff` describe equality of fractions.
* `HomogeneousLocalization.Away.mk_eq_mk_of_le`: a fraction rewritten over a larger power of `a`.
* `HomogeneousLocalization.Away.exists_forall_eq_mk`: **a finite family of elements of
  `Away 𝒜 a` can be written over a common denominator.**
* `HomogeneousLocalization.Away.directLimitEquiv`: **`Away 𝒜 a` is the direct limit of the
  `𝒜 (n • d)` along multiplication by `a`**, as an isomorphism of `R`-modules.

## Implementation notes

The elementary statements are proved for a grading by an arbitrary `SetLike` family of additive
subgroups, which is the generality Mathlib's `HomogeneousLocalization.Away.mk` has. The bundled
direct limit is stated for a grading by `R`-submodules, where the terms of the system and the
limit are `R`-modules: a `SetLike` family of additive subgroups carries no module structure over
the degree-zero part in Mathlib (there is no `Module ↥(𝒜 0) ↥(𝒜 i)` instance), so the system
could otherwise only be formed over `ℤ`.

The system is indexed by `ℕ` and its transition map from `n` to `m` is multiplication by
`a ^ (m - n)`; truncated subtraction keeps the map total and is harmless because it is only ever
used with `n ≤ m`. `HomogeneousLocalization.Away.directedSystem` is the pair of
`DirectedSystem` axioms for it.

Injectivity of the induced map out of the direct limit does **not** come from injectivity of the
maps `HomogeneousLocalization.Away.mkLinearMap` out of the individual terms — those are not
injective. It comes from `Module.DirectLimit.exists_of`: an element of the limit is the image of
some `x` in the `n`-th term, and if `x / aⁿ = 0` then `a ^ k * x = 0` for some `k`, which says
that `x` already dies at stage `n + k` of the system, hence was `0` in the limit.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01M8](https://stacks.math.columbia.edu/tag/01M8)
-/

@[expose] public noncomputable section

namespace HomogeneousLocalization.Away

universe u v w

/-! ### Fractions over a common denominator -/

section Elementary

variable {ι : Type u} {A : Type v} {σ : Type w} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜]
  {d : ι} {a : A}

/-- Multiplying a homogeneous element of degree `n • d` by `a ^ k` lands in degree
`(n + k) • d`. -/
public theorem pow_mul_mem (ha : a ∈ 𝒜 d) {n : ℕ} {x : A} (hx : x ∈ 𝒜 (n • d)) (k : ℕ) :
    a ^ k * x ∈ 𝒜 ((n + k) • d) := by
  rw [add_smul, add_comm (n • d)]
  exact SetLike.mul_mem_graded (SetLike.pow_mem_graded k ha) hx

/-- **Equality of two fractions.** `x / aⁿ = y / aᵐ` in `Away 𝒜 a` exactly when
`a ^ (k + m) * x = a ^ (k + n) * y` for some `k`. -/
public theorem mk_eq_mk_iff (ha : a ∈ 𝒜 d) (n m : ℕ) (x y : A)
    (hx : x ∈ 𝒜 (n • d)) (hy : y ∈ 𝒜 (m • d)) :
    Away.mk 𝒜 ha n x hx = Away.mk 𝒜 ha m y hy ↔
      ∃ k : ℕ, a ^ (k + m) * x = a ^ (k + n) * y := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk, Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  constructor
  · rintro ⟨⟨c, k, (rfl : a ^ k = c)⟩, hc⟩
    exact ⟨k, by simpa only [pow_add, mul_assoc] using hc⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨a ^ k, k, rfl⟩, by simpa only [pow_add, mul_assoc] using hk⟩

/-- **A fraction vanishes** exactly when some power of `a` annihilates its numerator. -/
public theorem mk_eq_zero_iff (ha : a ∈ 𝒜 d) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 ha n x hx = 0 ↔ ∃ k : ℕ, a ^ k * x = 0 := by
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := s.property
    exact ⟨k, by simpa only [hk] using hs⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨a ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers a) k⟩, hk⟩

/-- **Enlarging the denominator of a fraction**: `(a ^ k * x) / a ^ (n + k) = x / aⁿ`. This is the
compatibility of `x ↦ x / aⁿ` with the transition maps of the system. -/
public theorem mk_pow_mul (ha : a ∈ 𝒜 d) (n k : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d))
    (h : a ^ k * x ∈ 𝒜 ((n + k) • d)) :
    Away.mk 𝒜 ha (n + k) (a ^ k * x) h = Away.mk 𝒜 ha n x hx :=
  (mk_eq_mk_iff 𝒜 ha (n + k) n _ x h hx).mpr
    ⟨0, by rw [zero_add, zero_add, ← mul_assoc, ← pow_add]⟩

/-- **Rewriting a fraction over a larger power of `a`.** -/
public theorem mk_eq_mk_of_le (ha : a ∈ 𝒜 d) {n m : ℕ} (hnm : n ≤ m) (x : A)
    (hx : x ∈ 𝒜 (n • d)) (h : a ^ (m - n) * x ∈ 𝒜 (m • d)) :
    Away.mk 𝒜 ha m (a ^ (m - n) * x) h = Away.mk 𝒜 ha n x hx :=
  (mk_eq_mk_iff 𝒜 ha m n _ x h hx).mpr
    ⟨0, by rw [zero_add, zero_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]⟩

/-- **A finite family of elements of `Away 𝒜 a` can be put over a common denominator.** -/
public theorem exists_forall_eq_mk (ha : a ∈ 𝒜 d) {κ : Type*} [Finite κ] (z : κ → Away 𝒜 a) :
    ∃ (n : ℕ) (y : κ → A) (hy : ∀ i, y i ∈ 𝒜 (n • d)),
      ∀ i, z i = Away.mk 𝒜 ha n (y i) (hy i) := by
  classical
  have := Fintype.ofFinite κ
  choose n y hy hz using fun i ↦ Away.mk_surjective 𝒜 ha (z i)
  set N := Finset.univ.sup n with hN
  have hle : ∀ i, n i ≤ N := fun i ↦ Finset.le_sup (f := n) (Finset.mem_univ i)
  have hmem : ∀ i, a ^ (N - n i) * y i ∈ 𝒜 (N • d) := fun i ↦ by
    have := pow_mul_mem 𝒜 ha (hy i) (N - n i)
    rwa [Nat.add_sub_cancel' (hle i)] at this
  exact ⟨N, fun i ↦ a ^ (N - n i) * y i, hmem,
    fun i ↦ ((mk_eq_mk_of_le 𝒜 ha (hle i) (y i) (hy i) (hmem i)).trans (hz i)).symm⟩

end Elementary

/-! ### The direct limit -/

section DirectLimit

variable {ι : Type u} {R : Type v} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → Submodule R A) [GradedRing 𝒜]
  {d : ι} {a : A} (ha : a ∈ 𝒜 d)

/-- The transition map `𝒜 (n • d) → 𝒜 (m • d)` of the system, multiplication by `a ^ (m - n)`.
It is only meaningful for `n ≤ m`; the truncated subtraction keeps it total. -/
public def mulPow (n m : ℕ) (_ : n ≤ m) : 𝒜 (n • d) →ₗ[R] 𝒜 (m • d) where
  toFun x := ⟨a ^ (m - n) * x, by
    rcases Nat.le_total n m with h | h
    · have := pow_mul_mem 𝒜 ha x.2 (m - n)
      rwa [Nat.add_sub_cancel' h] at this
    · rw [Nat.sub_eq_zero_of_le h, pow_zero, one_mul]
      exact (Nat.le_antisymm h (by omega) ▸ x.2 : (x : A) ∈ 𝒜 (m • d))⟩
  map_add' x y := Subtype.ext (by simpa using mul_add (a ^ (m - n)) (x : A) y)
  map_smul' r x := Subtype.ext (by simp)

@[simp]
public theorem coe_mulPow (n m : ℕ) (h : n ≤ m) (x : 𝒜 (n • d)) :
    (mulPow 𝒜 ha n m h x : A) = a ^ (m - n) * x := rfl

public instance directedSystem :
    DirectedSystem (fun n : ℕ ↦ (𝒜 (n • d) : Type _)) (mulPow 𝒜 ha · · ·) := by
  refine ⟨?_, ?_⟩
  · intro i x
    exact Subtype.ext (by simp)
  · intro k j i hij hjk x
    refine Subtype.ext ?_
    simp only [coe_mulPow, ← mul_assoc, ← pow_add]
    congr 2
    omega

/-- The `n`-th map into the degree-zero localization, `x ↦ x / aⁿ`. -/
public def mkLinearMap (n : ℕ) : 𝒜 (n • d) →ₗ[R] Away 𝒜 a where
  toFun x := Away.mk 𝒜 ha n x x.2
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
      Localization.add_mk_self]
    rfl
  map_smul' r x := by
    apply HomogeneousLocalization.val_injective
    rw [RingHom.id_apply, Algebra.smul_def, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_algebraMap, Away.val_mk, Away.val_mk,
      ← Algebra.smul_def, Localization.smul_mk]
    rfl

@[simp]
public theorem mkLinearMap_apply (n : ℕ) (x : 𝒜 (n • d)) :
    mkLinearMap 𝒜 ha n x = Away.mk 𝒜 ha n x x.2 := rfl

/-- The maps `x ↦ x / aⁿ` are compatible with the transition maps of the system. -/
public theorem mkLinearMap_mulPow (n m : ℕ) (h : n ≤ m) (x : 𝒜 (n • d)) :
    mkLinearMap 𝒜 ha m (mulPow 𝒜 ha n m h x) = mkLinearMap 𝒜 ha n x :=
  mk_eq_mk_of_le 𝒜 ha h x x.2 _

/-- The map out of the direct limit induced by the fractions `x ↦ x / aⁿ`. -/
public def directLimitLift :
    Module.DirectLimit (fun n : ℕ ↦ (𝒜 (n • d) : Type _)) (mulPow 𝒜 ha) →ₗ[R] Away 𝒜 a :=
  Module.DirectLimit.lift R ℕ _ _ (mkLinearMap 𝒜 ha) fun _ _ h x ↦ mkLinearMap_mulPow 𝒜 ha _ _ h x

@[simp]
public theorem directLimitLift_of (n : ℕ) (x : 𝒜 (n • d)) :
    directLimitLift 𝒜 ha (Module.DirectLimit.of R ℕ _ (mulPow 𝒜 ha) n x) =
      Away.mk 𝒜 ha n x x.2 :=
  Module.DirectLimit.lift_of ..

public theorem directLimitLift_surjective : Function.Surjective (directLimitLift 𝒜 ha) := by
  intro z
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 ha z
  exact ⟨Module.DirectLimit.of R ℕ _ (mulPow 𝒜 ha) n ⟨x, hx⟩, directLimitLift_of 𝒜 ha n ⟨x, hx⟩⟩

public theorem directLimitLift_injective : Function.Injective (directLimitLift 𝒜 ha) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨n, x, rfl⟩ := Module.DirectLimit.exists_of z
  rw [directLimitLift_of] at hz
  obtain ⟨k, hk⟩ := (mk_eq_zero_iff 𝒜 ha n x x.2).mp hz
  have hstep : mulPow 𝒜 ha n (n + k) (Nat.le_add_right n k) x = 0 :=
    Subtype.ext (by simpa using hk)
  rw [show Module.DirectLimit.of R ℕ _ (mulPow 𝒜 ha) n x =
      Module.DirectLimit.of R ℕ _ (mulPow 𝒜 ha) (n + k)
        (mulPow 𝒜 ha n (n + k) (Nat.le_add_right n k) x) from Module.DirectLimit.of_f.symm,
    hstep, map_zero]

/-- **`Away 𝒜 a` is the direct limit of the graded pieces `𝒜 (n • d)` along multiplication by
`a`.** The fraction `x / aⁿ` is the image of `x` in the `n`-th term of the system. -/
public def directLimitEquiv :
    Module.DirectLimit (fun n : ℕ ↦ (𝒜 (n • d) : Type _)) (mulPow 𝒜 ha) ≃ₗ[R] Away 𝒜 a :=
  LinearEquiv.ofBijective (directLimitLift 𝒜 ha)
    ⟨directLimitLift_injective 𝒜 ha, directLimitLift_surjective 𝒜 ha⟩

@[simp]
public theorem directLimitEquiv_of (n : ℕ) (x : 𝒜 (n • d)) :
    directLimitEquiv 𝒜 ha (Module.DirectLimit.of R ℕ _ (mulPow 𝒜 ha) n x) =
      Away.mk 𝒜 ha n x x.2 :=
  directLimitLift_of 𝒜 ha n x

end DirectLimit

end HomogeneousLocalization.Away

end
