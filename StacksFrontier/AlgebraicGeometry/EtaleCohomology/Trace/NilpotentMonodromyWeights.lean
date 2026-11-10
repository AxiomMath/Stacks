module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Weights on the kernel of a nilpotent monodromy operator

Let `V` be a finite-dimensional vector space with an endomorphism `F` (a Frobenius) and a nilpotent
endomorphism `N` (the logarithm of a unipotent local monodromy) such that `N F = q F N`. Suppose
that the eigenvalues of `F ⊗ F` on `ker (N ⊗ 1 + 1 ⊗ N) ⊆ V ⊗ V` have absolute value at most `Q`,
and dually for `V^∨` with a bound `Q'`, where `Q Q' = 1`. Then every eigenvalue `α` of `F` on
`ker N` satisfies `|α|² |q|^i = Q` for a natural number `i`. With `Q = |q| ^ w` this says that
`ker N` is strongly `ι`-mixed of weights `w - i`, `i ∈ ℕ`.

## Main definitions

* `Stacks.EtaleCohomology.monodromyTensor`: the tensor `∑_{j ≤ i} (-1)^j N^j x ⊗ N^{i-j} x`.

## Main results

* `Stacks.EtaleCohomology.norm_sq_mul_le_of_mem_range_pow`: the upper bound `|α|² |q|^i ≤ Q`.
* `Stacks.EtaleCohomology.norm_inv_sq_mul_le_of_mem_range_pow_of_notMem`: the dual bound.
* `Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_monodromy`: the equality `|α|² |q|^i = Q`
  with `i ∈ ℕ` for every eigenvalue `α` of `F` on `ker N`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.6 and 1.8.4.
* K. Kedlaya, *Fourier transforms and `p`-adic Weil II*, Compos. Math. 142 (2006),
  Proposition 6.3.3.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

namespace Stacks.EtaleCohomology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ### Generalities -/

/-- In a subspace stable under `A`, a nonzero generalized eigenvector of `A` for `μ` gives a
nonzero eigenvector for `μ`. -/
public theorem exists_eigenvector_of_pow_sub_smul_apply_eq_zero {A : Module.End K V}
    {S : Submodule K V} (hS : ∀ y ∈ S, A y ∈ S) {μ : K} :
    ∀ (k : ℕ) {y : V}, y ∈ S → y ≠ 0 → ((A - μ • 1) ^ k) y = 0 →
      ∃ z ∈ S, z ≠ 0 ∧ A z = μ • z := by
  intro k
  induction k with
  | zero => intro y _ hy h; rw [pow_zero, Module.End.one_apply] at h; exact absurd h hy
  | succ k ih =>
    intro y hyS hy h
    by_cases h1 : (A - μ • 1) y = 0
    · refine ⟨y, hyS, hy, ?_⟩
      rw [LinearMap.sub_apply, sub_eq_zero] at h1
      simpa using h1
    · refine ih ?_ h1 ?_
      · rw [LinearMap.sub_apply]
        exact S.sub_mem (hS y hyS) (by simpa using S.smul_mem μ hyS)
      · rw [← Module.End.mul_apply, ← pow_succ]
        exact h

variable {F N : Module.End K V} {q : K}

/-- `A^k N' = s^k N' B^k` from `A N' = s N' B`. -/
private theorem pow_mul_eq_smul_mul_pow_of_mul_eq {A B N' : Module.End K V} {s : K}
    (h : A * N' = s • (N' * B)) (k : ℕ) : A ^ k * N' = s ^ k • (N' * B ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, h, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc, smul_smul,
      mul_assoc, ← pow_succ, ← pow_succ']

/-- `N^j F = q^j F N^j` from `N F = q F N`. -/
public theorem pow_mul_eq_smul_mul_pow (hNF : N * F = q • (F * N)) (j : ℕ) :
    N ^ j * F = q ^ j • (F * N ^ j) :=
  pow_mul_eq_smul_mul_pow_of_mul_eq hNF j

/-- `N^j p(F) = p(q^j F) N^j` from `N F = q F N`. -/
public theorem pow_mul_aeval_eq (hNF : N * F = q • (F * N)) (j : ℕ) (p : K[X]) :
    N ^ j * aeval F p = aeval (q ^ j • F) p * N ^ j := by
  have hpow : ∀ m : ℕ, N ^ j * F ^ m = (q ^ j • F) ^ m * N ^ j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, pow_mul_eq_smul_mul_pow hNF, mul_smul_comm,
        ← mul_assoc, pow_succ (q ^ j • F), mul_smul_comm, smul_mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, mul_add, add_mul, hp, hr]
  | monomial m a =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      mul_smul_comm, hpow]

/-- Evaluating a polynomial in `c • F` at an eigenvector of `F`. -/
public theorem aeval_smul_apply_of_apply_eq {α : K} {v : V} (hv : F v = α • v) (c : K)
    (p : K[X]) : aeval (c • F) p v = p.eval (c * α) • v := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, LinearMap.add_apply, hp, hr, eval_add, add_smul]
  | monomial m a =>
    have hpow : ∀ m : ℕ, ((c • F) ^ m) v = (c * α) ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, Module.End.mul_apply, LinearMap.smul_apply, hv, map_smul, map_smul, ih,
          smul_smul, smul_smul, pow_succ]
        ring_nf
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, hpow, eval_monomial, smul_smul]

/-- **A projector onto a generalized eigenspace, as a polynomial in `F`.** For every `μ` there are
`m` and a polynomial `P` with `P(μ) = 1` such that `(F - μ)^m P(F) = 0` and `P(F)` is the identity
on `ker (F - μ)^m`. -/
public theorem exists_aeval_projector [FiniteDimensional K V] (F : Module.End K V) (μ : K) :
    ∃ (m : ℕ) (P : K[X]), P.eval μ = 1 ∧ (F - μ • 1) ^ m * aeval F P = 0 ∧
      ∀ y, ((F - μ • 1) ^ m) y = 0 → aeval F P y = y := by
  set χ := F.charpoly
  obtain ⟨r, hχ, hr⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd χ
    (LinearMap.charpoly_monic F).ne_zero μ
  set a := χ.rootMultiplicity μ
  have hcop : IsCoprime ((X - C μ) ^ (a + 1)) r :=
    ((Polynomial.irreducible_X_sub_C μ).coprime_iff_not_dvd.2 hr).pow_left
  obtain ⟨A, B, hAB⟩ := hcop
  have hXF : aeval F (X - C μ) = F - μ • 1 := by
    simp [Algebra.algebraMap_eq_smul_one]
  refine ⟨a + 1, B * r, ?_, ?_, ?_⟩
  · simpa using congrArg (eval μ) hAB
  · have hmul : (X - C μ) ^ (a + 1) * (B * r) = B * (X - C μ) * χ := by
      rw [hχ]; ring
    have hz : aeval F χ = 0 := LinearMap.aeval_self_charpoly F
    have := congrArg (aeval F) hmul
    rw [map_mul, map_pow, hXF, map_mul, map_mul, hz, mul_zero] at this
    rwa [map_mul]
  · intro y hy
    have hP : B * r = 1 - A * (X - C μ) ^ (a + 1) := by rw [← hAB]; ring
    rw [hP, map_sub, map_one, map_mul, map_pow, hXF, LinearMap.sub_apply, Module.End.one_apply,
      Module.End.mul_apply, hy, map_zero, sub_zero]

/-- A vector outside a subspace is detected by a linear form vanishing on the subspace. -/
private theorem exists_dual_ne_zero_of_notMem {p : Submodule K V} {x : V} (hx : x ∉ p) :
    ∃ φ : Module.Dual K V, φ x ≠ 0 ∧ ∀ y ∈ p, φ y = 0 := by
  obtain ⟨φ, hφx, hφp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨φ, hφx, fun y hy => ?_⟩
  have : φ y ∈ p.map φ := Submodule.mem_map_of_mem hy
  rw [hφp] at this
  simpa using this

/-- The generalized eigenvectors of `F ⊗ F`: if `(F - l₁)^k a = 0` and `(F - l₂)^l b = 0`, then
`(F ⊗ F - l₁ l₂)^(k + l) (a ⊗ b) = 0`. -/
public theorem map_sub_smul_pow_tmul_eq_zero {F : Module.End K V} {l₁ l₂ : K} :
    ∀ (n k l : ℕ) {a b : V}, k + l = n → ((F - l₁ • 1) ^ k) a = 0 → ((F - l₂ • 1) ^ l) b = 0 →
      ((TensorProduct.map F F - (l₁ * l₂) • 1) ^ n) (a ⊗ₜ[K] b) = 0 := by
  intro n
  induction n with
  | zero =>
    intro k l a b hkl ha _
    have hk : k = 0 := by omega
    subst hk
    simp at ha
    simp [ha]
  | succ n ih =>
    intro k l a b hkl ha hb
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp at ha; simp [ha]
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp at hb; simp [hb]
    have hstep : (TensorProduct.map F F - (l₁ * l₂) • 1) (a ⊗ₜ[K] b) =
        ((F - l₁ • 1) a) ⊗ₜ[K] (F b) + a ⊗ₜ[K] (l₁ • ((F - l₂ • 1) b)) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        TensorProduct.map_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
        TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_sub, smul_smul]
      abel
    rw [pow_succ, Module.End.mul_apply, hstep, map_add]
    have hcomm : ∀ m : ℕ, ((F - l₂ • 1) ^ m) (F b) = F (((F - l₂ • 1) ^ m) b) := by
      intro m
      rw [← Module.End.mul_apply, ← Module.End.mul_apply]
      congr 1
      exact ((Commute.sub_left (Commute.refl F)
        (Commute.smul_left (Commute.one_left F) _)).pow_left m).eq
    have h1 := ih (k - 1) l (by omega) (a := (F - l₁ • 1) a) (b := F b)
      (by rwa [← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel hk])
      (by rw [hcomm, hb, map_zero])
    have h2 := ih k (l - 1) (by omega) (a := a) (b := l₁ • ((F - l₂ • 1) b)) ha
      (by rw [map_smul, ← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel hl, hb,
        smul_zero])
    rw [h1, h2, add_zero]

/-! ### The upper bound -/

/-- `A^k N' = s^k N' B^k` from `A N' = s N' B`. -/
public theorem pow_mul_eq_smul_pow_mul_of_mul_eq {A B N' : Module.End K V} {s : K}
    (h : A * N' = s • (N' * B)) (k : ℕ) : A ^ k * N' = s ^ k • (N' * B ^ k) :=
  pow_mul_eq_smul_mul_pow_of_mul_eq h k

/-- `N^j` maps the generalized eigenspace of `F` for `μ` to that for `μ q^{-j}`. -/
public theorem pow_sub_smul_pow_apply_eq_zero (hNF : N * F = q • (F * N)) (hq : q ≠ 0) {μ : K}
    {k : ℕ} {x : V} (hx : ((F - μ • 1) ^ k) x = 0) (j : ℕ) :
    ((F - (μ * q⁻¹ ^ j) • 1) ^ k) ((N ^ j) x) = 0 := by
  have hFN : (F - (μ * q⁻¹ ^ j) • 1) * N ^ j = q⁻¹ ^ j • (N ^ j * (F - μ • 1)) := by
    have h1 := pow_mul_eq_smul_mul_pow hNF j
    have h2 : F * N ^ j = q⁻¹ ^ j • (N ^ j * F) := by
      rw [h1, smul_smul, ← mul_pow, inv_mul_cancel₀ hq, one_pow, one_smul]
    rw [sub_mul, h2, mul_sub, smul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
      smul_smul, mul_comm μ]
  have := pow_mul_eq_smul_pow_mul_of_mul_eq hFN k
  rw [← Module.End.mul_apply, this, LinearMap.smul_apply, Module.End.mul_apply, hx, map_zero,
    smul_zero]

/-- The tensor `∑_{j ≤ i} (-1)^j N^j x ⊗ N^{i-j} x`. -/
public def monodromyTensor (N : Module.End K V) (x : V) (i : ℕ) : V ⊗[K] V :=
  ∑ j ∈ Finset.range (i + 1), ((-1 : K) ^ j) • ((N ^ j) x ⊗ₜ[K] (N ^ (i - j)) x)

/-- If `N^{i+1} x = 0`, the tensor `∑_{j ≤ i} (-1)^j N^j x ⊗ N^{i-j} x` is killed by
`N ⊗ 1 + 1 ⊗ N`. -/
public theorem rTensor_add_lTensor_monodromyTensor {x : V} {i : ℕ} (hx : (N ^ (i + 1)) x = 0) :
    (N.rTensor V + N.lTensor V) (monodromyTensor N x i) = 0 := by
  set t : ℕ → V ⊗[K] V := fun j => (N ^ j) x ⊗ₜ[K] (N ^ (i + 1 - j)) x
  have hterm : ∀ j ∈ Finset.range (i + 1),
      (N.rTensor V + N.lTensor V) (((-1 : K) ^ j) • ((N ^ j) x ⊗ₜ[K] (N ^ (i - j)) x)) =
        (-1 : K) ^ j • t j - (-1 : K) ^ (j + 1) • t (j + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have e1 : i + 1 - (j + 1) = i - j := by omega
    have e2 : i + 1 - j = i - j + 1 := by omega
    simp only [t, e1, e2, map_smul, LinearMap.add_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, pow_succ (-1 : K), mul_neg_one, neg_smul, sub_neg_eq_add,
      smul_add]
    rw [← Module.End.mul_apply N (N ^ j), ← pow_succ', ← Module.End.mul_apply N (N ^ (i - j)),
      ← pow_succ']
    abel
  rw [monodromyTensor, map_sum, Finset.sum_congr rfl hterm,
    Finset.sum_range_sub' (fun j => (-1 : K) ^ j • t j)]
  simp only [t, Nat.sub_zero, Nat.sub_self, pow_zero, hx, TensorProduct.tmul_zero,
    TensorProduct.zero_tmul, smul_zero, sub_zero]

/-- If `N^i x ≠ 0` and `N^{i+1} x = 0`, the tensor `∑_{j ≤ i} (-1)^j N^j x ⊗ N^{i-j} x` is
nonzero. -/
public theorem monodromyTensor_ne_zero {x : V} {i : ℕ} (hx : (N ^ i) x ≠ 0)
    (hx' : (N ^ (i + 1)) x = 0) : monodromyTensor N x i ≠ 0 := by
  set p := Submodule.span K (Set.range fun j : Fin i => (N ^ ((j : ℕ) + 1)) x)
  have hp : p ≤ LinearMap.ker (N ^ i) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_add,
      show i + ((j : ℕ) + 1) = (j : ℕ) + (i + 1) by omega, pow_add, Module.End.mul_apply, hx',
      map_zero]
  have hxp : x ∉ p := fun h => hx (hp h)
  obtain ⟨φ, hφx, hφp⟩ := exists_dual_ne_zero_of_notMem hxp
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (p := (⊥ : Submodule K V)) (by simpa using hx) inferInstance
  let Φ : V ⊗[K] V →ₗ[K] K := TensorProduct.lift ((LinearMap.mul K K).compl₁₂ φ ψ)
  have hΦ : ∀ a b, Φ (a ⊗ₜ[K] b) = φ a * ψ b := fun a b => by simp [Φ]
  intro h0
  have hval := congrArg Φ h0
  rw [map_zero, monodromyTensor, map_sum, Finset.sum_range_succ'] at hval
  have hrest : ∀ j ∈ Finset.range i, Φ (((-1 : K) ^ (j + 1)) •
      ((N ^ (j + 1)) x ⊗ₜ[K] (N ^ (i - (j + 1))) x)) = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hmem : (N ^ (j + 1)) x ∈ p := Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    rw [map_smul, hΦ, hφp _ hmem, zero_mul, smul_zero]
  rw [Finset.sum_eq_zero hrest, zero_add, pow_zero, one_smul, hΦ, pow_zero, Nat.sub_zero,
    Module.End.one_apply] at hval
  exact mul_ne_zero hφx hψ hval

/-- If `x` is a generalized eigenvector of `F` for `μ`, the tensor
`∑_{j ≤ i} (-1)^j N^j x ⊗ N^{i-j} x` is a generalized eigenvector of `F ⊗ F` for `μ² q^{-i}`. -/
public theorem monodromyTensor_genEigen (hNF : N * F = q • (F * N)) (hq : q ≠ 0) {μ : K}
    {k : ℕ} {x : V} (hx : ((F - μ • 1) ^ k) x = 0) (i : ℕ) :
    ((TensorProduct.map F F - (μ ^ 2 * q⁻¹ ^ i) • 1) ^ (k + k)) (monodromyTensor N x i) = 0 := by
  rw [monodromyTensor, map_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hc : μ ^ 2 * q⁻¹ ^ i = (μ * q⁻¹ ^ j) * (μ * q⁻¹ ^ (i - j)) := by
    rw [show μ * q⁻¹ ^ j * (μ * q⁻¹ ^ (i - j)) = μ ^ 2 * (q⁻¹ ^ j * q⁻¹ ^ (i - j)) by ring,
      ← pow_add, Nat.add_sub_cancel' (by omega)]
  rw [map_smul, hc, map_sub_smul_pow_tmul_eq_zero (k + k) k k rfl
    (pow_sub_smul_pow_apply_eq_zero hNF hq hx j) (pow_sub_smul_pow_apply_eq_zero hNF hq hx _),
    smul_zero]

/-- `ker (N ⊗ 1 + 1 ⊗ N)` is stable under `F ⊗ F` when `N F = q F N`. -/
public theorem rTensor_add_lTensor_map_eq_zero (hNF : N * F = q • (F * N)) {T : V ⊗[K] V}
    (hT : (N.rTensor V + N.lTensor V) T = 0) :
    (N.rTensor V + N.lTensor V) (TensorProduct.map F F T) = 0 := by
  have hcomm : (N.rTensor V + N.lTensor V) ∘ₗ TensorProduct.map F F =
      q • (TensorProduct.map F F ∘ₗ (N.rTensor V + N.lTensor V)) := by
    apply TensorProduct.ext'
    intro a b
    have hNa : N (F a) = q • F (N a) := by
      simpa using congrArg (fun g : Module.End K V => g a) hNF
    have hNb : N (F b) = q • F (N b) := by
      simpa using congrArg (fun g : Module.End K V => g b) hNF
    simp [hNa, hNb, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
  have := congrArg (fun g => g T) hcomm
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, hT, map_zero,
    smul_zero] using this

/-- A preimage under `N^i` of an eigenvector of `F`, projected to the generalized eigenspace of
`F` for `q^i α`, is still a preimage and is killed by a power of `F - q^i α`. -/
private theorem exists_aeval_projector_pow_apply_eq [FiniteDimensional K V]
    (hNF : N * F = q • (F * N)) {v x₀ : V} {α : K} (hFv : F v = α • v) {i : ℕ}
    (hx₀ : (N ^ i) x₀ = v) :
    ∃ (m : ℕ) (P : K[X]), (F - (q ^ i * α) • 1) ^ m * aeval F P = 0 ∧
      (∀ y, ((F - (q ^ i * α) • 1) ^ m) y = 0 → aeval F P y = y) ∧
      (N ^ i) (aeval F P x₀) = v ∧ ((F - (q ^ i * α) • 1) ^ m) (aeval F P x₀) = 0 := by
  obtain ⟨m, P, hPμ, hPker, hPid⟩ := exists_aeval_projector F (q ^ i * α)
  refine ⟨m, P, hPker, hPid, ?_, ?_⟩
  · rw [← Module.End.mul_apply, pow_mul_aeval_eq hNF, Module.End.mul_apply, hx₀,
      aeval_smul_apply_of_apply_eq hFv, hPμ, one_smul]
  · rw [← Module.End.mul_apply, hPker, LinearMap.zero_apply]

/-- If `G F = 1` and `F v = α v` with `v ≠ 0`, then `α ≠ 0`. -/
private theorem ne_zero_of_apply_eq_smul {G : Module.End K V} (hGF : G * F = 1) {v : V} {α : K}
    (hv0 : v ≠ 0) (hFv : F v = α • v) : α ≠ 0 := by
  rintro rfl
  refine hv0 ?_
  have : G (F v) = v := by rw [← Module.End.mul_apply, hGF, Module.End.one_apply]
  rw [← this, hFv, zero_smul, map_zero]

/-- **The upper bound.** Let `N F = q F N` with `q ≠ 0`, and suppose every eigenvalue `c` of
`F ⊗ F` on `ker (N ⊗ 1 + 1 ⊗ N)` satisfies `|ι c| ≤ Q`. If `v ≠ 0` lies in `ker N` and in the image
of `N^i` and `F v = α v`, then `|ι α|² |ι q|^i ≤ Q`. -/
public theorem norm_sq_mul_le_of_mem_range_pow [FiniteDimensional K V] (ι : K →+* ℂ) {Q : ℝ}
    (hNF : N * F = q • (F * N)) (hq : q ≠ 0)
    (H : ∀ (T : V ⊗[K] V) (c : K), T ≠ 0 → (N.rTensor V + N.lTensor V) T = 0 →
      TensorProduct.map F F T = c • T → ‖ι c‖ ≤ Q)
    {v : V} {α : K} (hv0 : v ≠ 0) (hNv : N v = 0) (hFv : F v = α • v) {i : ℕ}
    (hvi : v ∈ LinearMap.range (N ^ i)) : ‖ι α‖ ^ 2 * ‖ι q‖ ^ i ≤ Q := by
  obtain ⟨x₀, hx₀⟩ := hvi
  set μ := q ^ i * α
  obtain ⟨m, P, -, -, hxv, hxμ⟩ := exists_aeval_projector_pow_apply_eq hNF hFv hx₀
  set x := aeval F P x₀
  have hx' : (N ^ (i + 1)) x = 0 := by
    rw [pow_succ', Module.End.mul_apply, hxv, hNv]
  set S := LinearMap.ker (N.rTensor V + N.lTensor V)
  have hS : ∀ y ∈ S, TensorProduct.map F F y ∈ S := fun y hy =>
    LinearMap.mem_ker.2 (rTensor_add_lTensor_map_eq_zero hNF (LinearMap.mem_ker.1 hy))
  obtain ⟨T, hTS, hT0, hTF⟩ := exists_eigenvector_of_pow_sub_smul_apply_eq_zero hS (m + m)
    (rTensor_add_lTensor_monodromyTensor hx') (monodromyTensor_ne_zero (by rwa [hxv]) hx')
    (monodromyTensor_genEigen hNF hq hxμ i)
  have hb := H T _ hT0 hTS hTF
  have hc : μ ^ 2 * q⁻¹ ^ i = α ^ 2 * q ^ i := by
    simp only [μ]
    rw [inv_pow, mul_pow, ← pow_mul, show i * 2 = i + i by ring, pow_add]
    field_simp
  rwa [hc, map_mul, map_pow, map_pow, norm_mul, norm_pow, norm_pow] at hb

/-! ### The lower bound, by duality -/

/-- An endomorphism commuting with `F` commutes with every polynomial in `F`. -/
public theorem commute_aeval_of_commute {G : Module.End K V} (h : Commute G F) (p : K[X]) :
    Commute G (aeval F p) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add]; exact hp.add_right hr
  | monomial m a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (h.pow_right m).smul_right a

/-- A linear form vanishing on `ker g` factors through `g`. -/
public theorem exists_comp_eq_of_ker_le {W : Type*} [AddCommGroup W] [Module K W]
    {g : V →ₗ[K] W} {f : V →ₗ[K] K} (h : LinearMap.ker g ≤ LinearMap.ker f) :
    ∃ ψ : W →ₗ[K] K, ∀ y, ψ (g y) = f y := by
  let h₀ : LinearMap.range g →ₗ[K] K :=
    (LinearMap.ker g).liftQ f h ∘ₗ g.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend h₀
  refine ⟨ψ, fun y => ?_⟩
  have := congrArg (fun φ => φ ⟨g y, y, rfl⟩) hψ
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
  have hu : g.quotKerEquivRange.symm ⟨g y, y, rfl⟩ = (LinearMap.ker g).mkQ y := by
    apply g.quotKerEquivRange.injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk g y).symm
  rw [this]
  simp only [h₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [hu, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- The `i`-th power of `-N^∨ : φ ↦ -(φ ∘ N)` sends `ψ` to `(-1)^i ψ ∘ N^i`. -/
public theorem neg_dualMap_pow_apply (N : Module.End K V) (i : ℕ) (ψ : Module.Dual K V) (y : V) :
    (((-N.dualMap) ^ i) ψ) y = (-1 : K) ^ i * ψ ((N ^ i) y) := by
  induction i generalizing y with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, LinearMap.neg_apply,
      LinearMap.dualMap_apply, ih, pow_succ, pow_succ, Module.End.mul_apply]
    ring

/-- `(G^∨ - c)^k φ = φ ∘ (G - c)^k`. -/
public theorem dualMap_sub_smul_pow_apply (G : Module.End K V) (c : K) (k : ℕ)
    (φ : Module.Dual K V) (y : V) :
    (((G.dualMap - c • 1) ^ k) φ) y = φ (((G - c • 1) ^ k) y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    have e1 : ((G - c • 1) ^ (k + 1)) y = ((G - c • 1) ^ k) (G y) - c • ((G - c • 1) ^ k) y := by
      rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, map_smul]
    rw [e1, map_sub, map_smul, smul_eq_mul, ← ih, ← ih, pow_succ', Module.End.mul_apply]
    simp [LinearMap.dualMap_apply]

/-- **The lower bound.** Let `N F = q F N` with `q ≠ 0` and `G F = F G = 1`, and suppose every
eigenvalue `c` of `G^∨ ⊗ G^∨` on `ker ((-N^∨) ⊗ 1 + 1 ⊗ (-N^∨)) ⊆ V^∨ ⊗ V^∨` satisfies
`|ι c| ≤ Q'`, where `G^∨ : φ ↦ φ ∘ G` and `-N^∨ : φ ↦ -(φ ∘ N)`. If `v ≠ 0` lies in `ker N` and in
the image of `N^i` but not of `N^{i+1}`, and `F v = α v`, then `|ι (q^i α)⁻¹|² |ι q|^i ≤ Q'`. -/
public theorem norm_inv_sq_mul_le_of_mem_range_pow_of_notMem [FiniteDimensional K V]
    (ι : K →+* ℂ) {Q' : ℝ} (hNF : N * F = q • (F * N)) (hq : q ≠ 0) {G : Module.End K V}
    (hGF : G * F = 1) (hFG : F * G = 1)
    (H : ∀ (T : Module.Dual K V ⊗[K] Module.Dual K V) (c : K), T ≠ 0 →
      ((-N.dualMap).rTensor (Module.Dual K V) + (-N.dualMap).lTensor (Module.Dual K V)) T = 0 →
      TensorProduct.map G.dualMap G.dualMap T = c • T → ‖ι c‖ ≤ Q')
    {v : V} {α : K} (hv0 : v ≠ 0) (_hNv : N v = 0) (hFv : F v = α • v) {i : ℕ}
    (hvi : v ∈ LinearMap.range (N ^ i)) (hvi' : v ∉ LinearMap.range (N ^ (i + 1))) :
    ‖ι (q ^ i * α)⁻¹‖ ^ 2 * ‖ι q‖ ^ i ≤ Q' := by
  obtain ⟨x₀, hx₀⟩ := hvi
  set μ := q ^ i * α
  obtain ⟨m, P, hPker, hPid, hxv, hxμ⟩ := exists_aeval_projector_pow_apply_eq hNF hFv hx₀
  set x := aeval F P x₀
  have hPx : aeval F P x = x := hPid x hxμ
  have hxnot : x ∉ LinearMap.range N ⊔ LinearMap.ker (N ^ i) := by
    intro hx
    obtain ⟨y, ⟨z, rfl⟩, w, hw, hyw⟩ := Submodule.mem_sup.1 hx
    refine hvi' ⟨z, ?_⟩
    rw [← hxv, ← hyw, map_add, LinearMap.mem_ker.1 hw, add_zero, pow_succ,
      Module.End.mul_apply]
  obtain ⟨φ₀, hφ₀x, hφ₀⟩ := exists_dual_ne_zero_of_notMem hxnot
  set φ : Module.Dual K V := φ₀ ∘ₗ aeval F P
  have hφx : φ x ≠ 0 := by simpa [φ, hPx] using hφ₀x
  have hNF' : N * (q⁻¹ • F) = q • ((q⁻¹ • F) * N) := by
    rw [mul_smul_comm, hNF, smul_mul_assoc, smul_smul, smul_smul, mul_comm]
  have hPN : ∀ y, aeval F P (N y) ∈ LinearMap.range N := fun y => by
    have := pow_mul_aeval_eq hNF' 1 P
    rw [pow_one, pow_one, smul_smul, mul_inv_cancel₀ hq, one_smul] at this
    exact ⟨aeval (q⁻¹ • F) P y, by rw [← Module.End.mul_apply, this, Module.End.mul_apply]⟩
  have hφN : ∀ y, φ (N y) = 0 := fun y => hφ₀ _ (Submodule.mem_sup_left (hPN y))
  have hφker : LinearMap.ker (N ^ i) ≤ LinearMap.ker φ := fun y hy => by
    refine LinearMap.mem_ker.2 (hφ₀ _ (Submodule.mem_sup_right ?_))
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, pow_mul_aeval_eq hNF, Module.End.mul_apply,
      LinearMap.mem_ker.1 hy, map_zero]
  set N' : Module.End K (Module.Dual K V) := -N.dualMap
  set S := LinearMap.ker N' ⊓ LinearMap.range (N' ^ i)
  have hφS : φ ∈ S := by
    refine ⟨LinearMap.mem_ker.2 (LinearMap.ext fun y => ?_), ?_⟩
    · simp [N', hφN]
    · obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_ker_le hφker
      refine ⟨(-1 : K) ^ i • ψ, LinearMap.ext fun y => ?_⟩
      rw [neg_dualMap_pow_apply, LinearMap.smul_apply, smul_eq_mul, hψ, ← mul_assoc, ← pow_add,
        ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have hNF'' : N' * G.dualMap = q • (G.dualMap * N') := by
    have hGN : G * N = q • (N * G) := by
      calc G * N = G * (N * F) * G := by rw [mul_assoc, mul_assoc, hFG, mul_one]
        _ = G * (q • (F * N)) * G := by rw [hNF]
        _ = q • (N * G) := by
          rw [mul_smul_comm, ← mul_assoc, hGF, one_mul, smul_mul_assoc]
    ext φ' y
    simp only [N', Module.End.mul_apply, LinearMap.neg_apply, LinearMap.dualMap_apply,
      LinearMap.smul_apply, map_neg, LinearMap.neg_apply, LinearMap.smul_apply]
    have := congrArg (fun g : Module.End K V => φ' (g y)) hGN
    simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul] at this
    rw [this]
    simp
  have hSst : ∀ y ∈ S, G.dualMap y ∈ S := by
    rintro y ⟨hy1, ⟨z, rfl⟩⟩
    have hy1' : N' ((N' ^ i) z) = 0 := hy1
    refine ⟨?_, ?_⟩
    · change G.dualMap ((N' ^ i) z) ∈ LinearMap.ker N'
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, hNF'', LinearMap.smul_apply,
        Module.End.mul_apply, hy1', map_zero, smul_zero]
    · refine ⟨(q⁻¹ ^ i) • G.dualMap z, ?_⟩
      rw [map_smul, ← Module.End.mul_apply, pow_mul_eq_smul_mul_pow hNF'', LinearMap.smul_apply,
        smul_smul, ← mul_pow, inv_mul_cancel₀ hq, one_pow, one_smul, Module.End.mul_apply]
  have hμ : μ ≠ 0 := mul_ne_zero (pow_ne_zero _ hq) (ne_zero_of_apply_eq_smul hGF hv0 hFv)
  have hGcomm : Commute G F := (hGF.trans hFG.symm)
  have hGμ : G - μ⁻¹ • 1 = (-μ⁻¹) • (G * (F - μ • 1)) := by
    rw [mul_sub, mul_smul_comm, mul_one, hGF, smul_sub, neg_smul, neg_smul, sub_neg_eq_add,
      smul_smul, inv_mul_cancel₀ hμ, one_smul]
    abel
  have hGμpow : (G - μ⁻¹ • 1) ^ m * aeval F P = 0 := by
    have hc : Commute G (F - μ • 1) :=
      hGcomm.sub_right (Commute.smul_right (Commute.one_right G) μ)
    rw [hGμ, smul_pow, hc.mul_pow, smul_mul_assoc, mul_assoc, hPker, mul_zero, smul_zero]
  have hφgen : ((G.dualMap - μ⁻¹ • 1) ^ m) φ = 0 := by
    ext y
    have hPc : Commute (aeval F P) ((G - μ⁻¹ • 1) ^ m) :=
      ((commute_aeval_of_commute
        (hGcomm.sub_left (Commute.smul_left (Commute.one_left F) _)) P).symm).pow_right m
    rw [dualMap_sub_smul_pow_apply, LinearMap.zero_apply]
    simp only [φ, LinearMap.coe_comp, Function.comp_apply]
    rw [← Module.End.mul_apply, hPc.eq, hGμpow, LinearMap.zero_apply, map_zero]
  have hφ0 : φ ≠ 0 := fun h => hφx (by rw [h, LinearMap.zero_apply])
  obtain ⟨ψ, hψS, hψ0, hψG⟩ := exists_eigenvector_of_pow_sub_smul_apply_eq_zero hSst m hφS hφ0
    hφgen
  exact norm_sq_mul_le_of_mem_range_pow ι hNF'' hq H hψ0 hψS.1 hψG hψS.2

/-! ### Strong mixedness of `ker N` -/

/-- **The eigenvalues of `F` on `ker N` drop the weight by integers** (Weil II, 1.8.4; Kedlaya,
Proposition 6.3.3). Let `N` be nilpotent with `N F = q F N`, `q ≠ 0`, `F` invertible with inverse
`G`, and `Q Q' = 1`. Suppose every eigenvalue `c` of `F ⊗ F` on `ker (N ⊗ 1 + 1 ⊗ N)` has
`|ι c| ≤ Q`, and every eigenvalue `c` of `G^∨ ⊗ G^∨` on `ker ((-N^∨) ⊗ 1 + 1 ⊗ (-N^∨))` has
`|ι c| ≤ Q'`. Then every eigenvalue `α` of `F` on `ker N` satisfies `|ι α|² |ι q|^i = Q` for a
natural number `i`.

With `Q = |q| ^ w` this says that `ker N` is strongly mixed of weights `w - i`, `i ∈ ℕ`. -/
public theorem exists_norm_sq_mul_pow_eq_of_monodromy [FiniteDimensional K V] (ι : K →+* ℂ)
    {Q Q' : ℝ} (hQQ' : Q * Q' = 1) (hNF : N * F = q • (F * N)) (hq : q ≠ 0)
    (hN : IsNilpotent N) {G : Module.End K V} (hGF : G * F = 1) (hFG : F * G = 1)
    (H : ∀ (T : V ⊗[K] V) (c : K), T ≠ 0 → (N.rTensor V + N.lTensor V) T = 0 →
      TensorProduct.map F F T = c • T → ‖ι c‖ ≤ Q)
    (H' : ∀ (T : Module.Dual K V ⊗[K] Module.Dual K V) (c : K), T ≠ 0 →
      ((-N.dualMap).rTensor (Module.Dual K V) + (-N.dualMap).lTensor (Module.Dual K V)) T = 0 →
      TensorProduct.map G.dualMap G.dualMap T = c • T → ‖ι c‖ ≤ Q')
    {v : V} {α : K} (hv0 : v ≠ 0) (hNv : N v = 0) (hFv : F v = α • v) :
    ∃ i : ℕ, ‖ι α‖ ^ 2 * ‖ι q‖ ^ i = Q := by
  classical
  obtain ⟨n, hn⟩ := hN
  have hex : ∃ k, v ∉ LinearMap.range (N ^ (k + 1)) := by
    refine ⟨n, fun ⟨y, hy⟩ => hv0 ?_⟩
    rw [← hy, pow_succ, hn, zero_mul, LinearMap.zero_apply]
  set i := Nat.find hex
  have hi' : v ∉ LinearMap.range (N ^ (i + 1)) := Nat.find_spec hex
  have hi : v ∈ LinearMap.range (N ^ i) := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0, pow_zero]
      exact ⟨v, rfl⟩
    · have := Nat.find_min hex (show i - 1 < i by omega)
      rwa [not_not, Nat.sub_add_cancel hpos] at this
  refine ⟨i, ?_⟩
  have hub := norm_sq_mul_le_of_mem_range_pow ι hNF hq H hv0 hNv hFv hi
  have hlb := norm_inv_sq_mul_le_of_mem_range_pow_of_notMem ι hNF hq hGF hFG H' hv0 hNv hFv hi
    hi'
  have hα := ne_zero_of_apply_eq_smul hGF hv0 hFv
  have hqn : 0 < ‖ι q‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hq)
  have han : 0 < ‖ι α‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hα)
  set a := ‖ι α‖ ^ 2 * ‖ι q‖ ^ i
  have ha : 0 < a := by positivity
  have hinv : ‖ι (q ^ i * α)⁻¹‖ ^ 2 * ‖ι q‖ ^ i = a⁻¹ := by
    simp only [a, map_inv₀, map_mul, map_pow, norm_inv, norm_mul, norm_pow]
    field_simp
  rw [hinv] at hlb
  have hQ' : 0 < Q' := (inv_pos.2 ha).trans_le hlb
  have h1 : 1 ≤ a * Q' := by
    have := mul_le_mul_of_nonneg_left hlb ha.le
    rwa [mul_inv_cancel₀ ha.ne'] at this
  have h2 : Q ≤ a := by
    by_contra hlt
    push Not at hlt
    have : a * Q' < Q * Q' := mul_lt_mul_of_pos_right hlt hQ'
    linarith
  exact le_antisymm hub h2

end Stacks.EtaleCohomology

end
