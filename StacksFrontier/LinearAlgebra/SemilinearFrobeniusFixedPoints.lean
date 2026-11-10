module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Lang's lemma for Frobenius-semilinear bijections

Let `Ω` be an algebraically closed field of characteristic `p`, let `q = p ^ f` with `f ≥ 1`, and
let `T` be an injective `q`-semilinear endomorphism of a finite-dimensional `Ω`-vector space `V`
of dimension `n`: `T (c • v) = c ^ q • T v`. Then `V` has a basis of `T`-fixed vectors, so the
fixed vectors are the `𝔽_q`-span of that basis; there are exactly `q ^ n` of them, and the
`T`-stable lines number `(q ^ n - 1) / (q - 1)`. Every `T`-stable subspace is again spanned by
fixed vectors, so there are only finitely many of them.

This is the linear algebra behind the count of Frobenius-stable effective divisors in a linear
system on a curve over `𝔽̄_q`: there `V` is the space of sections of an invertible sheaf whose
class is fixed by the `q`-Frobenius, and `T` is pullback along the Frobenius followed by the
fixing isomorphism.

The existence of one fixed vector is the heart (`Stacks.Lang.exists_fixed_ne_zero`). For
`v ≠ 0` let `k` be least with `T^k v` in the span of `v, …, T^{k-1} v`, say
`T^k v = ∑ c_i T^i v`; then `c_0 ≠ 0` by injectivity and minimality. The vector
`w = ∑_{i<k} x_i T^i v` with `x_0 = c_0 y^q`, `x_i = x_{i-1}^q + c_i y^q` satisfies
`T w - w = (x_{k-1}^q - y^q) T^k v`, and `x_{k-1} = P(y)` for a polynomial `P` of degree `q^k`
divisible by `T^2`, so `P(y) = y` has a nonzero root. A fixed basis follows by induction on the
dimension, lifting a fixed basis of `V / Ω w` with Artin–Schreier roots.

## Main results

* `Stacks.Lang.exists_fixed_ne_zero`, `Stacks.Lang.exists_basis_fixed`.
* `Stacks.Lang.natCard_fixed`: `q ^ n` fixed vectors.
* `Stacks.Lang.natCard_stable_mul`: `(q - 1) · #{T-stable points of ℙ(V)} = q ^ n - 1`.
* `Stacks.Lang.finite_stableSubmodules`: finitely many `T`-stable subspaces.
-/

@[expose] public noncomputable section

open Polynomial Module

namespace Stacks.Lang

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
  (f : ℕ) (hf : 0 < f)

/-! ### The fixed field -/

include hf in
/-- **The fixed field of `x ↦ x ^ q` has `q` elements.** -/
theorem natCard_pow_eq_self : Nat.card {a : Ω // a ^ p ^ f = a} = p ^ f := by
  classical
  have hq : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt
  have hsep : (X ^ p ^ f - X : Ω[X]).Separable :=
    galois_poly_separable p (p ^ f) (dvd_pow_self p hf.ne')
  have hdeg : (X ^ p ^ f - X : Ω[X]).natDegree = p ^ f := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hq]
  have hsplit : ((X ^ p ^ f - X : Ω[X]).map (algebraMap Ω Ω)).Splits :=
    IsAlgClosed.splits _
  calc Nat.card {a : Ω // a ^ p ^ f = a} = Nat.card ((X ^ p ^ f - X : Ω[X]).rootSet Ω) := by
        refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
        rw [mem_rootSet_of_ne (FiniteField.X_pow_card_pow_sub_X_ne_zero Ω hf.ne'
          hp.out.one_lt)]
        simp [sub_eq_zero]
    _ = p ^ f := by rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hsep hsplit, hdeg]

/-! ### One fixed vector -/

variable {V : Type*} [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V]
  (T : V →ₛₗ[iterateFrobenius Ω p f] V)

omit [IsAlgClosed Ω] [FiniteDimensional Ω V] in
/-- A `q`-semilinear map satisfies `T (c • v) = c ^ q • T v`, where `q = p ^ f`. -/
theorem map_smul_pow (c : Ω) (v : V) : T (c • v) = c ^ p ^ f • T v := by
  rw [T.map_smulₛₗ, iterateFrobenius_def]

/-- The polynomials `X_0 = c_0 Y^q`, `X_{j+1} = X_j ^ q + c_{j+1} Y^q` of the Krylov
computation. -/
def krylovPoly (c : ℕ → Ω) : ℕ → Ω[X]
  | 0 => C (c 0) * X ^ p ^ f
  | j + 1 => krylovPoly c j ^ p ^ f + C (c (j + 1)) * X ^ p ^ f

omit [IsAlgClosed Ω] [CharP Ω p] in
include hf in
/-- If `c 0 ≠ 0`, then `krylovPoly p f c j` has degree `q ^ (j + 1)`, where `q = p ^ f`. -/
theorem natDegree_krylovPoly (c : ℕ → Ω) (hc : c 0 ≠ 0) (j : ℕ) :
    (krylovPoly p f c j).natDegree = (p ^ f) ^ (j + 1) := by
  have hq : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt
  induction j with
  | zero => simp [krylovPoly, natDegree_C_mul_X_pow _ _ hc]
  | succ j ih =>
    rw [krylovPoly, natDegree_add_eq_left_of_natDegree_lt, natDegree_pow, ih, ← pow_succ']
    rw [natDegree_pow, ih]
    calc (C (c (j + 1)) * X ^ p ^ f : Ω[X]).natDegree ≤ p ^ f := natDegree_C_mul_X_pow_le _ _
      _ < p ^ f * (p ^ f) ^ (j + 1) := by
        have : 1 < (p ^ f) ^ (j + 1) := Nat.one_lt_pow (Nat.succ_ne_zero j) hq
        nlinarith

omit [IsAlgClosed Ω] [CharP Ω p] in
include hf in
/-- Every polynomial `krylovPoly p f c j` is divisible by `X ^ 2`. -/
theorem X_sq_dvd_krylovPoly (c : ℕ → Ω) (j : ℕ) : (X ^ 2 : Ω[X]) ∣ krylovPoly p f c j := by
  have hq : 2 ≤ p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt
  have h2 : (X ^ 2 : Ω[X]) ∣ X ^ p ^ f := pow_dvd_pow X hq
  induction j with
  | zero => exact dvd_mul_of_dvd_right h2 _
  | succ j ih =>
    exact dvd_add (dvd_pow ih (by omega)) (dvd_mul_of_dvd_right h2 _)

omit [CharP Ω p] in
include hf in
/-- **The additive equation has a nonzero solution**: `X_{k-1}(y) = y` for some `y ≠ 0`. -/
theorem exists_eval_krylovPoly_eq (c : ℕ → Ω) (hc : c 0 ≠ 0) (j : ℕ) :
    ∃ y : Ω, y ≠ 0 ∧ (krylovPoly p f c j).eval y = y := by
  obtain ⟨S, hS⟩ := X_sq_dvd_krylovPoly p f hf c j
  have hdeg := natDegree_krylovPoly p f hf c hc j
  have hS0 : S ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hS
    rw [hS, natDegree_zero] at hdeg
    exact (pow_ne_zero _ (pow_ne_zero _ hp.out.ne_zero)) hdeg.symm
  have hU : (X * S - 1 : Ω[X]).degree ≠ 0 := by
    have h1 : (1 : Ω[X]).degree < (X * S).degree := by
      rw [degree_one, degree_mul, degree_X]
      exact lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_right (zero_le_degree_iff.2 hS0))
    rw [degree_sub_eq_left_of_degree_lt h1]
    exact ne_of_gt (lt_of_le_of_lt (le_of_eq degree_one.symm) h1)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hU
  have hy' : y * S.eval y = 1 := by
    simpa [sub_eq_zero] using hy
  refine ⟨y, fun h => by simp [h] at hy', ?_⟩
  rw [hS, eval_mul, eval_pow, eval_X]
  linear_combination y * hy'

omit [IsAlgClosed Ω] hp [CharP Ω p] in
variable {p f} in
/-- The coefficients `x_j(y)` of the Krylov vector. -/
theorem eval_krylovPoly_succ (c : ℕ → Ω) (y : Ω) (j : ℕ) :
    (krylovPoly p f c (j + 1)).eval y =
      (krylovPoly p f c j).eval y ^ p ^ f + c (j + 1) * y ^ p ^ f := by
  simp [krylovPoly]

omit [FiniteDimensional Ω V] in
/-- In the Krylov relation `T^{k'+1} v = ∑_{i ≤ k'} c_i T^i v` of an injective `T`, the
coefficient `c 0` is nonzero as soon as `T^{k'} v` is not in the span of the earlier vectors. -/
theorem coeff_zero_ne_zero_of_krylov (hT : Function.Injective T) (v : V) (k' : ℕ)
    (c : Fin (k' + 1) → Ω) (hc : ∑ i, c i • (⇑T)^[i] v = (⇑T)^[k' + 1] v)
    (hmin : (⇑T)^[k'] v ∉ Submodule.span Ω (Set.range fun i : Fin k' => (⇑T)^[i] v)) :
    c 0 ≠ 0 := by
  -- `c_0 ≠ 0`: otherwise `T^{k'+1} v` is `T` of a vector in the span of `v, …, T^{k'-1} v`
  intro h0
  have hroot : ∀ i : Fin k', ∃ r : Ω, r ^ p ^ f = c i.succ := fun i =>
    IsAlgClosed.exists_pow_nat_eq _ (pow_pos hp.out.pos f)
  choose r hr using hroot
  have hsplit : (⇑T)^[k' + 1] v = T (∑ i : Fin k', r i • (⇑T)^[i] v) := by
    rw [← hc, Fin.sum_univ_succ, h0, zero_smul, zero_add, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_smul_pow, hr, Fin.val_succ, Function.iterate_succ_apply']
  have hT' : (⇑T)^[k'] v = ∑ i : Fin k', r i • (⇑T)^[i] v := hT <| by
    rw [← hsplit]
    exact (Function.iterate_succ_apply' _ _ _).symm
  exact hmin (hT' ▸ Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

omit [FiniteDimensional Ω V] in
include hf in
/-- **The Krylov step.** Let `v, T v, …, T^{k'} v` be such that no `T^j v` with `j ≤ k'` lies in
the span of the earlier ones, while `T^{k'+1} v = ∑_{i ≤ k'} c_i T^i v`. Then `T` has a nonzero
fixed vector in their span. -/
theorem exists_fixed_of_krylov (hT : Function.Injective T) (v : V) (k' : ℕ)
    (c : Fin (k' + 1) → Ω) (hc : ∑ i, c i • (⇑T)^[i] v = (⇑T)^[k' + 1] v)
    (hmin : ∀ j ≤ k', (⇑T)^[j] v ∉
      Submodule.span Ω (Set.range fun i : Fin j => (⇑T)^[i] v)) :
    ∃ w : V, w ≠ 0 ∧ T w = w := by
  classical
  have hc0 := coeff_zero_ne_zero_of_krylov p f T hT v k' c hc (hmin k' le_rfl)
  set e : ℕ → V := fun i => (⇑T)^[i] v with he
  change ∑ i, c i • e i = e (k' + 1) at hc
  change ∀ j ≤ k', e j ∉ Submodule.span Ω (Set.range fun i : Fin j => e i) at hmin
  have hTe : ∀ i, T (e i) = e (i + 1) := fun i => by
    simp only [he, Function.iterate_succ_apply']
  have hmemW : ∀ (j : ℕ) (a : Fin j → Ω),
      ∑ i, a i • e i ∈ Submodule.span Ω (Set.range fun i : Fin j => e i) := fun j a =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set c' : ℕ → Ω := fun j => if h : j < k' + 1 then c ⟨j, h⟩ else 0
  have hc'0 : c' 0 = c 0 := by simp [c']
  have hc's : ∀ i : Fin k', c' (i + 1) = c i.succ := fun i => by simp [c', Fin.succ]
  obtain ⟨y, hy0, hy⟩ := exists_eval_krylovPoly_eq p f hf c' (hc'0 ▸ hc0) k'
  set x : ℕ → Ω := fun j => (krylovPoly p f c' j).eval y
  have hx0 : x 0 = c 0 * y ^ p ^ f := by simp [x, krylovPoly, hc'0]
  have hxs : ∀ i : Fin k', x (i + 1) = x i ^ p ^ f + c i.succ * y ^ p ^ f := fun i => by
    rw [← hc's]
    exact eval_krylovPoly_succ c' y i
  have hyk : x k' = y := hy
  set w : V := ∑ i : Fin (k' + 1), x i • e i with hwdef
  have hw : w = y ^ p ^ f • e (k' + 1) + ∑ i : Fin k', x i ^ p ^ f • e (i + 1) := by
    rw [hwdef, ← hc, Fin.sum_univ_succ, Fin.sum_univ_succ, smul_add, Finset.smul_sum]
    simp only [Fin.val_zero, Fin.val_succ, hx0, hxs, add_smul, Finset.sum_add_distrib,
      smul_smul, mul_comm (y ^ p ^ f)]
    abel
  have hTw : T w = w := by
    rw [hwdef, map_sum, Fin.sum_univ_castSucc]
    simp only [map_smul_pow, hTe, Fin.val_castSucc, Fin.val_last, hyk]
    rw [← hwdef, hw, add_comm]
  refine ⟨w, fun h0 => ?_, hTw⟩
  -- `w ≠ 0`, its last coordinate being `y ≠ 0`
  have hsplit : w = ∑ i : Fin k', x i • e i + y • e k' := by
    rw [hwdef, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, hyk]
  have hlast : y • e k' = -∑ i : Fin k', x i • e i := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm, ← hsplit, h0]
  have hmem : y • e k' ∈ Submodule.span Ω (Set.range fun i : Fin k' => e i) := by
    rw [hlast]
    exact Submodule.neg_mem _ (hmemW k' _)
  exact hmin k' le_rfl ((Submodule.smul_mem_iff _ hy0).1 hmem)

include hf in
/-- **Lang's lemma, existence of a fixed vector.** An injective `q`-semilinear endomorphism of a
nonzero finite-dimensional vector space over an algebraically closed field of characteristic `p`
has a nonzero fixed vector. -/
theorem exists_fixed_ne_zero [Nontrivial V] (hT : Function.Injective T) :
    ∃ w : V, w ≠ 0 ∧ T w = w := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set e : ℕ → V := fun i => (⇑T)^[i] v with he
  set W : ℕ → Submodule Ω V := fun k => Submodule.span Ω (Set.range fun i : Fin k => e i)
  have hWmono : ∀ k, W k ≤ W (k + 1) := fun k => Submodule.span_mono fun x ⟨i, hi⟩ =>
    ⟨Fin.castSucc i, by simpa using hi⟩
  have heW : ∀ k, e k ∈ W (k + 1) := fun k => Submodule.subset_span ⟨Fin.last k, by simp⟩
  have hex : ∃ k, e k ∈ W k := by
    by_contra hne
    push Not at hne
    have hgrow : ∀ k, k ≤ finrank Ω (W k) := by
      intro k
      induction k with
      | zero => exact Nat.zero_le _
      | succ k ih =>
        have hlt : W k < W (k + 1) := lt_of_le_of_ne (hWmono k) fun h => hne k (h ▸ heW k)
        exact lt_of_le_of_lt ih (Submodule.finrank_lt_finrank_of_lt hlt)
    have := (hgrow (finrank Ω V + 1)).trans (Submodule.finrank_le _)
    omega
  have hk := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, e j ∉ W j := fun j hj => Nat.find_min hex hj
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hk
    exact hv (by simpa [W, he] using hk)
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  rw [hk'] at hk hmin
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hk
  exact exists_fixed_of_krylov p f hf T hT v k' c hc fun j hj => hmin j (Nat.lt_succ_of_le hj)

/-! ### A fixed basis -/

omit [CharP Ω p] in
include hf in
/-- An Artin–Schreier root: `a ^ q - a + c = 0` has a solution. -/
theorem exists_artinSchreier (c : Ω) : ∃ a : Ω, a ^ p ^ f + c = a := by
  have hq : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt
  have hdeg : (X ^ p ^ f - X + C c : Ω[X]).degree ≠ 0 := by
    have h1 : (X ^ p ^ f - X + C c : Ω[X]).natDegree = p ^ f := by
      rw [natDegree_add_C, natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hq]
    have hne : (X ^ p ^ f - X + C c : Ω[X]) ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at h1
      omega
    rw [degree_eq_natDegree hne, h1]
    exact_mod_cast (by omega : p ^ f ≠ 0)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨a, ?_⟩
  simp only [IsRoot, eval_add, eval_sub, eval_pow, eval_X, eval_C] at ha
  linear_combination ha

omit [FiniteDimensional Ω V] in
/-- If `T` is injective and fixes `w`, the map it induces on `V ⧸ Ω ∙ w` is injective. -/
theorem injective_mapQ_span_singleton (hT : Function.Injective T) {w : V} (hw : T w = w)
    (hP : (Ω ∙ w) ≤ (Ω ∙ w).comap T) : Function.Injective ((Ω ∙ w).mapQ (Ω ∙ w) T hP) := by
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with | H x =>
  induction y using Submodule.Quotient.induction_on with | H y =>
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq, ← map_sub] at hxy
  rw [Submodule.Quotient.eq]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hxy
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq a (pow_pos hp.out.pos f)
  have : T (r • w) = T (x - y) := by rw [map_smul_pow, hr, hw, ha]
  rw [← hT this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)

/-- The generator of `K ∙ w` maps to zero in the quotient `M ⧸ K ∙ w`. -/
private theorem mkQ_span_singleton_self {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (w : M) : (K ∙ w).mkQ w = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self w)

omit [FiniteDimensional Ω V] in
include hf in
/-- A fixed vector of the map `T` induces on `V ⧸ Ω ∙ w` lifts to a fixed vector of `V`. -/
theorem exists_fixed_lift {w : V} (hw : T w = w) (hP : (Ω ∙ w) ≤ (Ω ∙ w).comap T)
    {q : V ⧸ (Ω ∙ w)} (hq : (Ω ∙ w).mapQ (Ω ∙ w) T hP q = q) :
    ∃ u : V, (Ω ∙ w).mkQ u = q ∧ T u = u := by
  obtain ⟨v, rfl⟩ := (Ω ∙ w).mkQ_surjective q
  have hTv : T v - v ∈ Ω ∙ w := by
    rw [← Submodule.Quotient.eq]
    simpa [Submodule.mapQ_apply] using hq
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hTv
  obtain ⟨a, ha⟩ := exists_artinSchreier p f hf c
  refine ⟨v + a • w, by rw [map_add, map_smul, mkQ_span_singleton_self, smul_zero, add_zero], ?_⟩
  rw [map_add, map_smul_pow, hw]
  rw [eq_add_of_sub_eq' hc.symm, add_assoc, ← add_smul, add_comm c, ha]

include hf in
/-- **Lang's lemma.** An injective `q`-semilinear endomorphism of a finite-dimensional vector
space over an algebraically closed field of characteristic `p` fixes the vectors of a basis. -/
theorem exists_basis_fixed (hT : Function.Injective T) :
    ∃ b : Basis (Fin (finrank Ω V)) Ω V, ∀ i, T (b i) = b i := by
  classical
  induction h : finrank Ω V generalizing V with
  | zero =>
    exact ⟨(Module.finBasis Ω V).reindex (finCongr h), fun i => i.elim0⟩
  | succ n ih =>
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
    obtain ⟨w, hw0, hw⟩ := exists_fixed_ne_zero p f hf T hT
    have hP : (Ω ∙ w) ≤ (Ω ∙ w).comap T := fun x hx => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [Submodule.mem_comap, map_smul_pow, hw]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    have hdim : finrank Ω (V ⧸ (Ω ∙ w)) = n := by
      have := (Ω ∙ w).finrank_quotient_add_finrank
      rw [finrank_span_singleton hw0, h] at this
      omega
    obtain ⟨bq, hbq⟩ := ih _ (injective_mapQ_span_singleton p f T hT hw hP) hdim
    -- lift the fixed basis of `V / Ω w` to fixed vectors of `V`
    choose u hu using fun i => exists_fixed_lift p f hf T hw hP (hbq i)
    have hli : LinearIndependent Ω (Fin.snoc u w : Fin (n + 1) → V) := by
      rw [linearIndependent_finSnoc]
      have hu' : LinearIndependent Ω u :=
        LinearIndependent.of_comp (Ω ∙ w).mkQ
          (by simpa [Function.comp_def, (fun i => (hu i).1)] using bq.linearIndependent)
      refine ⟨hu', fun hmem => hw0 ?_⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hmem
      have h0 : ∑ i, a i • bq i = 0 := by
        have := congrArg (Ω ∙ w).mkQ ha
        rw [map_sum, mkQ_span_singleton_self] at this
        simpa [(fun i => (hu i).1)] using this
      have hz := (Fintype.linearIndependent_iff.1 bq.linearIndependent) a h0
      rw [← ha]
      simp [hz]
    have hcard : Fintype.card (Fin (n + 1)) = finrank Ω V := by simp [h]
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i => ?_⟩
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    induction i using Fin.lastCases with
    | last => simp [hw]
    | cast j => simp [(hu j).2]

/-! ### Counting -/

omit [IsAlgClosed Ω] [FiniteDimensional Ω V] in
/-- In a fixed basis, `T` raises the coordinates to the `q`-th power. -/
theorem equivFun_apply_pow {ι : Type*} [Finite ι] (b : Basis ι Ω V) (hb : ∀ i, T (b i) = b i)
    (v : V) : T v = b.equivFun.symm fun i => b.equivFun v i ^ p ^ f := by
  have := Fintype.ofFinite ι
  conv_lhs => rw [← b.sum_equivFun v]
  rw [map_sum, Basis.equivFun_symm_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul_pow, hb]

include hf in
/-- **The number of fixed vectors is `q ^ n`.** -/
theorem natCard_fixed (hT : Function.Injective T) :
    Nat.card {v : V // T v = v} = (p ^ f) ^ finrank Ω V := by
  obtain ⟨b, hb⟩ := exists_basis_fixed p f hf T hT
  have e : {v : V // T v = v} ≃ (Fin (finrank Ω V) → {a : Ω // a ^ p ^ f = a}) :=
    (b.equivFun.toEquiv.subtypeEquiv fun v => by
      rw [equivFun_apply_pow p f T b hb, LinearEquiv.coe_toEquiv, LinearEquiv.symm_apply_eq,
        funext_iff]).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_fun, natCard_pow_eq_self p f hf, Nat.card_fin]

include hf in
/-- An injective `T` has only finitely many fixed vectors. -/
theorem finite_fixed (hT : Function.Injective T) : Finite {v : V // T v = v} :=
  Nat.finite_of_card_ne_zero (by
    rw [natCard_fixed p f hf T hT]
    exact pow_ne_zero _ (pow_ne_zero _ hp.out.ne_zero))

/-- A `T`-stable point of the projective space `ℙ(V)`: a line `Ω v` with `T v ∈ Ω v`. -/
def IsStablePoint (hT : Function.Injective T) (x : Projectivization Ω V) : Prop :=
  Projectivization.map T hT x = x

omit [FiniteDimensional Ω V] in
include hf in
/-- **A stable line contains a nonzero fixed vector.** -/
theorem exists_fixed_rep (hT : Function.Injective T) {x : Projectivization Ω V}
    (hx : IsStablePoint p f T hT x) :
    ∃ v : V, ∃ hv : v ≠ 0, T v = v ∧ Projectivization.mk Ω v hv = x := by
  obtain ⟨a, ha⟩ : ∃ a : Ω, a • x.rep = T x.rep := by
    rwa [IsStablePoint, ← Projectivization.mk_rep x, Projectivization.map_mk,
      Projectivization.mk_eq_mk_iff'] at hx
  have hTr : T x.rep ≠ 0 := fun h => x.rep_nonzero (hT (h.trans (map_zero T).symm))
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact hTr ha.symm
  have hq1 : 0 < p ^ f - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hf.ne' hp.out.one_lt)
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ hq1
  have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_pow hq1.ne'] at hμ; exact inv_ne_zero ha0 hμ.symm
  refine ⟨μ • x.rep, smul_ne_zero hμ0 x.rep_nonzero, ?_, ?_⟩
  · rw [map_smul_pow, ← ha, smul_smul]
    congr 1
    have : μ ^ p ^ f = μ ^ (p ^ f - 1) * μ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [this, hμ]
    field_simp
  · conv_rhs => rw [← Projectivization.mk_rep x]
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨μ, rfl⟩

/-- Removing `0` from a subtype containing it lowers its cardinality by one. -/
private theorem natCard_subtype_ne_zero {α : Type*} [Zero α] (P : α → Prop) (h0 : P 0) :
    Nat.card {a // P a ∧ a ≠ 0} = Nat.card {a // P a} - 1 := by
  have : Nat.card {a // P a ∧ a ≠ 0} = ({a | P a} \ {0}).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp)
  rw [this, Set.ncard_sdiff_singleton_of_mem (s := {a | P a}) h0, ← Nat.card_coe_set_eq]
  rfl

include hf in
/-- **The number of stable lines.** `(q - 1) · #{T-stable points of ℙ(V)} = q ^ n - 1`. -/
theorem natCard_stable_mul (hT : Function.Injective T) :
    (p ^ f - 1) * Nat.card {x : Projectivization Ω V // IsStablePoint p f T hT x} =
      (p ^ f) ^ finrank Ω V - 1 := by
  classical
  choose r hr0 hr hrx using fun x : {x : Projectivization Ω V // IsStablePoint p f T hT x} =>
    exists_fixed_rep p f hf T hT x.2
  -- nonzero fixed vectors are `a r(x)` for a unique stable `x` and `a ∈ 𝔽_q^×`
  have hstable : ∀ v : V, ∀ hv : v ≠ 0, T v = v →
      IsStablePoint p f T hT (Projectivization.mk Ω v hv) := fun v hv hTv => by
    rw [IsStablePoint, Projectivization.map_mk]
    congr 1
  let π : {v : V // T v = v ∧ v ≠ 0} →
      {x : Projectivization Ω V // IsStablePoint p f T hT x} :=
    fun v => ⟨Projectivization.mk Ω v.1 v.2.2, hstable v.1 v.2.2 v.2.1⟩
  have hfib : ∀ x : {x : Projectivization Ω V // IsStablePoint p f T hT x},
      {a : Ω // a ^ p ^ f = a ∧ a ≠ 0} ≃ {v : {v : V // T v = v ∧ v ≠ 0} // π v = x} :=
    fun x => Equiv.ofBijective
    (fun a => ⟨⟨a.1 • r x, by rw [map_smul_pow, hr, a.2.1], smul_ne_zero a.2.2 (hr0 x)⟩,
      Subtype.ext (by
        change Projectivization.mk Ω (a.1 • r x) _ = x.1
        rw [← hrx x, Projectivization.mk_eq_mk_iff']
        exact ⟨a.1, rfl⟩)⟩)
    ⟨fun a b hab => Subtype.ext (smul_left_injective Ω (hr0 x)
        (congrArg (fun v : {v : {v : V // T v = v ∧ v ≠ 0} // π v = x} => v.1.1) hab)),
    fun v => by
      have hmk : Projectivization.mk Ω v.1.1 v.1.2.2 = Projectivization.mk Ω (r x) (hr0 x) := by
        rw [hrx x]; exact congrArg Subtype.val v.2
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' Ω _ _ _ _).1 hmk
      have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact v.1.2.2 ha.symm
      have haq : a ^ p ^ f = a := by
        have h1 : T (a • r x) = a • r x := by rw [ha]; exact v.1.2.1
        rw [map_smul_pow, hr] at h1
        exact smul_left_injective Ω (hr0 x) h1
      exact ⟨⟨a, haq, ha0⟩, Subtype.ext (Subtype.ext ha)⟩⟩
  have e : {v : V // T v = v ∧ v ≠ 0} ≃
      {x : Projectivization Ω V // IsStablePoint p f T hT x} × {a : Ω // a ^ p ^ f = a ∧ a ≠ 0} :=
    (Equiv.sigmaFiberEquiv π).symm.trans ((Equiv.sigmaCongrRight fun x => (hfib x).symm).trans
      (Equiv.sigmaEquivProd _ _))
  have hF : Nat.card {a : Ω // a ^ p ^ f = a ∧ a ≠ 0} = p ^ f - 1 := by
    rw [natCard_subtype_ne_zero _ (by simp [zero_pow (pow_ne_zero _ hp.out.ne_zero)])]
    exact congrArg (· - 1) (natCard_pow_eq_self p f hf)
  have hV : Nat.card {v : V // T v = v ∧ v ≠ 0} = (p ^ f) ^ finrank Ω V - 1 := by
    rw [natCard_subtype_ne_zero _ (by simp)]
    exact congrArg (· - 1) (natCard_fixed p f hf T hT)
  rw [← hV, Nat.card_congr e, Nat.card_prod, hF, mul_comm]

include hf in
/-- **Finitely many stable subspaces.** Every `T`-stable subspace is spanned by the fixed vectors
it contains, and there are finitely many fixed vectors. -/
theorem finite_stableSubmodules (hT : Function.Injective T) :
    {W : Submodule Ω V | ∀ v ∈ W, T v ∈ W}.Finite := by
  classical
  have := finite_fixed p f hf T hT
  have hspan : ∀ W : Submodule Ω V, (∀ v ∈ W, T v ∈ W) →
      W = Submodule.span Ω (Subtype.val '' {v : {v : V // T v = v} | v.1 ∈ W}) := by
    intro W hW
    refine le_antisymm ?_ (Submodule.span_le.2 fun v ⟨w, hw, hwv⟩ => hwv ▸ hw)
    set TW : W →ₛₗ[iterateFrobenius Ω p f] W := T.restrict hW
    have hTW : Function.Injective TW := fun a b hab =>
      Subtype.ext (hT (congrArg Subtype.val hab))
    obtain ⟨b, hb⟩ := exists_basis_fixed p f hf TW hTW
    intro v hv
    have hv' : (⟨v, hv⟩ : W) ∈ Submodule.span Ω (Set.range b) := b.mem_span _
    have := Submodule.apply_mem_span_image_of_mem_span W.subtype hv'
    rw [← Set.range_comp] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨(b i).1, congrArg Subtype.val (hb i)⟩, (b i).2, rfl⟩
  refine ((Set.toFinite (Set.univ : Set (Set {v : V // T v = v}))).image
    fun S => Submodule.span Ω (Subtype.val '' S)).subset fun W hW => ⟨_, trivial, (hspan W hW).symm⟩

end Stacks.Lang

end
