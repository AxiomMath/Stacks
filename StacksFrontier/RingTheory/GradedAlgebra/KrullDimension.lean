module

import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf

public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import StacksFrontier.RingTheory.HilbertSamuel.DimensionTheorem
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Dimension of a graded algebra generated in degree one over a field

Let `k` be a field and let `S = ⨁_{d ≥ 0} S_d` be a graded `k`-algebra with `S_0 = k` which is
generated over `k` by finitely many elements of degree `1`. This file proves Stacks 00P6.

The irrelevant ideal `m = S_+` is the kernel of the degree-zero projection, a ring homomorphism
onto `S_0 = k`; an element outside it has a nonzero, hence invertible, degree-zero part, so `m`
is maximal. A minimal prime `p` contains the prime ideal `p_*` spanned by the homogeneous
elements of `p`, so equals it and is homogeneous; its degree-zero part then lies in the field
`S_0` and cannot be invertible, so is zero and `p ⊆ m`.

Therefore every irreducible component of `Spec S` — the closed set cut out by a minimal prime —
passes through the closed point `x` given by `m`. Since the local dimension of `Spec S` at a
point is the largest dimension of a component through it (Stacks 00OT), the local dimension is
largest at `x`, so `dim S = dim_x Spec S`, which by the second half of Stacks 00OT is the
smallest `height 𝔪` over the maximal ideals `𝔪 ⊇ m`, that is `height m` itself.

Finally `m^d / m^{d + 1} ≅ S_d` is already a module over the residue field, so it is unchanged
by localizing at `m`: the Hilbert function of `S_m` is `d ↦ dim_k S_d`, and Stacks 00KQ turns
that into `dim S_m = deg P + 1` for the polynomial `P` with `dim_k S_d = P(d)` for `d ≫ 0`.

## Main results

* `Stacks.GradedAlgebra.HilbertDimension.solution`: items (1)–(4) of Stacks 00P6.

## Implementation notes

Finite generation in degree one enters twice: through `Algebra.FiniteType k S`, which Stacks
00OT needs, and through the identification `m^d / m^{d + 1} ≅ S_d`. Both uses factor through the
single statement that generation in degree one is, namely `S_d = (S_1)^d` for every `d`: the
submodule `⨆_e (S_1)^e` is a subalgebra containing `S_1`, hence all of `S`, and the degree-`d`
projection carries `(S_1)^e` into `(S_1)^d`. From it, `S_e ⊆ m^d` for `e ≥ d` and
`m = (S_1)S`, hence `m^d ⊆ (S_d)S ⊆ ⨁_{e ≥ d} S_e`; the two inclusions together say
`m^d = ⨁_{e ≥ d} S_e`, which is what makes `m^d / m^{d + 1} ≅ S_d`.

## References

* [Stacks Project, Tag 00P6](https://stacks.math.columbia.edu/tag/00P6)
-/

namespace Stacks.GradedAlgebra.HilbertDimension

open HomogeneousIdeal

/-! ### Length over a ring acting through a field -/

/-- If every element of `R` acts on `M` as a scalar from `k`, then the `R`-submodules and the
`k`-submodules of `M` are the same, so the two lengths agree. This is how a module over a local
ring that is annihilated by the maximal ideal is measured by its dimension over the residue
field. -/
private lemma length_eq_length_of_exists_smul_eq {k R M : Type*} [Field k] [CommRing R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    (h : ∀ r : R, ∃ c : k, ∀ x : M, r • x = c • x) :
    Module.length R M = Module.length k M := by
  classical
  have hinv : ∀ q : Submodule k M, ∃ p : Submodule R M, Submodule.restrictScalars k p = q := by
    intro q
    have hsm : ∀ (r : R) (x : M), x ∈ q → r • x ∈ q := by
      intro r x hx
      obtain ⟨c, hc⟩ := h r
      rw [hc]
      exact q.smul_mem c hx
    exact ⟨⟨q.toAddSubmonoid, fun r x hx => hsm r x hx⟩, rfl⟩
  have e : Submodule R M ≃o Submodule k M :=
    { toFun := fun p => Submodule.restrictScalars k p
      invFun := fun q => Classical.choose (hinv q)
      left_inv := fun p => Submodule.restrictScalars_injective k R M
        (Classical.choose_spec (hinv (Submodule.restrictScalars k p)))
      right_inv := fun q => Classical.choose_spec (hinv q)
      map_rel_iff' := Iff.rfl }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length, Order.krullDim_eq_of_orderIso e]

/-! ### Binomial-basis polynomials -/

open Polynomial in
/-- The polynomial `(X choose i)` over `ℚ`: the unique polynomial whose value at a natural number
`n` is the binomial coefficient `n.choose i`. It is `descPochhammer ℚ i` divided by `i !`. -/
@[sga "6 V 2.5"]
private noncomputable def binomialPoly (i : ℕ) : Polynomial ℚ :=
  C ((Nat.factorial i : ℚ))⁻¹ * descPochhammer ℚ i

private lemma factorialCast_inv_ne_zero (i : ℕ) : ((Nat.factorial i : ℚ))⁻¹ ≠ 0 :=
  inv_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i))

open Polynomial in
private lemma binomialPoly_eval_natCast (i n : ℕ) :
    (binomialPoly i).eval (n : ℚ) = n.choose i := by
  rw [binomialPoly, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i))]

open Polynomial in
private lemma binomialPoly_natDegree (i : ℕ) : (binomialPoly i).natDegree = i := by
  rw [binomialPoly, natDegree_C_mul (factorialCast_inv_ne_zero i), descPochhammer_natDegree]

open Polynomial in
private lemma binomialPoly_coeff_self (i : ℕ) :
    (binomialPoly i).coeff i = ((Nat.factorial i : ℚ))⁻¹ := by
  rw [binomialPoly, coeff_C_mul]
  have h : (descPochhammer ℚ i).coeff i = 1 := by
    have h := monic_descPochhammer ℚ i
    rw [Monic, leadingCoeff, descPochhammer_natDegree] at h
    exact h
  rw [h, mul_one]

open Polynomial in
/-- The combination `∑_{i < m} b i * (X choose i)` of binomial polynomials. Every polynomial over
`ℚ` of degree less than `m` is of this form, and the first difference of `binomialSum b (m + 1)`
is `binomialSum (b ∘ (· + 1)) m`. -/
private noncomputable def binomialSum (b : ℕ → ℚ) (m : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range m, C (b i) * binomialPoly i

open Polynomial in
private lemma binomialSum_eval_natCast (b : ℕ → ℚ) (m n : ℕ) :
    (binomialSum b m).eval (n : ℚ) = ∑ i ∈ Finset.range m, b i * n.choose i := by
  simp only [binomialSum, eval_finsetSum, eval_mul, eval_C, binomialPoly_eval_natCast]

private lemma binomialSum_zero (b : ℕ → ℚ) : binomialSum b 0 = 0 := by simp [binomialSum]

open Polynomial in
private lemma natDegree_binomialSum_le (b : ℕ → ℚ) (m : ℕ) :
    (binomialSum b (m + 1)).natDegree ≤ m := by
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [binomialPoly_natDegree]
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)

open Polynomial in
private lemma coeff_binomialSum_self (b : ℕ → ℚ) (m : ℕ) :
    (binomialSum b (m + 1)).coeff m = b m * ((Nat.factorial m : ℚ))⁻¹ := by
  rw [binomialSum, Finset.sum_range_succ, coeff_add, coeff_C_mul, binomialPoly_coeff_self,
    finsetSum_coeff]
  have h0 : ∀ i ∈ Finset.range m, (C (b i) * binomialPoly i).coeff m = 0 := fun i hi =>
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      ((natDegree_C_mul_le _ _).trans_eq (binomialPoly_natDegree i)) (Finset.mem_range.1 hi))
  rw [Finset.sum_congr rfl h0, Finset.sum_const_zero, zero_add]

open Polynomial in
private lemma binomialSum_ne_zero_and_natDegree (b : ℕ → ℚ) (m : ℕ) (hb : b m ≠ 0) :
    binomialSum b (m + 1) ≠ 0 ∧ (binomialSum b (m + 1)).natDegree = m := by
  have hc : (binomialSum b (m + 1)).coeff m ≠ 0 := by
    rw [coeff_binomialSum_self]
    exact mul_ne_zero hb (factorialCast_inv_ne_zero m)
  exact ⟨fun h => hc (by rw [h, coeff_zero]),
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_binomialSum_le b m) hc⟩

/-- Two polynomials over `ℚ` that agree at all natural numbers from some point on are equal. -/
private lemma eq_of_forall_eval_natCast_eq {p q : Polynomial ℚ} (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q :=
  Polynomial.eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => ((N + j : ℕ) : ℚ)) (fun i j h => by simpa using h)
    fun j => h _ (Nat.le_add_right _ _))

open Polynomial in
/-- The first difference of a combination of binomial polynomials shifts the coefficients: this is
`(n + 1 choose i + 1) - (n choose i + 1) = (n choose i)`. -/
private lemma binomialSum_comp_sub_self (a : ℕ → ℚ) (e : ℕ) :
    (binomialSum a (e + 1)).comp (X + C 1) - binomialSum a (e + 1)
      = binomialSum (fun i => a (i + 1)) e := by
  refine eq_of_forall_eval_natCast_eq 0 fun n _ => ?_
  simp only [eval_sub, eval_comp, eval_add, eval_X, eval_C]
  have hcast : (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [hcast, binomialSum_eval_natCast, binomialSum_eval_natCast, binomialSum_eval_natCast,
    ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, sub_self, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.choose_succ_succ' n i]
  push_cast
  ring

open Polynomial in
/-- **The comparison of Hilbert functions.** If the partial sums of `f : ℕ → ℕ` are eventually the
binomial combination `∑_{i ≤ e} a i * (n choose i)` with `a e ≠ 0`, and `f` is eventually the value
of a polynomial `P`, then `e = deg P + 1` — the convention `deg 0 = -1` being unfolded into the
two cases `P = 0` and `P ≠ 0`. -/
private lemma eq_natDegree_add_one_of_eventually {P : Polynomial ℚ} {f : ℕ → ℕ} {a : ℕ → ℚ}
    {e : ℕ} (hae : a e ≠ 0) (hf : ∀ᶠ d : ℕ in Filter.atTop, P.eval (d : ℚ) = f d)
    (hL : ∀ᶠ n : ℕ in Filter.atTop, ((∑ d ∈ Finset.range (n + 1), f d : ℕ) : ℚ)
      = ∑ i ∈ Finset.range (e + 1), a i * (n.choose i : ℚ)) :
    (P = 0 → e = 0) ∧ (P ≠ 0 → e = P.natDegree + 1) := by
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hf
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hL
  have hHval : ∀ n : ℕ, max N₁ N₂ ≤ n → (binomialSum a (e + 1)).eval (n : ℚ)
      = ((∑ d ∈ Finset.range (n + 1), f d : ℕ) : ℚ) := fun n hn => by
    rw [binomialSum_eval_natCast]
    exact (hN₂ n (le_trans (le_max_right N₁ N₂) hn)).symm
  have hPD : binomialSum (fun i => a (i + 1)) e = P.comp (X + C 1) := by
    refine eq_of_forall_eval_natCast_eq (max N₁ N₂) fun n hn => ?_
    rw [← binomialSum_comp_sub_self a e]
    simp only [eval_sub, eval_comp, eval_add, eval_X, eval_C]
    have hc : (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [hc, hHval (n + 1) (by omega), hHval n hn, hN₁ (n + 1) (by omega),
      Finset.sum_range_succ (n := n + 1)]
    push_cast
    ring
  refine ⟨fun hP0 => ?_, fun hP => ?_⟩
  · rcases Nat.eq_zero_or_pos e with he | he
    · exact he
    · obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by omega⟩
      exact absurd (hPD.trans (by rw [hP0]; simp))
        (binomialSum_ne_zero_and_natDegree (fun i => a (i + 1)) m hae).1
  · rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      exact absurd (comp_X_add_C_eq_zero_iff.1 (((binomialSum_zero _).symm.trans hPD).symm)) hP
    · obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by omega⟩
      obtain ⟨-, hdeg⟩ := binomialSum_ne_zero_and_natDegree (fun i => a (i + 1)) m hae
      rw [hPD, natDegree_comp, natDegree_X_add_C, mul_one] at hdeg
      omega


section

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] (𝒜 : ℕ → Submodule k S)
  [GradedAlgebra 𝒜]

/-- The degree-zero projection is the identity on the degree-zero part. -/
private lemma projZeroRingHom_eq_self {y : S} (hy : y ∈ 𝒜 0) :
    GradedRing.projZeroRingHom 𝒜 y = y := by
  show (DirectSum.decompose 𝒜 y 0 : S) = y
  rw [DirectSum.decompose_of_mem_same 𝒜 hy]

omit [GradedAlgebra 𝒜] in
/-- A graded algebra generated by a finite-dimensional space of elements of degree one is of
finite type. -/
private lemma finiteType_of_adjoin_eq_top [Module.Finite k ↥(𝒜 1)]
    (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤) : Algebra.FiniteType k S := by
  obtain ⟨s, hs⟩ := (Module.Finite.iff_fg (N := 𝒜 1)).1 inferInstance
  refine ⟨s, top_le_iff.1 ?_⟩
  rw [← hgen]
  refine Algebra.adjoin_le ?_
  rw [← hs]
  exact Algebra.span_le_adjoin k (s : Set S)

/-! ### The degree filtration of a graded algebra generated in degree one -/

private noncomputable def proj (e : ℕ) : S →ₗ[k] S :=
  (𝒜 e).subtype ∘ₗ DirectSum.component k ℕ (fun i => ↥(𝒜 i)) e ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

private lemma proj_apply (e : ℕ) (x : S) : proj 𝒜 e x = (DirectSum.decompose 𝒜 x e : S) := rfl

private lemma proj_eq_self {e : ℕ} {x : S} (hx : x ∈ 𝒜 e) : proj 𝒜 e x = x := by
  rw [proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx]

private lemma proj_eq_zero_of_mem_ne {e i : ℕ} {x : S} (hx : x ∈ 𝒜 i) (h : i ≠ e) :
    proj 𝒜 e x = 0 := by
  rw [proj_apply]; exact DirectSum.decompose_of_mem_ne 𝒜 hx h

private lemma mul_mem_iSup_ge (n : ℕ) (c : S) {x : S}
    (hx : x ∈ (⨆ i, ⨆ _ : n ≤ i, 𝒜 i : Submodule k S)) :
    c * x ∈ (⨆ i, ⨆ _ : n ≤ i, 𝒜 i : Submodule k S) := by
  classical
  refine (iSup_le fun i => iSup_le fun hi => ?_ :
    (⨆ i, ⨆ _ : n ≤ i, 𝒜 i : Submodule k S) ≤
      Submodule.comap (LinearMap.mulLeft k c) (⨆ i, ⨆ _ : n ≤ i, 𝒜 i)) hx
  intro a ha
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
  rw [← DirectSum.sum_support_decompose 𝒜 c, Finset.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.mem_iSup_of_mem (j + i)
    (Submodule.mem_iSup_of_mem (hi.trans (Nat.le_add_left i j))
      (SetLike.GradedMul.mul_mem (SetLike.coe_mem _) ha))

private lemma span_le_iSup_ge (n : ℕ) {x : S} (hx : x ∈ Ideal.span (𝒜 n : Set S)) :
    x ∈ (⨆ i, ⨆ _ : n ≤ i, 𝒜 i : Submodule k S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.mem_iSup_of_mem n (Submodule.mem_iSup_of_mem le_rfl hy)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_eq_mul]; exact mul_mem_iSup_ge 𝒜 n c hy

private lemma pow_one_le (h0 : 𝒜 0 = 1) (e : ℕ) : ((𝒜 1) ^ e : Submodule k S) ≤ 𝒜 e := by
  induction e with
  | zero => rw [pow_zero, ← h0]
  | succ e ih =>
      rw [pow_succ]
      exact Submodule.mul_le.2 fun a ha b hb => SetLike.GradedMul.mul_mem (ih ha) hb

private lemma le_pow_one (h0 : 𝒜 0 = 1) (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤) (e : ℕ) :
    𝒜 e ≤ ((𝒜 1) ^ e : Submodule k S) := by
  set B : Submodule k S := ⨆ n, (𝒜 1) ^ n with hB
  have hone : (1 : S) ∈ B := Submodule.mem_iSup_of_mem 0 (by
    rw [pow_zero]; exact Submodule.one_le.1 le_rfl)
  have hBB : B * B ≤ B := by
    rw [hB, Submodule.iSup_mul]
    refine iSup_le fun i => ?_
    rw [Submodule.mul_iSup]
    refine iSup_le fun j => ?_
    rw [← pow_add]
    exact le_iSup _ (i + j)
  have hBtop : B = ⊤ := by
    have h1 : (𝒜 1 : Set S) ⊆ (B.toSubalgebra hone
        fun x y hx hy => hBB (Submodule.mul_mem_mul hx hy) : Subalgebra k S) := by
      intro x hx
      exact Submodule.mem_iSup_of_mem 1 (by rw [pow_one]; exact hx)
    have h2 := (Algebra.adjoin_le h1 : Algebra.adjoin k (𝒜 1 : Set S) ≤ _)
    rw [hgen] at h2
    exact top_le_iff.1 (fun x _ => h2 (Algebra.mem_top))
  intro x hx
  have hkey : B ≤ Submodule.comap (proj 𝒜 e) ((𝒜 1) ^ e) := by
    refine iSup_le fun n => fun y hy => ?_
    simp only [Submodule.mem_comap]
    rcases eq_or_ne n e with rfl | hne
    · rw [proj_eq_self 𝒜 (pow_one_le 𝒜 h0 n hy)]; exact hy
    · rw [proj_eq_zero_of_mem_ne 𝒜 (pow_one_le 𝒜 h0 n hy) hne]; exact Submodule.zero_mem _
  have := hkey (hBtop ▸ Submodule.mem_top : x ∈ B)
  rw [Submodule.mem_comap, proj_eq_self 𝒜 hx] at this
  exact this

private lemma grade_eq_pow_one (h0 : 𝒜 0 = 1) (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤)
    (e : ℕ) : 𝒜 e = ((𝒜 1) ^ e : Submodule k S) :=
  le_antisymm (le_pow_one 𝒜 h0 hgen e) (pow_one_le 𝒜 h0 e)

omit [GradedAlgebra 𝒜] in
private lemma pow_one_succ_le_span (j : ℕ) :
    ((𝒜 1) ^ (j + 1) : Submodule k S) ≤ (Ideal.span (𝒜 1 : Set S)).restrictScalars k := by
  rw [pow_succ]
  exact Submodule.mul_le.2 fun a _ b hb => Ideal.mul_mem_left _ a (Ideal.subset_span hb)

private lemma irrelevant_eq_span_one (h0 : 𝒜 0 = 1)
    (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤) :
    (𝒜₊).toIdeal = Ideal.span (𝒜 1 : Set S) := by
  refine le_antisymm ?_ (Ideal.span_le.2 fun x hx => mem_irrelevant_of_mem 𝒜 one_pos hx)
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro x hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact pow_one_succ_le_span 𝒜 j ((grade_eq_pow_one 𝒜 h0 hgen (j + 1)).le hxi)

private lemma pow_one_le_pow_irrelevant (e : ℕ) :
    ((𝒜 1) ^ e : Submodule k S) ≤ ((𝒜₊).toIdeal ^ e).restrictScalars k := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [pow_succ, pow_succ]
      exact Submodule.mul_le.2 fun a ha b hb =>
        Ideal.mul_mem_mul (ih ha) (mem_irrelevant_of_mem 𝒜 one_pos hb)

open Pointwise in
private lemma pow_le_span (h0 : 𝒜 0 = 1) (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤) (n : ℕ) :
    (𝒜₊).toIdeal ^ n ≤ Ideal.span (𝒜 n : Set S) := by
  induction n with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      exact top_le_iff.2 ((Ideal.eq_top_iff_one (Ideal.span (𝒜 0 : Set S))).2
        (Ideal.subset_span SetLike.GradedOne.one_mem))
  | succ n ih =>
      calc (𝒜₊).toIdeal ^ (n + 1) = (𝒜₊).toIdeal ^ n * (𝒜₊).toIdeal := pow_succ _ _
        _ ≤ Ideal.span (𝒜 n : Set S) * Ideal.span (𝒜 1 : Set S) :=
            Ideal.mul_mono ih (irrelevant_eq_span_one 𝒜 h0 hgen).le
        _ = Ideal.span ((𝒜 n : Set S) * (𝒜 1 : Set S)) := Ideal.span_mul_span _ _
        _ ≤ Ideal.span (𝒜 (n + 1) : Set S) := by
            rw [Ideal.span_le]
            rintro x ⟨a, ha, b, hb, rfl⟩
            exact Ideal.subset_span (SetLike.GradedMul.mul_mem ha hb)

private lemma grade_le_pow_irrelevant (h0 : 𝒜 0 = 1)
    (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤) {d e : ℕ} (hde : d ≤ e) {x : S} (hx : x ∈ 𝒜 e) :
    x ∈ (𝒜₊).toIdeal ^ d :=
  Ideal.pow_le_pow_right hde
    (pow_one_le_pow_irrelevant 𝒜 e ((grade_eq_pow_one 𝒜 h0 hgen e).le hx))

/-- A linear map sending each graded piece of degree at least `d` into `N` sends every element of
the ideal `S_+^d` into `N`. -/
private lemma map_mem_of_mem_pow (h0 : 𝒜 0 = 1) (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤)
    {d : ℕ} (f : S →ₗ[k] S) (N : Submodule k S) (hf : ∀ i, d ≤ i → ∀ y ∈ 𝒜 i, f y ∈ N)
    {a : S} (ha : a ∈ (𝒜₊).toIdeal ^ d) : f a ∈ N :=
  (iSup_le fun i => iSup_le fun hi y hy => hf i hi y hy :
    (⨆ i, ⨆ _ : d ≤ i, 𝒜 i : Submodule k S) ≤ N.comap f)
    (span_le_iSup_ge 𝒜 d (pow_le_span 𝒜 h0 hgen d ha))

private lemma eq_zero_of_mem_pow_of_lt (h0 : 𝒜 0 = 1)
    (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤) {d e : ℕ} (hed : e < d) {x : S}
    (hx : x ∈ 𝒜 e) (hxp : x ∈ (𝒜₊).toIdeal ^ d) : x = 0 := by
  have := map_mem_of_mem_pow 𝒜 h0 hgen (proj 𝒜 e) ⊥
    (fun i hi y hy => (proj_eq_zero_of_mem_ne 𝒜 hy (by omega) : proj 𝒜 e y = 0)) hxp
  rw [proj_eq_self 𝒜 hx] at this
  exact (Submodule.mem_bot k).1 this

/-- The graded pieces of a graded algebra generated over `k` by a finite-dimensional space of
elements of degree one are finite dimensional. -/
private lemma finite_grade (h0 : 𝒜 0 = 1) (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤)
    [Module.Finite k ↥(𝒜 1)] (d : ℕ) : Module.Finite k ↥(𝒜 d) := by
  have h1 : (𝒜 1).FG := Module.Finite.iff_fg.1 inferInstance
  rw [Module.Finite.iff_fg, grade_eq_pow_one 𝒜 h0 hgen d]
  exact h1.pow d

/-! ### Saturation of the irrelevant ideal -/

omit [GradedAlgebra 𝒜] in
private lemma algebraMap_mem_grade_zero (h0 : 𝒜 0 = 1) (c : k) : algebraMap k S c ∈ 𝒜 0 := by
  rw [h0, Submodule.one_eq_range]
  exact ⟨c, rfl⟩

/-- The degree-zero part of any element is a scalar when `S_0 = k`. -/
private lemma exists_algebraMap_eq_projZero (h0 : 𝒜 0 = 1) (x : S) :
    ∃ c : k, algebraMap k S c = GradedRing.projZeroRingHom 𝒜 x := by
  have h : GradedRing.projZeroRingHom 𝒜 x ∈ 𝒜 0 := SetLike.coe_mem _
  rw [h0, Submodule.one_eq_range] at h
  exact h

/-- Every element of `S` differs from a scalar by an element of the irrelevant ideal: this is the
decomposition `S = S_0 ⊕ S_+` together with `S_0 = k`. -/
private lemma exists_sub_algebraMap_mem_irrelevant (h0 : 𝒜 0 = 1) (a : S) :
    ∃ c : k, a - algebraMap k S c ∈ (𝒜₊).toIdeal := by
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_projZero 𝒜 h0 a
  refine ⟨c, ?_⟩
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker, map_sub,
    projZeroRingHom_eq_self 𝒜 (algebraMap_mem_grade_zero 𝒜 h0 c), hc, sub_self]

private lemma exists_ne_zero_sub_algebraMap_mem_irrelevant (h0 : 𝒜 0 = 1) {t : S}
    (ht : t ∉ (𝒜₊).toIdeal) : ∃ c : k, c ≠ 0 ∧ t - algebraMap k S c ∈ (𝒜₊).toIdeal := by
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_irrelevant 𝒜 h0 t
  refine ⟨c, fun h => ht ?_, hc⟩
  subst h
  simpa using hc

/-- **Stacks 00P6 (1).** If the degree-zero part of a graded algebra over a field is the image of
the structure map, the irrelevant ideal is maximal. -/
private lemma irrelevant_isMaximal [Nontrivial S] (h0 : 𝒜 0 = 1) : (𝒜₊).toIdeal.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J x hJ hx hxJ => ?_⟩
  · rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker, map_one] at h
    exact one_ne_zero h
  · obtain ⟨c, hc0, hc⟩ := exists_ne_zero_sub_algebraMap_mem_irrelevant 𝒜 h0 hx
    have hcJ : algebraMap k S c ∈ J := by simpa using J.sub_mem hxJ (hJ hc)
    have h1 : (1 : S) = algebraMap k S c * algebraMap k S c⁻¹ := by
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    rw [h1]
    exact J.mul_mem_right _ hcJ

/-- **Stacks 00P6 (2).** A minimal prime of a graded algebra whose degree-zero part is the image
of the structure map is homogeneous and contained in the irrelevant ideal. -/
private lemma isHomogeneous_and_le_irrelevant_of_mem_minimalPrimes (h0 : 𝒜 0 = 1) {p : Ideal S}
    (hp : p ∈ minimalPrimes S) : Ideal.IsHomogeneous 𝒜 p ∧ p ≤ (𝒜₊).toIdeal := by
  rw [minimalPrimes_eq_minimals] at hp
  have hpp : p.IsPrime := hp.prop
  have hhom : Ideal.IsHomogeneous 𝒜 p := by
    rw [Ideal.IsHomogeneous.iff_eq]
    exact hp.eq_of_le hpp.homogeneousCore (Ideal.toIdeal_homogeneousCore_le 𝒜 p)
  refine ⟨hhom, fun x hx => ?_⟩
  have hmem : GradedRing.projZeroRingHom 𝒜 x ∈ p := hhom 0 hx
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_projZero 𝒜 h0 x
  have hc0 : c = 0 := by
    by_contra hne
    refine hpp.ne_top (Ideal.eq_top_of_isUnit_mem p hmem ?_)
    rw [← hc]
    exact (algebraMap k S).isUnit_map (isUnit_iff_ne_zero.2 hne)
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker, ← hc, hc0, map_zero]

/-- The powers of the irrelevant ideal are saturated with respect to the complement of the
irrelevant ideal: if `t ∉ S_+` and `t * a ∈ S_+^N` then `a ∈ S_+^N`. This is the statement that
`S_+` is its own primary decomposition, and it is what makes the map to the localization at `S_+`
injective on the graded pieces. -/
private lemma mem_pow_of_mul_mem_pow (h0 : 𝒜 0 = 1) {t a : S} (ht : t ∉ (𝒜₊).toIdeal) {N : ℕ}
    (h : t * a ∈ (𝒜₊).toIdeal ^ N) : a ∈ (𝒜₊).toIdeal ^ N := by
  obtain ⟨c, hc0, hy⟩ := exists_ne_zero_sub_algebraMap_mem_irrelevant 𝒜 h0 ht
  suffices H : ∀ j : ℕ, j ≤ N → a ∈ (𝒜₊).toIdeal ^ j from H N le_rfl
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      have haj : a ∈ (𝒜₊).toIdeal ^ j := ih (by omega)
      have h1 : algebraMap k S c * a ∈ (𝒜₊).toIdeal ^ (j + 1) := by
        rw [show algebraMap k S c * a = t * a - (t - algebraMap k S c) * a by ring]
        refine Ideal.sub_mem _ (Ideal.pow_le_pow_right hj h) ?_
        rw [pow_succ, mul_comm ((𝒜₊).toIdeal ^ j) (𝒜₊).toIdeal]
        exact Ideal.mul_mem_mul hy haj
      have h2 := Ideal.mul_mem_left ((𝒜₊).toIdeal ^ (j + 1)) (algebraMap k S c⁻¹) h1
      rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul] at h2

private lemma proj_mem (e : ℕ) (x : S) : proj 𝒜 e x ∈ 𝒜 e := SetLike.coe_mem _

/-- An element of `S_+^d` is congruent modulo `S_+^{d + 1}` to its degree-`d` part: with the
identification `S_+^d = ⨁_{e ≥ d} S_e` this is just dropping the terms of degree `> d`. -/
private lemma sub_proj_mem_pow (h0 : 𝒜 0 = 1) (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤)
    {d : ℕ} {a : S} (ha : a ∈ (𝒜₊).toIdeal ^ d) : a - proj 𝒜 d a ∈ (𝒜₊).toIdeal ^ (d + 1) := by
  have := map_mem_of_mem_pow 𝒜 h0 hgen (LinearMap.id - proj 𝒜 d)
    (((𝒜₊).toIdeal ^ (d + 1)).restrictScalars k)
    (fun i hi y hy => by
      simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, Submodule.restrictScalars_mem]
      rcases eq_or_lt_of_le hi with rfl | hlt
      · rw [proj_eq_self 𝒜 hy, sub_self]
        exact Submodule.zero_mem _
      · rw [proj_eq_zero_of_mem_ne 𝒜 hy (by omega), sub_zero]
        exact grade_le_pow_irrelevant 𝒜 h0 hgen (by omega) hy) ha
  simpa using this


/-- **Stacks 00P6 (3), first half.** For a graded algebra of finite type over a field whose
degree-zero part is the image of the structure map, the Krull dimension is the height of the
irrelevant ideal: every irreducible component of the spectrum passes through the closed point
cut out by the irrelevant ideal, so the local dimension is largest there. -/
private lemma ringKrullDim_eq_height_irrelevant (k' : Type*) [Field k'] [Algebra k' S]
    [Algebra.FiniteType k' S] (hm : (𝒜₊).toIdeal.IsMaximal)
    (hmin : ∀ p ∈ minimalPrimes S, p ≤ (𝒜₊).toIdeal) :
    ringKrullDim S = (𝒜₊).toIdeal.height := by
  set x : PrimeSpectrum S := ⟨(𝒜₊).toIdeal, hm.isPrime⟩ with hx
  have hall : ∀ Z ∈ irreducibleComponents (PrimeSpectrum S), x ∈ Z := by
    intro Z hZ
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hZ
    obtain ⟨p, hp, rfl⟩ := hZ
    exact fun f hf => hmin p hp hf
  have key : ∀ y : PrimeSpectrum S, TopologicalSpace.localKrullDim (PrimeSpectrum S) y ≤
      TopologicalSpace.localKrullDim (PrimeSpectrum S) x := by
    intro y
    rw [(PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k' y).1,
      (PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k' x).1]
    exact biSup_mono fun Z hZ => ⟨hZ.1, hall Z hZ.1⟩
  have h1 : topologicalKrullDim (PrimeSpectrum S) =
      TopologicalSpace.localKrullDim (PrimeSpectrum S) x := by
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    exact le_antisymm (iSup_le key) (le_iSup _ x)
  have hset : {𝔪 : Ideal S | 𝔪.IsMaximal ∧ x.asIdeal ≤ 𝔪} = {x.asIdeal} := by
    ext 𝔪
    refine ⟨fun h => (hm.eq_of_le h.1.ne_top h.2).symm, ?_⟩
    rintro rfl
    exact ⟨hm, le_rfl⟩
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, h1,
    (PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k' x).2, hset]
  simp [hx]

/-! ### The Hilbert function of the localization at the irrelevant ideal -/

section Localized

variable [hpr : Ideal.IsPrime (𝒜₊).toIdeal] {R : Type*} [CommRing R] [Algebra S R] [Algebra k R]
  [IsScalarTower k S R] [IsLocalization.AtPrime R (𝒜₊).toIdeal]

omit [Algebra k R] [IsScalarTower k S R] in
/-- Contraction along the localization map: the preimage of `(S_+R)^N` is `S_+^N`. -/
private lemma mem_pow_of_algebraMap_mem_map_pow (h0 : 𝒜 0 = 1) {a : S} {N : ℕ}
    (h : algebraMap S R a ∈ Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ N) :
    a ∈ (𝒜₊).toIdeal ^ N := by
  rw [← Ideal.map_pow, IsLocalization.mem_map_algebraMap_iff (𝒜₊).toIdeal.primeCompl R] at h
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy, t, htc, hx'⟩ : ∃ y : S, y ∈ (𝒜₊).toIdeal ^ N ∧ ∃ t : S, t ∉ (𝒜₊).toIdeal ∧
      algebraMap S R a * algebraMap S R t = algebraMap S R y := ⟨x.1, x.1.2, x.2, x.2.2, hx⟩
  rw [← map_mul] at hx'
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists (𝒜₊).toIdeal.primeCompl R).1 hx'
  refine mem_pow_of_mul_mem_pow 𝒜 h0 (t := (u : S) * t) (fun hmem => ?_) ?_
  · rcases hpr.mem_or_mem hmem with h' | h'
    · exact u.2 h'
    · exact htc h'
  · rw [show (u : S) * t * a = (u : S) * (a * t) by ring, hu]
    exact Ideal.mul_mem_left _ _ hy

omit [Algebra k R] [IsScalarTower k S R] in
/-- The localization map is surjective modulo every power of the maximal ideal: a geometric series
inverts the denominator `t` after replacing it by the unit `1 + u` with `u ∈ S_+`. -/
private lemma exists_sub_algebraMap_mem_map_pow (h0 : 𝒜 0 = 1) (r : R) (N : ℕ) :
    ∃ a : S, r - algebraMap S R a ∈ Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ N := by
  obtain ⟨x, hx⟩ := IsLocalization.surj (𝒜₊).toIdeal.primeCompl r
  obtain ⟨y, t, htc, hx'⟩ : ∃ y t : S, t ∉ (𝒜₊).toIdeal ∧
      r * algebraMap S R t = algebraMap S R y := ⟨x.1, x.2, x.2.2, hx⟩
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_sub_algebraMap_mem_irrelevant 𝒜 h0 htc
  set u : S := algebraMap k S c⁻¹ * (t - algebraMap k S c) with hu
  have hum : u ∈ (𝒜₊).toIdeal := Ideal.mul_mem_left _ _ hc
  have hut : algebraMap k S c⁻¹ * t = 1 + u := by
    rw [hu, mul_sub, ← map_mul, inv_mul_cancel₀ hc0, map_one]
    ring
  have hgeom : (∑ i ∈ Finset.range N, (-u) ^ i) * (1 + u) = 1 - (-u) ^ N := by
    linear_combination -geom_sum_mul (-u) N
  have hkey : t * (algebraMap k S c⁻¹ * ∑ i ∈ Finset.range N, (-u) ^ i) = 1 - (-u) ^ N := by
    linear_combination (∑ i ∈ Finset.range N, (-u) ^ i) * hut + hgeom
  refine ⟨y * (algebraMap k S c⁻¹ * ∑ i ∈ Finset.range N, (-u) ^ i), ?_⟩
  have hstep : r - algebraMap S R (y * (algebraMap k S c⁻¹ * ∑ i ∈ Finset.range N, (-u) ^ i))
      = r * algebraMap S R ((-u) ^ N) := by
    have h1 : algebraMap S R (y * (algebraMap k S c⁻¹ * ∑ i ∈ Finset.range N, (-u) ^ i))
        = r * algebraMap S R (t * (algebraMap k S c⁻¹ * ∑ i ∈ Finset.range N, (-u) ^ i)) := by
      simp only [map_mul]
      rw [← hx']
      ring
    rw [h1, hkey, map_sub, map_one]
    ring
  rw [hstep, map_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ (neg_mem hum)) N)

omit hpr [Algebra k R] [IsScalarTower k S R] [IsLocalization.AtPrime R (𝒜₊).toIdeal] in
/-- The maximal ideal of the localization annihilates `m_R^d / m_R^{d + 1}`. -/
private lemma smul_eq_zero_of_mem_map_irrelevant (d : ℕ) {s : R}
    (hs : s ∈ Ideal.map (algebraMap S R) (𝒜₊).toIdeal)
    (x : ↥(Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ d) ⧸
      (Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ (d + 1)).submoduleOf
        (Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ d)) : s • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hmem : ((s • y : ↥(Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ d)) : R)
      ∈ Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ (d + 1) := by
    rw [Submodule.coe_smul, smul_eq_mul, pow_succ']
    exact Ideal.mul_mem_mul hs y.2
  exact hmem

/-- **Stacks 00P6 (4).** The Hilbert function of the localization at the irrelevant ideal is the
Hilbert function `d ↦ dim_k S_d` of `S`: the map `S_d → m_R^d / m_R^{d + 1}` induced by the
localization map is a `k`-linear isomorphism, and the target is killed by `m_R`, so its length over
`R` is its dimension over `k`. -/
private lemma length_quot_map_pow_eq_finrank (h0 : 𝒜 0 = 1) [Module.Finite k ↥(𝒜 1)]
    (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤) (d : ℕ) :
    Module.length R (↥(Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ d) ⧸
        (Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ (d + 1)).submoduleOf
          (Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ d))
      = Module.finrank k ↥(𝒜 d) := by
  have hmemI : ∀ y : S, y ∈ 𝒜 d →
      algebraMap S R y ∈ Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ d := by
    intro y hy
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (grade_le_pow_irrelevant 𝒜 h0 hgen le_rfl hy)
  set I : Ideal R := Ideal.map (algebraMap S R) (𝒜₊).toIdeal with hI
  let g : ↥(𝒜 d) →ₗ[k] ↥(I ^ d) :=
    { toFun := fun y => ⟨algebraMap S R (y : S), hmemI y y.2⟩
      map_add' := fun y z => by
        refine Subtype.ext ?_
        simp only [Submodule.coe_add, map_add]
      map_smul' := fun c y => by
        refine Subtype.ext ?_
        simp only [RingHom.id_apply, Submodule.coe_smul, Submodule.coe_smul_of_tower]
        rw [Algebra.smul_def, Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply k S R] }
  let π : ↥(I ^ d) →ₗ[k] (↥(I ^ d) ⧸ (I ^ (d + 1)).submoduleOf (I ^ d)) :=
    ((I ^ (d + 1)).submoduleOf (I ^ d)).mkQ.restrictScalars k
  have hπg : ∀ y : ↥(𝒜 d), π (g y) = Submodule.Quotient.mk (g y) := fun _ => rfl
  have hinj : Function.Injective (π ∘ₗ g) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [LinearMap.comp_apply, hπg, Submodule.Quotient.mk_eq_zero] at hy
    exact Subtype.ext (eq_zero_of_mem_pow_of_lt 𝒜 h0 hgen (Nat.lt_succ_self d) y.2
      (mem_pow_of_algebraMap_mem_map_pow 𝒜 h0 hy))
  have hsurj : Function.Surjective (π ∘ₗ g) := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_map_pow 𝒜 h0 (z : R) (d + 1)
    have haId : algebraMap S R a ∈ I ^ d := by
      simpa using Submodule.sub_mem (I ^ d) z.2 (Ideal.pow_le_pow_right (Nat.le_succ d) ha)
    have ham : a ∈ (𝒜₊).toIdeal ^ d := mem_pow_of_algebraMap_mem_map_pow 𝒜 h0 haId
    refine ⟨⟨proj 𝒜 d a, proj_mem 𝒜 d a⟩, ?_⟩
    rw [LinearMap.comp_apply, hπg, Submodule.Quotient.eq]
    have h2 : algebraMap S R (a - proj 𝒜 d a) ∈ I ^ (d + 1) := by
      rw [hI, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (sub_proj_mem_pow 𝒜 h0 hgen ham)
    have h4 : algebraMap S R (proj 𝒜 d a) - (z : R)
        = -(algebraMap S R (a - proj 𝒜 d a) + ((z : R) - algebraMap S R a)) := by
      rw [map_sub]
      ring
    show algebraMap S R (proj 𝒜 d a) - (z : R) ∈ I ^ (d + 1)
    rw [h4]
    exact neg_mem (add_mem h2 ha)
  have hfin : Module.Finite k ↥(𝒜 d) := finite_grade 𝒜 h0 hgen d
  let e : ↥(𝒜 d) ≃ₗ[k] (↥(I ^ d) ⧸ (I ^ (d + 1)).submoduleOf (I ^ d)) :=
    LinearEquiv.ofBijective (π ∘ₗ g) ⟨hinj, hsurj⟩
  have : Module.Finite k (↥(I ^ d) ⧸ (I ^ (d + 1)).submoduleOf (I ^ d)) := Module.Finite.equiv e
  have hscal : ∀ r : R, ∃ c : k,
      ∀ x : (↥(I ^ d) ⧸ (I ^ (d + 1)).submoduleOf (I ^ d)), r • x = c • x := by
    intro r
    obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_map_pow 𝒜 h0 r 1
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_irrelevant 𝒜 h0 a
    refine ⟨c, fun x => ?_⟩
    rw [pow_one] at ha
    have h3 := Submodule.add_mem _ ha (Ideal.mem_map_of_mem (algebraMap S R) hc)
    rw [map_sub, ← IsScalarTower.algebraMap_apply k S R] at h3
    have h5 : (r - algebraMap k R c) • x = 0 :=
      smul_eq_zero_of_mem_map_irrelevant 𝒜 d (by simpa using h3) x
    rwa [sub_smul, sub_eq_zero, algebraMap_smul] at h5
  rw [length_eq_length_of_exists_smul_eq (k := k) hscal, Module.length_eq_finrank, ← e.finrank_eq]

/-- The Hilbert–Samuel function of the localization at the irrelevant ideal, computed from the
Hilbert function of `S` by the filtration `m_R^d / m_R^{d + 1} ≅ S_d`. -/
private lemma length_quotient_map_pow_eq_sum (h0 : 𝒜 0 = 1) [Module.Finite k ↥(𝒜 1)]
    (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤) (n : ℕ) :
    Module.length R (R ⧸ Ideal.map (algebraMap S R) (𝒜₊).toIdeal ^ n)
      = ((∑ d ∈ Finset.range n, Module.finrank k ↥(𝒜 d) : ℕ) : ℕ∞) := by
  set I : Ideal R := Ideal.map (algebraMap S R) (𝒜₊).toIdeal with hI
  induction n with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top,
        Module.length_eq_zero_iff.2 (Ideal.Quotient.subsingleton_iff.2 rfl)]
      simp
  | succ n ih =>
      let f : (↥(I ^ n) ⧸ (I ^ (n + 1)).submoduleOf (I ^ n)) →ₗ[R] (R ⧸ I ^ (n + 1)) :=
        Submodule.mapQ _ _ (I ^ n).subtype le_rfl
      let g : (R ⧸ I ^ (n + 1)) →ₗ[R] (R ⧸ I ^ n) :=
        Submodule.mapQ _ _ LinearMap.id (by simpa using Ideal.pow_le_pow_right (Nat.le_succ n))
      have hf : ∀ y : ↥(I ^ n),
          f (Submodule.Quotient.mk y) = Submodule.Quotient.mk (y : R) := fun _ => rfl
      have hg : ∀ r : R,
          g (Submodule.Quotient.mk r) = Submodule.Quotient.mk r := fun _ => rfl
      have hfinj : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro z hz
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        rw [Submodule.Quotient.mk_eq_zero]
        rwa [hf, Submodule.Quotient.mk_eq_zero] at hz
      have hgsurj : Function.Surjective g := by
        intro z
        obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        exact ⟨Submodule.Quotient.mk r, hg r⟩
      have hex : Function.Exact f g := by
        rw [LinearMap.exact_iff]
        refine le_antisymm (fun z hz => ?_) ?_
        · obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
          rw [LinearMap.mem_ker, hg, Submodule.Quotient.mk_eq_zero] at hz
          exact ⟨Submodule.Quotient.mk ⟨r, hz⟩, hf ⟨r, hz⟩⟩
        · rw [LinearMap.range_le_ker_iff]
          refine LinearMap.ext fun z => ?_
          obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
          rw [LinearMap.comp_apply, hf, hg, LinearMap.zero_apply,
            Submodule.Quotient.mk_eq_zero]
          exact y.2
      rw [Module.length_eq_add_of_exact f g hfinj hgsurj hex, ih,
        length_quot_map_pow_eq_finrank 𝒜 h0 hgen n, Finset.sum_range_succ, Nat.cast_add, add_comm]

/-- **Stacks 00P6 (3), second half.** The Hilbert function of the localization determines its
dimension by Stacks 00KQ, and comparing first differences turns the binomial expression of the
Hilbert–Samuel function into `deg P + 1`. -/
private lemma ringKrullDim_eq_natDegree_add_one_of_isLocalization (h0 : 𝒜 0 = 1)
    [Module.Finite k ↥(𝒜 1)] (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤) [IsNoetherianRing R]
    [IsLocalRing R] [FiniteRingKrullDim R] (P : Polynomial ℚ)
    (hP : ∀ᶠ d : ℕ in Filter.atTop, P.eval (d : ℚ) = Module.finrank k ↥(𝒜 d)) :
    (P = 0 → ringKrullDim R = 0) ∧ (P ≠ 0 → ringKrullDim R = (P.natDegree + 1 : ℕ)) := by
  have hmax : Ideal.map (algebraMap S R) (𝒜₊).toIdeal = IsLocalRing.maximalIdeal R :=
    IsLocalization.AtPrime.map_eq_maximalIdeal _ R
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim R = (e : ℕ) := by
    have hbot : ringKrullDim R ≠ ⊥ := by
      have h1 := ringKrullDim_nonneg_of_nontrivial (R := R)
      intro h
      rw [h] at h1
      simp at h1
    obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.1 hbot
    have hyt : y ≠ ⊤ := by
      intro h
      refine ringKrullDim_ne_top (R := R) ?_
      rw [← hy, h]
      rfl
    obtain ⟨m, hm'⟩ := ENat.ne_top_iff_exists.1 hyt
    exact ⟨m, by rw [← hy, ← hm']; simp⟩
  obtain ⟨a, hae, ha⟩ := ((IsLocalRing.ringKrullDim_eq_tfae (R := R) e).out 1 2).1 he
  have hL : ∀ᶠ n : ℕ in Filter.atTop,
      ((∑ d ∈ Finset.range (n + 1), Module.finrank k ↥(𝒜 d) : ℕ) : ℚ)
        = ∑ i ∈ Finset.range (e + 1), (a i : ℚ) * (n.choose i : ℚ) := by
    filter_upwards [ha] with n hn
    obtain ⟨p, hp1, hp2⟩ := hn
    have hlen : ((∑ d ∈ Finset.range (n + 1), Module.finrank k ↥(𝒜 d) : ℕ) : ℕ∞) = (p : ℕ∞) := by
      rw [← length_quotient_map_pow_eq_sum 𝒜 (R := R) h0 hgen (n + 1), hmax, hp1]
    have hnat : (∑ d ∈ Finset.range (n + 1), Module.finrank k ↥(𝒜 d)) = p := by
      exact_mod_cast hlen
    have hp2' : ((p : ℕ) : ℚ) = ∑ i ∈ Finset.range (e + 1), ((n.choose i : ℚ) * (a i : ℚ)) := by
      exact_mod_cast hp2
    rw [hnat, hp2']
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hkey := eq_natDegree_add_one_of_eventually (P := P)
    (f := fun d => Module.finrank k ↥(𝒜 d)) (a := fun i => (a i : ℚ)) (e := e)
    (by exact_mod_cast hae) hP hL
  exact ⟨fun hP0 => by rw [he, hkey.1 hP0]; rfl, fun hP0 => by rw [he, hkey.2 hP0]⟩

end Localized

/-- **Stacks 00P6 (4).** The Hilbert function of the local ring `S_m` at the irrelevant ideal
agrees with the Hilbert function `d ↦ dim_k S_d` of `S`. -/
private lemma length_maximalIdeal_pow_quotient_eq_finrank (h0 : 𝒜 0 = 1)
    [Module.Finite k ↥(𝒜 1)] (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤)
    (hm : (𝒜₊).toIdeal.IsMaximal) (d : ℕ) :
    have := hm.isPrime
    Module.length (Localization.AtPrime (𝒜₊).toIdeal)
        (↥(IsLocalRing.maximalIdeal (Localization.AtPrime (𝒜₊).toIdeal) ^ d) ⧸
          (IsLocalRing.maximalIdeal (Localization.AtPrime (𝒜₊).toIdeal) ^ (d + 1)).submoduleOf
            (IsLocalRing.maximalIdeal (Localization.AtPrime (𝒜₊).toIdeal) ^ d))
      = Module.finrank k ↥(𝒜 d) := by
  have := hm.isPrime
  have h := length_quot_map_pow_eq_finrank 𝒜
    (R := Localization.AtPrime (𝒜₊).toIdeal) h0 hgen d
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal (𝒜₊).toIdeal
    (Localization.AtPrime (𝒜₊).toIdeal)] at h
  exact h

/-- **Stacks 00P6 (3), second half.** Given that `dim S = height m`, Stacks 00KQ computes `dim S`
as `deg P + 1`, with `deg 0 = -1`. -/
private lemma ringKrullDim_eq_natDegree_add_one (h0 : 𝒜 0 = 1)
    [Module.Finite k ↥(𝒜 1)] (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤)
    (hm : (𝒜₊).toIdeal.IsMaximal) (P : Polynomial ℚ)
    (hP : ∀ᶠ d : ℕ in Filter.atTop, P.eval (d : ℚ) = Module.finrank k ↥(𝒜 d))
    (hdim : ringKrullDim S = (𝒜₊).toIdeal.height) :
    (P = 0 → ringKrullDim S = 0) ∧ (P ≠ 0 → ringKrullDim S = (P.natDegree + 1 : ℕ)) := by
  have := hm.isPrime
  have : Algebra.FiniteType k S := finiteType_of_adjoin_eq_top 𝒜 hgen
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have heq : ringKrullDim S = ringKrullDim (Localization.AtPrime (𝒜₊).toIdeal) := by
    rw [hdim, IsLocalization.AtPrime.ringKrullDim_eq_height (𝒜₊).toIdeal]
  rw [heq]
  exact ringKrullDim_eq_natDegree_add_one_of_isLocalization 𝒜 h0 hgen P hP


end

open HomogeneousIdeal Polynomial in
/-- **Stacks 00P6.** Items (1)–(4) of the tag; see the module docstring. -/
public theorem solution
    {k S : Type*} [Field k] [CommRing S] [Nontrivial S] [Algebra k S]
    (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜] (h0 : 𝒜 0 = 1)
    [Module.Finite k ↥(𝒜 1)] (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤)
    (P : ℚ[X]) (hP : ∀ᶠ d : ℕ in Filter.atTop, P.eval (d : ℚ) = Module.finrank k ↥(𝒜 d)) :
    ∃ hm : 𝒜₊.toIdeal.IsMaximal,
      letI := hm.isPrime
      (∀ p ∈ minimalPrimes S, Ideal.IsHomogeneous 𝒜 p ∧ p ≤ 𝒜₊.toIdeal) ∧
      (P = 0 → ringKrullDim S = 0) ∧
      (P ≠ 0 → ringKrullDim S = (P.natDegree + 1 : ℕ)) ∧
      ringKrullDim S = 𝒜₊.toIdeal.height ∧
      ∀ d : ℕ, Module.length (Localization.AtPrime (𝒜₊).toIdeal)
          (↥(IsLocalRing.maximalIdeal (Localization.AtPrime (𝒜₊).toIdeal) ^ d) ⧸
            (IsLocalRing.maximalIdeal (Localization.AtPrime (𝒜₊).toIdeal) ^ (d + 1)).submoduleOf
              (IsLocalRing.maximalIdeal (Localization.AtPrime (𝒜₊).toIdeal) ^ d))
        = Module.finrank k ↥(𝒜 d) := by
  have hft : Algebra.FiniteType k S := finiteType_of_adjoin_eq_top 𝒜 hgen
  have hm : (𝒜₊).toIdeal.IsMaximal := irrelevant_isMaximal 𝒜 h0
  have h2 : ∀ p ∈ minimalPrimes S, Ideal.IsHomogeneous 𝒜 p ∧ p ≤ (𝒜₊).toIdeal :=
    fun p hp => isHomogeneous_and_le_irrelevant_of_mem_minimalPrimes 𝒜 h0 hp
  have hdim : ringKrullDim S = (𝒜₊).toIdeal.height :=
    ringKrullDim_eq_height_irrelevant 𝒜 k hm fun p hp => (h2 p hp).2
  have hHilb := length_maximalIdeal_pow_quotient_eq_finrank 𝒜 h0 hgen hm
  obtain ⟨h3, h3'⟩ :=
    ringKrullDim_eq_natDegree_add_one 𝒜 h0 hgen hm P hP hdim
  exact ⟨hm, h2, h3, h3', hdim, hHilb⟩

end Stacks.GradedAlgebra.HilbertDimension

/-!
# Dimension of a graded algebra generated in degree one over a field

Let `k` be a field and let `S` be a graded `k`-algebra, `S = ⨁_{d ≥ 0} S_d`, which is generated
over `k` by finitely many elements of degree `1` and whose degree-zero part is `S_0 = k`. The
irrelevant ideal `S_+ = ⨁_{d > 0} S_d` is then a maximal ideal `m` of `S`, and every minimal
prime of `S` is homogeneous and contained in `S_+` — as is every homogeneous ideal other than `S`
itself, `S_0` being a field. So every irreducible component of `Spec(S)` passes through the closed
point `x` corresponding to `m`.
Consequently the dimension of `S` is already visible at that one point, and it is computed by the
Hilbert function `d ↦ dim_k S_d`: writing `P ∈ ℚ[T]` for the polynomial with `dim_k S_d = P(d)`
for all `d ≫ 0` (Tag 00K1), one has

  `dim(S) = deg(P) + 1 = dim_x Spec(S)`,

with the convention `deg(0) = -1`. Finally the Hilbert function of the local ring `S_m` — the
function `d ↦ length_{S_m} (m^d S_m / m^{d + 1} S_m)` — coincides with the Hilbert function
`d ↦ dim_k S_d` of `S`, because `m^d / m^{d + 1} ≅ S_d` is already a module over the residue
field and so is unaffected by the localization.

## Main results

* `GradedAlgebra.irrelevant_isMaximal_and_ringKrullDim_eq_natDegree_add_one`: items (1)–(4) of
  the source, as a single conjunction.

## Implementation notes

The grading is Mathlib's internal grading of an algebra, `𝒜 : ℕ → Submodule k S` with
`[GradedAlgebra 𝒜]`, so that `S_d` is `↥(𝒜 d)` and `dim_k S_d` is `Module.finrank k ↥(𝒜 d)`; the
irrelevant ideal is `HomogeneousIdeal.irrelevant 𝒜`, written `𝒜₊`. The source's `S_0 = k` is
`𝒜 0 = 1`, that is `𝒜 0 = LinearMap.range (Algebra.linearMap k S)` (`Submodule.one_eq_range`),
together with `Nontrivial S`; the two together say exactly that `k → S` is injective with image
`𝒜 0`. Being generated over `k` by finitely many elements of degree `1` is split into the two
conditions it is the conjunction of, `Algebra.adjoin k ↑(𝒜 1) = ⊤` and `Module.Finite k ↥(𝒜 1)`:
given `𝒜 0 = 1`, a finite set of degree-one generators spans `𝒜 1` over `k`, and conversely a
`k`-basis of `𝒜 1` is a finite set of degree-one generators. Noetherianness of `S` is not
assumed, being a consequence (`Algebra.FiniteType` over a field).

The polynomial `P` of the source is not asserted to exist here but is taken as a parameter,
pinned by the property that defines it, `dim_k S_d = P(d)` for all `d ≫ 0` (`Filter.atTop`); its
existence is Tag 00K1. The source's convention `deg(0) = -1` is unfolded into the two cases
`P = 0` and `P ≠ 0` rather than transported into `WithBot ℕ`, where `Polynomial.degree 0 = ⊥`
absorbs `+ 1` and would force `dim(S) = ⊥`, a value `ringKrullDim` takes only on the zero ring.

The local dimension `dim_x Spec(S)` at the closed point `x` corresponding to `m = S_+` is
`Ideal.height m`: for a prime `m` the height is the Krull dimension of `S_m`
(`IsLocalization.AtPrime.ringKrullDim_eq_height`), which is what `dim_x Spec(S)` equals for a
closed point of the spectrum of a finite type algebra over a field (Tag 00OU, a special case of
Tag 00OT). Item (4) is stated for the concrete local ring `Localization.AtPrime m`, with its
Hilbert function written as in Tag 00K8 — `length_R (m_R^d / m_R^{d + 1})` — save that the
submodule `m_R^d • ⊤` of `R` is the ideal `m_R^d` itself, which is used directly.

Items (1) and (4) are entangled: the type `Localization.AtPrime m` needs `m` to be prime, which
is part of item (1). The conjunction is therefore stated as `∃ hm : m.IsMaximal, …`, with the
remaining items living under `letI := hm.isPrime`; this is item (1) followed by the items that
depend on it, not an existential statement about some auxiliary datum.

Faithfulness. (1) Every hypothesis is used by the conclusion. `𝒜 0 = 1` and `Nontrivial S` are
what make `S_+` maximal: `S / S_+ ≅ S_0`, so `S_+` is maximal exactly when `S_0` is a field, and
in the zero ring there is no maximal ideal at all. Generation in degree `1` is what makes
`S_+^d = ⨁_{e ≥ d} S_e`, hence `m^d / m^{d + 1} ≅ S_d`, and so is used by item (4): for
`S = k[y]` with `deg y = 2`, the ideal `m = S_+` satisfies `m^d = (y^d)` and
`length (m^d / m^{d + 1}) = 1` for every `d`, while `dim_k S_d = 0` for odd `d`. Finiteness of
`𝒜 1` is used by item (3): for `S = k[x_1, x_2, …]` with every `x_i` of degree `1`, each
`Module.finrank k ↥(𝒜 d)` is `0` by the convention for infinite-dimensional spaces, so the
hypothesis on `P` holds with `P = 0` while `ringKrullDim S = ⊤ ≠ 0`. Finally `P` and its defining
property are used by item (3). (2) The scalars are the source's: `dim_k S_d` is a dimension over
the base field `k`, the lengths in item (4) are lengths over the local ring `S_m`, not over `S`
and not over the residue field, and the ideals in item (2) are ideals of `S`. (3) The canonical
objects the source names are pinned rather than asserted to exist: `S_+` is
`HomogeneousIdeal.irrelevant 𝒜`, `m` is that same ideal and not merely some maximal ideal, the
point `x` enters only through `m`, and `P` is pinned by `dim_k S_d = P(d)` for `d ≫ 0`. (4) A
witness: for `S = k[x_0, …, x_n]` with the standard grading one has `𝒜 0 = 1`, `𝒜 1` of dimension
`n + 1`, `P(T) = (T + 1) ⋯ (T + n) / n!` of degree `n`, `S_+ = (x_0, …, x_n)` maximal of height
`n + 1 = dim S`, and `length (m^d / m^{d + 1}) = binom(d + n, n) = dim_k S_d`; the Hilbert
function is nonconstant for `n ≥ 1`, so item (4) is not vacuous.

## References

* [Stacks Project, Tag 00P6](https://stacks.math.columbia.edu/tag/00P6)

## Tags

graded ring, irrelevant ideal, Hilbert function, dimension
-/

open HomogeneousIdeal Polynomial in
/-- **Stacks 00P6.** Let `k` be a field and let `S` be a graded `k`-algebra with `S_0 = k` that is
generated over `k` by finitely many elements of degree `1`. Let `P ∈ ℚ[T]` be the polynomial with
`dim_k S_d = P(d)` for all `d ≫ 0`. Then: (1) the irrelevant ideal `m = S_+` is maximal;
(2) every minimal prime of `S` is homogeneous and contained in `S_+`; (3) `dim(S) = deg(P) + 1`,
with `deg(0) = -1`, and this equals the dimension `dim_x Spec(S) = dim(S_m) = height(m)` of
`Spec(S)` at the closed point `x` given by `m`; (4) the Hilbert function
`d ↦ length_{S_m} (m^d S_m / m^{d + 1} S_m)` of the local ring `S_m` is the Hilbert function
`d ↦ dim_k S_d` of `S`. -/
@[stacks 00P6 "Items (1)-(4). `dim_x Spec(S)` is the height of the irrelevant ideal, and the
convention `deg 0 = -1` is unfolded into the cases `P = 0`, `P ≠ 0`. See the module docstring.",
  ega "IV 6.10.5" "special case"]
public theorem GradedAlgebra.irrelevant_isMaximal_and_ringKrullDim_eq_natDegree_add_one
    {k S : Type*} [Field k] [CommRing S] [Nontrivial S] [Algebra k S]
    (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜] (h0 : 𝒜 0 = 1)
    [Module.Finite k ↥(𝒜 1)] (hgen : Algebra.adjoin k (𝒜 1 : Set S) = ⊤)
    (P : ℚ[X]) (hP : ∀ᶠ d : ℕ in Filter.atTop, P.eval (d : ℚ) = Module.finrank k ↥(𝒜 d)) :
    ∃ hm : 𝒜₊.toIdeal.IsMaximal,
      letI := hm.isPrime
      (∀ p ∈ minimalPrimes S, Ideal.IsHomogeneous 𝒜 p ∧ p ≤ 𝒜₊.toIdeal) ∧
      (P = 0 → ringKrullDim S = 0) ∧
      (P ≠ 0 → ringKrullDim S = (P.natDegree + 1 : ℕ)) ∧
      ringKrullDim S = 𝒜₊.toIdeal.height ∧
      ∀ d : ℕ, Module.length (Localization.AtPrime (𝒜₊).toIdeal)
          (↥(IsLocalRing.maximalIdeal (Localization.AtPrime (𝒜₊).toIdeal) ^ d) ⧸
            (IsLocalRing.maximalIdeal (Localization.AtPrime (𝒜₊).toIdeal) ^ (d + 1)).submoduleOf
              (IsLocalRing.maximalIdeal (Localization.AtPrime (𝒜₊).toIdeal) ^ d))
        = Module.finrank k ↥(𝒜 d) :=
          by apply Stacks.GradedAlgebra.HilbertDimension.solution <;> assumption
