module

public import StacksFrontier.Algebra.Polynomial.TorsionCharpoly
public import StacksFrontier.Algebra.Polynomial.PowerProductGrading
public import StacksFrontier.AlgebraicGeometry.Picard.WeilPairingCharpoly
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The eigenvalues of Frobenius are the reciprocal roots of the zeta function

Let `χ ∈ ℚ[X]` be monic of degree `2γ` with the symmetry `χ(0) χ_j = q^{2γ-j} χ_{2γ-j}` (from the
Weil pairing) and norm form `N(R mod χ)` computing the orders `h_m = #Ker(1 - F^m)`, and let
`α_1, …, α_r` (`r ≤ 2γ`) be the algebraic integers of the zeta function, with
`h_m = ∏ (1 - α_i^m)` and its functional equation. Then `χ = ∏ (X - α_i)`
(`Stacks.Zeta.map_eq_prod_of_zeta`).

## Main results

* `Stacks.Zeta.normForm_eq_prod_roots`: `N(R mod χ) = ∏_{χ(b) = 0} R(b)`.
* `Stacks.Zeta.roots_map_div_eq_of_coeff_symm`: the roots of `χ` are stable under `b ↦ q/b`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.Zeta

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- **The norm form as a product over the roots.** -/
theorem normForm_eq_prod_roots {χ : ℚ[X]} (hχ : χ.Monic) (R : ℤ[X]) :
    algebraMap ℚ K (Stacks.Polynomial.normForm χ R) =
      ((χ.map (algebraMap ℚ K)).roots.map fun b => (R.map (Int.castRingHom K)).eval b).prod := by
  have hinj : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
  rw [Stacks.Polynomial.normForm_eq_resultant hχ, ← resultant_map_map,
    ← natDegree_map_eq_of_injective hinj χ,
    ← natDegree_map_eq_of_injective hinj (R.map (Int.castRingHom ℚ)), Polynomial.map_map,
    show (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K from RingHom.ext_int _ _,
    resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _), (hχ.map _).leadingCoeff, one_pow,
    one_mul]

/-- A root of a monic polynomial whose constant coefficient is nonzero is nonzero. -/
private theorem ne_zero_of_mem_roots_of_coeff_zero_ne_zero {F : Type*} [Field F] {χ : F[X]}
    (hχ : χ.Monic) (h0 : χ.coeff 0 ≠ 0) : ∀ b ∈ χ.roots, b ≠ 0 := by
  intro b hb e
  rw [e, mem_roots hχ.ne_zero, IsRoot, ← coeff_zero_eq_eval_zero] at hb
  exact h0 hb

omit [CharZero K] in
/-- **The roots of a polynomial with the symmetry `χ(0) χ_j = q^{N-j} χ_{N-j}` are stable under
`b ↦ q / b`.** For `x ≠ 0`, `x^N χ(q/x) = χ(0) χ(x)`, and `x^N χ(q/x) = ∏ (q - b x)` over the
roots `b`, so `χ(0) χ = χ(0) ∏ (X - q/b)`. -/
theorem roots_map_div_eq_of_coeff_symm (χ : K[X]) (hχ : χ.Monic) (q : K) (hq : q ≠ 0)
    (h0 : χ.coeff 0 ≠ 0)
    (hsym : ∀ j ≤ χ.natDegree, χ.coeff 0 * χ.coeff j =
      q ^ (χ.natDegree - j) * χ.coeff (χ.natDegree - j)) :
    χ.roots.map (fun b => q / b) = χ.roots := by
  set N := χ.natDegree
  have hsplit : χ = (χ.roots.map fun b => X - C b).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hχ
      (IsAlgClosed.splits χ).natDegree_eq_card_roots.symm).symm
  have hcard : Multiset.card χ.roots = N := (IsAlgClosed.splits χ).natDegree_eq_card_roots.symm
  have hb0 := ne_zero_of_mem_roots_of_coeff_zero_ne_zero hχ h0
  -- `x^N χ(q/x) = χ(0) χ(x)` for `x ≠ 0`
  have hscal : ∀ x : K, x ≠ 0 → x ^ N * χ.eval (q / x) = χ.coeff 0 * χ.eval x := by
    intro x hx
    rw [eval_eq_sum_range, eval_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hjN : j ≤ N := by omega
    rw [show N + 1 - 1 - j = N - j by omega, ← mul_assoc (χ.coeff 0), hsym j hjN, div_pow,
      show x ^ N = x ^ (N - j) * x ^ j by rw [← pow_add]; congr 1; omega]
    field_simp
  -- the product form
  have hprod : ∀ x : K, x ≠ 0 →
      ((χ.roots.map fun b => C q - C b * X).prod).eval x = χ.coeff 0 * χ.eval x := by
    intro x hx
    rw [← hscal x hx, eval_multiset_prod]
    conv_rhs => rw [hsplit]
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    have e1 : (χ.roots.map ((fun p : K[X] => p.eval x) ∘ fun b => C q - C b * X)) =
        χ.roots.map fun b => x * ((fun p : K[X] => p.eval (q / x)) ∘ fun b => X - C b) b := by
      refine Multiset.map_congr rfl fun b _ => ?_
      simp only [Function.comp, eval_sub, eval_C, eval_mul, eval_X]
      field_simp
    rw [e1, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]
  have hpoly : (χ.roots.map fun b => C q - C b * X).prod = C (χ.coeff 0) * χ := by
    refine eq_of_infinite_eval_eq _ _ ((Set.infinite_univ.diff (Set.finite_singleton 0)).mono ?_)
    intro x hx
    have hx0 : x ≠ 0 := fun e => hx.2 e
    rw [Set.mem_setOf_eq, hprod x hx0, eval_mul, eval_C]
  have hfac : (χ.roots.map fun b => C q - C b * X).prod =
      C (χ.coeff 0) * (χ.roots.map fun b => X - C (q / b)).prod := by
    have e2 : (χ.roots.map fun b => C q - C b * X) =
        χ.roots.map fun b => C (-b) * (X - C (q / b)) := by
      refine Multiset.map_congr rfl fun b hb => ?_
      rw [mul_sub, ← C_mul, show -b * (q / b) = -q by field_simp [hb0 b hb], C_neg, C_neg,
        sub_neg_eq_add, neg_mul, mul_comm]
      ring
    have e3 : (χ.roots.map fun b => C (-b)) = (χ.roots.map fun b => -b).map C := by
      rw [Multiset.map_map]; rfl
    rw [e2, Multiset.prod_map_mul, e3, ← map_multiset_prod]
    congr 2
    conv_rhs => rw [coeff_zero_eq_eval_zero, hsplit, eval_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp, eval_sub, eval_X, eval_C, zero_sub]
  rw [hfac] at hpoly
  have hχ' : χ = (χ.roots.map fun b => X - C (q / b)).prod :=
    (mul_left_cancel₀ (C_ne_zero.mpr h0) hpoly).symm
  have := roots_multiset_prod_X_sub_C (χ.roots.map fun b => q / b)
  rw [Multiset.map_map] at this
  conv_rhs => rw [hχ']
  exact this.symm

/-! ### The weight `|N_{L/ℚ}|` on a number field -/

section Weight

variable (L : Type*) [Field L] [Algebra ℚ L]

/-- The weight `x ↦ |N_{L/ℚ}(x)|` on the units of `L`. -/
def normWeight : Lˣ →* ℚ where
  toFun x := |Algebra.norm ℚ (x : L)|
  map_one' := by simp
  map_mul' x y := by simp [abs_mul]

variable {L} [FiniteDimensional ℚ L]

/-- The weight `|N_{L/ℚ}(x)|` of a unit `x` of `L` is positive. -/
theorem normWeight_pos (x : Lˣ) : 0 < normWeight L x :=
  abs_pos.mpr ((Algebra.norm_ne_zero_iff (R := ℚ)).mpr x.ne_zero)

/-- A unit `x` of `L` that is integral over `ℤ` has weight `|N_{L/ℚ}(x)| ≥ 1`. -/
theorem one_le_normWeight (x : Lˣ) (hx : IsIntegral ℤ (x : L)) : 1 ≤ normWeight L x := by
  have hint : IsIntegral ℤ (Algebra.norm ℚ (x : L)) := Algebra.isIntegral_norm ℚ hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn
    exact (Algebra.norm_ne_zero_iff (R := ℚ)).mpr x.ne_zero hn.symm
  show 1 ≤ |Algebra.norm ℚ (x : L)|
  rw [← hn, algebraMap_int_eq, eq_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs hn0

/-- A natural number `q > 1` that is nonzero in `L` has weight `|N_{L/ℚ}(q)| > 1`. -/
theorem one_lt_normWeight_natCast (q : ℕ) (hq : 1 < q) (hq0 : ((q : L)) ≠ 0) :
    1 < normWeight L (Units.mk0 (q : L) hq0) := by
  show 1 < |Algebra.norm ℚ (q : L)|
  rw [show (q : L) = algebraMap ℚ L q by simp, Algebra.norm_algebraMap, abs_pow,
    Nat.abs_cast]
  exact one_lt_pow₀ (by exact_mod_cast hq) Module.finrank_pos.ne'

end Weight

/-- **The characteristic polynomial of Frobenius has the reciprocal roots of the zeta function as
roots**, in the form needed for the trace: `χ.nextCoeff = -∑ α_i`. Hypotheses: `χ ∈ ℚ[X]` monic of
degree `2γ`, symmetric for `b ↦ q/b` with `χ(0) ≥ 0`, its norm form computing
`h_m = ∏ (1 - α_i^m) ≠ 0`, the `α_i` algebraic integers with the functional equation of the zeta
function. -/
theorem nextCoeff_eq_neg_sum_of_zeta (χ : ℚ[X]) (hχ : χ.Monic) (γ : ℕ)
    (hdeg : χ.natDegree = 2 * γ) (q : ℕ) (hq : 1 < q)
    (hsym : ∀ j ≤ 2 * γ, χ.coeff 0 * χ.coeff j = (q : ℚ) ^ (2 * γ - j) * χ.coeff (2 * γ - j))
    (hpos : 0 ≤ χ.coeff 0) (r : ℕ) (α : Fin r → K) (hr : r ≤ 2 * γ)
    (hαint : ∀ i, IsIntegral ℤ (α i)) (h : ℕ → ℕ)
    (hh : ∀ m, 0 < m → (h m : K) = ∏ i, (1 - α i ^ m)) (hh0 : ∀ m, 0 < m → h m ≠ 0)
    (hfunc : ∀ m, 0 < m → (q : K) ^ (m * (2 * γ - r)) * ∏ i, ((q : K) ^ m - α i ^ m) =
      (q : K) ^ (m * γ) * h m)
    (hnorm : ∀ m, 0 < m → (h m : ℚ) = Stacks.Polynomial.normForm χ (1 - Polynomial.X ^ m)) :
    algebraMap ℚ K χ.nextCoeff = -∑ i, α i := by
  classical
  set χK := χ.map (algebraMap ℚ K)
  have hχK : χK.Monic := hχ.map _
  have hdegK : χK.natDegree = 2 * γ := by rw [natDegree_map, hdeg]
  set T₀ := χK.roots
  have hcardT : Multiset.card T₀ = 2 * γ := by
    rw [← hdegK]; exact (IsAlgClosed.splits χK).natDegree_eq_card_roots.symm
  have hqK : (q : K) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  -- `χ(0) = q^γ`
  have hχ0 : χ.coeff 0 = (q : ℚ) ^ γ := by
    have h0 := hsym 0 (Nat.zero_le _)
    rw [Nat.sub_zero, ← hdeg, hχ.coeff_natDegree, mul_one, hdeg, pow_mul] at h0
    have hq0 : (0 : ℚ) ≤ (q : ℚ) ^ γ := by positivity
    exact (sq_eq_sq₀ hpos hq0).mp (by rw [sq, h0, ← pow_mul, ← pow_mul, mul_comm])
  have hχ0K : χK.coeff 0 ≠ 0 := by
    rw [coeff_map, hχ0, map_pow, map_natCast]; exact pow_ne_zero _ hqK
  -- the symmetry of the roots
  have hsymT : T₀.map (fun b => (q : K) / b) = T₀ := by
    refine roots_map_div_eq_of_coeff_symm χK hχK (q : K) hqK hχ0K fun j hj => ?_
    rw [hdegK] at hj ⊢
    have := congrArg (algebraMap ℚ K) (hsym j hj)
    simp only [map_mul, map_pow, map_natCast] at this
    simpa only [χK, coeff_map] using this
  have hprodT : T₀.prod = (q : K) ^ γ := by
    have := (IsAlgClosed.splits χK).coeff_zero_eq_prod_roots_of_monic hχK
    rw [hdegK, pow_mul, neg_one_sq, one_pow, one_mul, coeff_map, hχ0, map_pow, map_natCast] at this
    exact this.symm
  have hT0 := ne_zero_of_mem_roots_of_coeff_zero_ne_zero hχK hχ0K
  -- the products over `T₀`
  have hG1T : ∀ m, 0 < m → (h m : K) = (T₀.map fun b => 1 - b ^ m).prod := by
    intro m hm
    have := normForm_eq_prod_roots (K := K) hχ (1 - Polynomial.X ^ m)
    rw [← hnorm m hm, map_natCast] at this
    rw [this]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  have hne : ∀ m, 0 < m → (T₀.map fun b => 1 - b ^ m).prod ≠ 0 := fun m hm => by
    rw [← hG1T m hm]; exact_mod_cast hh0 m hm
  -- the number field
  set Sset : Finset K := Finset.univ.image α ∪ T₀.toFinset
  set L := IntermediateField.adjoin ℚ (Sset : Set K)
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin fun x hx => by
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (hαint i).tower_top
    · refine ⟨χ, hχ, ?_⟩
      have := (mem_roots hχK.ne_zero).mp (Multiset.mem_toFinset.mp hx)
      rwa [IsRoot, eval_map, ← aeval_def] at this
  have hmem : ∀ x ∈ Sset, x ∈ L := fun x hx => IntermediateField.subset_adjoin ℚ _ hx
  let lift : ∀ x : K, x ∈ Sset → x ≠ 0 → Lˣ := fun x hx h0 =>
    Units.mk0 ⟨x, hmem x hx⟩ fun e => h0 (congrArg Subtype.val e)
  let ι : Lˣ → K := fun u => ((u : L) : K)
  have hι : Function.Injective ι := fun u v e => Units.ext (Subtype.ext e)
  set SI := Finset.univ.filter fun i => α i ≠ 0
  have hSI : ∀ i ∈ SI, α i ≠ 0 := fun i hi => (Finset.mem_filter.mp hi).2
  let SL : Multiset Lˣ := SI.attach.val.map fun i =>
    lift (α i.1) (Finset.mem_union_left _ (Finset.mem_image_of_mem α (Finset.mem_univ _)))
      (hSI i.1 i.2)
  let TL : Multiset Lˣ := T₀.attach.map fun b =>
    lift b.1 (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr b.2)) (hT0 b.1 b.2)
  have hSL : SL.map ι = SI.val.map α := by
    simp only [SL, Multiset.map_map, Function.comp, ι, lift, Units.val_mk0]
    conv_rhs => rw [← Multiset.attach_map_val SI.val, Multiset.map_map]
    rfl
  have hTL : TL.map ι = T₀ := by
    simp only [TL, Multiset.map_map, Function.comp, ι, lift, Units.val_mk0]
    exact Multiset.attach_map_val T₀
  -- products, read in `K`
  have hSprod : ∀ (f : K → K) (hf : f 0 = 1),
      (SI.val.map fun i => f (α i)).prod = ∏ i, f (α i) := by
    intro f hf
    rw [← Finset.prod_filter_of_ne (p := fun i => α i ≠ 0) fun i _ hi => by
      by_contra h0; exact hi (by rw [h0, hf])]
    rfl
  -- the products in `K`
  have hιinj : Function.Injective (fun x : L => (x : K)) := Subtype.val_injective
  have hqL : ((q : ℕ) : L) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  set qL : Lˣ := Units.mk0 ((q : ℕ) : L) hqL
  have hιq : ι qL = (q : K) := by simp [ι, qL]
  have hG2T : ∀ m, 0 < m → (T₀.map fun b => 1 - b⁻¹ ^ m).prod = ((q : K) ^ γ)⁻¹ ^ m * h m := by
    intro m hm
    have e1 : (T₀.map fun b => 1 - b⁻¹ ^ m) =
        T₀.map fun b => (-1) * ((b ^ m)⁻¹ * (1 - b ^ m)) := by
      refine Multiset.map_congr rfl fun b hb => ?_
      have := pow_ne_zero m (hT0 b hb)
      rw [inv_pow, mul_sub, mul_one, inv_mul_cancel₀ this]
      ring
    rw [e1, Multiset.prod_map_mul, Multiset.prod_map_mul, Multiset.map_const',
      Multiset.prod_replicate, Multiset.prod_map_inv, Multiset.prod_map_pow, Multiset.map_id',
      hcardT, hprodT,
      ← hG1T m hm, pow_mul, neg_one_sq, one_pow, one_mul, inv_pow, ← pow_mul]
  have hG2S : ∀ m, 0 < m → ∏ i, (1 - (α i / q) ^ m) = ((q : K) ^ γ)⁻¹ ^ m * h m := by
    intro m hm
    set Q : K := (q : K)
    set A := ∏ i, (Q ^ m - α i ^ m)
    have hQm : Q ^ m ≠ 0 := pow_ne_zero m hqK
    have e1 : ∏ i, (1 - (α i / Q) ^ m) = A * ((Q ^ m) ^ r)⁻¹ := by
      rw [show ((Q ^ m) ^ r)⁻¹ = ∏ _i : Fin r, (Q ^ m)⁻¹ by rw [Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, inv_pow], ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [div_pow]
      field_simp
    have key : Q ^ (m * (2 * γ - r)) * A = Q ^ (m * γ) * h m := hfunc m hm
    have h3 : Q ^ (m * γ) * A = Q ^ (m * r) * h m := by
      have h2 : Q ^ (m * γ) * (Q ^ (m * γ) * A) = Q ^ (m * γ) * (Q ^ (m * r) * h m) := by
        rw [← mul_assoc, ← pow_add, show m * γ + m * γ = m * (2 * γ - r) + m * r by
          rw [← mul_add, ← mul_add]; congr 1; omega, pow_add, mul_assoc, mul_left_comm, key]
        ring
      exact mul_left_cancel₀ (pow_ne_zero _ hqK) h2
    rw [e1, inv_pow, ← pow_mul, ← pow_mul]
    field_simp
    linear_combination h3
  -- products of a function of the units of `L`, read in `K`
  have hgen : ∀ (s : Multiset Lˣ) (F : Lˣ → L) (f : K → K), (∀ x, ((F x : L) : K) = f (ι x)) →
      (((s.map F).prod : L) : K) = ((s.map ι).map f).prod := by
    intro s F f hF
    rw [← IntermediateField.coe_val, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun x _ => hF x)
  have hSK : ∀ (f : K → K), f 0 = 1 → ((SL.map ι).map f).prod = ∏ i, f (α i) := by
    intro f hf
    rw [hSL, Multiset.map_map]
    exact hSprod f hf
  -- the hypotheses of the multiset lemma, in `L`
  have hSge : ∀ x ∈ SL, 1 ≤ normWeight L x := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    apply one_le_normWeight
    exact (isIntegral_algHom_iff ((IntermediateField.val L).restrictScalars ℤ)
      Subtype.val_injective).mp (hαint i.1)
  have hsymL : TL.map (fun y => qL * y⁻¹) = TL := by
    apply Multiset.map_injective hι
    rw [Multiset.map_map]
    have : (ι ∘ fun y => qL * y⁻¹) = (fun b => (q : K) / b) ∘ ι := by
      funext y
      simp [ι, qL, div_eq_mul_inv]
    rw [this, ← Multiset.map_map, hTL, hsymT]
  have hneL : ∀ m, 0 < m → (TL.map fun y : Lˣ => 1 - (y : L) ^ m).prod ≠ 0 := by
    intro m hm h0
    apply hne m hm
    have := congrArg (fun z : L => (z : K)) h0
    rw [hgen TL _ (fun z => 1 - z ^ m) (fun x => by simp [ι]), hTL] at this
    simpa using this
  have hG1L : ∀ m, 0 < m → (SL.map fun x : Lˣ => 1 - (x : L) ^ m).prod =
      (TL.map fun y : Lˣ => 1 - (y : L) ^ m).prod := by
    intro m hm
    apply hιinj
    simp only
    rw [hgen SL _ (fun z => 1 - z ^ m) (fun x => by simp [ι]),
      hgen TL _ (fun z => 1 - z ^ m) (fun x => by simp [ι]), hSK _ (by simp [zero_pow hm.ne']),
      hTL, ← hG1T m hm, hh m hm]
  have hG2L : ∀ m, 0 < m → ((SL.map (· * qL⁻¹)).map fun x : Lˣ => 1 - (x : L) ^ m).prod =
      ((TL.map (·⁻¹)).map fun y : Lˣ => 1 - (y : L) ^ m).prod := by
    intro m hm
    apply hιinj
    simp only
    rw [Multiset.map_map (fun x : Lˣ => 1 - (x : L) ^ m) (· * qL⁻¹) SL,
      Multiset.map_map (fun y : Lˣ => 1 - (y : L) ^ m) (·⁻¹) TL,
      hgen SL _ (fun z => 1 - (z / q) ^ m) (fun x => by simp [ι, qL, div_eq_mul_inv]),
      hgen TL _ (fun z => 1 - z⁻¹ ^ m) (fun x => by simp [ι]),
      hSK _ (by simp [zero_pow hm.ne']), hTL, hG2S m hm, hG2T m hm]
  have hST := Stacks.PowerProduct.eq_of_prodOneSub_eq_of_map_div_eq (normWeight L)
    normWeight_pos qL (one_lt_normWeight_natCast q hq hqL) SL TL hSge hsymL hneL hG1L hG2L
  have hST' : SI.val.map α = T₀ := by
    have := congrArg (Multiset.map ι) hST
    rwa [hSL, hTL] at this
  -- the trace
  rw [← nextCoeff_map (algebraMap ℚ K).injective,
    (IsAlgClosed.splits χK).nextCoeff_eq_neg_sum_roots_of_monic hχK]
  show -T₀.sum = _
  rw [← hST', neg_inj]
  rw [show (SI.val.map α).sum = ∑ i ∈ SI, α i from rfl, Finset.sum_filter_ne_zero]

end Stacks.Zeta
