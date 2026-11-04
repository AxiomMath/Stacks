module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.FieldTheory.PBasis

/-!
# Fields spanned over their `p`-th powers by one element, and the inseparability of extensions

Let `p` be a prime and `R` a commutative ring of characteristic `p`. Say that `R` is
*`p`-spanned by `t`* — `IsPSpannedBy p t` — when

$$ R = R^p + R^p t + \dots + R^p t^{p-1}, $$

that is, when `1, t, …, t^{p-1}` span `R` over the subring of `p`-th powers. For a field `K` this
is the spanning half of `PBasis (ZMod p) (fun _ : Fin 1 => t) p`, and combined with `t ∉ K^p` it
gives `[K : K^p] = p`.

If `K` is `p`-spanned by an element `t` that is not a `p`-th power, then for every finite extension
`M / K` there are `n` and `ρ ∈ M` with `ρ ^ p ^ n = t`, `minpoly K ρ = X ^ p ^ n - C t`, and
`M / K⟮ρ⟯` separable.

## Main definitions

* `IsPSpannedBy p t`: `1, t, …, t ^ (p - 1)` span the ring over its `p`-th powers.

## Main results

* `exists_fin_repr_of_sum`: any finite sum `∑ a j ^ p * t ^ e j` can be rewritten in the normal
  form `∑ i : Fin p, c i ^ p * t ^ i`.
* `IsPSpannedBy.map_ringEquiv`, `IsPSpannedBy.algebraMap_fractionRing`: the property transports
  along a ring isomorphism, and passes from a domain to its fraction field.
* `IsPSpannedBy.of_adjoin_root`: if `K` is `p`-spanned by `t` and `F = K[ρ]` with
  `ρ ^ p ^ n = t`, then `F` is `p`-spanned by `ρ`.
* `Algebra.IsSeparable.of_isPSpannedBy`: if `F` is `p`-spanned by `t` and `t` has no `p`-th
  root in an algebraic extension `M`, then `M / F` is separable.
* `minpoly_eq_X_pow_sub_C_of_pow_eq`: for `y ^ p ^ j = t` with `t` not a `p`-th power in `K`, the
  minimal polynomial of `y` is `X ^ p ^ j - C t`.
* `exists_pow_eq_minpoly_eq_and_isSeparable_adjoin`: for `M / K` finite, there are `n` and `ρ ∈ M`
  with `ρ ^ p ^ n = t`, `minpoly K ρ = X ^ p ^ n - C t`, and `M / K⟮ρ⟯` separable.

## References

* [Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

open Polynomial

variable {R : Type*} [CommRing R]

/-- `IsPSpannedBy p t`: the ring is spanned by `1, t, …, t ^ (p - 1)` over its `p`-th powers.

For a field of characteristic `p` this is the spanning half of "`{t}` is a `p`-basis". -/
def IsPSpannedBy (p : ℕ) (t : R) : Prop :=
  ∀ x : R, ∃ c : Fin p → R, x = ∑ i : Fin p, c i ^ p * t ^ (i : ℕ)

/-- In characteristic `p`, a finite sum `∑ a j ^ p * t ^ e j` with arbitrary exponents `e j` can
be written as `∑ i : Fin p, c i ^ p * t ^ i`. -/
theorem exists_fin_repr_of_sum (p : ℕ) [hp : Fact p.Prime] [CharP R p] (t : R)
    {ι : Type*} (s : Finset ι) (a : ι → R) (e : ι → ℕ) :
    ∃ c : Fin p → R, ∑ j ∈ s, a j ^ p * t ^ e j = ∑ i : Fin p, c i ^ p * t ^ (i : ℕ) := by
  classical
  have hppos : 0 < p := hp.out.pos
  have hexp : ExpChar R p := .prime hp.out
  set g : ι → Fin p := fun j => ⟨e j % p, Nat.mod_lt _ hppos⟩ with hg
  refine ⟨fun i => ∑ j ∈ s with g j = i, a j * t ^ (e j / p), ?_⟩
  rw [← Finset.sum_fiberwise s g (fun j => a j ^ p * t ^ e j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_pow_char p, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : e j % p = (i : ℕ) := by
    simpa [hg, Fin.ext_iff] using (Finset.mem_filter.mp hj).2
  have hdm : p * (e j / p) + e j % p = e j := Nat.div_add_mod (e j) p
  have hj' : e j / p * p + (i : ℕ) = e j := by rw [Nat.mul_comm]; lia
  rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, hj']

/-- If `R` is `p`-spanned by `t`, then `S` is `p`-spanned by `e t` for a ring isomorphism
`e : R ≃+* S`. -/
theorem IsPSpannedBy.map_ringEquiv {S : Type*} [CommRing S] {p : ℕ} {t : R}
    (h : IsPSpannedBy p t) (e : R ≃+* S) : IsPSpannedBy p (e t) := by
  intro y
  obtain ⟨c, hc⟩ := h (e.symm y)
  exact ⟨fun i => e (c i), by simpa using congrArg e hc⟩

/-- If a domain `A` is `p`-spanned by `t`, then its fraction field `K` is `p`-spanned by the image
of `t`. -/
theorem IsPSpannedBy.algebraMap_fractionRing {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] {p : ℕ} (hp : p ≠ 0) {t : A} (h : IsPSpannedBy p t) :
    IsPSpannedBy p (algebraMap A K t) := by
  intro z
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := A) z
  have hy0 : algebraMap A K y ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne (mem_nonZeroDivisors_iff_ne_zero.mp hy)
  have hYp : algebraMap A K y ^ p ≠ 0 := pow_ne_zero _ hy0
  obtain ⟨c, hc⟩ := h (x * y ^ (p - 1))
  have hpow : algebraMap A K y ^ (p - 1) * algebraMap A K y = algebraMap A K y ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp)]
  have hxe : algebraMap A K (x * y ^ (p - 1)) = z * algebraMap A K y ^ p := by
    rw [← hxy, map_mul, map_pow, div_mul_eq_mul_div, eq_div_iff hy0, mul_assoc, hpow]
  have hsum := congrArg (algebraMap A K) hc
  rw [hxe, map_sum] at hsum
  refine ⟨fun i => algebraMap A K (c i) / algebraMap A K y, ?_⟩
  have key : (∑ i : Fin p, (algebraMap A K (c i) / algebraMap A K y) ^ p
        * (algebraMap A K t) ^ (i : ℕ)) * algebraMap A K y ^ p
      = ∑ i : Fin p, algebraMap A K (c i ^ p * t ^ (i : ℕ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, div_pow]
    field_simp
  exact (mul_right_cancel₀ hYp (key.trans hsum.symm)).symm

/-- If `K` is `p`-spanned by `t`, `ρ ^ p ^ n = t` in an extension `F` of `K`, and every element of
`F` is a polynomial in `ρ` over `K`, then `F` is `p`-spanned by `ρ`. -/
theorem IsPSpannedBy.of_adjoin_root {K F : Type*} [Field K] [Field F] [Algebra K F]
    (p : ℕ) [hp : Fact p.Prime] [CharP K p] {t : K} (ht : IsPSpannedBy p t)
    {n : ℕ} {ρ : F} (hρ : ρ ^ p ^ n = algebraMap K F t)
    (hgen : ∀ x : F, ∃ g : K[X], x = aeval ρ g) :
    IsPSpannedBy p ρ := by
  classical
  have hCF : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  choose c hc using ht
  have hA : ∀ a : K, algebraMap K F a
      = ∑ i : Fin p, (algebraMap K F (c a i)) ^ p * ρ ^ ((i : ℕ) * p ^ n) := by
    intro a
    have hcast := congrArg (algebraMap K F) (hc a)
    rw [map_sum] at hcast
    rw [hcast]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, ← hρ, ← pow_mul, Nat.mul_comm]
  intro x
  obtain ⟨g, hg⟩ := hgen x
  have hxsum : x = ∑ j ∈ (Finset.range (g.natDegree + 1) ×ˢ (Finset.univ : Finset (Fin p))),
      (algebraMap K F (c (g.coeff j.1) j.2)) ^ p * ρ ^ ((j.2 : ℕ) * p ^ n + j.1) := by
    rw [hg, Polynomial.aeval_eq_sum_range, Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, hA (g.coeff k), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← pow_add]
  obtain ⟨d, hd⟩ := exists_fin_repr_of_sum p (R := F) ρ
    (Finset.range (g.natDegree + 1) ×ˢ (Finset.univ : Finset (Fin p)))
    (fun j => algebraMap K F (c (g.coeff j.1) j.2)) (fun j => (j.2 : ℕ) * p ^ n + j.1)
  exact ⟨d, hxsum.trans hd⟩

/-- If `F` is `p`-spanned by `t` and `t` has no `p`-th root in the algebraic extension `M`, then
`M / F` is separable. -/
theorem Algebra.IsSeparable.of_isPSpannedBy {F M : Type*} [Field F] [Field M] [Algebra F M]
    [Algebra.IsIntegral F M] (p : ℕ) [hp : Fact p.Prime] [CharP F p] {t : F}
    (ht : IsPSpannedBy p t) (hroot : ∀ y : M, y ^ p ≠ algebraMap F M t) :
    Algebra.IsSeparable F M := by
  classical
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hCM : CharP M p := charP_of_injective_algebraMap (algebraMap F M).injective p
  have hexpM : ExpChar M p := .prime hp.out
  have hexpFX : ExpChar F[X] p := .prime hp.out
  set Mf : Subfield M := (frobenius M p).fieldRange with hMfdef
  have htMf : algebraMap F M t ∉ Mf := by
    rintro ⟨y, hy⟩
    exact hroot y (by rw [← frobenius_def p y]; exact hy)
  have hli : LinearIndependent Mf (fun i : Fin p => (algebraMap F M t) ^ (i : ℕ)) :=
    linearIndependent_pow_of_pow_mem_of_notMem p Mf
      ⟨algebraMap F M t, frobenius_def p (algebraMap F M t)⟩ htMf
  have hzero : ∀ b : Fin p → M,
      (∑ i : Fin p, b i ^ p * (algebraMap F M t) ^ (i : ℕ)) = 0 → ∀ i, b i = 0 := by
    intro b hb i
    have hmem : ∀ i : Fin p, b i ^ p ∈ Mf := fun i => ⟨b i, frobenius_def p (b i)⟩
    have hcoe : (∑ i : Fin p, (⟨b i ^ p, hmem i⟩ : Mf) • (algebraMap F M t) ^ (i : ℕ)) = 0 := by
      rw [← hb]
      exact Finset.sum_congr rfl fun i _ => rfl
    have := (Fintype.linearIndependent_iff.mp hli) (fun i => ⟨b i ^ p, hmem i⟩) hcoe i
    have hbp : b i ^ p = 0 := by
      simpa using congrArg (fun z : Mf => (z : M)) this
    exact pow_eq_zero_iff hp0 |>.mp hbp
  rw [Algebra.isSeparable_def]
  intro y
  have hyint : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  by_contra hns
  have hirr : Irreducible (minpoly F y) := minpoly.irreducible hyint
  have hder : derivative (minpoly F y) = 0 := by
    by_contra h
    exact hns ((separable_iff_derivative_ne_zero hirr).mpr h)
  set f := minpoly F y with hf
  have hfne : f ≠ 0 := minpoly.ne_zero hyint
  have hsupp : ∀ k ∈ f.support, p ∣ k := by
    intro k hk
    by_contra hdvd
    refine (Polynomial.mem_support_iff.mp hk) ?_
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact absurd (dvd_zero p) hdvd
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
    have hcd := Polynomial.coeff_derivative f j
    rw [hder, Polynomial.coeff_zero] at hcd
    have hcast : ((j + 1 : ℕ) : F) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff F p]
      exact hdvd
    have hne : ((j : F) + 1) ≠ 0 := by push_cast at hcast; exact hcast
    exact (mul_eq_zero.mp hcd.symm).resolve_right hne
  choose c hc using ht
  set h : Fin p → F[X] := fun i => ∑ k ∈ f.support, C (c (f.coeff k) i) * X ^ (k / p) with hh
  have hfid : f = ∑ i : Fin p, C (t ^ (i : ℕ)) * h i ^ p := by
    have hterm : ∀ i : Fin p, C (t ^ (i : ℕ)) * h i ^ p
        = ∑ k ∈ f.support, C (c (f.coeff k) i ^ p * t ^ (i : ℕ)) * X ^ k := by
      intro i
      rw [hh, sum_pow_char p, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hpk : k / p * p = k := by
        obtain ⟨m, rfl⟩ := hsupp k hk
        rw [Nat.mul_div_cancel_left _ hp.out.pos, Nat.mul_comm]
      rw [mul_pow, ← C_pow, ← pow_mul, hpk, map_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_comm]
    conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow f]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, ← map_sum, ← hc (f.coeff k)]
  have haev : (∑ i : Fin p, (aeval y (h i)) ^ p * (algebraMap F M t) ^ (i : ℕ)) = 0 := by
    have hev := congrArg (aeval y) hfid
    rw [minpoly.aeval F y, map_sum] at hev
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hev.symm
    simp only [map_mul, map_pow, Polynomial.aeval_C]
    ring
  have hzeroh : ∀ i : Fin p, (aeval y (h i)) = 0 := hzero _ haev
  have hdeg : ∀ i : Fin p, (h i).natDegree ≤ f.natDegree / p := by
    intro i
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
    exact Nat.div_le_div_right (Polynomial.le_natDegree_of_mem_supp k hk)
  have hlt : f.natDegree / p < f.natDegree :=
    Nat.div_lt_self (minpoly.natDegree_pos hyint) hp.out.one_lt
  have hh0 : ∀ i : Fin p, h i = 0 := by
    intro i
    by_contra hne
    have hle := minpoly.degree_le_of_ne_zero F y hne (hzeroh i)
    rw [← hf] at hle
    have hnat := Polynomial.natDegree_le_natDegree hle
    have hdi := hdeg i
    lia
  refine hfne ?_
  rw [hfid]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hh0 i, zero_pow hp0, mul_zero]

/-- If `y ^ p ^ j = t` and `t` is not a `p`-th power in `K`, then
`minpoly K y = X ^ p ^ j - C t`. -/
theorem minpoly_eq_X_pow_sub_C_of_pow_eq {K M : Type*} [Field K] [Field M] [Algebra K M]
    (p : ℕ) [hp : Fact p.Prime] [CharP K p] {t : K} (hnp : ∀ a : K, a ^ p ≠ t)
    {j : ℕ} {y : M} (hy : y ^ p ^ j = algebraMap K M t) :
    minpoly K y = X ^ p ^ j - C t := by
  have hexpK : ExpChar K p := .prime hp.out
  have hinj : Function.Injective (algebraMap K M) := (algebraMap K M).injective
  have hcand : (aeval y) (X ^ p ^ j - C t : K[X]) = 0 := by
    simp [hy]
  have hcandmonic : (X ^ p ^ j - C t : K[X]).Monic :=
    Polynomial.monic_X_pow_sub_C t (pow_ne_zero j hp.out.ne_zero)
  have hcandne : (X ^ p ^ j - C t : K[X]) ≠ 0 := hcandmonic.ne_zero
  have hmem : y ^ p ^ j ∈ (algebraMap K M).range := ⟨t, hy.symm⟩
  have hsep1 : (minpoly K y).natSepDegree = 1 :=
    (minpoly.natSepDegree_eq_one_iff_pow_mem p).mpr ⟨j, hmem⟩
  obtain ⟨m, z, hmz⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C p).mp hsep1
  have hyint : IsIntegral K y := ⟨_, hcandmonic, hcand⟩
  have hym : y ^ p ^ m = algebraMap K M z := by
    have := minpoly.aeval K y
    rw [hmz] at this
    simpa [sub_eq_zero] using this
  have hmj : m ≤ j := by
    have hle := minpoly.degree_le_of_ne_zero K y hcandne hcand
    rw [hmz] at hle
    have := Polynomial.natDegree_le_natDegree hle
    rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_X_pow_sub_C] at this
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp this
  have hjm : j ≤ m := by
    by_contra hcon
    have hlt : m < j := not_le.mp hcon
    obtain ⟨k, hk⟩ : ∃ k, j = m + (k + 1) := ⟨j - m - 1, by lia⟩
    have : algebraMap K M t = algebraMap K M (z ^ p ^ (k + 1)) := by
      rw [← hy, hk, pow_add, pow_mul, hym, map_pow]
    have htz : t = z ^ p ^ (k + 1) := hinj this
    exact hnp (z ^ p ^ k) (by rw [htz, pow_succ, pow_mul])
  have hmj' : m = j := le_antisymm hmj hjm
  subst hmj'
  have hzt : z = t := hinj (by rw [← hym, hy])
  rw [hmz, hzt]

/-- Let `K` be a field of characteristic `p` which is `p`-spanned by an element `t` that is not a
`p`-th power, and let `M / K` be finite. Then there are `n` and `ρ ∈ M` with

* `ρ ^ p ^ n = t`,
* `minpoly K ρ = X ^ p ^ n - C t`, and
* `M / K⟮ρ⟯` separable. -/
theorem exists_pow_eq_minpoly_eq_and_isSeparable_adjoin {K M : Type*} [Field K] [Field M]
    [Algebra K M] [Module.Finite K M] (p : ℕ) [hp : Fact p.Prime] [CharP K p] {t : K}
    (ht : IsPSpannedBy p t) (hnp : ∀ a : K, a ^ p ≠ t) :
    ∃ (n : ℕ) (ρ : M), ρ ^ p ^ n = algebraMap K M t ∧
      minpoly K ρ = X ^ p ^ n - C t ∧
      Algebra.IsSeparable (IntermediateField.adjoin K {ρ}) M := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  set P : ℕ → Prop := fun j => ∃ y : M, y ^ p ^ j = algebraMap K M t with hP
  have hP0 : P 0 := ⟨algebraMap K M t, by simp⟩
  have hbound : ∀ j, P j → j ≤ Module.finrank K M := by
    intro j ⟨y, hy⟩
    have hmin := minpoly_eq_X_pow_sub_C_of_pow_eq p hnp hy
    have hdeg : (minpoly K y).natDegree = p ^ j := by
      rw [hmin]; exact Polynomial.natDegree_X_pow_sub_C
    have hle : (minpoly K y).natDegree ≤ Module.finrank K M :=
      minpoly.natDegree_le y
    rw [hdeg] at hle
    exact le_trans (le_trans (Nat.lt_two_pow_self).le
      (Nat.pow_le_pow_left hp.out.two_le j)) hle
  set n := Nat.findGreatest P (Module.finrank K M) with hn
  have hPn : P n := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ m, P m → m ≤ n := by
    intro m hm
    by_contra hcon
    exact Nat.findGreatest_is_greatest (not_le.mp hcon) (hbound m hm) hm
  obtain ⟨ρ, hρ⟩ := hPn
  have hmin := minpoly_eq_X_pow_sub_C_of_pow_eq p hnp hρ
  have hnoroot : ∀ y : M, y ^ p ≠ ρ := by
    intro y hy
    have hPn1 : P (n + 1) := ⟨y, by rw [pow_succ', pow_mul, hy, hρ]⟩
    have := hmax _ hPn1
    lia
  refine ⟨n, ρ, hρ, hmin, ?_⟩
  have hρint : IsIntegral K ρ := Algebra.IsIntegral.isIntegral ρ
  set L := IntermediateField.adjoin K ({ρ} : Set M)
  have hgenmap : algebraMap L M (IntermediateField.AdjoinSimple.gen K ρ) = ρ :=
    IntermediateField.AdjoinSimple.algebraMap_gen K ρ
  have hCF : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hIntF : Algebra.IsIntegral L M := Algebra.IsIntegral.tower_top (R := K)
  have hgenpow : (IntermediateField.AdjoinSimple.gen K ρ) ^ p ^ n = algebraMap K L t := by
    refine (algebraMap L M).injective ?_
    rw [map_pow, hgenmap, hρ, ← IsScalarTower.algebraMap_apply K L M]
  have hgen : ∀ x : L, ∃ g : K[X], x = aeval (IntermediateField.AdjoinSimple.gen K ρ) g := by
    intro x
    have hsub : L.toSubalgebra = Algebra.adjoin K ({ρ} : Set M) :=
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hρint.isAlgebraic
    have hmemsub : (x : M) ∈ Algebra.adjoin K ({ρ} : Set M) := by
      rw [← hsub]; exact x.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmemsub
    obtain ⟨g, hgx⟩ := hmemsub
    refine ⟨g, (algebraMap L M).injective ?_⟩
    have hcomm := Polynomial.aeval_algebraMap_apply M (IntermediateField.AdjoinSimple.gen K ρ) g
    rw [hgenmap] at hcomm
    exact hgx.symm.trans hcomm
  exact Algebra.IsSeparable.of_isPSpannedBy p
    (IsPSpannedBy.of_adjoin_root p ht hgenpow hgen)
    fun y hy => hnoroot y (by rwa [hgenmap] at hy)
