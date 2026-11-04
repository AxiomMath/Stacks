module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Sequence.Powers
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
public import StacksFrontier.RingTheory.Smoothing.OgomaKernelStabilization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Parameters at a regular prime whose powers lie in a given ideal

Let `Λ` be a Noetherian ring, let `I ⊆ Λ` be an ideal, let `q ⊂ Λ` be a prime ideal, and let
`n`, `e` be positive integers. Assume `q ^ n Λ_q ⊆ I Λ_q` and that the localization `Λ_q` is a
regular local ring of dimension `d`. Then one can choose `π₁, …, π_d ∈ Λ` which

1. generate `q Λ_q`,
2. satisfy `π_i ^ n ∈ I`, and
3. have the property that, in `Λ ⧸ (π₁ ^ e, …, π_{i-1} ^ e)`, the annihilator of `π_i` agrees
   with the annihilator of `π_i ^ 2`.

The three assertions are the content of Stacks 07FD.

## Main results

* `Stacks.Smoothing.exists_parameters_pow_mem_and_annihilator_sq_eq`: the lemma above.

## Implementation notes

The tuple `π₁, …, π_d` is a function `Fin d → Λ`; assertion (1) is the equality of the
extensions of `Ideal.span (Set.range π)` and of `q` to `Λ_q` along the canonical algebra map,
and assertion (3) is spelled out elementwise, which is equivalent to equality of the two
annihilator ideals.

The argument is the source's. Generators of the maximal ideal of `Λ_q` are lifted to `Λ` and
rescaled by elements of `Λ \ q` so that their `n`-th powers land in `I`; rescaling does not
disturb (1). Assertion (3) is then installed one index at a time: a minimal generating set of
the maximal ideal of a regular local ring is a regular sequence
(`IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay`),
and raising its members to positive powers preserves this
(`RingTheory.Sequence.isRegular_zipWith_pow_iff`), so `π_i` is a nonzerodivisor on
`Λ_q ⧸ (π₁ ^ e, …, π_{i-1} ^ e) Λ_q`; Ogoma's lemma
(`ogoma_ker_eq_of_localization`) descends the resulting annihilator equality from this
localization to `Λ ⧸ (π₁ ^ e, …, π_{i-1} ^ e)` at the cost of one further rescaling of `π_i`.

The source also assumes `I ⊆ q`; it is not needed, so it is omitted.

## References

* [Stacks Project, Tag 07FD](https://stacks.math.columbia.edu/tag/07FD)
-/

@[expose] public section

namespace Stacks.Smoothing

/-- Rescaling an element by an element of `Λ \ q` does not change the ideal it generates in
`Λ_q`. -/
private lemma span_algebraMap_mul_eq
    {Λ : Type*} [CommRing Λ] (q : Ideal Λ) [q.IsPrime] (s : q.primeCompl) (a : Λ) :
    Ideal.span ({algebraMap Λ (Localization.AtPrime q) (s * a)} : Set _) =
      Ideal.span ({algebraMap Λ (Localization.AtPrime q) a} : Set _) := by
  rw [map_mul]
  exact Ideal.span_singleton_mul_left_unit (IsLocalization.map_units _ s) _

/-- Two families of elements whose members pairwise generate the same principal ideals span the
same ideal. -/
private lemma span_range_eq_of_span_singleton_eq
    {R ι : Type*} [CommRing R] {x y : ι → R}
    (h : ∀ i, Ideal.span ({x i} : Set R) = Ideal.span ({y i} : Set R)) :
    Ideal.span (Set.range x) = Ideal.span (Set.range y) := by
  rw [Ideal.span_range_eq_iSup, Ideal.span_range_eq_iSup]
  exact iSup_congr h

/-- An element of a prime `q` may be rescaled by an element of `Λ \ q`, without changing the
ideal it generates in `Λ_q`, so that its `n`-th power lies in `I`, provided
`q ^ n Λ_q ⊆ I Λ_q`. -/
private lemma exists_mul_pow_mem_of_map_pow_le
    {Λ : Type*} [CommRing Λ] (I q : Ideal Λ) [q.IsPrime] (n : ℕ) (hn : 0 < n)
    (h : Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n) ≤
      Ideal.map (algebraMap Λ (Localization.AtPrime q)) I)
    {a : Λ} (ha : a ∈ q) :
    ∃ b : Λ, b ^ n ∈ I ∧
      Ideal.span ({algebraMap Λ (Localization.AtPrime q) b} : Set _) =
        Ideal.span ({algebraMap Λ (Localization.AtPrime q) a} : Set _) := by
  obtain ⟨s, hs, hsa⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl
      (Localization.AtPrime q) I (a ^ n)).mp
        (h (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow ha n)))
  refine ⟨s * a, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simpa only [mul_pow, pow_succ, mul_assoc, mul_left_comm] using I.mul_mem_left (s ^ k) hsa
  · exact span_algebraMap_mul_eq q ⟨s, hs⟩ a

/-- Ogoma's lemma in the form used below: if `a` is a nonzerodivisor on
`Λ_q ⧸ J Λ_q`, then after rescaling `a` by a suitable element of `Λ \ q` the annihilators of
`a` and of `a ^ 2` in `Λ ⧸ J` coincide. -/
private lemma exists_mul_annihilator_sq_eq_of_isSMulRegular
    {Λ : Type*} [CommRing Λ] [IsNoetherianRing Λ] (q J : Ideal Λ) [q.IsPrime] (a : Λ)
    (h : IsSMulRegular (Localization.AtPrime q ⧸
        J.map (algebraMap Λ (Localization.AtPrime q)))
      (algebraMap Λ (Localization.AtPrime q) a)) :
    ∃ s ∈ q.primeCompl, ∀ x : Λ ⧸ J,
      x * Ideal.Quotient.mk J (s * a) = 0 ↔
        x * Ideal.Quotient.mk J ((s * a) ^ 2) = 0 := by
  set B := Localization.AtPrime q with hB
  set S := q.primeCompl with hS
  -- `B ⧸ J B` is the localization of `Λ ⧸ J` at `S`, in the guise of `Submodule.localized'`.
  have hJ : Submodule.localized' B S (Algebra.linearMap Λ B) J = J.map (algebraMap Λ B) :=
    Ideal.localized'_eq_map B S J
  have hquot : IsSMulRegular (B ⧸ Submodule.localized' B S (Algebra.linearMap Λ B) J) a :=
    (((Submodule.quotEquivOfEq _ _ hJ).restrictScalars Λ).isSMulRegular_congr a).mpr
      (h.of_map (algebraMap Λ B) fun m => IsScalarTower.algebraMap_smul B a m)
  have hL : IsSMulRegular (LocalizedModule S (Λ ⧸ J)) a :=
    ((IsLocalizedModule.linearEquiv S (J.toLocalizedQuotient' B S (Algebra.linearMap Λ B))
      (LocalizedModule.mkLinearMap S (Λ ⧸ J))).isSMulRegular_congr a).mp hquot
  have hker : LinearMap.ker (LinearMap.lsmul Λ (LocalizedModule S (Λ ⧸ J)) a) =
      LinearMap.ker (LinearMap.lsmul Λ (LocalizedModule S (Λ ⧸ J)) (a ^ 2)) := by
    rw [(isSMulRegular_iff_ker_lsmul_eq_bot _ _).mp hL,
      (isSMulRegular_iff_ker_lsmul_eq_bot _ _).mp (hL.pow 2)]
  obtain ⟨s, hs, H⟩ := ogoma_ker_eq_of_localization (M := Λ ⧸ J) S a hker
  refine ⟨s, hs, fun x => ?_⟩
  have hx := SetLike.ext_iff.mp (H 1 Nat.one_pos) x
  change (s ^ 1 * a) • x = 0 ↔ ((s ^ 1 * a) ^ 2) • x = 0 at hx
  simpa only [pow_one, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm] using hx

/-- Generators of the maximal ideal of a regular local localization `Λ_q` of dimension `d` can
be lifted to a `d`-tuple in `Λ` all of whose `n`-th powers lie in `I`, provided
`q ^ n Λ_q ⊆ I Λ_q`. -/
private lemma exists_fun_map_span_eq_maximalIdeal_and_pow_mem
    {Λ : Type*} [CommRing Λ] (I q : Ideal Λ) [q.IsPrime] (n d : ℕ) (hn : 0 < n)
    (hqI : Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n) ≤
      Ideal.map (algebraMap Λ (Localization.AtPrime q)) I)
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hd : ringKrullDim (Localization.AtPrime q) = d) :
    ∃ π : Fin d → Λ,
      Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (π i)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ∧
      ∀ i, π i ^ n ∈ I := by
  classical
  set B := Localization.AtPrime q with hB
  set f := algebraMap Λ B with hf
  set m := IsLocalRing.maximalIdeal B with hm
  obtain ⟨t, ht, htspan⟩ := (IsNoetherian.noetherian m).exists_span_finset_card_eq_spanFinrank
  have htd : t.card = d := ht.trans (by
    exact_mod_cast IsRegularLocalRing.spanFinrank_maximalIdeal.trans hd)
  set z : Fin d → B := fun i => (t.equivFin.symm (Fin.cast htd.symm i)).val with hz
  have hzrange : Set.range z = (t : Set B) := by
    ext y
    refine ⟨?_, fun hy => ⟨Fin.cast htd (t.equivFin ⟨y, hy⟩), by simp [hz]⟩⟩
    rintro ⟨i, rfl⟩
    exact (t.equivFin.symm (Fin.cast htd.symm i)).property
  have hzspan : Ideal.span (Set.range z) = m := by simpa [hzrange] using htspan
  have hzmem (i : Fin d) : z i ∈ q.map f := by
    rw [hf, Localization.AtPrime.map_eq_maximalIdeal, ← hm, ← hzspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have H (i : Fin d) : ∃ b : Λ, b ^ n ∈ I ∧
      Ideal.span ({f b} : Set B) = Ideal.span ({z i} : Set B) := by
    obtain ⟨⟨a, s⟩, has⟩ :=
      (IsLocalization.mem_map_algebraMap_iff q.primeCompl B).mp (hzmem i)
    obtain ⟨b, hb, hba⟩ := exists_mul_pow_mem_of_map_pow_le I q n hn hqI a.property
    refine ⟨b, hb, hba.trans ?_⟩
    rw [← has, mul_comm]
    exact Ideal.span_singleton_mul_left_unit (IsLocalization.map_units B s) _
  choose π hπ hspan using H
  refine ⟨π, ?_, hπ⟩
  rw [← hzspan]
  exact span_range_eq_of_span_singleton_eq hspan

/-- A minimal generating tuple of the maximal ideal of a regular local ring `B` of dimension
`d` has the property that `a i` is a nonzerodivisor on `B ⧸ (a 0 ^ e, …, a (i-1) ^ e)` for
every positive exponent `e`. -/
@[ega "IV 19.7.3" "partial"]
private lemma isSMulRegular_quotient_span_prev_pow
    {B : Type*} [CommRing B] [IsRegularLocalRing B] {d : ℕ} (a : Fin d → B)
    (hspan : Ideal.span (Set.range a) = IsLocalRing.maximalIdeal B)
    (hd : ringKrullDim B = d) (e : ℕ) (he : 0 < e) (i : Fin d) :
    IsSMulRegular (B ⧸ Ideal.span
      (Set.range fun j : Fin i.1 => a (j.castLE (Nat.le_of_lt i.2)) ^ e)) (a i) := by
  have hdim : (IsLocalRing.maximalIdeal B).spanFinrank = d := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := B)).trans hd
  have hreg : RingTheory.Sequence.IsRegular B (List.ofFn a) :=
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      B).1 _ ((Ideal.ofList_ofFn a).trans hspan) (by simpa using hdim.symm)).1
  have hzip : (List.ofFn a).zipWith (· ^ ·) (List.ofFn fun _ : Fin d => e) =
      List.ofFn fun j => a j ^ e := by
    apply List.ext_getElem <;> simp
  have hpow := (RingTheory.Sequence.isRegular_zipWith_pow_iff B
    (rs := List.ofFn a) (es := List.ofFn fun _ : Fin d => e) (by simp)
    (by intro k hk; simpa using (List.mem_ofFn.mp hk).choose_spec ▸ he)).mpr hreg
  rw [hzip] at hpow
  have hi := hpow.regular_mod_prev i.1 (by simp)
  rw [← Fin.ofFn_take_eq_take_ofFn (Nat.le_of_lt i.2) fun j => a j ^ e,
    Ideal.ofList_ofFn] at hi
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at hi
  simp only [List.getElem_ofFn] at hi
  exact (IsSMulRegular.pow_iff he).mp hi

/-- **Stacks 07FD.** Let `Λ` be a Noetherian ring, let `I` and `q` be ideals of `Λ` with `q`
prime, and let `n`, `e` be positive integers. Assume that the extension of `q ^ n` to `Λ_q` is
contained in the extension of `I`, and that `Λ_q` is a regular local ring of dimension `d`.
Then there are `π₁, …, π_d ∈ Λ` such that `(π₁, …, π_d) Λ_q = q Λ_q`, such that `π_i ^ n ∈ I`
for every `i`, and such that for every `i` the annihilator of `π_i` in
`Λ ⧸ (π₁ ^ e, …, π_{i-1} ^ e)` is the annihilator of `π_i ^ 2`. -/
@[stacks 07FD]
theorem exists_parameters_pow_mem_and_annihilator_sq_eq
    (Λ : Type*) [CommRing Λ] [IsNoetherianRing Λ] (I q : Ideal Λ) [q.IsPrime]
    (n e d : ℕ) (hn : 0 < n) (he : 0 < e)
    (hqI : Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n) ≤
      Ideal.map (algebraMap Λ (Localization.AtPrime q)) I)
    [IsRegularLocalRing (Localization.AtPrime q)]
    (hd : ringKrullDim (Localization.AtPrime q) = d) :
    ∃ π : Fin d → Λ,
      Ideal.map (algebraMap Λ (Localization.AtPrime q)) (Ideal.span (Set.range π)) =
          Ideal.map (algebraMap Λ (Localization.AtPrime q)) q ∧
      (∀ i : Fin d, π i ^ n ∈ I) ∧
      (∀ i : Fin d, ∀ x : Λ ⧸ Ideal.span
          (Set.range fun j : Fin i.1 => π (j.castLE (Nat.le_of_lt i.2)) ^ e),
        x * Ideal.Quotient.mk _ (π i) = 0 ↔ x * Ideal.Quotient.mk _ (π i ^ 2) = 0) := by
  classical
  set B := Localization.AtPrime q with hB
  set f := algebraMap Λ B with hf
  obtain ⟨π₀, hspan₀, hpow₀⟩ :=
    exists_fun_map_span_eq_maximalIdeal_and_pow_mem I q n d hn hqI hd
  -- Install the annihilator condition for the first `k` indices, by induction on `k`.
  have H : ∀ k ≤ d, ∃ π : Fin d → Λ,
      Ideal.span (Set.range fun i => f (π i)) = IsLocalRing.maximalIdeal B ∧
      (∀ i, π i ^ n ∈ I) ∧
      (∀ i : Fin d, i.1 < k → ∀ x : Λ ⧸ Ideal.span
        (Set.range fun j : Fin i.1 => π (j.castLE (Nat.le_of_lt i.2)) ^ e),
        x * Ideal.Quotient.mk _ (π i) = 0 ↔ x * Ideal.Quotient.mk _ (π i ^ 2) = 0) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨π₀, hspan₀, hpow₀, fun i hi => (Nat.not_lt_zero _ hi).elim⟩
    | succ k ih =>
      intro hk
      obtain ⟨π, hspan, hpow, hann⟩ := ih (by omega)
      set t : Fin d := ⟨k, by omega⟩ with htdef
      set J : Ideal Λ :=
        Ideal.span (Set.range fun j : Fin t.1 => π (j.castLE (Nat.le_of_lt t.2)) ^ e) with hJdef
      have hJ : J.map f = Ideal.span
          (Set.range fun j : Fin t.1 => f (π (j.castLE (Nat.le_of_lt t.2))) ^ e) := by
        simp only [hJdef, Ideal.map_span, ← Set.range_comp, Function.comp_def, map_pow]
      have hreg : IsSMulRegular (B ⧸ J.map f) (f (π t)) := by
        rw [hJ]
        exact isSMulRegular_quotient_span_prev_pow (fun i => f (π i)) hspan hd e he t
      obtain ⟨s, hs, hsa⟩ := exists_mul_annihilator_sq_eq_of_isSMulRegular q J (π t) hreg
      set π' := Function.update π t (s * π t) with hπ'
      have hpres (j : Fin d) (hj : j ≠ t) : π' j = π j := by simp [hπ', hj]
      have hne (i : Fin d) (hi : i.1 < k) : i ≠ t := fun hcon => by
        have h1 : (i : ℕ) = k := congrArg Fin.val hcon
        omega
      have hprefix (i : Fin d) (hi : i.1 ≤ k) :
          (fun j : Fin i.1 => π' (j.castLE (Nat.le_of_lt i.2)) ^ e) =
          (fun j : Fin i.1 => π (j.castLE (Nat.le_of_lt i.2)) ^ e) :=
        funext fun j => congrArg (· ^ e) (hpres _ (hne _ (j.2.trans_le hi)))
      refine ⟨π', ?_, ?_, ?_⟩
      · calc
          Ideal.span (Set.range fun i => f (π' i)) =
              Ideal.span (Set.range fun i => f (π i)) := by
            refine span_range_eq_of_span_singleton_eq fun j => ?_
            by_cases hj : j = t
            · subst j
              simpa only [hπ', Function.update_self] using span_algebraMap_mul_eq q ⟨s, hs⟩ (π t)
            · rw [hpres j hj]
          _ = IsLocalRing.maximalIdeal B := hspan
      · intro j
        by_cases hj : j = t
        · subst j
          simp only [hπ', Function.update_self, mul_pow]
          exact I.mul_mem_left _ (hpow t)
        · rw [hpres j hj]
          exact hpow j
      · intro i hi
        by_cases hik : i.1 < k
        · rw [hprefix i (by omega), hpres i (hne i hik)]
          exact hann i hik
        · have hit : i = t := Fin.ext (show i.1 = k by omega)
          subst i
          rw [hprefix t le_rfl]
          simpa only [hπ', Function.update_self] using hsa
  obtain ⟨π, hspan, hpow, hann⟩ := H d le_rfl
  refine ⟨π, ?_, hpow, fun i => hann i i.2⟩
  rw [Ideal.map_span, ← Set.range_comp, hf, Localization.AtPrime.map_eq_maximalIdeal]
  exact hspan

end Stacks.Smoothing

end
