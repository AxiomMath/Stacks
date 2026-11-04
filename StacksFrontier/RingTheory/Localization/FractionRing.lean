module

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksCore.Tactic.StacksAttribute

/-!
# Total rings of fractions

The total ring of fractions `Q(R)` of `R` agrees with that of `S⁻¹R` for every multiplicative
subset `S` of nonzerodivisors; in particular `Q(R) ≅ Q(Q(R))` (Stacks tag 02LW).

## The total ring of fractions of a ring with no embedded points

Let `R` be a commutative ring. Assume that

* `R` has finitely many minimal primes, enumerated without repetition as
  `q_1, ..., q_t`; and
* the union `q_1 ∪ ... ∪ q_t`, as a subset of `R`, is exactly the set of zerodivisors
  of `R`.

Then the total ring of fractions `Q(R)` is isomorphic, as an `R`-algebra (equivalently, as
a ring), to the finite product `Q(R) ≅ R_{q_1} × R_{q_2} × ... × R_{q_t}`, where each
factor `R_{q_i}` is the localization of `R` at the minimal prime `q_i`. This is Stacks tag
02LX.

## Conventions

An element `x ∈ R` is a *zerodivisor* if `x * y = 0` for some nonzero `y ∈ R`;
equivalently, `x` is a *nonzerodivisor*, or regular element, if multiplication by `x` is
injective, i.e. `x ∈ nonZeroDivisors R`. Under this convention `0` is a zerodivisor
whenever `R` is not the zero ring, and the set of zerodivisors is the complement
`{ x | x ∉ nonZeroDivisors R }` of the submonoid of nonzerodivisors.

A prime ideal `q ⊂ R` is a *minimal prime* if it is minimal for inclusion among the prime
ideals of `R`; these form the set `minimalPrimes R`. For such a `q`, the localization `R_q`
is `S⁻¹R` with `S = R \ q`, that is, `Localization.AtPrime q`.

With `S₀ = { f ∈ R | f is a nonzerodivisor }`, a multiplicative subset of `R`, the *total
ring of fractions* of `R` is the localization `Q(R) = S₀⁻¹R` (Stacks tag 02C5); here it is
`FractionRing R = Localization (nonZeroDivisors R)`.
-/

@[expose] public section

/-- The total ring of fractions of `R` is isomorphic (as a ring) to the total ring of fractions of
`S⁻¹R`, whenever `S` is a multiplicative subset of `R` consisting of nonzerodivisors. -/
@[stacks 02LW]
theorem fractionRing_equiv_fractionRing_localization
    (R : Type*) [CommRing R] (S : Submonoid R) (hS : S ≤ nonZeroDivisors R) :
    Nonempty (FractionRing R ≃+* FractionRing (Localization S)) := by
  let : Algebra (Localization S) (FractionRing R) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization S) (FractionRing R) S (nonZeroDivisors R) hS
  have : IsScalarTower R (Localization S) (FractionRing R) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization S) (FractionRing R) S (nonZeroDivisors R) hS
  have : IsFractionRing (Localization S) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization S (Localization S) (FractionRing R) hS
  exact ⟨(IsLocalization.algEquiv (nonZeroDivisors (Localization S))
    (FractionRing R) (FractionRing (Localization S))).toRingEquiv⟩

/-- The total ring of fractions of `R` is isomorphic to the total ring of fractions of its own
total ring of fractions: `Q(R) ≅ Q(Q(R))`. -/
@[stacks 02LW]
theorem fractionRing_equiv_fractionRing_fractionRing
    (R : Type*) [CommRing R] :
    Nonempty (FractionRing R ≃+* FractionRing (FractionRing R)) :=
  have : IsFractionRing R (FractionRing (FractionRing R)) :=
    IsFractionRing.trans R (FractionRing R) (FractionRing (FractionRing R))
  ⟨(IsLocalization.algEquiv (nonZeroDivisors R)
    (FractionRing R) (FractionRing (FractionRing R))).toRingEquiv⟩

/-- The set of zerodivisors of a commutative ring `R`: those elements that are
not nonzerodivisors. This is the complement of the submonoid `nonZeroDivisors R`. -/
def zeroDivisorsSet (R : Type*) [CommRing R] : Set R :=
  { x : R | x ∉ nonZeroDivisors R }

/-- Membership in `zeroDivisorsSet`: in a commutative ring, `x ∈ zeroDivisorsSet R` if and
only if there is a nonzero `y` with `x * y = 0`. -/
theorem mem_zeroDivisorsSet_iff {R : Type*} [CommRing R] (x : R) :
    x ∈ zeroDivisorsSet R ↔ ∃ y : R, y ≠ 0 ∧ x * y = 0 := by
  have h : x ∈ zeroDivisorsSet R ↔ ¬ (∀ z : R, z * x = 0 → z = 0) := by
    unfold zeroDivisorsSet
    rw [Set.mem_ofPred_eq, mem_nonZeroDivisors_iff_right]
  rw [h]
  push Not
  constructor
  · rintro ⟨y, hxy, hy⟩
    exact ⟨y, hy, by rw [mul_comm]; exact hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, by rw [mul_comm]; exact hxy, hy⟩

/-- For a finite family `q : ι → Ideal R` of minimal primes of a commutative ring `R` and an index
`i` whose prime differs from all the others, there is `g : R` with `g ∉ q i` such that for every
`k ≠ i` some `c ∉ q k` satisfies `c * g = 0`, i.e. `g` maps to `0` in
`Localization.AtPrime (q k)`. -/
private theorem exists_local_indicator
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (q : ι → Ideal R) [∀ i, (q i).IsPrime]
    (hmin : ∀ i, q i ∈ minimalPrimes R) (i : ι)
    (hne : ∀ k, k ≠ i → q k ≠ q i) :
    ∃ g : R, g ∉ q i ∧ ∀ k, k ≠ i → ∃ c, c ∉ q k ∧ c * g = 0 := by
  have : ∀ i, (q i).IsPrime := fun i => inferInstance
  cases nonempty_fintype ι
  classical
  have hincomp : ∀ a : ι, q a ≤ q i → a = i := by
    intro a hab
    by_contra h
    exact hne a h (((IsMinimalPrime.iff_minimal _).mp (hmin i)).eq_of_le inferInstance hab)
  have horth : ∃ f : R, f ∉ q i ∧ ∀ j, j ≠ i → f ∈ q j := by
    set s : Finset ι := Finset.univ.filter (· ≠ i) with hs
    have hnotle : ¬ (s.inf q ≤ q i) := by
      intro hle'
      have hprodle : (∏ j ∈ s, q j) ≤ q i := le_trans (Ideal.prod_le_inf) hle'
      obtain ⟨j, hjs, hji⟩ := (this i).prod_le.mp hprodle
      have hjne : j ≠ i := by
        simp only [hs, Finset.mem_filter] at hjs; exact hjs.right
      exact hjne (hincomp j hji)
    rw [SetLike.not_le_iff_exists] at hnotle
    obtain ⟨f, hfin, hfout⟩ := hnotle
    refine ⟨f, hfout, ?_⟩
    intro j hj
    have hjs : j ∈ s := by simp only [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ j, hj⟩
    exact (Finset.inf_le hjs : s.inf q ≤ q j) hfin
  obtain ⟨f, hfi, hfk⟩ := horth
  have hpow : ∀ k : ι, ∃ N : ℕ, ∃ c : R, k ≠ i → c ∉ q k ∧ c * f ^ N = 0 := by
    intro k
    by_cases hk : k = i
    · exact ⟨0, 1, fun h => absurd hk h⟩
    · have hfmem : f ∈ q k := hfk k hk
      have hnil : IsNilpotent ((algebraMap R (Localization.AtPrime (q k))) f) := by
        rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
        intro J hJ
        have hJprime : Ideal.IsPrime J := hJ
        have hcomap : (Ideal.under R J).IsPrime := Ideal.IsPrime.under R J
        have hle2 : Ideal.under R J ≤ q k := by
          rw [IsLocalization.isPrime_iff_isPrime_disjoint (q k).primeCompl
            (Localization.AtPrime (q k)) J] at hJprime
          intro x hx
          by_contra hxq
          have hxc : x ∈ (q k).primeCompl := hxq
          exact (Set.disjoint_left.mp hJprime.right hxc) hx
        have heq2 : Ideal.under R J = q k :=
          le_antisymm hle2 ((hmin k).right ⟨hcomap, bot_le⟩ hle2)
        have hfu : f ∈ Ideal.under R J := by rw [heq2]; exact hfmem
        rw [Ideal.mem_under] at hfu
        exact hfu
      obtain ⟨N, hN⟩ := hnil
      have hzero : (algebraMap R (Localization.AtPrime (q k))) (f ^ N) = 0 := by
        rw [map_pow]; exact hN
      rw [IsLocalization.map_eq_zero_iff (q k).primeCompl] at hzero
      obtain ⟨c, hc⟩ := hzero
      exact ⟨N, c.val, fun _ => ⟨c.property, hc⟩⟩
  choose N c hNc using hpow
  set M : ℕ := Finset.univ.sup N
  refine ⟨f ^ M, ?_, ?_⟩
  · intro hcontra
    exact hfi ((this i).mem_of_pow_mem M hcontra)
  · intro k hk
    obtain ⟨hcq, hcg⟩ := hNc k hk
    refine ⟨c k, hcq, ?_⟩
    have hNleM : N k ≤ M := Finset.le_sup (Finset.mem_univ k)
    have hsplit : f ^ M = f ^ N k * f ^ (M - N k) := by
      rw [← pow_add, Nat.add_sub_cancel' hNleM]
    rw [hsplit, ← mul_assoc, hcg, zero_mul]

/-- Let `R` be a commutative ring whose set of minimal primes is finite and enumerated without
repetition as `q_1, ..., q_t` (encoded by an injective family `q : Fin t → Ideal R` of minimal
primes; the zerodivisor hypothesis forces it to enumerate every minimal prime). Assume moreover
that the union of the minimal primes equals the set of zerodivisors of `R`. Then the total ring of
fractions `Q(R) = FractionRing R` is isomorphic, as an `R`-algebra, to the finite product of the
localizations `R_{q_i}`.

(An `R`-algebra isomorphism between these localizations is automatically the canonical map
induced by the universal property, since it must commute with the structure maps from `R`.) -/
@[stacks 02LX, ega "II 6.4.7" "partial"]
theorem total_fraction_ring_isoProd_localization_atPrime
    {R : Type*} [CommRing R] (t : ℕ) (q : Fin t → Ideal R)
    (hmin : ∀ i, q i ∈ minimalPrimes R)
    (hinj : Function.Injective q)
    (hzd : zeroDivisorsSet R = ⋃ i, (q i : Set R)) :
    haveI : ∀ i, (q i).IsPrime := fun i => (hmin i).isPrime
    Nonempty (FractionRing R ≃ₐ[R] (∀ i, Localization.AtPrime (q i))) := by
  have : ∀ i, (q i).IsPrime := fun i => (hmin i).isPrime
  have hle : ∀ i, nonZeroDivisors R ≤ (q i).primeCompl := by
    intro i x hx
    by_contra hxq
    have hxz : x ∈ zeroDivisorsSet R := by
      rw [hzd]; exact Set.mem_iUnion.2 ⟨i, not_not.1 hxq⟩
    exact hxz hx
  have hIsLoc : IsLocalization (nonZeroDivisors R) (∀ i, Localization.AtPrime (q i)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      rw [Pi.isUnit_iff]
      intro i
      rw [Pi.algebraMap_apply]
      exact IsLocalization.map_units (Localization.AtPrime (q i)) ⟨(y : R), hle i y.property⟩
    · intro z
      classical
      have hlocal : ∀ i : Fin t, ∃ a : R, ∃ s' : R, s' ∉ q i ∧
          z i * (algebraMap R (Localization.AtPrime (q i))) s'
            = (algebraMap R (Localization.AtPrime (q i))) a := by
        intro i
        obtain ⟨x, hx⟩ := IsLocalization.surj (q i).primeCompl (z i)
        exact ⟨x.fst, (x.snd : R), x.snd.property, hx⟩
      choose a s' hs'mem hs'eq using hlocal
      have hind : ∀ i : Fin t, ∃ g : R, g ∉ q i ∧ ∀ k, k ≠ i → ∃ c, c ∉ q k ∧ c * g = 0 :=
        fun i => exists_local_indicator q hmin i fun _ hk h => hk (hinj.eq_iff.mp h)
      choose g hgmem hgann using hind
      have hgmem_qk : ∀ i k : Fin t, i ≠ k → g i ∈ q k := by
        intro i k hik
        obtain ⟨c, hc, hcg⟩ := hgann i k (Ne.symm hik)
        rcases (this k).mem_or_mem (show c * g i ∈ q k by rw [hcg]; exact (q k).zero_mem) with h | h
        · exact absurd h hc
        · exact h
      have hg_map_zero : ∀ i k : Fin t, i ≠ k →
          (algebraMap R (Localization.AtPrime (q k))) (g i) = 0 := by
        intro i k hik
        obtain ⟨c, hc, hcg⟩ := hgann i k (Ne.symm hik)
        rw [IsLocalization.map_eq_zero_iff (q k).primeCompl]
        exact ⟨⟨c, hc⟩, by simpa [mul_comm] using hcg⟩
      refine ⟨⟨∑ i, g i * a i, ⟨∑ i, g i * s' i, ?_⟩⟩, ?_⟩
      · by_contra h
        have hmem : (∑ i, g i * s' i) ∈ zeroDivisorsSet R := by
          simp only [zeroDivisorsSet, Set.mem_ofPred_eq]; exact h
        rw [hzd, Set.mem_iUnion] at hmem
        obtain ⟨k, hk⟩ := hmem
        rw [SetLike.mem_coe] at hk
        have hrest : (∑ i ∈ Finset.univ \ {k}, g i * s' i) ∈ q k := by
          apply Ideal.sum_mem
          intro i hi
          have hik : i ≠ k := by
            simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi
            exact hi.right
          exact Ideal.mul_mem_right _ _ (hgmem_qk i k hik)
        have hsplit : (∑ i, g i * s' i)
            = g k * s' k + (∑ i ∈ Finset.univ \ {k}, g i * s' i) := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
          congr 1
          rw [Finset.erase_eq]
        have hgk : g k * s' k ∈ q k := by
          have : g k * s' k = (∑ i, g i * s' i) - (∑ i ∈ Finset.univ \ {k}, g i * s' i) := by
            rw [hsplit]; ring
          rw [this]
          exact (q k).sub_mem hk hrest
        rcases (this k).mem_or_mem hgk with hg | hs
        · exact (hgmem k) hg
        · exact (hs'mem k) hs
      · funext k
        rw [Pi.mul_apply, Pi.algebraMap_apply, Pi.algebraMap_apply]
        rw [map_sum, map_sum, Finset.mul_sum]
        rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
        · rw [map_mul, map_mul]
          rw [show z k * ((algebraMap R (Localization.AtPrime (q k))) (g k)
              * (algebraMap R (Localization.AtPrime (q k))) (s' k))
              = (algebraMap R (Localization.AtPrime (q k))) (g k)
                * (z k * (algebraMap R (Localization.AtPrime (q k))) (s' k)) by ring]
          rw [hs'eq k]
        all_goals first
          | (intro i _ hik; rw [map_mul, hg_map_zero i k hik]; ring)
          | simp
    · intro x y hxy
      have hcomp : ∀ i, ∃ c ∈ (q i).primeCompl, c * (x - y) = 0 := by
        intro i
        have hi : (algebraMap R (Localization.AtPrime (q i))) x
            = (algebraMap R (Localization.AtPrime (q i))) y := by simpa using congrFun hxy i
        rw [IsLocalization.eq_iff_exists (q i).primeCompl] at hi
        obtain ⟨c, hc⟩ := hi
        refine ⟨(c : R), c.property, ?_⟩
        have : (c : R) * x = (c : R) * y := hc
        rw [mul_sub, this, sub_self]
      let I : Ideal R :=
        { carrier := { r : R | r * (x - y) = 0 }
          add_mem' := by
            intro a b ha hb
            simp only [Set.mem_ofPred_eq] at *
            rw [add_mul, ha, hb, add_zero]
          zero_mem' := by simp
          smul_mem' := by
            intro a b hb
            simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
            rw [mul_assoc, hb, mul_zero] }
      have hI_not : ¬ ((I : Set R) ⊆ ⋃ i, (q i : Set R)) := by
        intro hsub
        have hsub' : (I : Set R) ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin t)), (q i : Set R) := by
          intro r hr
          have := hsub hr
          simp only [Set.mem_iUnion] at this ⊢
          obtain ⟨i, hi⟩ := this
          exact ⟨i, Finset.mem_univ i, hi⟩
        rcases t with _ | t'
        · have h0 : (0 : R) ∈ I := I.zero_mem
          have := hsub h0
          simp only [Set.mem_iUnion] at this
          obtain ⟨i, _⟩ := this
          exact i.elim0
        · obtain ⟨i, -, hIi⟩ :=
            (Ideal.subset_union_prime (s := (Finset.univ : Finset (Fin (t'+1))))
              (f := q) ⟨0, by simp⟩ ⟨0, by simp⟩
              (fun i _ _ _ => this i)).mp hsub'
          obtain ⟨c, hcq, hceq⟩ := hcomp i
          exact hcq (hIi hceq)
      rw [← hzd] at hI_not
      have hI_zd : ¬ ((I : Set R) ⊆ zeroDivisorsSet R) := hI_not
      rw [Set.not_subset] at hI_zd
      obtain ⟨w, hwI, hwz⟩ := hI_zd
      have hwnzd : w ∈ nonZeroDivisors R := by
        by_contra h
        exact hwz h
      refine ⟨⟨w, hwnzd⟩, ?_⟩
      have hw0 : w * (x - y) = 0 := hwI
      have h2 : w * x - w * y = 0 := by rw [← mul_sub]; exact hw0
      exact sub_eq_zero.mp h2
  exact ⟨IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R)
    (∀ i, Localization.AtPrime (q i))⟩
