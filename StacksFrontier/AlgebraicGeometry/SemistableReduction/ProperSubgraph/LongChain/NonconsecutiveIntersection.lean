module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveChain
public import Mathlib.Basic.Real.Basic

/-!
# Non-consecutive components of a long chain

For a chain of at least six minus-two indices with constant inner weight and
inner edge intersection `W` and prescribed endpoint scales, components of the
chain that are not consecutive do not meet.

## Main definitions

* `AlgebraicGeometry.NumericalType.ChainEndpointScale`.

## Main results

* `AlgebraicGeometry.NumericalType.no_nonconsecutive_intersection`.
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

abbrev ChainEndpointScale (T : NumericalType) (a b : Fin T.componentCount)
    (W : ℤ) : Prop :=
  (T.weight a = W ∧ T.intersection a b = W) ∨
    (T.weight a = 2 * W ∧ T.intersection a b = 2 * W) ∨
    (2 * T.weight a = W ∧ T.intersection a b = W)

/-- The weighted intersections of a minus-two component with a set of other components
are bounded by the diagonal term. -/
private lemma sum_intersections_le_diagonal (T : NumericalType)
    (i : Fin T.componentCount) (S : Finset (Fin T.componentCount)) (hiS : i ∉ S)
    (hdiag : T.intersection i i = -2 * T.weight i) :
    ∑ j ∈ S, T.intersection i j * T.multiplicity j ≤
      2 * T.weight i * T.multiplicity i := by
  classical
  let f : Fin T.componentCount → ℤ :=
    fun j => T.intersection i j * T.multiplicity j
  have hsubset : S ⊆ Finset.univ.erase i :=
    fun j hj => Finset.mem_erase.mpr ⟨fun h => hiS (h ▸ hj), Finset.mem_univ _⟩
  have hnonneg : ∀ j ∈ Finset.univ.erase i, j ∉ S → 0 ≤ f j := by
    intro j hj _
    exact mul_nonneg (T.intersection_nonneg i j (Finset.mem_erase.mp hj).1.symm)
      (le_of_lt (T.multiplicity_pos j))
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hbalance := T.intersection_mul_multiplicity i
  change (∑ j, f j) = 0 at hbalance
  rw [← Finset.add_sum_erase (s := Finset.univ) (f := f) (a := i) (by simp)] at hbalance
  let c : ℤ := 2 * T.weight i * T.multiplicity i
  have hbalance' : -c + (∑ j ∈ Finset.univ.erase i, f j) = 0 := by
    simpa [f, hdiag, c, mul_assoc] using hbalance
  have hsumErase : (∑ j ∈ Finset.univ.erase i, f j) = c := by omega
  rw [hsumErase] at hsum
  exact hsum

private lemma two_intersections_le_diagonal (T : NumericalType)
    (i a b : Fin T.componentCount) (hia : i ≠ a) (hib : i ≠ b) (hab : a ≠ b)
    (hdiag : T.intersection i i = -2 * T.weight i) :
    T.intersection i a * T.multiplicity a +
      T.intersection i b * T.multiplicity b ≤
        2 * T.weight i * T.multiplicity i := by
  classical
  simpa [Finset.sum_pair hab] using
    sum_intersections_le_diagonal T i {a, b} (by simp [hia, hib]) hdiag

private lemma three_intersections_le_diagonal (T : NumericalType)
    (i a b c : Fin T.componentCount) (hia : i ≠ a) (hib : i ≠ b)
    (hic : i ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdiag : T.intersection i i = -2 * T.weight i) :
    T.intersection i a * T.multiplicity a +
      T.intersection i b * T.multiplicity b +
      T.intersection i c * T.multiplicity c ≤
        2 * T.weight i * T.multiplicity i := by
  classical
  simpa [hab, hac, hbc, add_assoc] using
    sum_intersections_le_diagonal T i {a, b, c} (by simp [hia, hib, hic]) hdiag

private lemma endpoint_scale_lower_bounds (T : NumericalType)
    (a b : Fin T.componentCount) (W : ℤ) (hW : 0 < W)
    (hscale : ChainEndpointScale T a b W) :
    T.weight a ≤ T.intersection a b ∧ W ≤ T.intersection a b := by
  rcases hscale with ⟨hw, he⟩ | ⟨hw, he⟩ | ⟨hw, he⟩
  · constructor <;> simp [hw, he]
  · constructor
    · simp [hw, he]
    · rw [he]
      omega
  · constructor
    · rw [he]
      omega
    · exact le_of_eq he.symm

private lemma chain_adjacent_edge_lower_bounds {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 3 ≤ t) (W : ℤ) (hW : 0 < W)
    (hweights : ∀ j, 0 < j.val → j.val + 1 < t → T.weight (i j) = W)
    (hedges : ∀ j k, k.val = j.val + 1 → 0 < j.val → k.val + 1 < t →
      T.intersection (i j) (i k) = W)
    (hleft : ChainEndpointScale T (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) W)
    (hright : ChainEndpointScale T (i ⟨t - 1, by omega⟩)
      (i ⟨t - 2, by omega⟩) W)
    (j k : Fin t) (hstep : k.val = j.val + 1) :
    W ≤ T.intersection (i j) (i k) ∧
      T.weight (i j) ≤ T.intersection (i j) (i k) ∧
      T.weight (i k) ≤ T.intersection (i j) (i k) := by
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hj0)
    have hk : k = ⟨1, by omega⟩ := by
      apply Fin.ext
      simp only [hj0] at hstep
      omega
    have hscale : ChainEndpointScale T (i j) (i k) W := by
      simpa [hj, hk] using hleft
    obtain ⟨hsource, hWle⟩ := endpoint_scale_lower_bounds T (i j) (i k) W hW hscale
    have htarget : T.weight (i k) = W := by
      have hkpos : 0 < k.val := by rw [hk]; omega
      have hkr : k.val + 1 < t := by rw [hk]; omega
      exact hweights k hkpos hkr
    exact ⟨hWle, hsource, htarget.trans_le hWle⟩
  · by_cases hlast : k.val + 1 = t
    · have hjval : j.val = t - 2 := by omega
      have hkval : k.val = t - 1 := by omega
      have hj : j = ⟨t - 2, by omega⟩ := Fin.ext (by simp only [hjval])
      have hk : k = ⟨t - 1, by omega⟩ := Fin.ext (by simp only [hkval])
      have hscale : ChainEndpointScale T (i k) (i j) W := by
        simpa [hj, hk] using hright
      obtain ⟨hsource, hWle⟩ := endpoint_scale_lower_bounds T (i k) (i j) W hW hscale
      have hsymm : T.intersection (i k) (i j) = T.intersection (i j) (i k) :=
        (T.intersection_symm _ _).symm
      have htarget : T.weight (i j) = W := by
        rw [hj]
        exact hweights ⟨t - 2, by omega⟩ (by omega) (by omega)
      exact ⟨hWle.trans_eq hsymm, htarget.trans_le (hWle.trans_eq hsymm),
        hsource.trans_eq hsymm⟩
    · have hjpos : 0 < j.val := by omega
      have hjr : j.val + 1 < t := by omega
      have hkr : k.val + 1 < t := by omega
      rw [hedges j k hstep hjpos hkr, hweights j hjpos hjr, hweights k (by omega) hkr]
      exact ⟨le_rfl, le_rfl, le_rfl⟩

private lemma multiplicity_add_le_of_weight_le (T : NumericalType)
    (i a b : Fin T.componentCount) (hia : i ≠ a) (hib : i ≠ b) (hab : a ≠ b)
    (hdiag : T.intersection i i = -2 * T.weight i)
    (hwa : T.weight i ≤ T.intersection i a)
    (hwb : T.weight i ≤ T.intersection i b) :
    T.multiplicity a + T.multiplicity b ≤ 2 * T.multiplicity i := by
  have hrow := two_intersections_le_diagonal T i a b hia hib hab hdiag
  have hma := mul_le_mul_of_nonneg_right hwa
    (le_of_lt (T.multiplicity_pos a))
  have hmb := mul_le_mul_of_nonneg_right hwb
    (le_of_lt (T.multiplicity_pos b))
  have hsum : T.weight i * T.multiplicity a +
      T.weight i * T.multiplicity b ≤
        2 * T.weight i * T.multiplicity i := by omega
  have hmul : T.weight i * (T.multiplicity a + T.multiplicity b) ≤
      T.weight i * (2 * T.multiplicity i) := by
    calc
      _ = T.weight i * T.multiplicity a + T.weight i * T.multiplicity b := by
        rw [mul_add]
      _ ≤ 2 * T.weight i * T.multiplicity i := hsum
      _ = T.weight i * (2 * T.multiplicity i) := by ac_rfl
  exact le_of_mul_le_mul_left hmul (T.weight_pos i)

private lemma multiplicity_row_strict_of_cross (T : NumericalType)
    (i a b c : Fin T.componentCount) (hia : i ≠ a) (hib : i ≠ b)
    (hic : i ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hdiag : T.intersection i i = -2 * T.weight i)
    (hwa : T.weight i ≤ T.intersection i a)
    (hwb : T.weight i ≤ T.intersection i b)
    (hc : 0 < T.intersection i c) :
    T.multiplicity a + T.multiplicity b < 2 * T.multiplicity i := by
  have hthree := three_intersections_le_diagonal T i a b c hia hib hic hab hac hbc hdiag
  have hma := mul_le_mul_of_nonneg_right hwa
    (le_of_lt (T.multiplicity_pos a))
  have hmb := mul_le_mul_of_nonneg_right hwb
    (le_of_lt (T.multiplicity_pos b))
  have hmc : 0 < T.intersection i c * T.multiplicity c :=
    mul_pos hc (T.multiplicity_pos c)
  have hsum : T.weight i * T.multiplicity a +
      T.weight i * T.multiplicity b <
        2 * T.weight i * T.multiplicity i := by
    have hlow : T.weight i * T.multiplicity a +
        T.weight i * T.multiplicity b +
        T.intersection i c * T.multiplicity c ≤
          2 * T.weight i * T.multiplicity i := by
      calc
        _ ≤ T.intersection i a * T.multiplicity a +
            T.intersection i b * T.multiplicity b +
            T.intersection i c * T.multiplicity c := by omega
        _ ≤ 2 * T.weight i * T.multiplicity i := hthree
    omega
  have hmul : T.weight i * (T.multiplicity a + T.multiplicity b) <
      T.weight i * (2 * T.multiplicity i) := by
    calc
      _ = T.weight i * T.multiplicity a + T.weight i * T.multiplicity b := by
        rw [mul_add]
      _ < 2 * T.weight i * T.multiplicity i := hsum
      _ = T.weight i * (2 * T.multiplicity i) := by ac_rfl
  exact lt_of_mul_lt_mul_left hmul (le_of_lt (T.weight_pos i))

private lemma weight_le_positive_intersection (T : NumericalType)
    (i j : Fin T.componentCount) (hij : 0 < T.intersection i j) :
    T.weight i ≤ T.intersection i j :=
  Int.le_of_dvd hij (T.weight_dvd_intersection i j)

private lemma concave_path_forbids_strict_row {d : ℕ} (hd : 2 ≤ d)
    (m : ℕ → ℤ)
    (hleft : m 1 + m d ≤ 2 * m 0)
    (hright : m (d - 1) + m 0 ≤ 2 * m d)
    (hconcave : ∀ r, 0 < r → r < d → m (r - 1) + m (r + 1) ≤ 2 * m r) :
    ¬ (m 1 + m d < 2 * m 0) ∧
    ¬ (m (d - 1) + m 0 < 2 * m d) ∧
    (∀ r, 0 < r → r < d →
      ¬ (m (r - 1) + m (r + 1) < 2 * m r)) := by
  let slope : ℕ → ℤ := fun r => m (r + 1) - m r
  have hstep : ∀ r, r + 1 < d → slope (r + 1) ≤ slope r := by
    intro r hr
    have h := hconcave (r + 1) (by omega) hr
    have hrsub : r + 1 - 1 = r := by omega
    rw [hrsub] at h
    dsimp [slope]
    omega
  have hmono : ∀ a b, a ≤ b → b < d → slope b ≤ slope a := by
    intro a b hab hb
    induction b generalizing a with
    | zero =>
        obtain rfl : a = 0 := by omega
        exact le_rfl
    | succ b ih =>
        by_cases hae : a = b + 1
        · subst a
          exact le_rfl
        · exact (hstep b hb).trans (ih a (by omega) (by omega))
  have hdsub : d - 1 + 1 = d := by omega
  have hleftSlope : slope 0 ≤ m 0 - m d := by
    change m 1 - m 0 ≤ m 0 - m d
    omega
  have hrightSlope : m 0 - m d ≤ slope (d - 1) := by
    change m 0 - m d ≤ m (d - 1 + 1) - m (d - 1)
    rw [hdsub]
    omega
  have hlastSlope : slope (d - 1) ≤ slope 0 := hmono 0 (d - 1) (by omega) (by omega)
  have heqSlope : slope 0 = slope (d - 1) := by omega
  refine ⟨fun hstrict => ?_, fun hstrict => ?_, fun r hrpos hrd hstrict => ?_⟩
  · have hstrictSlope : slope 0 < m 0 - m d := by
      dsimp [slope]
      omega
    omega
  · have hstrictSlope : m 0 - m d < slope (d - 1) := by
      dsimp [slope]
      rw [hdsub]
      omega
    omega
  · have hrsub : r - 1 + 1 = r := by omega
    have hdrop : slope r < slope (r - 1) := by
      dsimp [slope]
      rw [hrsub]
      omega
    have hfirst : slope (r - 1) ≤ slope 0 := hmono 0 (r - 1) (by omega) (by omega)
    have hlast : slope (d - 1) ≤ slope r := hmono r (d - 1) (by omega) (by omega)
    omega

lemma no_nonconsecutive_intersection {t : ℕ} (T : NumericalType)
    (i : Fin t → Fin T.componentCount) (ht : 6 ≤ t)
    (hproper : t < T.componentCount) (hinj : Function.Injective i)
    (hminusTwo : ∀ j, IsMinusTwoIndex T (i j))
    (W : ℤ) (hW : 0 < W)
    (hweights : ∀ j, 0 < j.val → j.val + 1 < t → T.weight (i j) = W)
    (hedges : ∀ j k, k.val = j.val + 1 → 0 < j.val → k.val + 1 < t →
      T.intersection (i j) (i k) = W)
    (hleft : ChainEndpointScale T (i ⟨0, by omega⟩) (i ⟨1, by omega⟩) W)
    (hright : ChainEndpointScale T (i ⟨t - 1, by omega⟩)
      (i ⟨t - 2, by omega⟩) W) :
    ∀ j k, j.val + 1 < k.val → T.intersection (i j) (i k) = 0 := by
  classical
  intro j k hgap
  by_contra hzero
  have hne : i j ≠ i k := by
    intro h
    apply hinj at h
    have := congrArg Fin.val h
    omega
  have hpos : 0 < T.intersection (i j) (i k) := by
    have hnonneg := T.intersection_nonneg (i j) (i k) hne
    omega
  let d : ℕ := k.val - j.val
  have hjle : j.val ≤ k.val := by omega
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hkd : j.val + d = k.val := by dsimp [d]; omega
  let ix : ℕ → Fin t := fun r => ⟨j.val + min r d, by
    have hle : j.val + min r d ≤ k.val := by
      rw [← hkd]
      exact Nat.add_le_add_left (Nat.min_le_right r d) j.val
    exact Nat.lt_of_le_of_lt hle k.isLt⟩
  let m : ℕ → ℤ := fun r => T.multiplicity (i (ix r))
  have hix0 : ix 0 = j := by
    apply Fin.ext
    simp [ix]
  have hixd : ix d = k := by
    apply Fin.ext
    simp [ix, hkd]
  have hnotSurj : ¬ Function.Surjective i := by
    intro hsurj
    have hcard : T.componentCount ≤ t := by
      simpa using Fintype.card_le_of_surjective i hsurj
    omega
  obtain ⟨z, hz⟩ : ∃ z : Fin T.componentCount, z ∉ Set.range i :=
    not_forall.mp hnotSurj
  let v : Fin (d + 1) → Fin T.componentCount := fun r =>
    i ⟨j.val + r.val, by have := r.isLt; omega⟩
  let I : Set (Fin T.componentCount) := Set.range v
  have hIne : I.Nonempty := ⟨v 0, ⟨0, rfl⟩⟩
  have hIproper : I ≠ Set.univ := by
    intro hEq
    have hzI : z ∈ I := by rw [hEq]; simp
    rcases hzI with ⟨r, hr⟩
    apply hz
    refine ⟨⟨j.val + r.val, by have := r.isLt; omega⟩, ?_⟩
    simpa [v] using hr
  have hcross : ∃ a ∈ I, ∃ b ∉ I, T.intersection a b ≠ 0 := by
    by_contra hnone
    apply T.connected
    refine ⟨I, hIne, hIproper, ?_⟩
    intro a ha b hb
    by_contra hab
    exact hnone ⟨a, ha, b, hb, hab⟩
  obtain ⟨a, haI, b, hbI, hab⟩ := hcross
  have habne : a ≠ b := by
    intro he
    subst b
    exact hbI haI
  have habpos : 0 < T.intersection a b := by
    have hnonneg := T.intersection_nonneg a b habne
    omega
  have ht3 : 3 ≤ t := by omega
  obtain ⟨r, hr⟩ := haI
  have hra : i (ix r.val) = a := by
    simpa [v, ix, Nat.min_eq_left (show r.val ≤ d by have := r.isLt; omega)] using hr
  have hmem (q : ℕ) (hq : q ≤ d) : i (ix q) ∈ I := by
    refine ⟨⟨q, by omega⟩, ?_⟩
    simp [v, ix, Nat.min_eq_left hq]
  have hidxNe : ∀ p q, p ≤ d → q ≤ d → p ≠ q → i (ix p) ≠ i (ix q) := by
    intro p q hp hq hpq he
    have hfin := hinj he
    have hval := congrArg Fin.val hfin
    simp [ix, Nat.min_eq_left hp, Nat.min_eq_left hq] at hval
    omega
  have hixv : ∀ q, q ≤ d → (ix q).val = j.val + q := fun q hq => by
    simp [ix, Nat.min_eq_left hq]
  have hbNotPath (q : ℕ) (hq : q ≤ d) : b ≠ i (ix q) := by
    rintro rfl
    exact hbI (hmem q hq)
  have hwt : ∀ p q, p ≤ d ∧ q ≤ d ∧
      (q = p + 1 ∨ p = q + 1 ∨ (p = 0 ∧ q = d) ∨ (p = d ∧ q = 0)) →
      T.weight (i (ix p)) ≤ T.intersection (i (ix p)) (i (ix q)) := by
    rintro p q ⟨hp, hq, h | h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact (chain_adjacent_edge_lower_bounds T i ht3 W hW hweights hedges hleft hright
        (ix p) (ix q) (by rw [hixv p hp, hixv q hq]; omega)).2.1
    · exact (chain_adjacent_edge_lower_bounds T i ht3 W hW hweights hedges hleft hright
        (ix q) (ix p) (by rw [hixv p hp, hixv q hq]; omega)).2.2.trans_eq
          (T.intersection_symm _ _)
    · rw [hix0, hixd]
      exact weight_le_positive_intersection T _ _ hpos
    · rw [hix0, hixd]
      exact weight_le_positive_intersection T _ _ (by rwa [T.intersection_symm])
  have hrow : ∀ p q s, p ≤ d ∧ q ≤ d ∧ s ≤ d ∧ p ≠ q ∧ p ≠ s ∧ q ≠ s →
      T.weight (i (ix p)) ≤ T.intersection (i (ix p)) (i (ix q)) →
      T.weight (i (ix p)) ≤ T.intersection (i (ix p)) (i (ix s)) →
      m q + m s ≤ 2 * m p := by
    rintro p q s ⟨hp, hq, hs, hpq, hps, hqs⟩ h1 h2
    exact multiplicity_add_le_of_weight_le T _ _ _ (hidxNe p q hp hq hpq)
      (hidxNe p s hp hs hps) (hidxNe q s hq hs hqs) (hminusTwo (ix p)).2 h1 h2
  have hstrict : ∀ p q s, p ≤ d ∧ q ≤ d ∧ s ≤ d ∧ p ≠ q ∧ p ≠ s ∧ q ≠ s →
      T.weight (i (ix p)) ≤ T.intersection (i (ix p)) (i (ix q)) →
      T.weight (i (ix p)) ≤ T.intersection (i (ix p)) (i (ix s)) →
      0 < T.intersection (i (ix p)) b → m q + m s < 2 * m p := by
    rintro p q s ⟨hp, hq, hs, hpq, hps, hqs⟩ h1 h2 h3
    exact multiplicity_row_strict_of_cross T _ _ _ b (hidxNe p q hp hq hpq)
      (hidxNe p s hp hs hps) (hbNotPath p hp).symm (hidxNe q s hq hs hqs)
      (hbNotPath q hq).symm (hbNotPath s hs).symm (hminusTwo (ix p)).2 h1 h2 h3
  have hconcave : ∀ r, 0 < r → r < d → m (r - 1) + m (r + 1) ≤ 2 * m r := fun r hrpos hrd =>
    hrow r (r - 1) (r + 1) (by omega) (hwt r (r - 1) (by omega)) (hwt r (r + 1) (by omega))
  obtain ⟨hleftTight, hrightTight, hinnerTight⟩ := concave_path_forbids_strict_row hd m
    (hrow 0 1 d (by omega) (hwt 0 1 (by omega)) (hwt 0 d (by omega)))
    (hrow d (d - 1) 0 (by omega) (hwt d (d - 1) (by omega)) (hwt d 0 (by omega)))
    hconcave
  have hcrossPos : 0 < T.intersection (i (ix r.val)) b := by
    rw [hra]
    exact habpos
  have hrd : r.val ≤ d := by have := r.isLt; omega
  rcases (by omega : r.val = 0 ∨ r.val = d ∨ (0 < r.val ∧ r.val < d)) with h0 | h0 | ⟨h0, h1⟩
  · rw [h0] at hcrossPos
    exact hleftTight (hstrict 0 1 d (by omega) (hwt 0 1 (by omega)) (hwt 0 d (by omega))
      hcrossPos)
  · rw [h0] at hcrossPos
    exact hrightTight (hstrict d (d - 1) 0 (by omega) (hwt d (d - 1) (by omega))
      (hwt d 0 (by omega)) hcrossPos)
  · exact hinnerTight r.val h0 h1 (hstrict r.val (r.val - 1) (r.val + 1) (by omega)
      (hwt _ _ (by omega)) (hwt _ _ (by omega)) hcrossPos)

end AlgebraicGeometry.NumericalType
