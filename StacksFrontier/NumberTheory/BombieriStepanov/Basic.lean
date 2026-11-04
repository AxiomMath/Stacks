module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.Int.Interval
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Places of a function field and the Riemann–Roch spaces at one place

This file sets up the language of the elementary proof of the Riemann hypothesis for a curve over
a finite field, the one of Stepanov and Bombieri. The curve enters through its function field `K`
over the field of constants `k`. A family of places `P : Pl` carries additive valuations
`v P : AddValuation K (WithTop ℤ)` and degrees `deg P`. Two geometric facts are used. First, the
degree of a principal divisor is zero: `∑_P deg P · ord_P f = 0` for `f ≠ 0`, the sum being finite.
Second, a place `P` of degree one has residue field `k`. In valuation terms: if `ord_P f = ord_P g`
then `ord_P (f - c g) > ord_P f` for some `c ∈ k`.

For a place `P₀` and `m ∈ ℕ` the Riemann–Roch space `L(m P₀)` is the set of `f ∈ K` with a pole of
order at most `m` at `P₀` and no other pole.

## Main definitions

* `Stacks.BombieriStepanov.ordZ`: the order `ord_P f ∈ ℤ` of a nonzero `f`, read off the valuation.
* `Stacks.BombieriStepanov.IsResidueRational`: a place whose residue field is `k`, expressed
  through the valuation.
* `Stacks.BombieriStepanov.poleSpace`: the Riemann–Roch space `L(m P₀)`.

## Main results

* `Stacks.BombieriStepanov.sum_ordZ_le_zero`: if `f ≠ 0` has no pole outside a finite set `U` of
  places, then `∑_{P ∈ U} deg P · ord_P f ≤ 0`. In words, the zeros of `f` are counted by its
  poles.
* `Stacks.BombieriStepanov.finite_and_natCard_le_of_ordZ_mem`: a subset of `K` closed under
  `f - c g`, whose nonzero elements take only the orders in a finite set `s` at a residue-rational
  place, is finite with at most `q ^ #s` elements.
* `Stacks.BombieriStepanov.finite_and_natCard_poleSpace_le`: `L(m P₀)` is finite with at most
  `q ^ (m + 1)` elements.
-/

@[expose] public noncomputable section

namespace Stacks.BombieriStepanov

open Finset

variable {k K Pl : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Orders -/

/-- The order `ord_P f ∈ ℤ` of `f` at a valuation, `0` at `f = 0`. -/
def ordZ (w : AddValuation K (WithTop ℤ)) (f : K) : ℤ := (w f).untopD 0

/-- For `f ≠ 0`, the integer `ordZ w f` coerces to the valuation `w f`. -/
theorem coe_ordZ {w : AddValuation K (WithTop ℤ)} {f : K} (hf : f ≠ 0) :
    ((ordZ w f : ℤ) : WithTop ℤ) = w f := by
  have h : w f ≠ ⊤ := (AddValuation.ne_top_iff w).2 hf
  unfold ordZ
  generalize w f = x at h ⊢
  induction x with
  | top => exact absurd rfl h
  | coe z => rfl

/-- The order of a product of nonzero elements is the sum of their orders. -/
theorem ordZ_mul {w : AddValuation K (WithTop ℤ)} {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordZ w (f * g) = ordZ w f + ordZ w g := by
  have h := AddValuation.map_mul w f g
  rw [← coe_ordZ hf, ← coe_ordZ hg, ← coe_ordZ (mul_ne_zero hf hg)] at h
  exact_mod_cast h

/-- The order of `f ^ n` is `n` times the order of `f`, for `f ≠ 0`. -/
theorem ordZ_pow {w : AddValuation K (WithTop ℤ)} {f : K} (hf : f ≠ 0) (n : ℕ) :
    ordZ w (f ^ n) = n * ordZ w f := by
  have h := AddValuation.map_pow w f n
  rw [← coe_ordZ hf, ← coe_ordZ (pow_ne_zero n hf)] at h
  rw [show ((n : ℤ) * ordZ w f) = n • ordZ w f by simp]
  exact_mod_cast h

/-- For `f ≠ 0`, `z ≤ ordZ w f` if and only if `z ≤ w f` in `WithTop ℤ`. -/
theorem le_ordZ_iff {w : AddValuation K (WithTop ℤ)} {f : K} (hf : f ≠ 0) (z : ℤ) :
    z ≤ ordZ w f ↔ (z : WithTop ℤ) ≤ w f := by
  rw [← coe_ordZ hf]
  exact WithTop.coe_le_coe.symm

/-- For `f ≠ 0`, `z < ordZ w f` if and only if `z < w f` in `WithTop ℤ`. -/
theorem lt_ordZ_iff {w : AddValuation K (WithTop ℤ)} {f : K} (hf : f ≠ 0) (z : ℤ) :
    z < ordZ w f ↔ (z : WithTop ℤ) < w f := by
  rw [← coe_ordZ hf]
  exact WithTop.coe_lt_coe.symm

/-- A nonzero constant has valuation zero at every valuation, the constants being a finite field:
`c ^ (q - 1) = 1`. -/
theorem val_algebraMap [Fintype k] (w : AddValuation K (WithTop ℤ)) {c : k} (hc : c ≠ 0) :
    w (algebraMap k K c) = 0 := by
  have hc' : algebraMap k K c ≠ 0 := by simpa using hc
  have h1 : (algebraMap k K c) ^ (Fintype.card k - 1) = 1 := by
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one c hc, map_one]
  have h := AddValuation.map_pow w (algebraMap k K c) (Fintype.card k - 1)
  rw [h1, AddValuation.map_one, ← coe_ordZ hc', ← WithTop.coe_nsmul] at h
  have h' : (Fintype.card k - 1) • ordZ w (algebraMap k K c) = 0 :=
    (WithTop.coe_injective h).symm
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hz : ordZ w (algebraMap k K c) = 0 := (smul_eq_zero.1 h').resolve_left (by omega)
  rw [← coe_ordZ hc', hz]
  rfl

/-- Multiplying by a constant does not decrease the valuation: `w g ≤ w (c g)`. -/
theorem le_val_algebraMap_mul [Fintype k] (w : AddValuation K (WithTop ℤ)) (c : k) (g : K) :
    w g ≤ w (algebraMap k K c * g) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [AddValuation.map_mul, val_algebraMap w hc, zero_add]

/-! ### The degree of a principal divisor -/

section Degree

variable (v : Pl → AddValuation K (WithTop ℤ)) (deg : Pl → ℕ)

/-- The degree formula for principal divisors: every nonzero `f` has finitely many zeros and
poles, and `∑_P deg P · ord_P f = 0`. -/
structure HasDegreeFormula : Prop where
  finite_support : ∀ f : K, f ≠ 0 → (Function.support fun P => ordZ (v P) f).Finite
  sum_eq_zero : ∀ f : K, f ≠ 0 → ∑ᶠ P, (deg P : ℤ) * ordZ (v P) f = 0

variable {v deg}

/-- **Zeros are bounded by poles.** If `f ≠ 0` has no pole outside the finite set `U` of places,
then `∑_{P ∈ U} deg P · ord_P f ≤ 0`. -/
theorem sum_ordZ_le_zero (hD : HasDegreeFormula v deg) {f : K} (hf : f ≠ 0) (U : Finset Pl)
    (hU : ∀ P, P ∉ U → 0 ≤ ordZ (v P) f) :
    ∑ P ∈ U, (deg P : ℤ) * ordZ (v P) f ≤ 0 := by
  classical
  set T := U ∪ (hD.finite_support f hf).toFinset with hT
  have hsupp : (Function.support fun P => (deg P : ℤ) * ordZ (v P) f) ⊆ (T : Set Pl) := by
    intro P hP
    have : ordZ (v P) f ≠ 0 := fun h => hP (by simp [h])
    simp [hT, this]
  have h0 := hD.sum_eq_zero f hf
  rw [finsum_eq_sum_of_support_subset _ hsupp] at h0
  have hsplit := Finset.sum_sdiff (f := fun P => (deg P : ℤ) * ordZ (v P) f)
    (Finset.subset_union_left : U ⊆ T)
  have hrest : 0 ≤ ∑ P ∈ T \ U, (deg P : ℤ) * ordZ (v P) f :=
    Finset.sum_nonneg fun P hP => mul_nonneg (Nat.cast_nonneg _) (hU P (Finset.mem_sdiff.1 hP).2)
  linarith

end Degree

/-! ### Residue-rational places and counting -/

/-- A valuation whose residue field is the field of constants `k`: two elements of the same order
differ, after scaling one of them by a constant, by an element of larger order. -/
def IsResidueRational (w : AddValuation K (WithTop ℤ)) : Prop :=
  ∀ f g : K, f ≠ 0 → g ≠ 0 → w f = w g → ∃ c : k, w f < w (f - algebraMap k K c * g)

/-- If `a ∈ s` and `a < b`, fewer elements of `s` lie above `b` than above `a`. -/
theorem card_filter_le_lt_of_lt {s : Finset ℤ} {a b : ℤ} (ha : a ∈ s) (hab : a < b) :
    (s.filter fun y => b ≤ y).card < (s.filter fun y => a ≤ y).card := by
  have hmem : a ∈ s.filter fun y => a ≤ y := Finset.mem_filter.2 ⟨ha, le_rfl⟩
  have hsub : (s.filter fun y => b ≤ y) ⊆ (s.filter fun y => a ≤ y).erase a := by
    intro y hy
    rw [Finset.mem_filter] at hy
    exact Finset.mem_erase.2 ⟨by omega, Finset.mem_filter.2 ⟨hy.1, by omega⟩⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at this
  have := Finset.card_pos.2 ⟨a, hmem⟩
  omega

/-- A sum `∑ j, c_j g_j` with `c = Pi.single i c₀` is `c₀ g_i`. -/
theorem sum_algebraMap_single_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → K) (i : ι)
    (c : k) : ∑ j, algebraMap k K ((Pi.single i c : ι → k) j) * g j = algebraMap k K c * g i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- A set `W ∋ 0` contains an element `g` that has order `z` if nonzero, and is nonzero as soon as
some nonzero element of `W` has order `z`. -/
theorem exists_mem_ordZ_witness (w : AddValuation K (WithTop ℤ)) {W : Set K} (hW0 : (0 : K) ∈ W)
    (z : ℤ) : ∃ g ∈ W, (g ≠ 0 → ordZ w g = z) ∧ ∀ f ∈ W, f ≠ 0 → ordZ w f = z → g ≠ 0 := by
  by_cases h : ∃ f ∈ W, f ≠ 0 ∧ ordZ w f = z
  · obtain ⟨f, hfW, hf0, hfz⟩ := h
    exact ⟨f, hfW, fun _ => hfz, fun _ _ _ _ => hf0⟩
  · exact ⟨0, hW0, fun h0 => absurd rfl h0, fun f hfW hf0 hfz => absurd ⟨f, hfW, hf0, hfz⟩ h⟩

/-- **Counting by orders.** Let `W ⊆ K` be closed under `f, g ↦ f - c g` for constants `c`, and let
the orders at a residue-rational valuation of its nonzero elements lie in the finite set `s`. Then
`W` is finite with at most `q ^ #s` elements. -/
theorem finite_and_natCard_le_of_ordZ_mem [Fintype k] {w : AddValuation K (WithTop ℤ)}
    (hw : IsResidueRational (k := k) w) (W : Set K) (hW0 : (0 : K) ∈ W)
    (hWsub : ∀ f ∈ W, ∀ g ∈ W, ∀ c : k, f - algebraMap k K c * g ∈ W) (s : Finset ℤ)
    (hs : ∀ f ∈ W, f ≠ 0 → ordZ w f ∈ s) :
    W.Finite ∧ Nat.card W ≤ Fintype.card k ^ s.card := by
  classical
  choose g hgW hgord hgne using fun z : s => exists_mem_ordZ_witness w hW0 (z : ℤ)
  let F : (s → k) → K := fun c => ∑ z, algebraMap k K (c z) * g z
  have hFadd : ∀ c d, F (c + d) = F c + F d := by
    intro c d
    simp only [F, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have key : ∀ N : ℕ, ∀ f ∈ W, (f ≠ 0 → (s.filter fun z => ordZ w f ≤ z).card ≤ N) →
      f ∈ Set.range F := by
    intro N
    induction N with
    | zero =>
      intro f hfW hN
      by_cases hf0 : f = 0
      · exact ⟨0, by simp [F, hf0]⟩
      · have hpos : 0 < (s.filter fun z => ordZ w f ≤ z).card :=
          Finset.card_pos.2 ⟨_, Finset.mem_filter.2 ⟨hs f hfW hf0, le_rfl⟩⟩
        have := hN hf0
        omega
    | succ N ih =>
      intro f hfW hN
      by_cases hf0 : f = 0
      · exact ⟨0, by simp [F, hf0]⟩
      set z : s := ⟨ordZ w f, hs f hfW hf0⟩
      have hg0 : g z ≠ 0 := hgne z f hfW hf0 rfl
      have hgz : ordZ w (g z) = ordZ w f := hgord z hg0
      have hval : w f = w (g z) := by rw [← coe_ordZ hf0, ← coe_ordZ hg0, hgz]
      obtain ⟨c, hc⟩ := hw f (g z) hf0 hg0 hval
      set f' := f - algebraMap k K c * g z with hf'
      have hf'W : f' ∈ W := hWsub f hfW (g z) (hgW z) c
      have hcount : f' ≠ 0 → (s.filter fun y => ordZ w f' ≤ y).card ≤ N := by
        intro hf'0
        have := card_filter_le_lt_of_lt (hs f hfW hf0)
          ((lt_ordZ_iff hf'0 _).2 (by rwa [coe_ordZ hf0]))
        have := hN hf0
        omega
      obtain ⟨c', hc'⟩ := ih f' hf'W hcount
      refine ⟨c' + Pi.single z c, ?_⟩
      rw [hFadd, hc']
      have : F (Pi.single z c) = algebraMap k K c * g z := sum_algebraMap_single_mul g z c
      rw [this, hf']
      ring
  have hsubset : W ⊆ Set.range F := fun f hfW =>
    key s.card f hfW fun _ => (Finset.card_filter_le _ _)
  have hfinR : (Set.range F).Finite := Set.finite_range F
  refine ⟨hfinR.subset hsubset, ?_⟩
  have : Finite (Set.range F) := hfinR.to_subtype
  calc Nat.card W ≤ Nat.card (Set.range F) := Nat.card_mono hfinR hsubset
    _ ≤ Nat.card (s → k) := Finite.card_range_le F
    _ = Fintype.card k ^ s.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]

/-! ### The Riemann–Roch space `L(m P₀)` -/

section PoleSpace

variable (v : Pl → AddValuation K (WithTop ℤ))

/-- The Riemann–Roch space `L(m P₀)`: the `f ∈ K` with a pole of order at most `m` at `P₀` and no
pole elsewhere. -/
def poleSpace (P₀ : Pl) (m : ℕ) : Set K :=
  {f | ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ v P₀ f ∧ ∀ P, P ≠ P₀ → 0 ≤ v P f}

variable {v}

/-- The space `L(m P₀)` contains `0`. -/
theorem zero_mem_poleSpace (P₀ : Pl) (m : ℕ) : (0 : K) ∈ poleSpace v P₀ m := by
  simp [poleSpace]

/-- The space `L(m P₀)` is closed under `f, g ↦ f - c g` for constants `c`. -/
theorem sub_mem_poleSpace [Fintype k] {P₀ : Pl} {m : ℕ} {f g : K} (hf : f ∈ poleSpace v P₀ m)
    (hg : g ∈ poleSpace v P₀ m) (c : k) : f - algebraMap k K c * g ∈ poleSpace v P₀ m :=
  ⟨AddValuation.map_le_sub _ hf.1 (hg.1.trans (le_val_algebraMap_mul _ c g)),
    fun P hP => AddValuation.map_le_sub _ (hf.2 P hP)
      ((hg.2 P hP).trans (le_val_algebraMap_mul _ c g))⟩

/-- The spaces `L(m P₀)` increase with `m`. -/
theorem poleSpace_mono {P₀ : Pl} {m n : ℕ} (h : m ≤ n) : poleSpace v P₀ m ⊆ poleSpace v P₀ n := by
  intro f hf
  refine ⟨le_trans ?_ hf.1, hf.2⟩
  exact_mod_cast (by omega : -(n : ℤ) ≤ -(m : ℤ))

variable {deg : Pl → ℕ}

/-- The order at `P₀` of a nonzero element of `L(m P₀)` lies in `[-m, 0]`, when `P₀` has degree
one. -/
theorem ordZ_mem_Icc_of_mem_poleSpace (hD : HasDegreeFormula v deg) {P₀ : Pl} (hP₀ : deg P₀ = 1)
    {m : ℕ} {f : K} (hf : f ∈ poleSpace v P₀ m) (hf0 : f ≠ 0) :
    ordZ (v P₀) f ∈ Finset.Icc (-(m : ℤ)) 0 := by
  classical
  refine Finset.mem_Icc.2 ⟨(le_ordZ_iff hf0 _).2 hf.1, ?_⟩
  simpa [hP₀] using sum_ordZ_le_zero hD hf0 {P₀} fun P hP =>
    (le_ordZ_iff hf0 0).2 (hf.2 P (by simpa using hP))

/-- `L(m P₀)` is finite, with at most `q ^ (m + 1)` elements, when `P₀` is residue-rational of
degree one. -/
theorem finite_and_natCard_poleSpace_le [Fintype k] (hD : HasDegreeFormula v deg) {P₀ : Pl}
    (hP₀ : deg P₀ = 1) (hres : IsResidueRational (k := k) (v P₀)) (m : ℕ) :
    (poleSpace v P₀ m).Finite ∧ Nat.card (poleSpace v P₀ m) ≤ Fintype.card k ^ (m + 1) := by
  obtain ⟨hfin, hcard⟩ := finite_and_natCard_le_of_ordZ_mem hres (poleSpace v P₀ m)
    (zero_mem_poleSpace P₀ m) (fun f hf g hg c => sub_mem_poleSpace hf hg c)
    (Finset.Icc (-(m : ℤ)) 0) fun f hf hf0 => ordZ_mem_Icc_of_mem_poleSpace hD hP₀ hf hf0
  refine ⟨hfin, hcard.trans_eq ?_⟩
  congr 1
  simp only [Int.card_Icc]
  omega

end PoleSpace

end Stacks.BombieriStepanov

end
