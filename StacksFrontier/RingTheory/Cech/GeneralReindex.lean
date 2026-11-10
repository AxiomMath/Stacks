module

public import StacksFrontier.RingTheory.Cech.Reindex

/-!
# Comparing Čech complexes along an arbitrary map of index sets

Let `R` be a commutative ring, `M` an `R`-module, `f : Fin r → R` and `g : Fin s → R` two finite
families of elements of `R`, and `α : Fin s → Fin r` an arbitrary map of index sets such that
`f (α j)` divides a power of `g j` for every `j`.  Then `M_{∏ i ∈ α(V), f i}` is a localization of
`M` at elements that are already invertible in `M_{∏ j ∈ V, g j}` for every `V ⊆ Fin s`, so there
is a unique map between the two localizations extending the identity of `M`, and reading off the
components of `C^•(f; M)` indexed by the images `α(V)` gives a map of complexes

`C^•(f; M) ⟶ C^•(g; M)`.

Two things have to be dealt with that do not arise for the restriction map of
`StacksFrontier/RingTheory/Cech/Reindex.lean`, where `α` is an order embedding and the entries
agree.
First, `α` need not be monotone, so the `V`-component carries the sign of the permutation that
sorts the images; it is `Cech.invSign`, the parity of the number of inversions of `α` on `V`.
Second, `α` need not be injective, so `α(V)` may have fewer than `#V` elements and there is no
component of the source to read off; the `V`-component is then zero.  That this still commutes
with the differential is the content of the two sign identities
`Cech.cechSign_mul_invSign_erase` and `Cech.cechSign_mul_invSign_pair`: where `α` is injective on
the index set the two alternating sums match term by term through `k ↦ α k`, and where it is not,
the surviving summands cancel in pairs — a summand survives only if `α` is injective off that one
index, which happens for exactly the two members of a single coincidence of `α`, and those two
carry opposite signs.

## Main definitions

* `Cech.invCount`, `Cech.invSign`: the number of inversions of `α` on a finite set of indices, and
  the corresponding sign.
* `Cech.coincidenceMate`, `Cech.pairSwap`: the partner of an index in a coincidence of `α`, and
  the fixed-point-free involution it defines on the indices that contribute to the differential.
* `Cech.locLift`: the map `M_{∏ i ∈ U, f i} → M_{∏ j ∈ V, g j}` for `U ⊆ α(V)`.
* `Cech.genTerm`: the degreewise comparison map `C^p(f; M) → C^p(g; M)`.
* `Cech.cechGenMap`: **the comparison map of complexes** `C^•(f; M) ⟶ C^•(g; M)`.

## Main results

* `Cech.cechSign_mul_invSign_erase`, `Cech.cechSign_mul_invSign_pair`: the two sign identities.
* `Cech.invSign_comp`: the signs multiply along a composite of reindexings.
* `Cech.genTerm_comm`: the comparison maps commute with the Čech differentials.
* `Cech.cechGenMap_id`, `Cech.cechGenMap_comp`: the comparison is the identity for the identity
  reindexing of a family by itself, and composes.
* `Cech.genTerm_lof_zero`: in degree zero the comparison map is the identity of `M`, under the
  identification of both degree-zero terms with `M`.

## Implementation notes

The localization lift is `IsLocalizedModule.lift` for the submonoid `Submonoid.closure (f '' U)`,
at which `cechMod f M U` is a localization of `M` by `Cech.instClosureOfPowers`; the divisibility
hypothesis enters only through `Cech.isUnit_locTarget`, which says that each generator `f i`,
`i ∈ U`, acts invertibly on the target.  Uniqueness of such a lift proves every identity between
composites of these maps, as in `StacksFrontier/RingTheory/Cech/RingBaseChange.lean`.

Because the divisibility hypothesis is a proposition, two proofs of it are definitionally equal,
so the comparison map does not depend on the proof supplied: `Cech.genTerm_congr_proof` and
`Cech.cechGenMap_congr_proof` are `rfl`.  The index map, by contrast, appears in the type of the
hypothesis, so changing it is a dependent rewrite; `Cech.genTerm_congr` and
`Cech.cechGenMap_congr` do it in one step.

The source of a component of `Cech.locLift` is indexed by a `Finset`, which appears in the type of
the map, so an equality of index sets cannot be rewritten in place either;
`Cech.locLift_component_congr` transports a component along such an equality.  For the same reason
the sign is pulled out of the differential's sum by `Finset.smul_sum` with the integer action
coming from the additive group structure (`AddCommGroup.toIntModule`) given explicitly: that is
the action the sign is written with, and it is only definitionally the one instance search finds.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory
open ExtendedAlternatingCech (Idx)

namespace Cech

universe u v

/-! ### Parity bookkeeping -/

/-- Two powers of `-1` whose exponents have the same parity agree. -/
theorem neg_one_pow_eq_of_two_dvd_add {m n : ℕ} (h : 2 ∣ m + n) :
    ((-1 : ℤ)) ^ m = (-1) ^ n := by
  obtain ⟨c, hc⟩ := h
  rcases Nat.even_or_odd n with hn | hn
  · have hm : Even m := by
      obtain ⟨d, hd⟩ := hn
      exact ⟨c - d, by omega⟩
    rw [hm.neg_one_pow, hn.neg_one_pow]
  · have hm : Odd m := by
      obtain ⟨d, hd⟩ := hn
      exact ⟨c - d - 1, by omega⟩
    rw [hm.neg_one_pow, hn.neg_one_pow]

/-- Two powers of `-1` whose exponents have opposite parities cancel. -/
theorem neg_one_pow_add_eq_zero {m n : ℕ} (h : 2 ∣ m + n + 1) :
    ((-1 : ℤ)) ^ m + (-1) ^ n = 0 := by
  rw [neg_one_pow_eq_of_two_dvd_add (n := n + 1) (by rwa [← add_assoc]), pow_succ]
  ring

/-! ### Inversions of a map of index sets -/

variable {r s : ℕ}

/-- The number of inversions of `α` on a finite set `V` of indices: the number of pairs
`j₁ < j₂` in `V` whose images are in the opposite order. -/
def invCount (α : Fin s → Fin r) (V : Finset (Fin s)) : ℕ :=
  ((V ×ˢ V).filter (fun q => q.1 < q.2 ∧ α q.2 < α q.1)).card

/-- The sign of the reindexing: `+1` if `α` is monotone on `V`, and in general the sign of the
permutation sorting the images `α j`, `j ∈ V`, when `α` is injective on `V`. -/
def invSign (α : Fin s → Fin r) (V : Finset (Fin s)) : ℤ := (-1) ^ invCount α V

/-- The number of inversions as an iterated sum of indicators. -/
theorem invCount_eq_sum (α : Fin s → Fin r) (V : Finset (Fin s)) :
    invCount α V = ∑ i ∈ V, ∑ j ∈ V, if i < j ∧ α j < α i then 1 else 0 := by
  rw [invCount, Finset.card_filter, Finset.sum_product]

/-- There are no inversions on the empty set. -/
@[simp] theorem invCount_empty (α : Fin s → Fin r) : invCount α ∅ = 0 := by
  simp [invCount_eq_sum]

/-- The sign of a reindexing on the empty set is `1`. -/
@[simp] theorem invSign_empty (α : Fin s → Fin r) : invSign α ∅ = 1 := by
  simp [invSign]

/-- A sign is its own inverse. -/
theorem invSign_mul_self (α : Fin s → Fin r) (V : Finset (Fin s)) :
    invSign α V * invSign α V = 1 := by
  rw [invSign, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- A Čech sign is its own inverse. -/
theorem cechSign_mul_self (V : Finset (Fin r)) (i : Fin r) :
    cechSign V i * cechSign V i = 1 := by
  rw [cechSign, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- Adding one index to `V` adds the inversions that index forms with the others. -/
theorem invCount_insert (α : Fin s → Fin r) (E : Finset (Fin s)) {k : Fin s} (hk : k ∉ E) :
    invCount α (insert k E) = invCount α E +
      (E.filter (fun j => (j < k ∧ α k < α j) ∨ (k < j ∧ α j < α k))).card := by
  have hself : ¬ (k < k ∧ α k < α k) := fun h => lt_irrefl k h.1
  have hpt : ∀ j : Fin s,
      ((if k < j ∧ α j < α k then (1 : ℕ) else 0) + if j < k ∧ α k < α j then 1 else 0)
        = if (j < k ∧ α k < α j) ∨ (k < j ∧ α j < α k) then 1 else 0 := by
    intro j
    by_cases h1 : j < k ∧ α k < α j
    · have h2 : ¬ (k < j ∧ α j < α k) := fun h => lt_irrefl j (h1.1.trans h.1)
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left (Or.inl h1)]
    · by_cases h2 : k < j ∧ α j < α k
      · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left (Or.inr h2)]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (not_or.mpr ⟨h1, h2⟩)]
  have key : (∑ j ∈ E, if k < j ∧ α j < α k then (1 : ℕ) else 0)
      + (∑ i ∈ E, if i < k ∧ α k < α i then (1 : ℕ) else 0)
      = ∑ j ∈ E, if (j < k ∧ α k < α j) ∨ (k < j ∧ α j < α k) then (1 : ℕ) else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpt j
  rw [invCount_eq_sum, invCount_eq_sum, Finset.card_filter]
  simp only [Finset.sum_insert hk, ite_eq_right hself, Finset.sum_add_distrib, zero_add]
  omega

/-- Removing one index from `V` removes the inversions that index forms with the others. -/
theorem invCount_erase (α : Fin s → Fin r) (V : Finset (Fin s)) {k : Fin s} (hk : k ∈ V) :
    invCount α V = invCount α (V.erase k) +
      ((V.erase k).filter (fun j => (j < k ∧ α k < α j) ∨ (k < j ∧ α j < α k))).card := by
  conv_lhs => rw [← Finset.insert_erase hk]
  exact invCount_insert α (V.erase k) (Finset.notMem_erase k V)

/-! ### The two sign identities -/

/-- The contribution of one index `j ≠ k` to the three counts compared in
`Cech.cechSign_mul_invSign_erase` is even. -/
theorem invCount_elem_parity {α : Fin s → Fin r} {j k : Fin s} (hjk : j ≠ k)
    (hne : α j ≠ α k) :
    2 ∣ ((if j < k then 1 else 0)
      + (if (j < k ∧ α k < α j) ∨ (k < j ∧ α j < α k) then 1 else 0)
      + (if α j < α k then (1 : ℕ) else 0)) := by
  rcases (lt_or_gt_of_ne hjk) with hj | hj <;> rcases (lt_or_gt_of_ne hne) with ha | ha <;>
    simp [hj, ha, asymm hj, asymm ha]

/-- **The injective sign identity.** If `α` is injective on `V` and `k ∈ V`, then erasing `k`
from `V` and from its image changes the two signs in the same way. -/
theorem cechSign_mul_invSign_erase (α : Fin s → Fin r) {V : Finset (Fin s)} {k : Fin s}
    (hk : k ∈ V) (hinj : Set.InjOn α ↑V) :
    cechSign V k * invSign α (V.erase k) = invSign α V * cechSign (V.image α) (α k) := by
  have hA : (V.erase k).filter (· < k) = V.filter (· < k) := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp)]
  have hD : (V.image α).filter (· < α k) = ((V.erase k).filter (fun j => α j < α k)).image α := by
    rw [Finset.filter_image, Finset.filter_erase, Finset.erase_eq_of_notMem (by simp)]
  have hDcard : ((V.image α).filter (· < α k)).card
      = ((V.erase k).filter (fun j => α j < α k)).card := by
    rw [hD, Finset.card_image_of_injOn]
    exact hinj.mono (Finset.coe_subset.mpr
      ((Finset.filter_subset _ _).trans (Finset.erase_subset _ _)))
  have hdvd : 2 ∣ ((V.erase k).filter (· < k)).card
      + ((V.erase k).filter (fun j => (j < k ∧ α k < α j) ∨ (k < j ∧ α j < α k))).card
      + ((V.erase k).filter (fun j => α j < α k)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.dvd_sum fun j hj => ?_
    obtain ⟨hjk, hjV⟩ := Finset.mem_erase.mp hj
    exact invCount_elem_parity hjk fun he => hjk (hinj hjV hk he)
  rw [cechSign, cechSign, invSign, invSign, ← pow_add, ← pow_add]
  refine neg_one_pow_eq_of_two_dvd_add ?_
  rw [invCount_erase α V hk, hDcard, ← hA]
  omega

/-- The contribution of one index `j` outside a coincidence pair `{k₁, k₂}` to the four counts
compared in `Cech.cechSign_mul_invSign_pair` is even. -/
theorem invCount_pair_parity {α : Fin s → Fin r} {j k₁ k₂ : Fin s} (hlt : k₁ < k₂)
    (hj1 : j ≠ k₁) (hj2 : j ≠ k₂) (heq : α k₁ = α k₂) (hja : α j ≠ α k₁) :
    2 ∣ ((if j < k₁ then 1 else 0) + (if j < k₂ then 1 else 0)
      + (if (j < k₂ ∧ α k₂ < α j) ∨ (k₂ < j ∧ α j < α k₂) then 1 else 0)
      + (if (j < k₁ ∧ α k₁ < α j) ∨ (k₁ < j ∧ α j < α k₁) then (1 : ℕ) else 0)) := by
  rw [← heq]
  rcases (lt_or_gt_of_ne hj1) with h1 | h1
  · have h2 : j < k₂ := h1.trans hlt
    rcases (lt_or_gt_of_ne hja) with ha | ha <;>
      simp [h1, h2, ha, asymm h1, asymm h2, asymm ha]
  · rcases (lt_or_gt_of_ne hj2) with h2 | h2
    · rcases (lt_or_gt_of_ne hja) with ha | ha <;>
        simp [h1, h2, ha, asymm h1, asymm h2, asymm ha]
    · have h1' : k₁ < j := hlt.trans h2
      rcases (lt_or_gt_of_ne hja) with ha | ha <;>
        simp [h1', h2, ha, asymm h1', asymm h2, asymm ha]

/-- **The degenerate sign identity**, for an increasing coincidence pair. -/
theorem cechSign_mul_invSign_pair_of_lt (α : Fin s → Fin r) (V : Finset (Fin s)) {k₁ k₂ : Fin s}
    (h₁ : k₁ ∈ V) (h₂ : k₂ ∈ V) (hlt : k₁ < k₂) (heq : α k₁ = α k₂)
    (hother : ∀ j ∈ V, j ≠ k₁ → j ≠ k₂ → α j ≠ α k₁) :
    cechSign V k₁ * invSign α (V.erase k₁) + cechSign V k₂ * invSign α (V.erase k₂) = 0 := by
  have hk₂₁ : k₂ ∈ V.erase k₁ := Finset.mem_erase.mpr ⟨(ne_of_lt hlt).symm, h₂⟩
  have hk₁₂ : k₁ ∈ V.erase k₂ := Finset.mem_erase.mpr ⟨ne_of_lt hlt, h₁⟩
  have e1 := invCount_erase α (V.erase k₁) hk₂₁
  have e2 := invCount_erase α (V.erase k₂) hk₁₂
  rw [Finset.erase_right_comm (a := k₂) (b := k₁) (s := V)] at e2
  set U := (V.erase k₁).erase k₂ with hUdef
  have hA₁ : U.filter (· < k₁) = V.filter (· < k₁) := by
    rw [hUdef, Finset.filter_erase, Finset.filter_erase,
      Finset.erase_eq_of_notMem (by simp [asymm hlt]), Finset.erase_eq_of_notMem (by simp)]
  have hA₂ : (V.filter (· < k₂)).card = (U.filter (· < k₂)).card + 1 := by
    have h0 : U.filter (· < k₂) = (V.filter (· < k₂)).erase k₁ := by
      rw [hUdef, Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (by simp)]
    have hmem : k₁ ∈ V.filter (· < k₂) := Finset.mem_filter.mpr ⟨h₁, hlt⟩
    rw [h0, Finset.card_erase_of_mem hmem]
    have hpos : 0 < (V.filter (· < k₂)).card := Finset.card_pos.mpr ⟨k₁, hmem⟩
    omega
  have hdvd : 2 ∣ (U.filter (· < k₁)).card + (U.filter (· < k₂)).card
      + (U.filter (fun j => (j < k₂ ∧ α k₂ < α j) ∨ (k₂ < j ∧ α j < α k₂))).card
      + (U.filter (fun j => (j < k₁ ∧ α k₁ < α j) ∨ (k₁ < j ∧ α j < α k₁))).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.dvd_sum fun j hj => ?_
    rw [hUdef] at hj
    obtain ⟨hj2, hj'⟩ := Finset.mem_erase.mp hj
    obtain ⟨hj1, hjV⟩ := Finset.mem_erase.mp hj'
    exact invCount_pair_parity hlt hj1 hj2 heq (hother j hjV hj1 hj2)
  rw [cechSign, cechSign, invSign, invSign, ← pow_add, ← pow_add]
  refine neg_one_pow_add_eq_zero ?_
  rw [e1, e2, hA₂, ← hA₁]
  omega

/-- **The degenerate sign identity.** The two members of a coincidence pair of `α` in `V`, all
of whose other elements have images distinct from theirs, contribute opposite signs. -/
theorem cechSign_mul_invSign_pair (α : Fin s → Fin r) (V : Finset (Fin s)) {k₁ k₂ : Fin s}
    (h₁ : k₁ ∈ V) (h₂ : k₂ ∈ V) (hne : k₁ ≠ k₂) (heq : α k₁ = α k₂)
    (hother : ∀ j ∈ V, j ≠ k₁ → j ≠ k₂ → α j ≠ α k₁) :
    cechSign V k₁ * invSign α (V.erase k₁) + cechSign V k₂ * invSign α (V.erase k₂) = 0 := by
  rcases (lt_or_gt_of_ne hne) with hlt | hlt
  · exact cechSign_mul_invSign_pair_of_lt α V h₁ h₂ hlt heq hother
  · rw [add_comm]
    refine cechSign_mul_invSign_pair_of_lt α V h₂ h₁ hlt heq.symm ?_
    intro j hj hj2 hj1
    rw [← heq]
    exact hother j hj hj1 hj2

/-! ### The sign of a composite reindexing -/

/-- For a map injective on `V`, erasing an index commutes with taking the image. -/
theorem image_erase_of_injOn {α : Fin s → Fin r} {V : Finset (Fin s)} (hinj : Set.InjOn α ↑V)
    {k : Fin s} (hk : k ∈ V) : (V.erase k).image α = (V.image α).erase (α k) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨j, ⟨hjk, hj⟩, rfl⟩
    exact ⟨fun he => hjk (hinj hj hk he), j, hj, rfl⟩
  · rintro ⟨hb, j, hj, rfl⟩
    exact ⟨j, ⟨fun he => hb (congrArg α he), hj⟩, rfl⟩

/-- The identity has no inversions. -/
@[simp] theorem invCount_id (V : Finset (Fin r)) : invCount (id : Fin r → Fin r) V = 0 := by
  rw [invCount_eq_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  exact ite_eq_right fun h => lt_irrefl i (h.1.trans h.2)

/-- The sign of the identity reindexing is `1`. -/
@[simp] theorem invSign_id (V : Finset (Fin r)) : invSign (id : Fin r → Fin r) V = 1 := by
  simp [invSign]

/-- Cancelling a sign: a square root of `1` moves across an equation. -/
theorem eq_mul_of_mul_eq {a b c : ℤ} (hc : c * c = 1) (h : a * c = b) : a = b * c := by
  rw [← h, mul_assoc, hc, mul_one]

/-- **The signs multiply along a composite of reindexings**, stated with the injectivity
hypotheses as implications so that it can be proved by induction on `W`. -/
theorem invSign_comp_aux {t : ℕ} (α : Fin s → Fin r) (β : Fin t → Fin s) (W : Finset (Fin t)) :
    Set.InjOn β ↑W → Set.InjOn α ↑(W.image β) →
      invSign β W * invSign α (W.image β) = invSign (α ∘ β) W := by
  induction W using Finset.induction_on_max with
  | empty => simp
  | insert a E ha ih =>
    intro hβ hα
    have hβE : Set.InjOn β ↑E :=
      hβ.mono (Finset.coe_subset.mpr (Finset.subset_insert a E))
    have hαE : Set.InjOn α ↑(E.image β) :=
      hα.mono (Finset.coe_subset.mpr (Finset.image_subset_image (Finset.subset_insert a E)))
    have haW : a ∈ insert a E := Finset.mem_insert_self a E
    have hcomp : Set.InjOn (α ∘ β) ↑(insert a E) :=
      hα.comp hβ fun j hj => Finset.mem_coe.mpr (Finset.mem_image_of_mem β hj)
    have herase : (insert a E).erase a = E := Finset.erase_insert fun h => lt_irrefl a (ha a h)
    have himage : ((insert a E).image β).erase (β a) = E.image β := by
      rw [← image_erase_of_injOn hβ haW, herase]
    have key1 := cechSign_mul_invSign_erase β haW hβ
    have key2 := cechSign_mul_invSign_erase α (Finset.mem_image_of_mem β haW) hα
    have key3 := cechSign_mul_invSign_erase (α ∘ β) haW hcomp
    rw [herase] at key1 key3
    rw [himage, Finset.image_image] at key2
    have hcs2 := cechSign_mul_self ((insert a E).image β) (β a)
    have hcs3 := cechSign_mul_self ((insert a E).image (α ∘ β)) (α (β a))
    have f1 := eq_mul_of_mul_eq hcs2 key1.symm
    have f2 := eq_mul_of_mul_eq hcs3 key2.symm
    have f3 := eq_mul_of_mul_eq hcs3 key3.symm
    have habs : ∀ u v w z y : ℤ, u * v * w * (w * z * y) = u * (v * z) * y * (w * w) :=
      fun _ _ _ _ _ => by ring
    rw [f1, f2, f3, ← ih hβE hαE, habs, hcs2, mul_one]

/-- **The signs multiply along a composite of reindexings.** -/
theorem invSign_comp {t : ℕ} (α : Fin s → Fin r) (β : Fin t → Fin s) (W : Finset (Fin t))
    (hβ : Set.InjOn β ↑W) (hα : Set.InjOn α ↑(W.image β)) :
    invSign β W * invSign α (W.image β) = invSign (α ∘ β) W :=
  invSign_comp_aux α β W hβ hα

/-! ### A single coincidence of `α` -/

/-- A coincidence partner of `k` in `V`: an index `j ≠ k` of `V` with `α j = α k`, chosen when
there is one, and `k` itself otherwise. -/
def coincidenceMate (α : Fin s → Fin r) (V : Finset (Fin s)) (k : Fin s) : Fin s :=
  if h : ∃ j ∈ V.erase k, α j = α k then h.choose else k

/-- The chosen partner lies in `V.erase k` and has the same image as `k`. -/
theorem coincidenceMate_spec {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s}
    (h : ∃ j ∈ V.erase k, α j = α k) :
    coincidenceMate α V k ∈ V.erase k ∧ α (coincidenceMate α V k) = α k := by
  unfold coincidenceMate
  rw [dite_eq_left h]
  exact h.choose_spec

/-- The partner of an index of `V` is an index of `V`, whether or not a coincidence exists. -/
theorem coincidenceMate_mem {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V) :
    coincidenceMate α V k ∈ V := by
  unfold coincidenceMate
  split_ifs with h
  · exact Finset.mem_of_mem_erase h.choose_spec.1
  · exact hk

/-- If `α` is injective on `V.erase k` but takes some value twice on `V`, the repetition
involves `k`. -/
theorem exists_coincidence {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V)
    (hdeg : (V.image α).card < V.card)
    (hinj : ((V.erase k).image α).card = (V.erase k).card) :
    ∃ j ∈ V.erase k, α j = α k := by
  have hecard : (V.erase k).card = V.card - 1 := Finset.card_erase_of_mem hk
  have hcard : (V.image α).card ≤ ((V.erase k).image α).card := by
    rw [hinj]
    omega
  have hmem : α k ∈ (V.erase k).image α := by
    rw [Finset.eq_of_subset_of_card_le
      (Finset.image_subset_image (Finset.erase_subset k V)) hcard]
    exact Finset.mem_image_of_mem α hk
  exact Finset.mem_image.mp hmem

/-- Under the same hypotheses, erasing `k` from `V` does not change the image of `α`. -/
theorem image_erase_eq_image {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V)
    (hdeg : (V.image α).card < V.card)
    (hinj : ((V.erase k).image α).card = (V.erase k).card) :
    (V.erase k).image α = V.image α := by
  refine Finset.eq_of_subset_of_card_le
    (Finset.image_subset_image (Finset.erase_subset k V)) ?_
  have hecard : (V.erase k).card = V.card - 1 := Finset.card_erase_of_mem hk
  rw [hinj]
  omega

/-- The partner is unique: no other index of `V` has the image of `k`. -/
theorem coincidence_unique {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V)
    (hdeg : (V.image α).card < V.card)
    (hinj : ((V.erase k).image α).card = (V.erase k).card) :
    ∀ j ∈ V, j ≠ k → j ≠ coincidenceMate α V k → α j ≠ α k := by
  intro j hjV hjk hjm hja
  have hinjE : Set.InjOn α ↑(V.erase k) := Finset.card_image_iff.mp hinj
  have hspec := coincidenceMate_spec (exists_coincidence hk hdeg hinj)
  exact hjm (hinjE (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hjk, hjV⟩))
    (Finset.mem_coe.mpr hspec.1) (by rw [hja, hspec.2]))

/-- `α` is injective on `V` with the partner of `k` removed as well: the only coincidence is the
pair `{k, partner}`. -/
theorem injOn_erase_mate {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V)
    (hdeg : (V.image α).card < V.card)
    (hinj : ((V.erase k).image α).card = (V.erase k).card) :
    Set.InjOn α ↑(V.erase (coincidenceMate α V k)) := by
  have hinjE : Set.InjOn α ↑(V.erase k) := Finset.card_image_iff.mp hinj
  have hspec := coincidenceMate_spec (exists_coincidence hk hdeg hinj)
  have huniq : ∀ j ∈ V.erase k, α j = α k → j = coincidenceMate α V k := fun j hj hjk =>
    hinjE (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr hspec.1) (by rw [hjk, hspec.2])
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_erase] at ha hb
  by_cases hak : a = k
  · by_cases hbk : b = k
    · rw [hak, hbk]
    · exact absurd (huniq b (Finset.mem_erase.mpr ⟨hbk, hb.2⟩) (by rw [← hab, hak])) hb.1
  · by_cases hbk : b = k
    · exact absurd (huniq a (Finset.mem_erase.mpr ⟨hak, ha.2⟩) (by rw [hab, hbk])) ha.1
    · exact hinjE (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hak, ha.2⟩))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hbk, hb.2⟩)) hab

/-- Injectivity of `α` off the partner of `k`, in the cardinality form. -/
theorem coincidenceMate_card {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V)
    (hdeg : (V.image α).card < V.card)
    (hinj : ((V.erase k).image α).card = (V.erase k).card) :
    ((V.erase (coincidenceMate α V k)).image α).card
      = (V.erase (coincidenceMate α V k)).card :=
  Finset.card_image_iff.mpr (injOn_erase_mate hk hdeg hinj)

/-- The partner of the partner of `k` is `k`. -/
theorem coincidenceMate_mate {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V)
    (hdeg : (V.image α).card < V.card)
    (hinj : ((V.erase k).image α).card = (V.erase k).card) :
    coincidenceMate α V (coincidenceMate α V k) = k := by
  obtain ⟨hmem, hαm⟩ := coincidenceMate_spec (exists_coincidence hk hdeg hinj)
  obtain ⟨hmk, hmV⟩ := Finset.mem_erase.mp hmem
  have hkmem : k ∈ V.erase (coincidenceMate α V k) :=
    Finset.mem_erase.mpr ⟨Ne.symm hmk, hk⟩
  have hex : ∃ j ∈ V.erase (coincidenceMate α V k), α j = α (coincidenceMate α V k) :=
    ⟨k, hkmem, hαm.symm⟩
  have hspec2 := coincidenceMate_spec hex
  exact injOn_erase_mate hk hdeg hinj (Finset.mem_coe.mpr hspec2.1)
    (Finset.mem_coe.mpr hkmem) (by rw [hspec2.2, hαm])

/-- The swap of a coincidence pair: the partner of `k` when `α` is injective on `V.erase k`,
and `k` itself otherwise. -/
def pairSwap (α : Fin s → Fin r) (V : Finset (Fin s)) (k : Fin s) : Fin s :=
  if ((V.erase k).image α).card = (V.erase k).card then coincidenceMate α V k else k

/-- When `α` is injective on `V.erase k`, `pairSwap α V k` is the partner of `k`. -/
theorem pairSwap_of_card {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s}
    (hinj : ((V.erase k).image α).card = (V.erase k).card) :
    pairSwap α V k = coincidenceMate α V k :=
  ite_eq_left hinj

/-- When `α` is not injective on `V.erase k`, `pairSwap α V k` is `k`. -/
theorem pairSwap_of_not_card {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s}
    (hinj : ¬ ((V.erase k).image α).card = (V.erase k).card) :
    pairSwap α V k = k :=
  ite_eq_right hinj

/-- The swap of an index of `V` lies in `V`. -/
theorem pairSwap_mem {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V) :
    pairSwap α V k ∈ V := by
  unfold pairSwap
  split_ifs
  · exact coincidenceMate_mem hk
  · exact hk

/-- When `α` is not injective on `V` but is injective on `V.erase k`, the swap of `k` differs
from `k`. -/
theorem pairSwap_ne {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V)
    (hdeg : (V.image α).card < V.card)
    (hinj : ((V.erase k).image α).card = (V.erase k).card) :
    pairSwap α V k ≠ k := by
  rw [pairSwap_of_card hinj]
  exact (Finset.mem_erase.mp (coincidenceMate_spec (exists_coincidence hk hdeg hinj)).1).1

/-- The swap is an involution. -/
theorem pairSwap_pairSwap {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V)
    (hdeg : (V.image α).card < V.card) :
    pairSwap α V (pairSwap α V k) = k := by
  by_cases hinj : ((V.erase k).image α).card = (V.erase k).card
  · rw [pairSwap_of_card hinj, pairSwap_of_card (coincidenceMate_card hk hdeg hinj),
      coincidenceMate_mate hk hdeg hinj]
  · rw [pairSwap_of_not_card hinj, pairSwap_of_not_card hinj]

/-- The two members of a coincidence pair carry opposite signs. -/
theorem pairSwap_sign {α : Fin s → Fin r} {V : Finset (Fin s)} {k : Fin s} (hk : k ∈ V)
    (hdeg : (V.image α).card < V.card)
    (hinj : ((V.erase k).image α).card = (V.erase k).card) :
    cechSign V k * invSign α (V.erase k)
      + cechSign V (pairSwap α V k) * invSign α (V.erase (pairSwap α V k)) = 0 := by
  rw [pairSwap_of_card hinj]
  obtain ⟨hmem, hαm⟩ := coincidenceMate_spec (exists_coincidence hk hdeg hinj)
  obtain ⟨hmk, hmV⟩ := Finset.mem_erase.mp hmem
  exact cechSign_mul_invSign_pair α V hk hmV (Ne.symm hmk) hαm.symm
    (coincidence_unique hk hdeg hinj)

/-! ### The localization lift -/

section Comparison

variable {R : Type u} [CommRing R] (f : Fin r → R) (g : Fin s → R) (α : Fin s → Fin r)
  (hα : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ g j ^ n) (M : Type v) [AddCommGroup M] [Module R M]

/-- A divisor of an element acting invertibly on a module acts invertibly itself: the two
multiplications commute, being the images of the central map `algebraMap`. -/
theorem isUnit_algebraMap_of_dvd {N : Type*} [AddCommGroup N] [Module R N] {a b : R}
    (hab : a ∣ b) (hb : IsUnit ((algebraMap R (Module.End R N)) b)) :
    IsUnit ((algebraMap R (Module.End R N)) a) := by
  obtain ⟨c, rfl⟩ := hab
  rw [map_mul] at hb
  exact (((Commute.all a c).map (algebraMap R (Module.End R N))).isUnit_mul_iff.mp hb).1

include hα in
/-- Every element of the submonoid generated by `{f i : i ∈ U}` acts invertibly on
`M_{∏ j ∈ V, g j}` as soon as `U ⊆ α(V)`: each generator `f (α j)` divides a power of `g j`,
which has been inverted there. -/
theorem isUnit_locTarget {U : Finset (Fin r)} {V : Finset (Fin s)} (hU : U ⊆ V.image α) {y : R}
    (hy : y ∈ Submonoid.closure (f '' (U : Set (Fin r)))) :
    IsUnit ((algebraMap R (Module.End R (cechMod g M V))) y) := by
  induction hy using Submonoid.closure_induction with
  | one => simp
  | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hU (by exact_mod_cast hi))
      obtain ⟨n, hn⟩ := hα j
      refine isUnit_algebraMap_of_dvd hn ?_
      have hmem : g j ^ n ∈ Submonoid.closure (g '' (V : Set (Fin s))) :=
        pow_mem (Submonoid.subset_closure (Set.mem_image_of_mem g (by exact_mod_cast hj))) n
      exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (cechSub g V) M)
        ⟨g j ^ n, hmem⟩
  | mul u v _ _ hu hv => simpa only [map_mul] using hu.mul hv

include hα in
/-- Every element of `Cech.cechSub f U` acts invertibly on `M_{∏ j ∈ V, g j}` for
`U ⊆ α(V)`. -/
theorem isUnit_locTarget_cechSub {U : Finset (Fin r)} {V : Finset (Fin s)} (hU : U ⊆ V.image α)
    (y : cechSub f U) : IsUnit ((algebraMap R (Module.End R (cechMod g M V))) (y : R)) :=
  isUnit_locTarget f g α hα M hU (cechSub_le_closure f le_rfl y.2)

/-- **The localization lift.** For `U ⊆ α(V)` the unique `R`-linear map
`M_{∏ i ∈ U, f i} → M_{∏ j ∈ V, g j}` compatible with the two localization maps out of `M`. -/
def locLift (U : Finset (Fin r)) (V : Finset (Fin s)) (hU : U ⊆ V.image α) :
    cechMod f M U →ₗ[R] cechMod g M V :=
  IsLocalizedModule.lift (Submonoid.closure (f '' (U : Set (Fin r))))
    (LocalizedModule.mkLinearMap (cechSub f U) M)
    (LocalizedModule.mkLinearMap (cechSub g V) M)
    fun y => isUnit_locTarget f g α hα M hU y.2

/-- The localization lift extends the localization map of `M`. -/
theorem locLift_mkLinearMap (U : Finset (Fin r)) (V : Finset (Fin s)) (hU : U ⊆ V.image α)
    (m : M) :
    locLift f g α hα M U V hU (LocalizedModule.mkLinearMap (cechSub f U) M m)
      = LocalizedModule.mkLinearMap (cechSub g V) M m :=
  LinearMap.congr_fun (IsLocalizedModule.lift_comp
    (Submonoid.closure (f '' (U : Set (Fin r))))
    (LocalizedModule.mkLinearMap (cechSub f U) M)
    (LocalizedModule.mkLinearMap (cechSub g V) M)
    fun y => isUnit_locTarget f g α hα M hU y.2) m

/-- The localization lift fixes a fraction with denominator one. -/
@[simp] theorem locLift_mk_one (U : Finset (Fin r)) (V : Finset (Fin s)) (hU : U ⊆ V.image α)
    (m : M) :
    locLift f g α hα M U V hU (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  rw [← LocalizedModule.mkLinearMap_apply (cechSub f U) M m, locLift_mkLinearMap,
    LocalizedModule.mkLinearMap_apply]

/-- A linear map which agrees with the localization map of `M` on `M` is the localization lift. -/
private theorem locLift_eq_of_apply_mk (U : Finset (Fin r)) (V : Finset (Fin s))
    (hU : U ⊆ V.image α) (φ : cechMod f M U →ₗ[R] cechMod g M V)
    (hφ : ∀ m, φ (LocalizedModule.mkLinearMap (cechSub f U) M m)
      = LocalizedModule.mkLinearMap (cechSub g V) M m) :
    locLift f g α hα M U V hU = φ :=
  IsLocalizedModule.ext (cechSub f U) (LocalizedModule.mkLinearMap (cechSub f U) M)
    (isUnit_locTarget_cechSub f g α hα M hU)
    (LinearMap.ext fun m => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
      locLift_mkLinearMap, hφ])

/-- The localization lift absorbs a transition map of the source complex. -/
theorem locLift_cechι {U' U : Finset (Fin r)} {V : Finset (Fin s)} (hU' : U' ⊆ U)
    (hU : U ⊆ V.image α) (x : cechMod f M U') :
    locLift f g α hα M U V hU (cechι f M hU' x)
      = locLift f g α hα M U' V (hU'.trans hU) x :=
  (LinearMap.congr_fun (locLift_eq_of_apply_mk f g α hα M U' V (hU'.trans hU)
    ((locLift f g α hα M U V hU).comp (cechι f M hU')) fun m => by
      simp only [LinearMap.comp_apply, cechι_mk, locLift_mkLinearMap]) x).symm

/-- The localization lift absorbs a transition map of the target complex. -/
theorem cechι_locLift {U : Finset (Fin r)} {V V' : Finset (Fin s)} (hU : U ⊆ V.image α)
    (hV : V ⊆ V') (x : cechMod f M U) :
    cechι g M hV (locLift f g α hα M U V hU x)
      = locLift f g α hα M U V' (hU.trans (Finset.image_subset_image hV)) x :=
  (LinearMap.congr_fun (locLift_eq_of_apply_mk f g α hα M U V'
    (hU.trans (Finset.image_subset_image hV)) ((cechι g M hV).comp (locLift f g α hα M U V hU))
    fun m => by simp only [LinearMap.comp_apply, locLift_mkLinearMap, cechι_mk]) x).symm

/-! ### The term map -/

/-- **The degreewise comparison map** `C^p(f; M) → C^p(g; M)`.  The component at a `p`-element
index set `V` for `g` is the component of the source at the image `α(V)`, carried over by the
localization lift and weighted by the inversion sign — unless `α` fails to be injective on `V`,
in which case the image has fewer than `p` elements and the component is zero. -/
def genTerm (p : ℕ) : cechTerm f M p →ₗ[R] cechTerm g M p :=
  (DirectSum.linearEquivFunOnFintype R _ _).symm.toLinearMap.comp
    (LinearMap.pi fun V : Idx s p =>
      if h : (V.1.image α).card = p then
        invSign α V.1 • (locLift f g α hα M (V.1.image α) V.1 Finset.Subset.rfl).comp
          (DirectSum.component R (Idx r p) (fun U => cechMod f M U.1) ⟨V.1.image α, h⟩)
      else 0)

/-- The components of the comparison map. -/
@[simp] theorem genTerm_apply (p : ℕ) (x : cechTerm f M p) (V : Idx s p) :
    genTerm f g α hα M p x V =
      if h : (V.1.image α).card = p then
        invSign α V.1 •
          locLift f g α hα M (V.1.image α) V.1 Finset.Subset.rfl (x ⟨V.1.image α, h⟩)
      else 0 := by
  change (if h : (V.1.image α).card = p then
      invSign α V.1 • (locLift f g α hα M (V.1.image α) V.1 Finset.Subset.rfl).comp
        (DirectSum.component R (Idx r p) (fun U => cechMod f M U.1) ⟨V.1.image α, h⟩)
      else 0) x = _
  split_ifs <;> rfl

/-- The comparison map does not depend on the divisibility proof. -/
theorem genTerm_congr_proof (hα' : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ g j ^ n) (p : ℕ) :
    genTerm f g α hα M p = genTerm f g α hα' M p := rfl

/-! ### The comparison map is a chain map -/

/-- The summand of the Čech differential of the comparison map belonging to an index `k` of `T`
at which `α` is injective off `k`: it is the component of `x` at the image of `T ∖ k`, carried
over by the localization lift. -/
theorem genTerm_summand (p : ℕ) (x : cechTerm f M p) (T : Idx s (p + 1)) (k : T.1)
    (A : Finset (Fin r)) (hA : (T.1.erase k.1).image α = A) (hAcard : A.card = p)
    (hAsub : A ⊆ T.1.image α) :
    cechSign T.1 k.1 • cechι g M (Finset.erase_subset k.1 T.1)
        (genTerm f g α hα M p x (idxErase T k)) =
      (cechSign T.1 k.1 * invSign α (T.1.erase k.1)) •
        locLift f g α hα M A T.1 hAsub (x ⟨A, hAcard⟩) := by
  subst hA
  rw [genTerm_apply, dite_eq_left hAcard, map_zsmul, cechι_locLift, smul_smul]

/-- A summand of the Čech differential of the comparison map vanishes at an index `k` of `T` at
which `α` is not injective off `k`. -/
theorem genTerm_summand_zero (p : ℕ) (x : cechTerm f M p) (T : Idx s (p + 1)) (k : T.1)
    (hk : ¬ ((T.1.erase k.1).image α).card = p) :
    cechSign T.1 k.1 • cechι g M (Finset.erase_subset k.1 T.1)
      (genTerm f g α hα M p x (idxErase T k)) = 0 := by
  rw [genTerm_apply, dite_eq_right hk, map_zero]
  exact zsmul_zero _

/-- **The comparison maps commute with the Čech differentials.** At an index set `T` on which
`α` is injective the two sums match term by term through `k ↦ α k`, by the injective sign
identity; where `α` is not injective on `T` the comparison vanishes in degree `p + 1`, and the
surviving summands of the differential cancel in pairs, by the degenerate sign identity. -/
theorem genTerm_comm (p : ℕ) (x : cechTerm f M p) :
    genTerm f g α hα M (p + 1) (cechD f M p x) = cechD g M p (genTerm f g α hα M p x) := by
  refine DirectSum.ext_component R fun T => ?_
  change genTerm f g α hα M (p + 1) (cechD f M p x) T
    = cechD g M p (genTerm f g α hα M p x) T
  have hecard : ∀ k : T.1, (T.1.erase k.1).card = p := fun k => by
    rw [Finset.card_erase_of_mem k.2, T.2]
    omega
  rw [genTerm_apply]
  by_cases hT : (T.1.image α).card = p + 1
  · rw [dite_eq_left hT]
    have hinj : Set.InjOn α ↑T.1 := Finset.card_image_iff.mp (by rw [hT, T.2])
    simp only [cechD_component, map_sum, map_zsmul]
    rw [@Finset.smul_sum ℤ _ _ _ (AddCommGroup.toIntModule _).toDistribMulAction.toDistribSMul]
    simp only [smul_smul, locLift_cechι]
    symm
    refine Finset.sum_bij
      (fun (k : ↥T.1) _ => (⟨α k.1, Finset.mem_image_of_mem α k.2⟩ : ↥(T.1.image α)))
      (fun k _ => Finset.mem_univ _) (fun a _ b _ hab => ?_) (fun b _ => ?_) (fun k _ => ?_)
    · exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
    · obtain ⟨j, hj, hjb⟩ := Finset.mem_image.mp b.2
      exact ⟨⟨j, hj⟩, Finset.mem_univ _, Subtype.ext hjb⟩
    · rw [genTerm_summand f g α hα M p x T k ((T.1.image α).erase (α k.1))
          (image_erase_of_injOn hinj k.2)
          (by rw [Finset.card_erase_of_mem (Finset.mem_image_of_mem α k.2), hT]; omega)
          (Finset.erase_subset _ _),
        cechSign_mul_invSign_erase α k.2 hinj]
  · rw [dite_eq_right hT]
    have hdeg : (T.1.image α).card < T.1.card := by
      have h1 : (T.1.image α).card ≤ T.1.card := Finset.card_image_le
      rw [T.2] at h1 ⊢
      omega
    rw [cechD_component]
    symm
    refine Finset.sum_involution
      (fun (k : ↥T.1) _ => (⟨pairSwap α T.1 k.1, pairSwap_mem k.2⟩ : ↥T.1)) ?_ ?_ ?_ ?_
    · intro k _
      by_cases hk : ((T.1.erase k.1).image α).card = (T.1.erase k.1).card
      · have hkc : ((T.1.erase k.1).image α).card = p := by rw [hk, hecard k]
        have hm : pairSwap α T.1 k.1 ∈ T.1 := pairSwap_mem k.2
        have hmc : ((T.1.erase (pairSwap α T.1 k.1)).image α).card
            = (T.1.erase (pairSwap α T.1 k.1)).card := by
          rw [pairSwap_of_card hk]
          exact coincidenceMate_card k.2 hdeg hk
        have himg1 : (T.1.erase k.1).image α = T.1.image α := image_erase_eq_image k.2 hdeg hk
        have himg2 : (T.1.erase (pairSwap α T.1 k.1)).image α = T.1.image α :=
          image_erase_eq_image hm hdeg hmc
        have hpcard : (T.1.image α).card = p := by rwa [← himg1]
        rw [genTerm_summand f g α hα M p x T k (T.1.image α) himg1 hpcard Finset.Subset.rfl,
          genTerm_summand f g α hα M p x T ⟨pairSwap α T.1 k.1, pairSwap_mem k.2⟩
            (T.1.image α) himg2 hpcard Finset.Subset.rfl, ← add_smul,
          pairSwap_sign k.2 hdeg hk, zero_smul]
      · have hk' : ¬ ((T.1.erase k.1).image α).card = p := by rwa [hecard k] at hk
        have hk2 : ¬ ((T.1.erase (pairSwap α T.1 k.1)).image α).card = p := by
          rw [pairSwap_of_not_card hk]
          exact hk'
        rw [genTerm_summand_zero f g α hα M p x T k hk',
          genTerm_summand_zero f g α hα M p x T ⟨pairSwap α T.1 k.1, pairSwap_mem k.2⟩ hk2]
        exact add_zero 0
    · intro k _ hne
      by_cases hk : ((T.1.erase k.1).image α).card = (T.1.erase k.1).card
      · intro he
        exact pairSwap_ne k.2 hdeg hk (congrArg Subtype.val he)
      · exact absurd
          (genTerm_summand_zero f g α hα M p x T k (by rwa [hecard k] at hk)) hne
    · exact fun k _ => Finset.mem_univ _
    · exact fun k _ => Subtype.ext (pairSwap_pairSwap k.2 hdeg)

/-! ### The comparison map of complexes -/

/-- **The comparison map of the alternating Čech complexes** `C^•(f; M) ⟶ C^•(g; M)` attached to
a map `α` of index sets along which each `f (α j)` divides a power of `g j`. -/
def cechGenMap : cechComplex f M ⟶ cechComplex g M where
  f p := ModuleCat.ofHom (genTerm f g α hα M p)
  comm' p q hpq := by
    change p + 1 = q at hpq
    subst q
    ext y
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, cechComplex, CochainComplex.of_d]
    exact (genTerm_comm f g α hα M p y).symm

/-- The degreewise components of the comparison map of complexes. -/
@[simp] theorem cechGenMap_f (p : ℕ) :
    ((cechGenMap f g α hα M).f p).hom = genTerm f g α hα M p := rfl

/-- The component of the comparison map depends on the index set only through its value, not
through the proof that the value has the right cardinality. -/
theorem locLift_component_congr {p : ℕ} {U U' : Idx r p} (hUU : U = U') (V : Finset (Fin s))
    (hU : U.1 ⊆ V.image α) (hU' : U'.1 ⊆ V.image α) (x : cechTerm f M p) :
    locLift f g α hα M U.1 V hU (x U) = locLift f g α hα M U'.1 V hU' (x U') := by
  subst hUU
  rfl

/-- Changing the index map changes the comparison term map accordingly; stated as a congruence
because the divisibility hypothesis depends on the index map. -/
theorem genTerm_congr {α' : Fin s → Fin r} (hα' : ∀ j : Fin s, ∃ n : ℕ, f (α' j) ∣ g j ^ n)
    (hαα : α = α') (p : ℕ) : genTerm f g α hα M p = genTerm f g α' hα' M p := by
  subst hαα
  rfl

/-- Changing the index map changes the comparison map of complexes accordingly. -/
theorem cechGenMap_congr {α' : Fin s → Fin r} (hα' : ∀ j : Fin s, ∃ n : ℕ, f (α' j) ∣ g j ^ n)
    (hαα : α = α') : cechGenMap f g α hα M = cechGenMap f g α' hα' M := by
  subst hαα
  rfl

/-- The comparison map of complexes does not depend on the divisibility proof. -/
theorem cechGenMap_congr_proof (hα' : ∀ j : Fin s, ∃ n : ℕ, f (α j) ∣ g j ^ n) :
    cechGenMap f g α hα M = cechGenMap f g α hα' M := rfl

/-- **In degree zero the comparison map is the identity of `M`**: both degree-zero terms are the
single summand indexed by the empty set, which is `M` itself.  This is what makes the comparison
compatible with the augmentations of the two Čech complexes. -/
theorem genTerm_lof_zero (m : M) :
    genTerm f g α hα M 0 (DirectSum.lof R (Idx r 0) (fun U => cechMod f M U.1) default
        (LocalizedModule.mkLinearMap (cechSub f (∅ : Finset (Fin r))) M m)) =
      DirectSum.lof R (Idx s 0) (fun V => cechMod g M V.1) default
        (LocalizedModule.mkLinearMap (cechSub g (∅ : Finset (Fin s))) M m) := by
  refine DirectSum.ext_component R fun V => ?_
  obtain rfl : V = default := Subsingleton.elim _ _
  rw [DirectSum.component.lof_self, ← DirectSum.apply_eq_component, genTerm_apply]
  have hempty : (default : Idx s 0).1 = (∅ : Finset (Fin s)) := rfl
  have h0 : ((default : Idx s 0).1.image α).card = 0 := by
    rw [hempty, Finset.image_empty, Finset.card_empty]
  rw [dite_eq_left h0]
  have h1 : (DirectSum.lof R (Idx r 0) (fun U => cechMod f M U.1) default
        (LocalizedModule.mkLinearMap (cechSub f (∅ : Finset (Fin r))) M m))
      ⟨(default : Idx s 0).1.image α, h0⟩ = LocalizedModule.mk m 1 := by
    rw [Subsingleton.elim (⟨(default : Idx s 0).1.image α, h0⟩ : Idx r 0) default,
      DirectSum.apply_eq_component (R := R)]
    exact (DirectSum.component.lof_self R (default : Idx r 0) _).trans
      (LocalizedModule.mkLinearMap_apply _ _ m)
  have h2 : invSign α (default : Idx s 0).1 = 1 := by rw [hempty, invSign_empty]
  rw [h1, h2, locLift_mk_one, one_zsmul, LocalizedModule.mkLinearMap_apply]

/-! ### Functoriality -/

/-- The localization lifts compose. -/
theorem locLift_locLift {t : ℕ} (h : Fin t → R) (β : Fin t → Fin s)
    (hβ : ∀ k : Fin t, ∃ n : ℕ, g (β k) ∣ h k ^ n)
    (hαβ : ∀ k : Fin t, ∃ n : ℕ, f (α (β k)) ∣ h k ^ n) {U : Finset (Fin r)}
    {V : Finset (Fin s)} {W : Finset (Fin t)} (hU : U ⊆ V.image α) (hV : V ⊆ W.image β)
    (hUW : U ⊆ W.image (α ∘ β)) (y : cechMod f M U) :
    locLift g h β hβ M V W hV (locLift f g α hα M U V hU y)
      = locLift f h (α ∘ β) hαβ M U W hUW y := by
  exact (LinearMap.congr_fun (locLift_eq_of_apply_mk f h (α ∘ β) hαβ M U W hUW
    ((locLift g h β hβ M V W hV).comp (locLift f g α hα M U V hU)) fun m => by
      simp only [LinearMap.comp_apply, locLift_mkLinearMap]) y).symm

/-- **The comparison term maps compose.** -/
theorem genTerm_comp {t : ℕ} (h : Fin t → R) (β : Fin t → Fin s)
    (hβ : ∀ k : Fin t, ∃ n : ℕ, g (β k) ∣ h k ^ n)
    (hαβ : ∀ k : Fin t, ∃ n : ℕ, f (α (β k)) ∣ h k ^ n) (p : ℕ) :
    (genTerm g h β hβ M p).comp (genTerm f g α hα M p) = genTerm f h (α ∘ β) hαβ M p := by
  refine LinearMap.ext fun x => DirectSum.ext_component R fun W => ?_
  change genTerm g h β hβ M p (genTerm f g α hα M p x) W = genTerm f h (α ∘ β) hαβ M p x W
  have himage : (W.1.image β).image α = W.1.image (α ∘ β) := Finset.image_image
  rw [genTerm_apply, genTerm_apply]
  by_cases hW : (W.1.image β).card = p
  · rw [dite_eq_left hW, genTerm_apply]
    by_cases hA : ((W.1.image β).image α).card = p
    · have hC : (W.1.image (α ∘ β)).card = p := by rwa [← himage]
      rw [dite_eq_left hA, dite_eq_left hC, map_zsmul, smul_smul,
        locLift_locLift f g α hα M h β hβ hαβ Finset.Subset.rfl Finset.Subset.rfl
          (le_of_eq himage),
        locLift_component_congr f h (α ∘ β) hαβ M
          (show (⟨(W.1.image β).image α, hA⟩ : Idx r p) = ⟨W.1.image (α ∘ β), hC⟩ from
            Subtype.ext himage) W.1 _ _ x,
        invSign_comp α β W.1 (Finset.card_image_iff.mp (by rw [hW, W.2]))
          (Finset.card_image_iff.mp (by rw [hA, hW]))]
    · have hC : ¬ (W.1.image (α ∘ β)).card = p := by rwa [← himage]
      rw [dite_eq_right hA, dite_eq_right hC, map_zero]
      exact zsmul_zero _
  · have hle : (W.1.image β).card ≤ p := by
      have h1 : (W.1.image β).card ≤ W.1.card := Finset.card_image_le
      rw [W.2] at h1
      omega
    have hC : ¬ (W.1.image (α ∘ β)).card = p := by
      rw [← himage]
      have h2 : ((W.1.image β).image α).card ≤ (W.1.image β).card := Finset.card_image_le
      omega
    rw [dite_eq_right hW, dite_eq_right hC]

/-- **The comparison maps of complexes compose.** -/
theorem cechGenMap_comp {t : ℕ} (h : Fin t → R) (β : Fin t → Fin s)
    (hβ : ∀ k : Fin t, ∃ n : ℕ, g (β k) ∣ h k ^ n)
    (hαβ : ∀ k : Fin t, ∃ n : ℕ, f (α (β k)) ∣ h k ^ n) :
    cechGenMap f g α hα M ≫ cechGenMap g h β hβ M = cechGenMap f h (α ∘ β) hαβ M := by
  refine HomologicalComplex.hom_ext _ _ fun p => ModuleCat.hom_ext ?_
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, cechGenMap_f, cechGenMap_f, cechGenMap_f]
  exact genTerm_comp f g α hα M h β hβ hαβ p

end Comparison

/-! ### The identity comparison -/

section Identity

variable {R : Type u} [CommRing R] (f : Fin r → R) (M : Type v) [AddCommGroup M] [Module R M]

/-- Along the identity reindexing the localization lift is the identity. -/
theorem locLift_id (hf : ∀ j : Fin r, ∃ n : ℕ, f (id j) ∣ f j ^ n) (U : Finset (Fin r))
    (hU : U ⊆ U.image id) : locLift f f id hf M U U hU = LinearMap.id :=
  locLift_eq_of_apply_mk f f id hf M U U hU LinearMap.id fun _ => rfl

/-- Along the identity reindexing the comparison term map is the identity. -/
theorem genTerm_id (hf : ∀ j : Fin r, ∃ n : ℕ, f (id j) ∣ f j ^ n) (p : ℕ) :
    genTerm f f id hf M p = LinearMap.id := by
  refine LinearMap.ext fun x => DirectSum.ext_component R fun V => ?_
  change genTerm f f id hf M p x V = x V
  have himage : V.1.image (id : Fin r → Fin r) = V.1 := Finset.image_id
  have hcard : (V.1.image (id : Fin r → Fin r)).card = p := by rw [himage]; exact V.2
  rw [genTerm_apply, dite_eq_left hcard,
    locLift_component_congr f f id hf M
      (show (⟨V.1.image (id : Fin r → Fin r), hcard⟩ : Idx r p) = V from Subtype.ext himage)
      V.1 Finset.Subset.rfl (by rw [himage]) x,
    locLift_id f M hf V.1, invSign_id, one_zsmul, LinearMap.id_apply]

/-- **Along the identity reindexing the comparison map of complexes is the identity.** -/
theorem cechGenMap_id (hf : ∀ j : Fin r, ∃ n : ℕ, f (id j) ∣ f j ^ n) :
    cechGenMap f f id hf M = 𝟙 (cechComplex f M) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ModuleCat.hom_ext ?_
  rw [cechGenMap_f, HomologicalComplex.id_f, ModuleCat.hom_id, genTerm_id]
  rfl

end Identity

end Cech

end
