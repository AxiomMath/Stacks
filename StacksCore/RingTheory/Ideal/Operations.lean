module

public import Mathlib.RingTheory.Ideal.Operations
import StacksCore.Tactic.StacksAttribute

/-! # Operations on ideals -/

add_to_stacks 00DT "(1)" Ideal.prod_eq_iInf_of_pairwise_isCoprime
add_to_stacks 00DT "(2)" Ideal.isCoprime_of_isMaximal
add_to_stacks 00DT "(2)" Ideal.IsMaximal.coprime_of_ne
add_to_stacks 00E0 "7" Ideal.radical_eq_sInf
add_to_stacks 07K1 Ideal.IsPrime.mul_le

@[expose] public section

open Ideal

/-- **Stacks 09GX** (generalization).
Two elements `x y` of a commutative semiring are coprime if and only if the ideal they
generate is the whole ring. -/
@[stacks 09GX "generalization"]
theorem coprime_iff_span_pair_eq_top {R : Type*} [CommSemiring R] (x y : R) :
    IsCoprime x y ↔ Ideal.span ({x, y} : Set R) = ⊤ := by
  rw [span_insert, ← isCoprime_iff_sup_eq, isCoprime_span_singleton_iff]

section AddIdeal

open scoped Pointwise

variable {R : Type*} [CommRing R]

/-- The submonoid `S + I`, for `S` a submonoid and `I` an ideal of `R`.

The set `S + I` is multiplicatively closed because `I` absorbs multiplication:
`(s₁ + i₁)(s₂ + i₂) = s₁s₂ + (s₁i₂ + i₁s₂ + i₁i₂)`, whose second summand is in `I`. It contains
`1 = 1 + 0`.

Its point is `Submonoid.add_mem_addIdeal` below: `S + I` absorbs `I` under addition, which is
exactly the hypothesis under which localizing sends `I` into the Jacobson radical (see
`Ideal.map_le_ringJacobson_of_add_mem`). -/
def Submonoid.addIdeal (S : Submonoid R) (I : Ideal R) : Submonoid R where
  carrier := (S : Set R) + (I : Set R)
  one_mem' := ⟨1, S.one_mem, 0, I.zero_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    exact ⟨a * c, S.mul_mem ha hc, a * d + b * c + b * d,
      I.add_mem (I.add_mem (I.mul_mem_left a hd) (I.mul_mem_right c hb))
        (I.mul_mem_left b hd), by ring⟩

@[simp]
theorem Submonoid.mem_addIdeal {S : Submonoid R} {I : Ideal R} {x : R} :
    x ∈ S.addIdeal I ↔ ∃ s ∈ S, ∃ i ∈ I, s + i = x := Set.mem_add

theorem Submonoid.le_addIdeal (S : Submonoid R) (I : Ideal R) : S ≤ S.addIdeal I :=
  fun _ hs => ⟨_, hs, 0, I.zero_mem, by simp⟩

/-- `S + I` absorbs `I` under addition. This is the property that makes it the right submonoid
to localize at: it forces every `1 + i/t` to be a unit downstairs. -/
theorem Submonoid.add_mem_addIdeal {S : Submonoid R} {I : Ideal R} {t : R}
    (ht : t ∈ S.addIdeal I) {i : R} (hi : i ∈ I) : t + i ∈ S.addIdeal I := by
  obtain ⟨s, hs, j, hj, rfl⟩ := Submonoid.mem_addIdeal.1 ht
  exact ⟨s, hs, j + i, I.add_mem hj hi, by ring⟩

/-- In particular `1 + I ⊆ S + I`, since `1 ∈ S`. -/
theorem Submonoid.one_add_mem_addIdeal (S : Submonoid R) {I : Ideal R} {i : R} (hi : i ∈ I) :
    1 + i ∈ S.addIdeal I :=
  Submonoid.add_mem_addIdeal (S.le_addIdeal I S.one_mem) hi

end AddIdeal

namespace Ideal

open scoped Pointwise

variable {R ι : Type*} [CommRing R]

/-- A coset `x + I` is contained in an ideal `p` exactly when `x ∈ p` and `I ≤ p`. -/
theorem vadd_coe_subset_iff {I p : Ideal R} {x : R} :
    x +ᵥ (I : Set R) ⊆ (p : Set R) ↔ x ∈ p ∧ I ≤ p := by
  constructor
  · intro h
    have hx : x ∈ p := by simpa using h ⟨0, I.zero_mem, by simp⟩
    refine ⟨hx, fun y hy => ?_⟩
    have hxy : x + y ∈ p := by simpa using h ⟨y, hy, rfl⟩
    simpa using p.sub_mem hxy hx
  · rintro ⟨hx, hI⟩ _ ⟨y, hy, rfl⟩
    simpa using p.add_mem hx (hI hy)

theorem exists_add_mem_notMem_of_not_le {I p : Ideal R} (h : ¬I ≤ p) (x : R) :
    ∃ y ∈ I, x + y ∉ p := by
  by_cases hx : x ∈ p
  · obtain ⟨u, huI, hup⟩ := SetLike.not_le_iff_exists.1 h
    exact ⟨u, huI, fun hm => hup (by simpa using p.sub_mem hm hx)⟩
  · exact ⟨0, I.zero_mem, by simpa using hx⟩

/-- Dropping a redundant index: if `p i ≤ p k` for distinct `i k ∈ s`, then anything avoiding
every `p j` for `j ∈ s.erase i` already avoids `p i` too, via `p k`. -/
private theorem exists_add_mem_notMem_of_le [DecidableEq ι] {s : Finset ι}
    {p : ι → Ideal R} {I : Ideal R} {x : R} {i k : ι} (hk : k ∈ s) (hik : i ≠ k) (hle : p i ≤ p k)
    (h : ∃ y ∈ I, ∀ j ∈ s.erase i, x + y ∉ p j) : ∃ y ∈ I, ∀ j ∈ s, x + y ∉ p j := by
  obtain ⟨y, hyI, hy⟩ := h
  refine ⟨y, hyI, fun j hj => ?_⟩
  rcases eq_or_ne j i with rfl | hji
  · exact fun hmem => hy k (Finset.mem_erase.2 ⟨fun h => hik h.symm, hk⟩) (hle hmem)
  · exact hy j (Finset.mem_erase.2 ⟨hji, hj⟩)

/-- Correcting at one index: a solution for `s.erase k` either already works at `k`, or can be
corrected by adding an element of `I ⊓ ⨅ j ∈ s.erase k, p j` lying outside `p k`. -/
private theorem exists_add_mem_notMem_of_inf_not_le [DecidableEq ι] {s : Finset ι} {p : ι → Ideal R}
    {I : Ideal R} {x : R} {k : ι} (hk : k ∈ s) (hnotle : ¬I ⊓ (s.erase k).inf p ≤ p k)
    (h : ∃ y ∈ I, ∀ j ∈ s.erase k, x + y ∉ p j) : ∃ y ∈ I, ∀ j ∈ s, x + y ∉ p j := by
  obtain ⟨y, hyI, hy⟩ := h
  by_cases hxk : x + y ∈ p k
  · obtain ⟨z, hz, hzk⟩ := SetLike.not_le_iff_exists.1 hnotle
    refine ⟨y + z, I.add_mem hyI hz.1, fun j hj => ?_⟩
    rcases eq_or_ne j k with rfl | hjk
    · intro hmem
      rw [← add_assoc] at hmem
      exact hzk (by simpa using (p j).sub_mem hmem hxk)
    · have hje : j ∈ s.erase k := Finset.mem_erase.2 ⟨hjk, hj⟩
      have hzj : z ∈ p j := SetLike.le_def.1 (Finset.inf_le hje) hz.2
      intro hmem
      rw [← add_assoc] at hmem
      exact hy j hje (by simpa using (p j).sub_mem hmem hzj)
  · refine ⟨y, hyI, fun j hj => ?_⟩
    rcases eq_or_ne j k with rfl | hjk
    · exact hxk
    · exact hy j (Finset.mem_erase.2 ⟨hjk, hj⟩)

private theorem exists_add_mem_notMem_aux (a : ι) (n : ℕ) :
    ∀ (s : Finset ι) (p : ι → Ideal R), s.card ≤ n → (∀ i ∈ s, i ≠ a → (p i).IsPrime) →
      ∀ I : Ideal R, (∀ i ∈ s, ¬I ≤ p i) → ∀ x : R, ∃ y ∈ I, ∀ i ∈ s, x + y ∉ p i := by
  classical
  induction n with
  | zero =>
    intro s p hcard _ I _ x
    obtain rfl : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact ⟨0, I.zero_mem, by simp⟩
  | succ n ih =>
    intro s p hcard hp I hI x
    rcases s.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
    · exact ⟨0, I.zero_mem, by simp⟩
    -- the induction hypothesis, applied after deleting any one index of `s`
    have ihs : ∀ {i}, i ∈ s → ∃ y ∈ I, ∀ j ∈ s.erase i, x + y ∉ p j := fun {i} hi =>
      ih (s.erase i) p
        (by have := Finset.card_erase_of_mem hi; have := Finset.card_pos.2 ⟨i, hi⟩; omega)
        (fun j hj => hp j (Finset.mem_of_mem_erase hj)) I
        (fun j hj => hI j (Finset.mem_of_mem_erase hj)) x
    by_cases hex : ∃ k ∈ s, k ≠ a
    · obtain ⟨k, hk, hka⟩ := hex
      have hpk : (p k).IsPrime := hp k hk hka
      by_cases hA : ∃ i ∈ s.erase k, p i ≤ p k
      · obtain ⟨i, hie, hik⟩ := hA
        exact exists_add_mem_notMem_of_le hk (Finset.ne_of_mem_erase hie) hik
          (ihs (Finset.mem_of_mem_erase hie))
      · push Not at hA
        refine exists_add_mem_notMem_of_inf_not_le hk ?_ (ihs hk)
        rw [hpk.inf_le, hpk.inf_le']
        push Not
        exact ⟨hI k hk, hA⟩
    · -- every index of `s` equals the exceptional one, so `s = {a}` and no primality is used
      push Not at hex
      have ha : a ∈ s := hex k₀ hk₀ ▸ hk₀
      obtain ⟨y, hyI, hy⟩ := exists_add_mem_notMem_of_not_le (hI a ha) x
      exact ⟨y, hyI, fun i hi => (hex i hi) ▸ hy⟩

/-- **Stacks 0EHL.** If the coset `x + I` is contained in none of the ideals `p i`, then some
`x + y` with `y ∈ I` avoids all of them simultaneously.

All but one of the `p i` must be prime; the exceptional index `a` matches the shape of
`Ideal.subset_union_prime`. Allowing *two* exceptional indices is false. -/
@[stacks 0EHL]
theorem exists_add_mem_notMem (a : ι) {s : Finset ι} {p : ι → Ideal R}
    (hp : ∀ i ∈ s, i ≠ a → (p i).IsPrime) {I : Ideal R} {x : R}
    (h : ∀ i ∈ s, ¬(x ∈ p i ∧ I ≤ p i)) : ∃ y ∈ I, ∀ i ∈ s, x + y ∉ p i := by
  classical
  -- indices with `I ≤ p i` are free: there `x ∉ p i`, so `x + y ∉ p i` for every `y ∈ I`
  obtain ⟨y, hyI, hy⟩ :=
    exists_add_mem_notMem_aux a (s.filter fun i => ¬I ≤ p i).card _ p le_rfl
      (fun i hi => hp i (Finset.mem_of_mem_filter i hi)) I
      (fun i hi => (Finset.mem_filter.1 hi).2) x
  refine ⟨y, hyI, fun i hi => ?_⟩
  by_cases hle : I ≤ p i
  · exact fun hmem => (h i hi) ⟨by simpa using (p i).sub_mem hmem (hle hyI), hle⟩
  · exact hy i (Finset.mem_filter.2 ⟨hi, hle⟩)

/-- **Stacks 0EHL** in the tag's literal wording, via `Ideal.vadd_coe_subset_iff`. -/
@[stacks 0EHL]
theorem exists_add_mem_notMem' (a : ι) {s : Finset ι} {p : ι → Ideal R}
    (hp : ∀ i ∈ s, i ≠ a → (p i).IsPrime) {I : Ideal R} {x : R}
    (h : ∀ i ∈ s, ¬x +ᵥ (I : Set R) ⊆ (p i : Set R)) : ∃ y ∈ I, ∀ i ∈ s, x + y ∉ p i :=
  exists_add_mem_notMem a hp fun i hi => fun hc => h i hi (vadd_coe_subset_iff.2 hc)

end Ideal
