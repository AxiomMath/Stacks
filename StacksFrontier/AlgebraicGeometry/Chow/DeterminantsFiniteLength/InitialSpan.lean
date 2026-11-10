module

public import Mathlib.RingTheory.FiniteLength
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Basic

/-!
# Initial spans of a sequence in a module

The span of an initial segment of a finite sequence in a module. Admissibility of a
sequence over a local ring is a statement about these spans, so the basic manipulations of
admissible sequences — replacing an entry by a unit multiple of it modulo the earlier
entries, and exchanging two adjacent entries — are recorded here, together with their
effect on the determinant symbol.

The final results of the file are the two forms of the length argument: a sequence whose
every entry is independent of its predecessors gives a strictly increasing chain of
submodules of length `moduleLength R M`, so an admissible sequence that fails to span has a
dependent entry and hence a vanishing symbol.

## Main definitions

* `Module.FiniteLength.initialSpan` is the span of the entries with index below a bound.
* `Module.FiniteLength.swapEntries` exchanges two entries of a sequence.

## Main results

* `Module.FiniteLength.initialSpan_update` says that replacing an entry by a unit multiple
  of it modulo the earlier entries leaves every initial span unchanged.
* `Module.FiniteLength.admissible_update` and `Module.FiniteLength.admissible_swap`
  propagate admissibility through those two operations.
* `Module.FiniteLength.exists_unit_entry` locates the first initial span containing a given
  element and extracts the unit coefficient admissibility forces on it.
* `Module.FiniteLength.exists_dependent_of_span_ne_top` and
  `Module.FiniteLength.span_eq_top_of_symbol_ne_zero` are the length argument.

## Implementation notes

`initialSpan e k` is indexed by a natural number bound rather than by an element of
`Fin n`, which is what makes induction on the bound and the comparison of sequences of
different lengths available; `spanBefore_eq_initialSpan` relates it to the `spanBefore` of
the determinant construction.

## References

* [Stacks Project, Tag 02P6](https://stacks.math.columbia.edu/tag/02P6)
* [Stacks Project, Tag 02P7](https://stacks.math.columbia.edu/tag/02P7)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M]

/-- The submodule spanned by the entries of `e` whose index is below the bound `k`. -/
public def initialSpan {n : ℕ} (e : Fin n → M) (k : ℕ) : Submodule R M :=
  Submodule.span R (e '' {i | i.val < k})

omit [IsLocalRing R] in
/-- `spanBefore` is the initial span cut off at the value of the index. -/
public lemma spanBefore_eq_initialSpan {n : ℕ} (e : Fin n → M) (i : Fin n) :
    spanBefore (R := R) e i = initialSpan (R := R) e i.val :=
  rfl

omit [IsLocalRing R] in
/-- Initial spans grow with the bound. -/
public lemma initialSpan_mono {n : ℕ} (e : Fin n → M) {j k : ℕ} (h : j ≤ k) :
    initialSpan (R := R) e j ≤ initialSpan e k :=
  Submodule.span_mono (Set.image_mono fun _ hi ↦ lt_of_lt_of_le hi h)

omit [IsLocalRing R] in
/-- An entry lies in every initial span whose bound exceeds its index. -/
public lemma entry_mem_initialSpan {n : ℕ} (e : Fin n → M) (i : Fin n) {k : ℕ}
    (hi : i.val < k) : e i ∈ initialSpan (R := R) e k :=
  Submodule.subset_span ⟨i, hi, rfl⟩

omit [IsLocalRing R] in
/-- The initial span at the full length is the span of the whole sequence. -/
public lemma initialSpan_all {n : ℕ} (e : Fin n → M) :
    initialSpan (R := R) e n = Submodule.span R (Set.range e) := by
  unfold initialSpan; congr 1; ext x; simp [Fin.is_lt]

omit [IsLocalRing R] in
/-- The initial span one past an index is spanned by that entry together with the earlier
ones. -/
public lemma initialSpan_succ {n : ℕ} (e : Fin n → M) (i : Fin n) :
    initialSpan (R := R) e (i.val + 1) =
      Submodule.span R (insert (e i) (e '' {j | j.val < i.val})) := by
  unfold initialSpan
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases h : j = i
    · simp [h]
    · refine Or.inr ⟨j, ?_, rfl⟩
      dsimp at hj ⊢
      have := Fin.val_ne_of_ne h
      omega
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨i, by dsimp; omega, rfl⟩
    · exact ⟨j, by dsimp at hj ⊢; omega, rfl⟩

omit [IsLocalRing R] in
/-- Initial spans only see the entries below the bound. -/
public lemma initialSpan_congr {n : ℕ} {e f : Fin n → M} {k : ℕ}
    (h : ∀ i, i.val < k → e i = f i) : initialSpan (R := R) e k = initialSpan f k := by
  unfold initialSpan; congr 1; exact Set.image_congr h

/-- An initial span is contained in another when each entry below the bound is an entry of the
other below the same bound. -/
private lemma initialSpan_le_of_forall {S N : Type*} [CommRing S] [AddCommGroup N]
    [Module S N] {n m : ℕ} {e : Fin n → N} {f : Fin m → N} {k : ℕ}
    (h : ∀ i : Fin n, i.val < k → ∃ j : Fin m, j.val < k ∧ f j = e i) :
    initialSpan (R := S) e k ≤ initialSpan f k := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨j, hj, hji⟩ := h i hi
  exact hji ▸ entry_mem_initialSpan f j hj

omit [IsLocalRing R] in
/-- Two sequences agreeing on their first `k` entries have the same initial span at `k`,
even when their lengths differ. -/
public lemma initialSpan_eq_of_prefix {n m : ℕ} (e : Fin n → M) (f : Fin m → M)
    (k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m)
    (h : ∀ j (hjn : j < k), e ⟨j, lt_of_lt_of_le hjn hkn⟩ =
      f ⟨j, lt_of_lt_of_le hjn hkm⟩) :
    initialSpan (R := R) e k = initialSpan f k := by
  exact le_antisymm
    (initialSpan_le_of_forall fun i hi ↦ ⟨⟨i.val, lt_of_lt_of_le hi hkm⟩, hi, (h i.val hi).symm⟩)
    (initialSpan_le_of_forall fun i hi ↦ ⟨⟨i.val, lt_of_lt_of_le hi hkn⟩, hi, h i.val hi⟩)

omit [IsLocalRing R] in
/-- Updating an entry does not change the initial spans below its index. -/
public lemma initialSpan_update_le {n : ℕ} (e : Fin n → M) (i : Fin n) (x : M)
    {k : ℕ} (h : k ≤ i.val) :
    initialSpan (R := R) (Function.update e i x) k = initialSpan e k := by
  classical
  apply initialSpan_congr; intro j hj
  exact Function.update_of_ne (by intro heq; subst j; omega) _ _

omit [IsLocalRing R] in
/-- Replacing an entry by a unit multiple of it modulo the earlier entries leaves every
initial span unchanged. -/
public lemma initialSpan_update {n : ℕ} (e : Fin n → M) (i : Fin n) (x y : M)
    (a : Rˣ) (hi : e i = (a : R) • x + y) (hy : y ∈ initialSpan (R := R) e i.val)
    (k : ℕ) : initialSpan (R := R) (Function.update e i x) k = initialSpan e k := by
  classical
  by_cases hki : k ≤ i.val
  · exact initialSpan_update_le e i x hki
  have hik : i.val < k := by omega
  have hp := initialSpan_update_le (R := R) e i x (le_refl i.val)
  have hy' : y ∈ initialSpan (R := R) (Function.update e i x) k :=
    initialSpan_mono _ (by omega) (hp.symm ▸ hy)
  have hx : x ∈ initialSpan (R := R) e k := by
    have h := (initialSpan (R := R) e k).sub_mem (entry_mem_initialSpan e i hik)
      (initialSpan_mono e (by omega) hy)
    rw [hi, add_sub_cancel_right] at h
    simpa only [smul_smul, Units.inv_mul, one_smul] using
      (initialSpan (R := R) e k).smul_mem (↑a⁻¹ : R) h
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨j, hj, rfl⟩
    by_cases hji : j = i
    · simpa [hji] using hx
    · simpa [Function.update_of_ne hji] using entry_mem_initialSpan (R := R) e j hj
  · apply Submodule.span_le.mpr
    rintro z ⟨j, hj, rfl⟩
    by_cases hji : j = i
    · subst j
      rw [hi]
      apply (initialSpan (R := R) (Function.update e i x) k).add_mem _ hy'
      apply Submodule.smul_mem
      simpa using entry_mem_initialSpan (R := R) (Function.update e i x) i hik
    · simpa [Function.update_of_ne hji] using
        entry_mem_initialSpan (R := R) (Function.update e i x) j hj

/-- Replacing an entry of an admissible sequence by a unit multiple of it modulo the
earlier entries, where the replacement is itself admissible at that index, yields an
admissible sequence. -/
public lemma admissible_update (e : AdmissibleSequence R M)
    (i : Fin (moduleLength R M)) (x y : M) (a : Rˣ)
    (hi : e.1 i = (a : R) • x + y) (hy : y ∈ initialSpan (R := R) e.1 i.val)
    (hx : ∀ r, r ∈ IsLocalRing.maximalIdeal R → r • x ∈ initialSpan (R := R) e.1 i.val) :
    IsAdmissibleSequence (R := R) (Function.update e.1 i x) := by
  classical
  intro j r hr
  change r • Function.update e.1 i x j ∈ initialSpan (R := R) (Function.update e.1 i x) j.val
  rw [initialSpan_update e.1 i x y a hi hy]
  by_cases h : j = i
  · subst j
    simpa using hx r hr
  · simpa [Function.update_of_ne h, initialSpan, spanBefore, Set.Iio] using e.2 j r hr

/-- The first initial span of an admissible spanning sequence that contains `x` meets it in
an entry whose coefficient on `x` is a unit: a nonunit coefficient would already place `x`
in the previous initial span. -/
public lemma exists_unit_entry (e : AdmissibleSequence R M)
    (he : initialSpan (R := R) e.1 (moduleLength R M) = ⊤)
    (x : M) {j : ℕ} (hx : x ∉ initialSpan (R := R) e.1 j) :
    ∃ (i : Fin (moduleLength R M)) (a : Rˣ) (y : M),
      j ≤ i.val ∧ e.1 i = (a : R) • x + y ∧ y ∈ initialSpan (R := R) e.1 i.val := by
  classical
  have hex : ∃ k, x ∈ initialSpan (R := R) e.1 k := ⟨_, he ▸ Submodule.mem_top⟩
  let k := Nat.find hex
  have hk : x ∈ initialSpan (R := R) e.1 k := Nat.find_spec hex
  have hkn : k ≤ moduleLength R M := Nat.find_min' hex (he ▸ Submodule.mem_top)
  have hjk : j < k := not_le.mp fun h ↦ hx (initialSpan_mono e.1 h hk)
  let i : Fin (moduleLength R M) := ⟨k - 1, by omega⟩
  have hik : i.val + 1 = k := by dsimp [i]; omega
  have hxmin : x ∉ initialSpan (R := R) e.1 i.val := Nat.find_min hex (by dsimp [i]; omega)
  rw [← hik, initialSpan_succ] at hk
  obtain ⟨r, y, hy, hxy⟩ := Submodule.mem_span_insert.mp hk
  have hr : IsUnit r := by
    by_contra hr
    exact hxmin (hxy ▸ (initialSpan (R := R) e.1 i.val).add_mem (e.2 i r hr) hy)
  obtain ⟨a, rfl⟩ := hr
  refine ⟨i, a⁻¹, -(↑a⁻¹ : R) • y, by dsimp [i]; omega, ?_, ?_⟩
  · rw [hxy, smul_add, smul_smul, Units.inv_mul, one_smul, neg_smul]
    simp
  · exact (initialSpan (R := R) e.1 i.val).smul_mem _ hy

/-- The sequence `e` with its entries at `a` and `b` exchanged. -/
public def swapEntries {n : ℕ} (e : Fin n → M) (a b : Fin n) : Fin n → M :=
  e ∘ Equiv.swap a b

omit [AddCommGroup M] in
/-- Exchanging two entries is the composite of two updates. -/
public lemma swapEntries_eq_update {n : ℕ} (e : Fin n → M) (a b : Fin n) :
    swapEntries e a b = Function.update (Function.update e b (e a)) a (e b) := by
  classical
  funext i
  by_cases hia : i = a
  · subst i; simp [swapEntries]
  by_cases hib : i = b
  · subst i; simp [swapEntries, hia]
  simp [swapEntries, Function.update_of_ne hia, Function.update_of_ne hib,
    Equiv.swap_apply_of_ne_of_ne hia hib]

omit [IsLocalRing R] in
/-- Exchanging two entries whose indices lie on the same side of the bound does not change
the initial span. -/
public lemma initialSpan_swap {n : ℕ} (e : Fin n → M) (a b : Fin n) {k : ℕ}
    (hk : (a.val < k ↔ b.val < k)) :
    initialSpan (R := R) (swapEntries e a b) k = initialSpan e k := by
  classical
  have hs (i : Fin n) : (Equiv.swap a b i).val < k ↔ i.val < k := by
    by_cases hia : i = a
    · subst i; simpa using hk.symm
    by_cases hib : i = b
    · subst i; simpa using hk
    simp [Equiv.swap_apply_of_ne_of_ne hia hib]
  exact le_antisymm
    (initialSpan_le_of_forall fun i hi ↦ ⟨Equiv.swap a b i, (hs i).mpr hi, rfl⟩)
    (initialSpan_le_of_forall fun i hi ↦ ⟨Equiv.swap a b i, (hs i).mpr hi, by simp [swapEntries]⟩)

/-- Exchanging two adjacent entries of an admissible sequence is admissible as soon as the
later entry is already admissible with respect to the entries preceding the earlier one. -/
public lemma admissible_swap (e : AdmissibleSequence R M)
    (a b : Fin (moduleLength R M)) (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 a ∈ initialSpan (R := R) e.1 b.val) :
    IsAdmissibleSequence (R := R) (swapEntries e.1 a b) := by
  classical
  have hp : initialSpan (R := R) (swapEntries e.1 a b) b.val = initialSpan e.1 b.val :=
    initialSpan_swap _ _ _ (by omega)
  intro i r hr
  change r • swapEntries e.1 a b i ∈ initialSpan (R := R) (swapEntries e.1 a b) i.val
  by_cases hib : i = b
  · subst i
    rw [hp]
    simpa [swapEntries] using ha r hr
  by_cases hia : i = a
  · subst i
    rw [show swapEntries e.1 a b a = e.1 b by simp [swapEntries]]
    apply initialSpan_mono _ (show b.val ≤ a.val by omega)
    rw [hp]
    exact e.2 b r hr
  · rw [initialSpan_swap _ _ _ (by
      have := Fin.val_ne_of_ne hia
      have := Fin.val_ne_of_ne hib
      omega)]
    simpa [swapEntries, Equiv.swap_apply_of_ne_of_ne hia hib, initialSpan, spanBefore,
      Set.Iio] using e.2 i r hr

/-- Exchanging two adjacent entries negates the symbol. -/
public lemma symbol_swap_entries (e : AdmissibleSequence R M)
    (a b : Fin (moduleLength R M)) (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 a ∈ initialSpan (R := R) e.1 b.val) :
    symbol e = -symbol ⟨swapEntries e.1 a b, admissible_swap e a b hba ha⟩ := by
  have hs := symbol_swap e a b hba ha
    (swapEntries_eq_update e.1 a b ▸ admissible_swap e a b hba ha)
  simpa only [swapEntries_eq_update] using hs

/-- The symbol of a sequence obtained by exchanging two adjacent entries stays in the line
spanned by the original symbol. -/
public lemma symbol_swap_mem (e : AdmissibleSequence R M)
    (a b : Fin (moduleLength R M)) (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 a ∈ initialSpan (R := R) e.1 b.val) :
    symbol (⟨swapEntries e.1 a b, admissible_swap e a b hba ha⟩ : AdmissibleSequence R M) ∈
      (IsLocalRing.ResidueField R) ∙ symbol e := by
  simpa only [symbol_swap_entries e a b hba ha, neg_neg] using
    (IsLocalRing.ResidueField R ∙ symbol e).neg_mem
      (Submodule.mem_span_singleton_self (symbol e))

/-- A subspace of the determinant containing every symbol is everything. -/
public lemma eq_top_of_symbols_mem
    (p : Submodule (IsLocalRing.ResidueField R) (determinant R M))
    (h : ∀ e : AdmissibleSequence R M, symbol e ∈ p) : p = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    induction z using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add z w hz hw =>
      rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hz hw
    | single f c =>
      rw [show Finsupp.single f c = c • Finsupp.single f (1 : IsLocalRing.ResidueField R) by
          simp,
        Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem _ _ (h f)

/-- An admissible sequence of a finite-length module that does not span has an entry in the
span of its predecessors: otherwise its initial spans form a strictly increasing chain of
length `moduleLength R M` inside a proper submodule. -/
public lemma exists_dependent_of_span_ne_top (hM : IsFiniteLength R M)
    (e : AdmissibleSequence R M) (he : Submodule.span R (Set.range e.1) ≠ ⊤) :
    ∃ i, e.1 i ∈ spanBefore (R := R) e.1 i := by
  classical
  by_contra h
  push Not at h
  let s : LTSeries (Submodule R M) := {
    length := moduleLength R M
    toFun := fun i ↦ initialSpan e.1 i.val
    step := fun i ↦ lt_of_le_not_ge (initialSpan_mono e.1 (by simp)) (by
      intro hle
      exact h i (hle (entry_mem_initialSpan e.1 i (by simp)))) }
  have hs : (moduleLength R M : ℕ∞) ≤
      Order.height (initialSpan (R := R) e.1 (moduleLength R M)) :=
    Order.length_le_height_last (p := s)
  rw [initialSpan_all, ← Module.length_submodule] at hs
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  have hlt := Submodule.length_lt he
  have hn : (moduleLength R M : ℕ∞) = Module.length R M :=
    ENat.natCast_toNat (Module.length_ne_top_iff.mpr hM)
  exact (not_lt_of_ge (hn ▸ hs)) hlt

/-- An admissible sequence with nonzero symbol spans. -/
public lemma span_eq_top_of_symbol_ne_zero (hM : IsFiniteLength R M)
    (e : AdmissibleSequence R M) (he : symbol e ≠ 0) :
    Submodule.span R (Set.range e.1) = ⊤ := by
  by_contra hspan
  obtain ⟨i, hi⟩ := exists_dependent_of_span_ne_top hM e hspan
  exact he (symbol_eq_zero_of_mem_spanBefore e i hi)

end Module.FiniteLength

end
