module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.InitialSpan

/-!
# The determinant of a finite length module has dimension at most one

The determinant of a finite-length module over a local ring is spanned over the residue
field by the symbol of any single admissible sequence that spans the module, and is zero
when no admissible sequence spans. Either way its dimension is at most one.

## Main results

* `Module.FiniteLength.span_symbol_eq_top` states that the symbol of a spanning admissible
  sequence generates the determinant.
* `Module.FiniteLength.finrank_determinant_le_one` bounds the dimension of the determinant
  by one.

## Implementation notes

The dimension appearing in the source is expressed using `Module.finrank`, and the
finite-length hypothesis, which is part of the standing notation of the source, is made
explicit. The generator assertion is the intermediate conclusion that Tag 02P9 needs, and
Tag 02P9 restates it verbatim; the two statements are the same, so one declaration carries
both tags.

The proof of the generator assertion compares an arbitrary admissible sequence with the
spanning one index by index: `symbol_mem_of_agree` makes the two agree on a longer and
longer prefix, using the unit-change relation to install the next entry and `move_entry`
to transport it into position by adjacent transpositions. Each step multiplies the symbol
by a unit of the residue field, so the symbol stays in the line spanned by the original
one.

## References

* [Stacks Project, Tag 02P7](https://stacks.math.columbia.edu/tag/02P7)
* [Stacks Project, Tag 02P9](https://stacks.math.columbia.edu/tag/02P9)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M]

/-- Membership in a line is transitive. -/
private lemma mem_span_singleton_trans {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    {x y z : V} (hxy : x ∈ K ∙ y) (hyz : y ∈ K ∙ z) : x ∈ K ∙ z :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr hyz hxy

/-- Move the entry at `i` left to position `j` using the adjacent-transposition relation,
keeping the span of the whole sequence, the entries before `j`, and the line spanned by the
symbol. -/
private lemma move_entry (e : AdmissibleSequence R M)
    (j i : Fin (moduleLength R M)) (hji : j.val ≤ i.val)
    (hi : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 i ∈ initialSpan (R := R) e.1 j.val) :
    ∃ f : AdmissibleSequence R M,
      initialSpan (R := R) f.1 (moduleLength R M) = initialSpan e.1 (moduleLength R M) ∧
      (∀ k, k.val < j.val → f.1 k = e.1 k) ∧ f.1 j = e.1 i ∧
      symbol f ∈ (IsLocalRing.ResidueField R) ∙ symbol e := by
  classical
  by_cases h : j = i
  · subst i
    exact ⟨e, rfl, fun _ _ ↦ rfl, rfl, Submodule.mem_span_singleton_self _⟩
  have hlt : j.val < i.val := by have := (fun heq ↦ h (Fin.ext heq) : j.val ≠ i.val); omega
  let b : Fin (moduleLength R M) := ⟨i.val - 1, by omega⟩
  have hbi : b.val + 1 = i.val := by dsimp [b]; omega
  have hjb : j.val ≤ b.val := by dsimp [b]; omega
  have ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 i ∈ initialSpan (R := R) e.1 b.val :=
    fun r hr ↦ initialSpan_mono e.1 hjb (hi r hr)
  let g : AdmissibleSequence R M := ⟨swapEntries e.1 i b, admissible_swap e i b hbi ha⟩
  have hg (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) :
      r • g.1 b ∈ initialSpan (R := R) g.1 j.val := by
    change r • swapEntries e.1 i b b ∈ initialSpan (R := R) (swapEntries e.1 i b) j.val
    rw [initialSpan_swap _ _ _ (by omega)]
    simpa [swapEntries] using hi r hr
  obtain ⟨f, hfspan, hfprev, hfj, hfsym⟩ := move_entry g j b hjb hg
  refine ⟨f, hfspan.trans ?_, ?_, ?_, ?_⟩
  · exact initialSpan_swap _ _ _ (by simp only [Fin.is_lt])
  · intro k hk
    rw [hfprev k hk]
    change swapEntries e.1 i b k = e.1 k
    have hki : k ≠ i := by intro h; subst k; omega
    have hkb : k ≠ b := by intro h; subst k; omega
    simp [swapEntries, Equiv.swap_apply_of_ne_of_ne hki hkb]
  · simpa [g, swapEntries] using hfj
  · exact mem_span_singleton_trans hfsym (symbol_swap_mem e i b hbi ha)
termination_by i.val

/-- Inductively match the target sequence entry by entry, keeping its symbol in the line
spanned by the symbol of the spanning sequence `f`. -/
private lemma symbol_mem_of_agree (e f : AdmissibleSequence R M)
    (hf : initialSpan (R := R) f.1 (moduleLength R M) = ⊤)
    (j : ℕ) (hj : j ≤ moduleLength R M) (hprev : ∀ k, k.val < j → f.1 k = e.1 k) :
    symbol e ∈ (IsLocalRing.ResidueField R) ∙ symbol f := by
  classical
  by_cases hjn : j = moduleLength R M
  · have hfe : f = e := Subtype.ext (funext fun k ↦ hprev k (hjn ▸ k.is_lt))
    subst f; exact Submodule.mem_span_singleton_self _
  let a : Fin (moduleLength R M) := ⟨j, by omega⟩
  have hp : initialSpan (R := R) f.1 j = initialSpan e.1 j := initialSpan_congr hprev
  by_cases hdep : e.1 a ∈ initialSpan (R := R) e.1 j
  · exact symbol_eq_zero_of_mem_spanBefore e a hdep ▸ Submodule.zero_mem _
  have hx : e.1 a ∉ initialSpan (R := R) f.1 j := hp ▸ hdep
  obtain ⟨i, unit, y, hji, hiy, hy⟩ := exists_unit_entry f hf (e.1 a) hx
  have hea (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) :
      r • e.1 a ∈ initialSpan (R := R) f.1 j := hp.symm ▸ e.2 a r hr
  have hadm := admissible_update f i (e.1 a) y unit hiy hy
    (fun r hr ↦ initialSpan_mono f.1 hji (hea r hr))
  let g : AdmissibleSequence R M := ⟨Function.update f.1 i (e.1 a), hadm⟩
  have hgspan : initialSpan (R := R) g.1 (moduleLength R M) = ⊤ :=
    (initialSpan_update f.1 i (e.1 a) y unit hiy hy _).trans hf
  have hgmem : symbol g ∈ (IsLocalRing.ResidueField R) ∙ symbol f :=
    (Submodule.smul_mem_iff_of_isUnit _ (unit.isUnit.map (IsLocalRing.residue R))).mp
      (symbol_unitChange f i unit (e.1 a) y hiy hy hadm ▸ Submodule.mem_span_singleton_self _)
  have hgadm (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) :
      r • g.1 i ∈ initialSpan (R := R) g.1 a.val := by
    change r • Function.update f.1 i (e.1 a) i ∈
      initialSpan (R := R) (Function.update f.1 i (e.1 a)) j
    rw [Function.update_self, initialSpan_update f.1 i (e.1 a) y unit hiy hy]
    exact hea r hr
  obtain ⟨f', hf'span, hf'prev, hf'a, hf'mem⟩ := move_entry g a i hji hgadm
  have hagree : ∀ k, k.val < j + 1 → f'.1 k = e.1 k := by
    intro k hk
    by_cases hka : k = a
    · subst k
      simpa [g] using hf'a
    · have hkj : k.val < j := by
        have : k.val ≠ a.val := fun heq ↦ hka (Fin.ext heq)
        dsimp [a] at this
        omega
      rw [hf'prev k hkj]
      change Function.update f.1 i (e.1 a) k = e.1 k
      rw [Function.update_of_ne (show k ≠ i by intro heq; subst k; omega), hprev k hkj]
  have ih := symbol_mem_of_agree e f' (hf'span.trans hgspan) (j + 1) (by omega) hagree
  exact mem_span_singleton_trans (mem_span_singleton_trans ih hf'mem) hgmem
termination_by moduleLength R M - j

/-- **Stacks Project, Tags 02P7 and 02P9.** The symbol of every admissible sequence that
spans a finite-length module generates its determinant over the residue field. -/
@[stacks 02P7 "generators", stacks 02P9 "generators"]
public theorem span_symbol_eq_top (_hM : IsFiniteLength R M)
    (e : AdmissibleSequence R M) (he : Submodule.span R (Set.range e.1) = ⊤) :
    (IsLocalRing.ResidueField R) ∙ symbol e = ⊤ := by
  apply eq_top_of_symbols_mem; intro f
  exact symbol_mem_of_agree f e ((initialSpan_all e.1).trans he) 0 (Nat.zero_le _)
    (fun _ h ↦ by omega)

/-- **Stacks Project, Tag 02P7.** The determinant of a finite-length module over a local
ring has dimension at most one over the residue field. -/
@[stacks 02P7]
public theorem finrank_determinant_le_one
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.finrank (IsLocalRing.ResidueField R) (determinant R M) ≤ 1 := by
  classical
  by_cases hex : ∃ e : AdmissibleSequence R M, Submodule.span R (Set.range e.1) = ⊤
  · obtain ⟨e, he⟩ := hex
    exact finrank_le_one (symbol e) fun x ↦
      Submodule.mem_span_singleton.mp (span_symbol_eq_top hM e he ▸ Submodule.mem_top)
  · have hz : (⊥ : Submodule (IsLocalRing.ResidueField R) (determinant R M)) = ⊤ := by
      apply eq_top_of_symbols_mem; intro e
      obtain ⟨i, hi⟩ := exists_dependent_of_span_ne_top hM e (fun he ↦ hex ⟨e, he⟩)
      exact symbol_eq_zero_of_mem_spanBefore e i hi ▸ Submodule.zero_mem _
    refine finrank_le_one (0 : determinant R M) fun x ↦ ⟨0, ?_⟩
    have hx : x ∈ (⊥ : Submodule (IsLocalRing.ResidueField R) (determinant R M)) :=
      hz.symm ▸ Submodule.mem_top
    simpa using ((Submodule.mem_bot (IsLocalRing.ResidueField R)).mp hx).symm

end Module.FiniteLength

end
