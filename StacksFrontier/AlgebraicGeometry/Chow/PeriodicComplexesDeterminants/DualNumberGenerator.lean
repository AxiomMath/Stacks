module

public import Mathlib.RingTheory.DualNumber
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.DimensionLeOne

/-!
# A generator for the determinant of the dual numbers

Let `k` be a field and regard the dual-number ring `k[ε]` as a module over `k`. It has length
two, and the admissible sequence `(ε, 1)` gives a generator of its determinant.

## Main definitions

* `DualNumber.dualGenerator` is the admissible sequence `(ε, 1)`.

## Main results

* `DualNumber.dualNumberModuleLength` computes the length of `k[ε]` over `k`.
* `DualNumber.span_symbol_dualGenerator_eq_top` says that the symbol of `(ε, 1)` spans the
  determinant.

## Implementation notes

Over the field `k` the admissibility condition is vacuous, so this is the `k`-linear variant
of the generator in Stacks Tag 02PP. The source's statement, over the dual-number ring, is
`DualNumber.span_symbol_dualNumberSequence_eq_top`.

The dual numbers and the class `ε` are Mathlib's `DualNumber k` and `DualNumber.eps`. The
equality `DualNumber.dualNumberModuleLength` is what lets the displayed two-term sequence be
indexed by the module length.

## References

* [Stacks Project, Tag 02PP](https://stacks.math.columbia.edu/tag/02PP)
-/

@[expose] public section

noncomputable section

namespace DualNumber

open Module.FiniteLength

universe u

/-- The dual numbers have length two as a module over their coefficient field, in `ℕ∞`. -/
private theorem length_dualNumber (k : Type u) [Field k] : Module.length k (DualNumber k) = 2 := by
  change Module.length k (k × k) = 2
  norm_num [Module.length_prod, Module.length_eq_one]

/-- The dual numbers have length two as a module over their coefficient field. -/
theorem dualNumberModuleLength (k : Type u) [Field k] :
    moduleLength k (DualNumber k) = 2 := by
  simp [moduleLength, length_dualNumber]

/-- The two entries `(ε, 1)`, indexed by the module length of the dual numbers. -/
def dualGeneratorEntries (k : Type u) [Field k] :
    Fin (moduleLength k (DualNumber k)) → DualNumber k :=
  fun i ↦ Fin.cases DualNumber.eps (fun _ ↦ 1) (Fin.cast (dualNumberModuleLength k) i)

/-- The sequence `(ε, 1)` is admissible. -/
theorem dualGeneratorEntries_isAdmissible (k : Type u) [Field k] :
    IsAdmissibleSequence (R := k) (dualGeneratorEntries k) := by
  intro i r hr
  simp only [IsLocalRing.maximalIdeal_eq_bot, Submodule.mem_bot] at hr
  subst r
  simp [spanBefore]

/-- The admissible sequence `(ε, 1)` in the dual numbers. -/
def dualGenerator (k : Type u) [Field k] : AdmissibleSequence k (DualNumber k) :=
  ⟨dualGeneratorEntries k, dualGeneratorEntries_isAdmissible k⟩

/-- The entries `(ε, 1)` span the dual numbers over the coefficient field. -/
private lemma dualGeneratorEntries_span_eq_top (k : Type u) [Field k] :
    Submodule.span k (Set.range (dualGeneratorEntries k)) = ⊤ := by
  apply top_unique
  intro x _
  rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
  apply add_mem
  · rw [← TrivSqZeroExt.algebraMap_eq_inl k k, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨1, by simp [dualNumberModuleLength]⟩, rfl⟩)
  · rw [DualNumber.inr_eq_smul_eps]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨0, by simp [dualNumberModuleLength]⟩,
        by simp [dualGeneratorEntries]⟩)

/-- The symbol `[ε, 1]` generates the determinant of the dual numbers regarded as a vector space
over `k`. This is the `k`-linear variant of the generator in Stacks Tag 02PP; the statement over
the dual numbers themselves is `DualNumber.span_symbol_dualNumberSequence_eq_top`. -/
theorem span_symbol_dualGenerator_eq_top (k : Type u) [Field k] :
    (IsLocalRing.ResidueField k) ∙ symbol (dualGenerator k) = ⊤ :=
  span_symbol_eq_top (by
    simp [← Module.length_ne_top_iff, length_dualNumber])
    (dualGenerator k) (dualGeneratorEntries_span_eq_top k)

end DualNumber
