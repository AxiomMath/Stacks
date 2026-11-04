module

public import StacksFrontier.RingTheory.Regular.LocallySpanned
public import StacksFrontier.RingTheory.Regular.Quasiregular
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic

/-!
# An ideal spanned by a quasi-regular sequence is a quasi-regular ideal

The quasi-regular ideals of [Stacks, Tag 07CV] (4) are defined by a condition that is local on
the zero locus: at every prime containing the ideal some principal localization has the extended
ideal spanned by a quasi-regular sequence. An ideal which is spanned by a quasi-regular sequence
satisfies that condition at every prime, with the trivial principal localization as the witness.

## Main results

* `Quasiregular.isQuasiregularIdeal_span_range`: the span of a quasi-regular sequence is a
  quasi-regular ideal.

## References

* [Stacks Project, Definition 10.69.1 (Tag 07CV)](https://stacks.math.columbia.edu/tag/07CV)
-/

@[expose] public section

universe u

namespace Quasiregular

/-- The ideal spanned by a quasi-regular sequence `f` is a quasi-regular ideal. -/
theorem isQuasiregularIdeal_span_range {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (hf : RingTheory.Sequence.IsQuasiRegular R (List.ofFn f)) :
    IsQuasiregularIdeal' (Ideal.span (Set.range f)) := by
  show IsQuasiregularIdeal (Ideal.span (Set.range f))
  rw [Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy]
  intro p _
  refine ⟨1, p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top, r,
    fun i => algebraMap R (Localization.Away (1 : R)) (f i), ?_, ?_⟩
  · have _ : Module.Flat R (Localization.Away (1 : R)) :=
      IsLocalization.flat _ (Submonoid.powers (1 : R))
    have hqr := RingTheory.Sequence.IsQuasiRegular.of_flat_of_isBaseChange
      (N := Localization.Away (1 : R))
      (IsBaseChange.linearMap (R := R) (S := Localization.Away (1 : R))) (rs := List.ofFn f) hf
    rw [List.map_ofFn] at hqr
    simpa only [Function.comp_def] using hqr
  · rw [Ideal.map_span, ← Set.range_comp]
    rfl

end Quasiregular

end
