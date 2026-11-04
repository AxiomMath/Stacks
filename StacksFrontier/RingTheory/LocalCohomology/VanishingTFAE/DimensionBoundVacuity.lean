module

public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.DimensionBound

/-!
# The arithmetic-rank route to the dimension bound is vacuous

`StacksFrontier/RingTheory/LocalCohomology/VanishingTFAE/DimensionBound.lean` reduces the second
assertion of Stacks 0DXC — `cd(A, I) ≤ dim A` — to a hypothesis in two different ways:

* `Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_isLocalRing`, whose
  hypothesis is the bound itself for *local* rings; and
* `Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators`,
  whose hypothesis `hara` asks that in a local ring `B` of Krull dimension at most `e` the zero
  locus of *every* finitely generated ideal be cut out by at most `e` elements.

The second hypothesis is **false**, so that theorem can never be applied: it is refuted by the
smallest possible instance, a field with the unit ideal. A field has Krull dimension `0`, so
`e = 0` is admissible and the only family of at most `0` elements is the empty one, whose zero
locus is all of `Spec B`; but `V(⊤) = ∅` and `Spec B ≠ ∅`. The usual statement of Kronecker's
bound gives `dim B + 1` elements, not `dim B`, and the gap is exactly this degenerate case.

Consequently the only live route in the library to `cd(A, I) ≤ dim A`, and hence to the
unconditional first assertion of Stacks 0DXC
(`Stacks.LocalCohomology.localCohomologyModule_isZero_of_supportDim_lt_of_quotient_bound` with
its `hbound` discharged), is the *local* hypothesis, i.e. Grothendieck's vanishing theorem for
spectral spaces (Stacks 0A3G) or the implication (3) ⇒ (1) of Stacks 0DX7. Neither is available
here.

## Main results

* `Stacks.LocalCohomology.not_forall_exists_zeroLocus_generators_card_le` — the hypothesis
  `hara` of `cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators` is
  unsatisfiable at universe `0`, hence that theorem has no instances.

## References

* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9)
-/

@[expose] public noncomputable section

namespace Stacks.LocalCohomology

/-- **The arithmetic-rank hypothesis of
`Stacks.LocalCohomology.cohomologicalDimension_le_ringKrullDim_of_exists_zeroLocus_generators` is
false.** A field is local of Krull dimension `0`, and the unit ideal has empty zero locus, which
no family of `0` elements cuts out. So that reduction of Stacks 0DXC (2) is vacuous. -/
theorem not_forall_exists_zeroLocus_generators_card_le :
    ¬ ∀ (B : Type) [CommRing B] [IsLocalRing B] (J : Ideal B), J.FG → ∀ e : ℕ,
      ringKrullDim B ≤ (e : WithBot ℕ∞) → ∃ (n : ℕ) (g : Fin n → B), n ≤ e ∧
        PrimeSpectrum.zeroLocus ((Ideal.span (Set.range g) : Ideal B) : Set B) =
          PrimeSpectrum.zeroLocus ((J : Ideal B) : Set B) := by
  intro h
  obtain ⟨n, g, hn, hg⟩ := h (ZMod 2) ⊤ ⟨{1}, by simp⟩ 0
    (by rw [ringKrullDim_eq_zero_of_field (ZMod 2)]; norm_num)
  have hn0 : n = 0 := Nat.le_zero.mp hn
  subst hn0
  have hrange : Set.range g = ∅ := by
    rw [Set.range_eq_empty_iff]
    exact ⟨fun x => x.elim0⟩
  rw [hrange, Ideal.span_empty] at hg
  have hempty : PrimeSpectrum.zeroLocus ((⊤ : Ideal (ZMod 2)) : Set (ZMod 2)) = ∅ :=
    PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr rfl
  rw [hempty] at hg
  simp only [Submodule.bot_coe, PrimeSpectrum.zeroLocus_singleton_zero] at hg
  exact (Set.univ_eq_empty_iff.mp hg).false (Classical.arbitrary (PrimeSpectrum (ZMod 2)))

end Stacks.LocalCohomology

end
