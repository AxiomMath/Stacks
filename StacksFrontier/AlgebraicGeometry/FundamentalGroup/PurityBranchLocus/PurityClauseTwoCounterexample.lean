module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Clause (2) of [Stacks, Tag 0BMA] is false as literally stated

Clause (2) of [Stacks, Tag 0BMA] reads: let `(A, 𝔪)` be a regular local ring of dimension
`d ≥ 2`; then any finite `A → B` with `B` normal which induces a finite étale morphism on
punctured spectra is étale. As stated this is false, for every such `A`: the residue field
`B = A ⧸ 𝔪` is a finite `A`-algebra and a field, hence a normal ring; its spectrum is the single
point lying over `𝔪`, so its preimage of the punctured spectrum `U` is empty and
`Spec B ×_X U → U` is (vacuously) finite étale; but `A` is a domain with `𝔪 ≠ 0`, so `A ⧸ 𝔪` is
not torsion-free, hence not flat, hence not étale over `A`.

The statements below use exactly the spelling of the corrected clause (2),
`Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_two_le_ringKrullDim`: `A` regular local with
`2 ≤ ringKrullDim A`, `B` with `Module.Finite A B` and `IsNormalRing B`, étaleness over the
punctured spectrum as
`Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_ Stacks.puncturedSpectrum A)`, and the
conclusion `Algebra.Etale A B`. That declaration adds the hypothesis `Module.IsTorsionFree A B`,
which is the one `A ⧸ 𝔪` violates.

## Main results

* `Stacks.PurityDimensionTwo.quotient_maximalIdeal_counterexample_clauseTwo` — for every regular
  local ring `A` of dimension at least two, `A ⧸ 𝔪` satisfies all hypotheses of the literal
  clause (2) (finite, normal, empty preimage of the punctured spectrum, étale there) and is not
  étale over `A`.
* `Stacks.PurityDimensionTwo.not_forall_etale_of_isNormalRing_of_two_le_ringKrullDim` — the
  literal clause (2) fails for every regular local ring `A` of dimension at least two.

## References

* [Stacks Project, Tag 0BMA](https://stacks.math.columbia.edu/tag/0BMA)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.PurityDimensionTwo

variable (A : Type u) [CommRing A]

/-- The residue ring `A ⧸ 𝔪` of a local ring is a normal ring: it is a field, and a field is an
integrally closed domain. -/
theorem isNormalRing_quotient_maximalIdeal [IsLocalRing A] :
    IsNormalRing (A ⧸ maximalIdeal A) := by
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  exact IsNormalRing.of_isIntegrallyClosed _

/-- For a local ring `A`, no point of `Spec (A ⧸ 𝔪)` maps into the punctured spectrum of `A`:
the only prime of `A ⧸ 𝔪` is `0`, whose contraction to `A` is `𝔪`. -/
theorem isEmpty_preimage_puncturedSpectrum_quotient_maximalIdeal [IsLocalRing A] :
    IsEmpty ↥(Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A))) ⁻¹ᵁ
      Stacks.puncturedSpectrum A) := by
  refine ⟨fun ⟨x, hx⟩ => hx ?_⟩
  ext1
  change Ideal.comap (algebraMap A (A ⧸ maximalIdeal A)) x.asIdeal = maximalIdeal A
  refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.comap _ (hK := x.isPrime)).ne_top)
    fun a ha => ?_
  change algebraMap A (A ⧸ maximalIdeal A) a ∈ x.asIdeal
  rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact x.asIdeal.zero_mem

/-- For a local ring `A`, `Spec (A ⧸ 𝔪) ⟶ Spec A` is étale over the punctured spectrum, vacuously:
the preimage of the punctured spectrum is empty. -/
theorem etale_restrict_puncturedSpectrum_quotient_maximalIdeal [IsLocalRing A] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A))) ∣_
      Stacks.puncturedSpectrum A) := by
  have : IsEmpty (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A))) ⁻¹ᵁ
      Stacks.puncturedSpectrum A).toScheme :=
    isEmpty_preimage_puncturedSpectrum_quotient_maximalIdeal A
  infer_instance

/-- For a local domain `A` which is not a field, `A ⧸ 𝔪` is not étale over `A`: a nonzero
`x ∈ 𝔪` is a nonzerodivisor of `A` which kills `A ⧸ 𝔪 ≠ 0`, so `A ⧸ 𝔪` is not torsion-free,
hence not flat, over `A`. -/
theorem not_etale_quotient_maximalIdeal [IsLocalRing A] [IsDomain A] (hA : ¬ IsField A) :
    ¬ Algebra.Etale A (A ⧸ maximalIdeal A) := by
  intro h
  have hne : maximalIdeal A ≠ ⊥ := fun h0 => hA ((isField_iff_maximalIdeal_eq).mpr h0)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hreg : IsSMulRegular (A ⧸ maximalIdeal A) x :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero hx0)
  have h1 : x • (1 : A ⧸ maximalIdeal A) = x • 0 := by
    rw [smul_zero, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hxm
  exact one_ne_zero (hreg h1)

/-- **Clause (2) of [Stacks, Tag 0BMA] as literally stated is false: the residue field is a
counterexample.** Let `A` be a regular local ring of dimension at least two and `B = A ⧸ 𝔪`.
Then `B` is a finite `A`-algebra and a normal ring, the preimage of the punctured spectrum `U`
under `Spec B ⟶ Spec A` is empty (so `Spec B ×_X U = ∅`), and `Spec B ⟶ Spec A` is étale over
`U` (it is finite everywhere); but `A → B` is not étale. These are the hypotheses of clause (2)
in the spelling of `Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_two_le_ringKrullDim`
without its added hypothesis `Module.IsTorsionFree A B`, which `A ⧸ 𝔪` violates. -/
@[stacks 0BMA "clause (2) as literally stated is false: for every regular local ring `A` with \
`2 ≤ ringKrullDim A`, `B = A ⧸ 𝔪` is a finite `A`-algebra and a normal ring (`IsNormalRing`), \
the preimage of the punctured spectrum under `Spec B ⟶ Spec A` is empty, so the induced morphism \
over the punctured spectrum is finite étale, but `A → B` is not étale (`A ⧸ 𝔪` is not even \
torsion-free over `A`). This is why the clause-(2) declaration \
`Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_two_le_ringKrullDim` carries the extra \
hypothesis `Module.IsTorsionFree A B`."]
theorem quotient_maximalIdeal_counterexample_clauseTwo [IsRegularLocalRing A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    Module.Finite A (A ⧸ maximalIdeal A) ∧ IsNormalRing (A ⧸ maximalIdeal A) ∧
      IsEmpty ↥(Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A))) ⁻¹ᵁ
        Stacks.puncturedSpectrum A) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ maximalIdeal A))) ∣_
        Stacks.puncturedSpectrum A) ∧
      ¬ Algebra.Etale A (A ⧸ maximalIdeal A) := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  refine ⟨inferInstance, isNormalRing_quotient_maximalIdeal A,
    isEmpty_preimage_puncturedSpectrum_quotient_maximalIdeal A,
    etale_restrict_puncturedSpectrum_quotient_maximalIdeal A,
    not_etale_quotient_maximalIdeal A fun hF => ?_⟩
  have h0 : ringKrullDim A = 0 := ringKrullDim_eq_zero_of_isField hF
  rw [h0] at hdim
  exact absurd hdim (by decide)

/-- **The literal clause (2) of [Stacks, Tag 0BMA] fails for every regular local ring of
dimension at least two.** It is not true that every finite `A`-algebra `B` which is a normal ring
and is étale over the punctured spectrum of `A` is étale over `A`; the witness is `B = A ⧸ 𝔪`,
see `quotient_maximalIdeal_counterexample_clauseTwo`. -/
theorem not_forall_etale_of_isNormalRing_of_two_le_ringKrullDim [IsRegularLocalRing A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    ¬ ∀ (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B], IsNormalRing B →
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_ Stacks.puncturedSpectrum A) →
      Algebra.Etale A B := by
  intro H
  obtain ⟨-, hB, -, het, hnot⟩ := quotient_maximalIdeal_counterexample_clauseTwo A hdim
  exact hnot (H (A ⧸ maximalIdeal A) hB het)

end Stacks.PurityDimensionTwo
