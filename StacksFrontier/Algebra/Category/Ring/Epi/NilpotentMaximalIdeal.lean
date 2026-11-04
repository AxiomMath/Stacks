module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import StacksCore.RingTheory.Nakayama
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic

/-!
# Epimorphisms out of a local ring with nilpotent maximal ideal

A ring epimorphism `R → S` out of a local ring `R` whose maximal ideal `𝔪` is nilpotent (for
instance an Artinian local ring) is surjective. Base changing to the residue field, the map
`R/𝔪 → S/𝔪S` is an epimorphism out of a field, hence surjective, that is `S = R + 𝔪S`; as `𝔪` is
nilpotent, Nakayama's lemma in the form of Stacks 00DV (11) gives `S = R`.

This is the algebraic step of the proof of Stacks 06S1.

## Main results

* `Algebra.IsEpi.surjective_algebraMap_of_isNilpotent_maximalIdeal`: an epimorphism out of a
  local ring with nilpotent maximal ideal is surjective.

## References

* [Stacks Project, Tag 06S1](https://stacks.math.columbia.edu/tag/06S1)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

namespace Algebra.IsEpi

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The composite of an epimorphism `R → S` with a quotient map `S → S ⧸ J` is an epimorphism. -/
theorem quotient (J : Ideal S) [Algebra.IsEpi R S] : Algebra.IsEpi R (S ⧸ J) :=
  (Algebra.isEpi_iff_forall_one_tmul_eq R _).2 fun x ↦ by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa using congrArg (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J)
      (Ideal.Quotient.mkₐ R J)) ((Algebra.isEpi_iff_forall_one_tmul_eq R S).1 ‹_› s)

/-- **An epimorphism out of a local ring with nilpotent maximal ideal is surjective.** The map
`R/𝔪 → S/𝔪S` is an epimorphism out of a field, so `S = R + 𝔪S`, and Nakayama's lemma for the
nilpotent ideal `𝔪` (Stacks 00DV (11)) gives `S = R`. -/
theorem surjective_algebraMap_of_isNilpotent_maximalIdeal [IsLocalRing R] [Algebra.IsEpi R S]
    (hm : IsNilpotent (IsLocalRing.maximalIdeal R)) : Function.Surjective (algebraMap R S) := by
  set m := IsLocalRing.maximalIdeal R
  set J := m.map (algebraMap R S)
  let := Ideal.Quotient.field m
  have := quotient (R := R) J
  have : Algebra.IsEpi (R ⧸ m) (S ⧸ J) := tower_top (A := R)
  refine LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent m (Algebra.linearMap R S) hm
    fun x ↦ ?_
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨r, hr⟩ := surjective_algebraMap_of_field (k := R ⧸ m) (Ideal.Quotient.mk J s)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨r, (Submodule.Quotient.eq _).2 ?_⟩
  rw [Ideal.smul_top_eq_map]
  exact Ideal.Quotient.eq.1 hr

end Algebra.IsEpi

end
