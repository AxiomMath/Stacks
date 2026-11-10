module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The complement of a nonempty open of the affine line

Let `K` be a field and `j : V ⟶ 𝔸¹_K = Spec K[X]` an open immersion with `V` nonempty. The
complement of the image of `j` is the image of a closed immersion `Spec (K[X] ⧸ I) ⟶ 𝔸¹_K`,
`I` the ideal of polynomials vanishing on it, and `Spec (K[X] ⧸ I)` is reduced and finite over
`K`.

## Main results

* `Polynomial.module_finite_quotient_of_ne_bot`: `K[X] ⧸ I` is finite over `K` for a nonzero
  ideal `I`.
* `AlgebraicGeometry.exists_closedImmersion_compl_range_affineLine`: the complement of a nonempty
  open of `𝔸¹_K` is the image of a closed immersion from a reduced scheme finite over `K`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u

/-- **`K[X] ⧸ I` is finite over `K` for a nonzero ideal `I`.** -/
theorem Polynomial.module_finite_quotient_of_ne_bot (K : Type*) [Field K] (I : Ideal K[X])
    (hI : I ≠ ⊥) : Module.Finite K (K[X] ⧸ I) := by
  obtain ⟨g, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  have hg : g ≠ 0 := fun h => hI (by rw [h, Submodule.span_singleton_eq_bot.2 rfl])
  exact (AdjoinRoot.powerBasis hg).finite

namespace AlgebraicGeometry

/-- **The complement of a nonempty open of `𝔸¹_K` is a reduced closed subscheme finite over
`K`**: for an open immersion `j : V ⟶ Spec K[X]` with `V` nonempty there is a closed immersion
`i : Z ⟶ Spec K[X]` with `Z` reduced, `Z` finite over `K`, and image the complement of the image
of `j`. -/
theorem exists_closedImmersion_compl_range_affineLine (K : Type u) [Field K] {V : Scheme.{u}}
    [Nonempty V] (jV : V ⟶ Spec (.of K[X])) [IsOpenImmersion jV] :
    ∃ (Z : Scheme.{u}) (iZ : Z ⟶ Spec (.of K[X])), IsClosedImmersion iZ ∧ IsReduced Z ∧
      IsFinite (iZ ≫ Spec.map (CommRingCat.ofHom (algebraMap K K[X]))) ∧
      Set.range jV.base = (Set.range iZ.base)ᶜ := by
  let C : Set (PrimeSpectrum K[X]) := (Set.range jV.base)ᶜ
  have hC : IsClosed C := jV.isOpenEmbedding.isOpen_range.isClosed_compl
  let I := PrimeSpectrum.vanishingIdeal C
  have hZ : PrimeSpectrum.zeroLocus (I : Set K[X]) = C := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hC.closure_eq]
  have hI : I ≠ ⊥ := by
    intro h
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv : jV.base v ∈ C := by
      rw [← hZ, h]
      simp only [Submodule.bot_coe, PrimeSpectrum.zeroLocus_singleton_zero]
      exact Set.mem_univ _
    exact hv ⟨v, rfl⟩
  have : _root_.IsReduced (K[X] ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).1 (PrimeSpectrum.isRadical_vanishingIdeal C)
  have : _root_.IsReduced (CommRingCat.of (K[X] ⧸ I)) := ‹_root_.IsReduced (K[X] ⧸ I)›
  have : Module.Finite K (K[X] ⧸ I) := Polynomial.module_finite_quotient_of_ne_bot K I hI
  refine ⟨Spec (.of (K[X] ⧸ I)), Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)),
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, inferInstance, ?_, ?_⟩
  · rw [← Spec.map_comp, IsFinite.SpecMap_iff]
    change (algebraMap K (K[X] ⧸ I)).Finite
    exact RingHom.finite_algebraMap.2 inferInstance
  · change Set.range jV.base = (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)))ᶜ
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, hZ, compl_compl]
    rfl

end AlgebraicGeometry
