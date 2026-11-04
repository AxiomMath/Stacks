module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectGlueAssembly
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectGlueRefine
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorLocalCase
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorRestrictTransfer
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageLocalCase

/-!
# Stacks Tag 0EXD

Let `p` be a prime, `A` a ring in which `p` vanishes and `f₁, f₂ ∈ A`.  For the almost blowup
square of [Stacks, Example 0EVH] in characteristic `p`,

```
Proj ((A/(f₁,f₂))[T₀,T₁]) ⟶ Proj (A[T₀,T₁]/(f₂T₀ - f₁T₁))
          ↓                             ↓
   Spec (A/(f₁,f₂))        ⟶          Spec A
```

the comparison functor
`G : colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`,
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison`, on the finite locally free modules over
the Frobenius colimits of the structure sheaves, is an equivalence.

## Main results

* `AlgebraicGeometry.essSurj_twoGeneratorFrobeniusColimitComparison`: essential surjectivity.
* `AlgebraicGeometry.isEquivalence_twoGeneratorFrobeniusColimitComparison`: **Tag 0EXD.**

## Implementation notes

Full faithfulness is `AlgebraicGeometry.fullyFaithful_twoGeneratorFrobeniusColimitComparison`.
Essential surjectivity follows the source: over a cover of `Spec A` by basic opens the centre
component is free (`AlgebraicGeometry.exists_cover_free_center_twoGeneratorFrobeniusColimitLoc`);
there the triple is in the essential image by the local case
(`AlgebraicGeometry.mem_essImage_twoGeneratorFrobeniusColimitComparison_of_free_center`, which
rests on the ordinary local case `Stacks.AlmostBlowUp.exists_vect_iso_of_free_center`), read over
the basic open by `AlgebraicGeometry.mem_essImage_frobeniusColimitComparisonRestrict_of_loc`; the
local solutions are refined to free ones over basic opens by
`AlgebraicGeometry.exists_cover_free_of_mem_essImage_restrict`, and glued by
`AlgebraicGeometry.mem_essImage_frobeniusColimitVectorBundlesComparison_of_cover`, whose full
faithfulness hypotheses over the pairwise and triple intersections — again basic opens — are
`AlgebraicGeometry.fullyFaithful_frobeniusColimitComparisonRestrict_of_eq_basicOpen`.  No
Noetherian hypothesis and no hypothesis beyond those of the source appears.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Example 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius Stacks.AlmostBlowUp

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A) (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0)

/-- **The essential surjectivity half of [Stacks, Tag 0EXD]**: every object of the categorical
fibre product of the square of [Stacks, Example 0EVH] in characteristic `p` is, up to isomorphism,
the image of a finite locally free `colim_F 𝒪_{Spec A}`-module. -/
theorem essSurj_twoGeneratorFrobeniusColimitComparison :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).EssSurj := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  refine ⟨fun T => ?_⟩
  obtain ⟨σ, a, hspan, hfree⟩ := exists_cover_free_center_twoGeneratorFrobeniusColimitLoc A f₁ f₂ p
    hpA T
  have hloc : ∀ s, (frobeniusColimitComparisonRestrict p (modificationToBase A f₁ f₂)
        (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
        (isInCharacteristic_spec A p hpA)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (twoGenerator_isPullback A f₁ f₂).w (PrimeSpectrum.basicOpen (a s))).essImage
      ((frobeniusColimitLocRestrict p (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
        (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (twoGenerator_isPullback A f₁ f₂).w (PrimeSpectrum.basicOpen (a s))).obj T) := by
    intro s
    obtain ⟨I, hI, hiso⟩ := hfree s
    exact mem_essImage_frobeniusColimitComparisonRestrict_of_loc A f₁ f₂ p hpA (a s) _ rfl T
      (mem_essImage_twoGeneratorFrobeniusColimitComparison_of_free_center
        (Localization.Away (a s)) _ _ p (natCast_eq_zero_of_algebra A p hpA _) _ I hiso)
  have hcov : ⨆ s, PrimeSpectrum.basicOpen (a s) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan
  obtain ⟨J, W, m, hWB, hWcov, hβ⟩ := exists_cover_free_of_mem_essImage_restrict p
    (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂)
    (exceptionalToCenter A f₁ f₂) (isInCharacteristic_spec A p hpA)
    (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
    (twoGenerator_isPullback A f₁ f₂).w PrimeSpectrum.isBasis_basic_opens
    (fun s => PrimeSpectrum.basicOpen (a s)) hcov T hloc
  choose x hx using hWB
  have hp : p.Prime := Fact.out
  have h2 : ∀ j k, W j ⊓ W k = PrimeSpectrum.basicOpen (x j * x k) := fun j k => by
    rw [← hx j, ← hx k]
    exact (PrimeSpectrum.basicOpen_mul _ _).symm
  have h3 : ∀ j k l, W j ⊓ W k ⊓ W l = PrimeSpectrum.basicOpen (x j * x k * x l) :=
    fun j k l => by
      rw [h2, ← hx l]
      exact (PrimeSpectrum.basicOpen_mul _ _).symm
  exact mem_essImage_frobeniusColimitVectorBundlesComparison_of_cover p _ _ _ _ _ _ _ _ _ W hWcov m
    T (fun j => (hβ j).some)
    (fun j k => (fullyFaithful_frobeniusColimitComparisonRestrict_of_eq_basicOpen A f₁ f₂ p hpA hp
      _ _ (h2 j k)).1)
    (fun j k => (fullyFaithful_frobeniusColimitComparisonRestrict_of_eq_basicOpen A f₁ f₂ p hpA hp
      _ _ (h2 j k)).2)
    (fun j k l => (fullyFaithful_frobeniusColimitComparisonRestrict_of_eq_basicOpen A f₁ f₂ p hpA
      hp _ _ (h3 j k l)).2)

/-- **[Stacks, Tag 0EXD].** Let `p` be a prime and consider the almost blowup square `X, X', Z, E`
of [Stacks, Example 0EVH] in characteristic `p`, i.e. over a ring `A` in which `p` vanishes, with
arbitrary `f₁, f₂ ∈ A`.  Then the functor
`G : colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`
is an equivalence. -/
@[stacks 0EXD]
theorem isEquivalence_twoGeneratorFrobeniusColimitComparison :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).IsEquivalence := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  obtain ⟨hfull, hfaith⟩ :=
    fullyFaithful_twoGeneratorFrobeniusColimitComparison p Fact.out A f₁ f₂ hpA
  have := essSurj_twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA
  exact { }

end AlgebraicGeometry

end
