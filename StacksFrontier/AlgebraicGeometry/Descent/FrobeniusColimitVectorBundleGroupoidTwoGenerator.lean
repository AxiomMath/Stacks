module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidSquare
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquareIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorSquare
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidFibrationStack

/-!
# Condition (3) of Stacks 0EX9 for Tag 0EXE at the squares of Example 0EVH, from the model

Condition (3) of Stacks 0EX9 for the shape of Example 0EVH,
`AlgebraicGeometry.BigHOver.IsTwoGeneratorAlmostBlowUpStack`, ranges over the squares of
`(Sch/S)_h` whose underlying pair of morphisms of schemes is *isomorphic* to the model pair
`Proj (A[T₀,T₁]/(f₂T₀ - f₁T₁)) ⟶ Spec A ⟵ Spec (A/(f₁,f₂))`, over an arbitrary base `S`.  The
comparison functor that Stacks Tag 0EXD is about,
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison`, lives on the model square itself.
This file carries the second to the first:

* the exceptional corner of a square of the site is identified with the exceptional line of the
  model, both being fibre products (`CategoryTheory.IsPullback.of_iso` and
  `CategoryTheory.IsPullback.isoIsPullback`);
* the comparison functor at the underlying square of schemes is then an equivalence by
  `AlgebraicGeometry.isEquivalence_frobeniusColimitVectorBundlesComparison_of_isIso`;
* and the comparison functor of the category fibred in groupoids is an equivalence by
  `isEquivalence_twoFibreProductComparison_frobeniusVectorBundleGroupoidFibration`.

## Main results

* `isTwoGeneratorAlmostBlowUpStack_frobeniusVectorBundleGroupoidFibration_of_model`: condition
  (3) of Stacks 0EX9 for the shape of Example 0EVH holds for the category fibred in groupoids of
  Stacks Tag 0EXE as soon as the comparison functor
  `AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` is an equivalence for every ring in
  which `p` vanishes and every pair of elements of it.  No `@[stacks]` attribute appears here:
  the hypothesis is the content of Stacks Tag 0EXD.
* `isStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_conditions`: the main clause of
  Stacks Tag 0EXE from condition (1) of Stacks 0EX9, condition (2), the 0EVG half of condition
  (3), and the equivalence of the model comparison functor of Stacks Tag 0EXD.
  This is the assembly the registration of Stacks Tag 0EXE instantiates; it carries no
  `@[stacks]` attribute itself.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius Stacks.AlmostBlowUp

namespace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

/-- A ring whose spectrum is in characteristic `p` has `p = 0`. -/
lemma natCast_eq_zero_of_isInCharacteristic_spec (A : Type u) [CommRing A]
    (h : IsInCharacteristic (Spec (.of A)) p) : (p : A) = 0 := by
  have h' : (p : Γ(Spec (.of A), ⊤)) = 0 := h
  have h2 := congrArg (Scheme.ΓSpecIso (.of A)).hom.hom h'
  rwa [map_natCast, map_zero] at h2

/-- **Condition (3) of Stacks 0EX9 for the shape of Example 0EVH, for the category fibred in
groupoids of Stacks Tag 0EXE, from the comparison functor of the model square.**  If for every
ring `A` in which `p` vanishes and every `f₁, f₂ ∈ A` the comparison functor
`AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison` of the square of Example 0EVH is an
equivalence, then so is the comparison functor `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` at every square of
`(Sch/S)_h` of that shape. -/
theorem isTwoGeneratorAlmostBlowUpStack_frobeniusVectorBundleGroupoidFibration_of_model
    (hmodel : ∀ (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0),
      (twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).IsEquivalence) :
    BigHOver.IsTwoGeneratorAlmostBlowUpStack B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS) := by
  intro X X' Z E b z d e I _ _ _ hsq hpb hshape
  obtain ⟨A, hA, f₁, f₂, hm⟩ := hshape
  let := hA
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  obtain ⟨iX, iX', iZ, hb, hz⟩ := hm
  have hpA : (p : A) = 0 := natCast_eq_zero_of_isInCharacteristic_spec p A
    (isInCharacteristic_of_hom iX.inv p (isInCharacteristic_bigHOver B S hS p hpS X))
  have h' : IsPullback ((BigHOver.toScheme B S hS).map d ≫ iX'.hom)
      ((BigHOver.toScheme B S hS).map e ≫ iZ.hom) (modificationToBase A f₁ f₂)
      (centerToBase A f₁ f₂) :=
    hpb.flip.of_iso (Iso.refl _) iX' iZ iX (by simp) (by simp) hb hz
  let iE := h'.isoIsPullback _ _ (twoGenerator_isPullback A f₁ f₂)
  refine isEquivalence_twoFibreProductComparison_frobeniusVectorBundleGroupoidFibration hpS
    b z d e hsq hpb.w.symm ?_
  exact isEquivalence_frobeniusColimitVectorBundlesComparison_of_isIso p
    ((BigHOver.toScheme B S hS).map b) ((BigHOver.toScheme B S hS).map z)
    ((BigHOver.toScheme B S hS).map d) ((BigHOver.toScheme B S hS).map e)
    (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂)
    (exceptionalToCenter A f₁ f₂)
    (isInCharacteristic_bigHOver B S hS p hpS X) (isInCharacteristic_bigHOver B S hS p hpS X')
    (isInCharacteristic_bigHOver B S hS p hpS Z) (isInCharacteristic_bigHOver B S hS p hpS E)
    (isInCharacteristic_spec A p hpA)
    (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
    hpb.w.symm (twoGenerator_isPullback A f₁ f₂).w iX.hom iX'.hom iZ.hom iE.hom hb hz
    (h'.isoIsPullback_hom_fst _ _ (twoGenerator_isPullback A f₁ f₂)).symm
    (h'.isoIsPullback_hom_snd _ _ (twoGenerator_isPullback A f₁ f₂)).symm
    (hmodel A f₁ f₂ hpA)

/-- **The main clause of Stacks Tag 0EXE from its inputs.**  The category fibred in groupoids of
finite locally free `colim_F 𝒪`-modules over the big h category over a scheme `S` in
characteristic `p` is a stack in groupoids for the h topology as soon as it satisfies condition (1)
of Stacks 0EX9, condition (2), the 0EVG half of condition (3), and the comparison functor of the
model square of Example 0EVH is an equivalence for every ring in which `p` vanishes. -/
theorem isStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_conditions
    (h1 : BigHOver.IsZariskiStackInGroupoids B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS))
    (h2 : BigHOver.IsAffineFlatProperFinitePresentationDescent B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS))
    (h3 : BigHOver.IsOneGeneratorAlmostBlowUpStack B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS))
    (hmodel : ∀ (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0),
      (twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).IsEquivalence) :
    (frobeniusVectorBundleGroupoidFibration B S hS p hpS).IsStackInGroupoids.{u + 1}
      (BigHOver.topology B S hS) :=
  isStackInGroupoids_frobeniusVectorBundleGroupoidFibration_of_generatorSquares B S hS p hpS
    h1 h2 h3
    (isTwoGeneratorAlmostBlowUpStack_frobeniusVectorBundleGroupoidFibration_of_model B S hS p hpS
      hmodel)

end AlgebraicGeometry

end
