module

import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveRelativeDualityInputProof
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerClassMapStalks
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFlatLevelZeroFirstProjectionProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormStableCharNe
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLatticeInputProof

/-!
# Weil II from the absolute irreducibility of Laumon's Fourier family for `ℓ ≠ p`

This file assembles [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) as
`Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_absIrr`, but from the absolute irreducibility
of the Fourier family on the line only for `ℓ` prime to the characteristic,
`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput'`. In the proof of Weil II, L6 is used once,
in the equal absolute values of the fibres of the Fourier family
(`Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_absIrr'`), at the prime `ℓ` of the
theorem and the characteristic `p` of `k`, where `ℓ ≠ p`.

## Main results

* `Stacks.EtaleCohomology.laumonFibrePurityInput_of_absIrr'`: the purity of the fibres of the
  Fourier family from L6 for `ℓ ≠ p` and the lattice comparison.
* `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_absIrr'`.

## Implementation notes

The cohomology groups in the statement are those of
`Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_absIrr`, defined in the standard model
`HasDerivedCategory.standard` of the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **The purity of the fibres of the Fourier family from L6 for `ℓ ≠ p`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): as
`Stacks.EtaleCohomology.laumonFibrePurityInput_of_leaves'`, with the equal absolute values from
`Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_absIrr'`. -/
theorem laumonFibrePurityInput_of_absIrr' (hL6' : LaumonFourierLineAbsIrrInput'.{u})
    (hlat : LaumonFourierLineLatticeInput.{u}) : LaumonFibrePurityInput.{u} :=
  laumonFibrePurityInput_of_stable
    (laumonFibreStableReductionInput_of_inputs laumonFibrePureDescentInput
      laumonFibrePureConstituentInput laumonStableDecompositionInput)
    (laumonFourierEquinormStableInput_of_absIrr' hL6'
      (laumonFourierLineLisseFibreInput_of_lattice hlat) laumonFourierFamilyFibreInput
      laumonFourierFamilyFieldExtensionInput)
    laumonFibreReciprocityInput

section WeightBound

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) from the absolute irreducibility of
Laumon's Fourier family for `ℓ ≠ p`.**
Let `k` be a finite field with `p ^ q` elements, `k̄` an algebraic closure, `ℓ ≠ p` a prime,
`X` connected and separated of finite type over `k` with a compactification `j`, and
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` continuous, satisfying the conclusions of Deligne's conjecture along
every embedding `ι : ℚ_ℓ → ℂ`. Then for every `i` the eigenvalues of `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` (finite dimensional) are algebraic numbers of absolute value
`(p ^ q) ^ (w / 2)` along `ι` with `w ∈ ℤ`, `w ≤ i`; and if `X` is smooth and proper over `k`, then
`w = i`.

This is `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_absIrr` with
`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput` replaced by
`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput'`. -/
theorem LAdicSheaf.weightBound_of_absIrr' (hL6' : LaumonFourierLineAbsIrrInput'.{u})
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ)
    (hD : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) :
    (∀ (i : ℤ) (ι : ℚ_[ℓ] →+* ℂ),
      haveI : FiniteDimensional ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
            (LAdicSheaf.representationSheaf B X x ρ hρ) i) :=
        LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q
          hcard hℓ X f j _ i
      IsCharpolyMixedOfWeightLE (p ^ q) ι i
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom) ∧
    (IsProper f → Smooth f → ∀ (i : ℤ) (ι : ℚ_[ℓ] →+* ℂ),
      haveI : FiniteDimensional ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
            (LAdicSheaf.representationSheaf B X x ρ hρ) i) :=
        LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q
          hcard hℓ X f j _ i
      IsCharpolyPureOfWeight (p ^ q) ι i
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom) :=
  LAdicSheaf.weightBound_of_inputs B ℓ
    (laumonFibrePurityInput_of_absIrr' hL6' laumonFourierLineLatticeInput)
    (laumonDegenerationFamilyInput_of_noPunctualSections
      (laumonFamilyNoPunctualSectionsInput'_of_levelZero'
        (laumonFamilyFlatLevelZeroVanishingInput'_of_firstProjection
          laumonFamilyFirstProjectionVanishingInput')))
    (Purity.relativeCurvePurityInput_of_isIsoStalksOver B ℓ
      (Purity.twistNegOneTowerInverseImageInput B ℓ) Purity.purityClassMapStalkIsoInput)
    (fun K _ _ hK => poincareDualityCore_of_leaves ℓ K hK (properCurveRelativeDualityInput ℓ K))
    (fun K _ _ hK => topCohomologyPointClass ℓ K hK)
    (LAdicSheaf.representationDualPairingInput B ℓ)
    (LAdicSheaf.rationalPointPurityReductionInput B ℓ)
    (LAdicSheaf.geometricConnectednessPurityReductionInput B ℓ)
    kbar p q hcard hℓ X f j x ρ hρ hD

end WeightBound

end Stacks.EtaleCohomology

end
