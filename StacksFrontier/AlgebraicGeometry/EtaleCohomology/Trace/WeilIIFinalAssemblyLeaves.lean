module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointPurityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationLevelPairingPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricComponentsPurityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreStableReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePurityStable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormStableWild
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreTwistPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreDualityUniformInertia
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreTopVanishingProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonUniformInertiaProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePureConstituent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonDegenerationFamilyAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyNoPunctualSectionsCharNe
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierFamilyFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierFamilyFieldExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineAwayFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePureDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.TwistNegOneTowerInverseImageIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyPointClassProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityFibrationStepProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SeparatedCohomologicalDimensionBoundProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RelativeCurveDualityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryDivisorDualityComponents
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekLowDegreeInputProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LisseDualityOfUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityLAdic

/-!
# Tag 03VH from the leaf inputs

[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Deligne, Weil II) is stated and proved in
`Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_inputs` from eight named inputs. Most of them are
now proved, or reduced to smaller named inputs; this file substitutes every proof and reduction,
so that the only extra hypotheses of `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves` are
the named inputs which are not yet proved:

* Poincaré duality on `X_k̄` (`Stacks.EtaleCohomology.PoincareDualityCore`), through the fibration
  step (`Stacks.EtaleCohomology.poincareDualityCore_of_inputs`): the cohomological dimension, the
  low degree vanishing of `Rf_!` and the duality for lisse sheaves are proved, and the relative
  duality of an elementary fibration is reduced to the relative duality of the smooth proper curve
  (`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`), the duality along the boundary
  divisor being proved (`Stacks.EtaleCohomology.boundaryDivisorDualityInput`);
* relative purity (`Stacks.EtaleCohomology.RelativeCurvePurityInput`), reduced to the twist of
  towers under inverse image (proved,
  `Stacks.EtaleCohomology.Purity.twistNegOneTowerInverseImageInput`) and the stalkwise purity of
  the class map (`Stacks.EtaleCohomology.Purity.PurityClassMapStalkIsoInput`);
* the purity of the fibres of the Fourier family (`Stacks.EtaleCohomology.LaumonFibrePurityInput`,
  L7), through the reduction to representations which stay absolutely irreducible: the reciprocity
  with complex conjugation, the purity of the constituents and the descent along a finite
  extension are proved; the inputs are the decomposition into stable constituents
  (`Stacks.EtaleCohomology.LaumonStableDecompositionInput`)
  and the two inputs of the equal absolute values not yet proved: the absolute irreducibility of
  the Fourier transform (`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput`) and Laumon's local
  theory away from `a = 0` on the fibres (`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreInput`,
  which gives `Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput`); the identification of the
  fibres of the Fourier family and its field extensions are proved
  (`Stacks.EtaleCohomology.laumonFourierFamilyFibreInput`,
  `Stacks.EtaleCohomology.laumonFourierFamilyFieldExtensionInput`);
* the degeneration of the Fourier family at the origin
  (`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`, L8), assembled in
  `Stacks.EtaleCohomology.laumonDegenerationFamilyInput_of_noPunctualSections` from the absence of
  punctual sections of `R¹pr₂!` of the family at the origin for `ℓ` different from the
  characteristic, which reduces
  (`Stacks.EtaleCohomology.laumonFamilyNoPunctualSectionsInput'_of_levelZero'`) to the vanishing
  of `R⁰pr₂!` and `H¹_c(𝔸²_k̄, -)` on the bottom flat level of the family sheaf
  (`Stacks.EtaleCohomology.LaumonFamilyFlatLevelZeroVanishingInput'`).

The point class, the dual coefficients and both reductions of purity are proved.

## Main results

* `Stacks.EtaleCohomology.laumonFibreReciprocityInput`: L7's reciprocity with complex conjugation.
* `Stacks.EtaleCohomology.laumonFibrePurityInput_of_leaves`: L7 from its leaf inputs.
* `Stacks.EtaleCohomology.poincareDualityCore_of_leaves`: `PoincareDualityCore` from its leaf
  inputs.
* `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves`: Tag 03VH from the leaf inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-! ### L7 -/

/-- **L7's reciprocity with complex conjugation**
(`Stacks.EtaleCohomology.LaumonFibreReciprocityInput`) holds: Poincaré duality on the fibres, from
the uniform inertia
(`Stacks.EtaleCohomology.laumonFibreDualityInput_of_uniformInertia`,
`Stacks.EtaleCohomology.laumonUniformInertiaInput`), and the vanishing of `H²_c`
(`Stacks.EtaleCohomology.laumonFibreTopVanishingInput`). -/
theorem laumonFibreReciprocityInput : LaumonFibreReciprocityInput.{u} :=
  laumonFibreReciprocityInput_of_duality_topVanishing
    (laumonFibreDualityInput_of_uniformInertia laumonUniformInertiaInput)
    laumonFibreTopVanishingInput

/-- **L7 from its leaf inputs** ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the purity
of the fibres of the Fourier family (`Stacks.EtaleCohomology.LaumonFibrePurityInput`) through the
reduction to representations which stay absolutely irreducible
(`Stacks.EtaleCohomology.laumonFibrePurityInput_of_stable`): the reduction from the
decomposition into stable constituents (the descent is
`Stacks.EtaleCohomology.laumonFibrePureDescentInput`, the purity of the constituents
`Stacks.EtaleCohomology.laumonFibrePureConstituentInput`), the equal absolute values from the
inputs of `Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_inputs'` (the local theory
away from `a = 0` through `Stacks.EtaleCohomology.laumonFourierLineLisseAwayInput_of_fibre`, the
fibres and field extensions by `Stacks.EtaleCohomology.laumonFourierFamilyFibreInput` and
`Stacks.EtaleCohomology.laumonFourierFamilyFieldExtensionInput`), and the reciprocity
`Stacks.EtaleCohomology.laumonFibreReciprocityInput`. -/
theorem laumonFibrePurityInput_of_leaves (hL6 : LaumonFourierLineAbsIrrInput.{u})
    (hAway : LaumonFourierLineAwayFibreInput.{u}) (hC : LaumonStableDecompositionInput.{u}) :
    LaumonFibrePurityInput.{u} :=
  laumonFibrePurityInput_of_stable
    (laumonFibreStableReductionInput_of_inputs laumonFibrePureDescentInput
      laumonFibrePureConstituentInput hC)
    (laumonFourierEquinormStableInput_of_inputs' hL6
      (laumonFourierLineLisseAwayInput_of_fibre hAway) laumonFourierFamilyFibreInput
      laumonFourierFamilyFieldExtensionInput)
    laumonFibreReciprocityInput

/-! ### Poincaré duality -/

/-- **Poincaré duality on a dense open from its leaf input**: for `k` algebraically closed and `ℓ`
invertible in `k`, `Stacks.EtaleCohomology.PoincareDualityCore ℓ k` follows from the relative
duality of a smooth proper curve (`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`): the
other inputs of the fibration step (`Stacks.EtaleCohomology.poincareDualityCore_of_inputs`) are
`Stacks.EtaleCohomology.cohomologicalDimensionInput_of_isAlgClosed`,
`Stacks.EtaleCohomology.lowerShriekLowDegreeInput`,
`Stacks.EtaleCohomology.lisseDualityOfUnitInput` and, through
`Stacks.EtaleCohomology.relativeCurveDualityInput_of_inputs`, the duality along the boundary
divisor `Stacks.EtaleCohomology.boundaryDivisorDualityInput`. -/
theorem poincareDualityCore_of_leaves (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [IsAlgClosed k] (hℓ : IsUnit (ℓ : k)) (he : ProperCurveRelativeDualityInput ℓ k) :
    PoincareDualityCore ℓ k :=
  poincareDualityCore_of_inputs ℓ hℓ (cohomologicalDimensionInput_of_isAlgClosed ℓ k)
    (relativeCurveDualityInput_of_inputs ℓ k (boundaryDivisorDualityInput ℓ k) he)
    (lowerShriekLowDegreeInput ℓ k) (lisseDualityOfUnitInput ℓ k)

/-! ### Tag 03VH -/

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

/-- **[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) from the leaf inputs.**
Let `k` be a finite field with `q = p ^ m` elements, `k̄` an algebraic closure, `ℓ ≠ p` a prime,
`X` connected and separated of finite type over `k` with a compactification `j`, and
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` continuous, satisfying the conclusions of Deligne's conjecture along
every embedding `ι : ℚ_ℓ → ℂ`. Then for every `i` the eigenvalues of `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` (finite dimensional) are algebraic numbers of absolute value `q ^ (w / 2)`
along `ι` with `w ∈ ℤ`, `w ≤ i`; and if `X` is smooth and proper over `k`, then `w = i`.

This is `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_inputs` with every proved input and
reduction substituted; the extra hypotheses are the named inputs not yet proved (see the module
docstring). -/
theorem LAdicSheaf.weightBound_of_leaves
    -- L7
    (hL6 : LaumonFourierLineAbsIrrInput.{u}) (hAway : LaumonFourierLineAwayFibreInput.{u})
    (hC : LaumonStableDecompositionInput.{u})
    -- L8
    (hH2 : LaumonFamilyFlatLevelZeroVanishingInput'.{u})
    -- relative purity
    (hcls : Purity.PurityClassMapStalkIsoInput.{u})
    -- Poincaré duality
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K], ProperCurveRelativeDualityInput ℓ K)
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
    (laumonFibrePurityInput_of_leaves hL6 hAway hC)
    (laumonDegenerationFamilyInput_of_noPunctualSections
      (laumonFamilyNoPunctualSectionsInput'_of_levelZero' hH2))
    (Purity.relativeCurvePurityInput_of_isIsoStalksOver B ℓ
      (Purity.twistNegOneTowerInverseImageInput B ℓ) hcls)
    (fun K _ _ hK => poincareDualityCore_of_leaves ℓ K hK (he K))
    (fun K _ _ hK => topCohomologyPointClass ℓ K hK)
    (LAdicSheaf.representationDualPairingInput B ℓ)
    (LAdicSheaf.rationalPointPurityReductionInput B ℓ)
    (LAdicSheaf.geometricConnectednessPurityReductionInput B ℓ)
    kbar p q hcard hℓ X f j x ρ hρ hD

end Stacks.EtaleCohomology

end
