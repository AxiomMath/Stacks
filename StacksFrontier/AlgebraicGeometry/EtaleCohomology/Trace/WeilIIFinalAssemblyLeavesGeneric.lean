module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssemblyLeaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormStableGeneric
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLisseGeneric
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonStableDecomposition

/-!
# Tag 03VH from the leaf inputs, through the generic lisse locus of the Fourier family

`Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) takes as inputs, for L7, the absolute
irreducibility of the Fourier transform, Laumon's local theory away from `a = 0` on the fibres
(`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreInput`, which needs the
Grothendieck–Ogg–Shafarevich formula) and the decomposition into stable constituents. This file
replaces the local theory by the GENERIC lisseness of the Fourier family on the `(a, t)`-plane,
uniform in the finite extension `k'` and in `a`
(`Stacks.EtaleCohomology.laumonFourierLineLisseFibreInput_of_lattice`, consumed by
`Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_inputs''`), which needs only the
constructibility of `R pr₂!` and one lattice comparison
(`Stacks.EtaleCohomology.LaumonFourierLineLatticeInput`: Brauer–Nesbitt, Clifford and the
Artin–Schreier base change), and substitutes the decomposition into stable constituents, now
proved (`Stacks.EtaleCohomology.laumonStableDecompositionInput`).

The remaining inputs of `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves'` are
`Stacks.EtaleCohomology.LaumonFourierLineAbsIrrInput`,
`Stacks.EtaleCohomology.LaumonFourierLineLatticeInput` (L7),
`Stacks.EtaleCohomology.LaumonFamilyFlatLevelZeroVanishingInput'` (L8),
`Stacks.EtaleCohomology.Purity.PurityClassMapStalkIsoInput` (relative purity) and
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput` (Poincaré duality).

## Main results

* `Stacks.EtaleCohomology.laumonFibrePurityInput_of_leaves'`: L7 from its leaf inputs.
* `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves'`: Tag 03VH from the leaf inputs.

## Implementation notes

The cohomology groups of the statement are those of
`Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves`, defined in the standard model
`HasDerivedCategory.standard` of the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- **L7 from its leaf inputs, through the generic lisse locus**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the purity of the fibres of the Fourier
family (`Stacks.EtaleCohomology.LaumonFibrePurityInput`) through the reduction to representations
which stay absolutely irreducible (`Stacks.EtaleCohomology.laumonFibrePurityInput_of_stable`): the
reduction from the decomposition into stable constituents
(`Stacks.EtaleCohomology.laumonStableDecompositionInput`, with the descent
`Stacks.EtaleCohomology.laumonFibrePureDescentInput` and the purity of the constituents
`Stacks.EtaleCohomology.laumonFibrePureConstituentInput`), the equal absolute values from
`Stacks.EtaleCohomology.laumonFourierEquinormStableInput_of_inputs''` (the generic lisse locus
through `Stacks.EtaleCohomology.laumonFourierLineLisseFibreInput_of_lattice`, the fibres and field
extensions by `Stacks.EtaleCohomology.laumonFourierFamilyFibreInput` and
`Stacks.EtaleCohomology.laumonFourierFamilyFieldExtensionInput`), and the reciprocity
`Stacks.EtaleCohomology.laumonFibreReciprocityInput`. -/
theorem laumonFibrePurityInput_of_leaves' (hL6 : LaumonFourierLineAbsIrrInput.{u})
    (hlat : LaumonFourierLineLatticeInput.{u}) : LaumonFibrePurityInput.{u} :=
  laumonFibrePurityInput_of_stable
    (laumonFibreStableReductionInput_of_inputs laumonFibrePureDescentInput
      laumonFibrePureConstituentInput laumonStableDecompositionInput)
    (laumonFourierEquinormStableInput_of_inputs'' hL6
      (laumonFourierLineLisseFibreInput_of_lattice hlat) laumonFourierFamilyFibreInput
      laumonFourierFamilyFieldExtensionInput)
    laumonFibreReciprocityInput

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

/-- **[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) from the leaf inputs, through the
generic lisse locus of the Fourier family.**
Let `k` be a finite field with `q = p ^ m` elements, `k̄` an algebraic closure, `ℓ ≠ p` a prime,
`X` connected and separated of finite type over `k` with a compactification `j`, and
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` continuous, satisfying the conclusions of Deligne's conjecture along
every embedding `ι : ℚ_ℓ → ℂ`. Then for every `i` the eigenvalues of `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` (finite dimensional) are algebraic numbers of absolute value `q ^ (w / 2)`
along `ι` with `w ∈ ℤ`, `w ≤ i`; and if `X` is smooth and proper over `k`, then `w = i`.

This is `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_leaves` with Laumon's local theory away
from `a = 0` (`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreInput`) replaced by the lattice
comparison over the `(a, t)`-plane (`Stacks.EtaleCohomology.LaumonFourierLineLatticeInput`), and
the decomposition into stable constituents substituted
(`Stacks.EtaleCohomology.laumonStableDecompositionInput`). -/
theorem LAdicSheaf.weightBound_of_leaves'
    -- L7
    (hL6 : LaumonFourierLineAbsIrrInput.{u}) (hlat : LaumonFourierLineLatticeInput.{u})
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
    (laumonFibrePurityInput_of_leaves' hL6 hlat)
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
