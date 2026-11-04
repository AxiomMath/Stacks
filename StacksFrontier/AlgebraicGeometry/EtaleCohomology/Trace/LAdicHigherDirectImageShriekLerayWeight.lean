module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LerayFrobeniusComparisonDischarge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional

/-!
# The Leray weight implication for `Rʳ g_! G`, from finiteness of compactly supported cohomology

The Leray step of the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) to curves rests on three inputs besides
the Leray comparison with Frobenius (`Stacks.EtaleCohomology.LAdicSheaf.lerayFrobeniusComparison`):
the constructibility of `Rᵠ g_!` (Tag 0GL0,
`Stacks.EtaleCohomology.lowerShriekConstructibilityInput`), the finiteness of `Hᵃ_c` with ℓ-power
torsion coefficients (`Stacks.EtaleCohomology.LAdicSheaf.torsionCompactSupportFinitenessInput`),
both proved, and the finiteness of compactly supported cohomology of ℓ-adic sheaves
(`Stacks.EtaleCohomology.LAdicSheaf.FiniteCompactSupportCohomologyInput`, Tag 03V3), which remains
the hypothesis.

## Main results

All names below are in the namespace `Stacks.EtaleCohomology.LAdicSheaf`.

* `lerayWeightInput_higherDirectImageShriekFamily_of_finiteCompactSupportCohomologyInput`:
  the Leray weight implication holds for the family `Rʳ g_! G`, given the finiteness of compactly
  supported cohomology of ℓ-adic sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

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

/-- **The Leray weight implication for `Rʳ g_! G`** (Weil II 3.3; the Leray step of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), given only the finiteness of compactly
supported cohomology of ℓ-adic sheaves (Tag 03V3): the Leray comparison with Frobenius, the
constructibility of `Rᵠ g_!` and the torsion finiteness are proved. -/
theorem
    LAdicSheaf.lerayWeightInput_higherDirectImageShriekFamily_of_finiteCompactSupportCohomologyInput
    (hfin : LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ) :
    LAdicSheaf.LerayWeightInput (LAdicSheaf.higherDirectImageShriekFamily B ℓ) :=
  LAdicSheaf.lerayWeightInput_higherDirectImageShriekFamily_of_constructibility B ℓ
    (lowerShriekConstructibilityInput B) hfin (LAdicSheaf.torsionCompactSupportFinitenessInput B ℓ)

end Stacks.EtaleCohomology

end
