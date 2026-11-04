module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.CompletedLocalPuncturedSpectrum
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit

/-!
# The closed point of an adic completion of a Noetherian local ring

Let `B` be a Noetherian local ring and `J ⊆ 𝔪_B` an ideal. The `J`-adic completion
`A' = AdicCompletion J B` is local with maximal ideal `𝔪_B A'`, so the only prime of `A'`
contracting to the closed point of `B` is the closed point of `A'`.

## Main results

* `Stacks.Algebraization.comap_adicCompletion_eq_closedPoint_iff` — only the closed point of
  `A'` contracts to the closed point of `B`.
* `Stacks.Algebraization.comap_maximalIdeal_adicCompletion` — the maximal ideal of `A'`
  contracts to the maximal ideal of `B`.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Stacks.Algebraization

/-- The only prime of the `I`-adic completion of a Noetherian local ring contracting to the closed
point is the closed point. -/
public theorem comap_adicCompletion_eq_closedPoint_iff {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≤ maximalIdeal R)
    (q : PrimeSpectrum (AdicCompletion I R)) :
    haveI := Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal I hI
    PrimeSpectrum.comap (algebraMap R (AdicCompletion I R)) q = closedPoint R ↔
      q = closedPoint (AdicCompletion I R) := by
  have := Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal I hI
  exact AlgebraicGeometry.CodimensionOneObstruction.comap_eq_closedPoint_iff_of_maximalIdeal_eq_map
    (algebraMap R (AdicCompletion I R))
    (IsLocalRing.eq_maximalIdeal
      (AdicCompletion.isMaximal_map_of_le I (maximalIdeal R) hI
        (Ideal.fg_of_isNoetherianRing I))).symm q

/-- **The maximal ideal of the adic completion contracts to the maximal ideal.** For a Noetherian
local ring `B` and an ideal `J ≤ 𝔪_B`, the maximal ideal of the `J`-adic completion of `B`
contracts to `𝔪_B`. -/
public theorem comap_maximalIdeal_adicCompletion {B : Type u} [CommRing B] [IsNoetherianRing B]
    [IsLocalRing B] (J : Ideal B) (hJ : J ≤ maximalIdeal B) :
    haveI := Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal J hJ
    (maximalIdeal (AdicCompletion J B)).comap (algebraMap B (AdicCompletion J B)) =
      maximalIdeal B := by
  have := Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal J hJ
  exact congrArg PrimeSpectrum.asIdeal
    ((comap_adicCompletion_eq_closedPoint_iff J hJ (closedPoint (AdicCompletion J B))).mpr rfl)

end Stacks.Algebraization

end
