module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpMaximalIdealNormal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CompletionBothClauses
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionVanishingDescends
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of a rational surface singularity to the completion

Let `(A, 𝔪, κ)` be a Nagata local normal domain of dimension two which defines a rational
singularity and whose completion `A^` is normal. Then `A^` defines a rational singularity, and
the completion of the local ring of the blowup of `Spec(A)` in `𝔪` at every closed point is a
normal domain.

## Main results

* `AlgebraicGeometry.definesRationalSingularity_adicCompletion_and_isNormalDomain_stalk_blowUp`:
  `A^` defines a rational singularity, and the completed local rings of the blowup of `Spec(A)`
  in `𝔪` at closed points are normal domains.

## References

* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Let `(A, 𝔪, κ)` be a Nagata local normal domain of dimension two which defines a rational
singularity and whose completion `A^` is normal. Then

1. `A^` defines a rational singularity, and
2. if `X ⟶ Spec(A)` is the blowup in `𝔪`, then for a closed point `x ∈ X` the completion of
   `𝒪_{X, x}` is normal (indeed a normal domain). -/
@[stacks 0BG7]
theorem definesRationalSingularity_adicCompletion_and_isNormalDomain_stalk_blowUp
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hNagata : IsNagataRing A)
    [IsNormalDomain (AdicCompletion (maximalIdeal A) A)]
    (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A) :
    DefinesRationalSingularity (AdicCompletion (maximalIdeal A) A) ∧
      ∀ x : blowUp (maximalIdealSheaf A), IsClosed ({x} : Set (blowUp (maximalIdealSheaf A))) →
        IsNormalDomain (AdicCompletion
          (maximalIdeal ((blowUp (maximalIdealSheaf A)).presheaf.stalk x))
          ((blowUp (maximalIdealSheaf A)).presheaf.stalk x)) := by
  have : IsNoetherianRing A := hNagata.1
  have hdim' : ringKrullDim (AdicCompletion (maximalIdeal A) A) = 2 :=
    IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal.trans hdim
  exact definesRationalSingularity_and_isNormalDomain_stalk_blowUp_maximalIdeal A hNagata hdim hrat
    (fun _ q hq => strictTransformOpenImmersion_of_isModification _ hdim' q hq)
    (completionVanishingDescends A hdim) blowUpMaximalIdealIsNormal

end AlgebraicGeometry

end
