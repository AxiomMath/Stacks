module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesUnwindingCriterion

/-!
# Stacks 0EJA in corrected form

Fix an algebraization situation (Stacks 0EHC): a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with
`X = Spec(A)`, `Y = V(I)`, `Z = V(𝔞)` and `U = X \ Z`, and let `(ℱ_n)` be an object of
`Coh(U, I𝒪_U)`. Assume (1) `A` is local with `𝔞 = 𝔪` and (2) `cd(A, I) = 1`. Stacks 0EJA
asserts that `(ℱ_n)` satisfies the `(2, 3)`-inequalities if and only if

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2`

for every `y ∈ U ∩ Y` with `dim({y}‾) = 1` and every prime `𝔭 ⊆ 𝒪_{X,y}^∧` with
`𝔭 ∉ V(I𝒪_{X,y}^∧)`.

The necessity direction is true at hypotheses (1) and (2). The sufficiency direction is false
there: `Stacks.NonCatenaryExample.not_stacks0EJA` is a counterexample, in which `A/I` is not
catenary. This file states the corrected lemma in one declaration: necessity at (1) and (2), and
the equivalence once one adds (3) `A/I` is catenary and (4) at every point `y'` of `U ∩ Y` with
`dim({y'}‾) = 1` the completed local ring `𝒪_{X,y'}^∧` is universally catenary with
Cohen--Macaulay formal fibres. Hypothesis (3) is what Stacks 0EIY (5), quoted by the published
proof, asks for; (4) is what the published proof's use of Stacks 0EHW needs. Both hold when `A`
has a dualizing complex, the standing hypothesis of the neighbouring Stacks 0EJ9 and 0EJB; see
`satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim_of_isDualizingComplex`.
Whether (3) without (4) suffices is open; the analysis is in the module docstring of
`StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesUnwindingCriterion`.

## Main results

* `Stacks.Algebraization.satisfiesDepthInequalities_two_three_imp_and_iff_of_isCatenary` —
  Stacks 0EJA in corrected form.

## References

* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY), the distance function.
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW), depth plus dimension
  under completion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Algebraization

/-- **Stacks 0EJA, corrected.** In Situation 0EHC let `(ℱ_n)` be an object of `Coh(U, I𝒪_U)`.
Assume (1) `A` is local with `𝔞 = 𝔪` and (2) `cd(A, I) = 1`. Then:

* if `(ℱ_n)` satisfies the `(2, 3)`-inequalities, then
  `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2` for every `y ∈ U ∩ Y` with `dim({y}‾) = 1` and every
  prime `𝔭 ⊆ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`;
* if moreover (3) `A/I` is catenary and (4) at every `y' ∈ U ∩ Y` with `dim({y'}‾) = 1` the
  completed local ring `𝒪_{X,y'}^∧` is universally catenary with Cohen--Macaulay formal fibres,
  then `(ℱ_n)` satisfies the `(2, 3)`-inequalities if and only if that bound holds.

At (1) and (2) alone the converse of the first part is false:
`Stacks.NonCatenaryExample.not_stacks0EJA`. -/
@[stacks 0EJA "corrected form: the necessity direction at hypotheses (1) and (2), and the \
equivalence with (3) A/I catenary and (4) the completed local rings of U at the points of U ∩ Y \
of dimension one universally catenary with Cohen-Macaulay formal fibres added; (3) and (4) hold \
when A has a dualizing complex. The published sufficiency direction at (1) and (2) is false, by \
Stacks.NonCatenaryExample.not_stacks0EJA, an example in which A/I is not catenary"]
public theorem satisfiesDepthInequalities_two_three_imp_and_iff_of_isCatenary
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (ha : S.a = maximalIdeal S.A)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) :
    (SatisfiesDepthInequalities S F 2 3 →
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        Order.height (S.U.ι.base y) = 1 →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          ((2 : ℤ) : EInt) <
            enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
              krullDimToEInt
                (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal))) ∧
    (Ring.IsCatenary (S.A ⧸ S.I) →
      (∀ (y' : S.U.toScheme) (z' : S.Y), S.U.ι.base y' = S.Yι.base z' →
        Order.height (S.U.ι.base y') = 1 →
        Ring.IsUniversallyCatenary (completedLocalRing (idealOnOpen S) y') ∧
          IsPRing Stacks.AdicCompletionFibre.cohenMacaulayRingMapProperty.{u}
            (completedLocalRing (idealOnOpen S) y')) →
      (SatisfiesDepthInequalities S F 2 3 ↔
        ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
          Order.height (S.U.ι.base y) = 1 →
          ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
            ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
            ((2 : ℤ) : EInt) <
              enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
                krullDimToEInt
                  (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)))) :=
  ⟨fun h y z hyz hd p hp =>
      two_lt_depth_add_dim_of_satisfiesDepthInequalities S ha hcd F h y z hyz hd p hp,
    fun hcat hstalk =>
      satisfiesDepthInequalities_two_three_iff_two_lt_depth_add_dim S ha hcat
        (fun y' z' hyz' hd' => (hstalk y' z' hyz' hd').1)
        (fun y' z' hyz' hd' => (hstalk y' z' hyz' hd').2) hcd F⟩

end Stacks.Algebraization

end
