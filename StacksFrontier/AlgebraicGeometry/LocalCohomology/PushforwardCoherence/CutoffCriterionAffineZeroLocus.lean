module

public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.CutoffCriterionAffine
public import StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresCriterionZeroLocus

/-!
# Coherence of the higher direct images on a punctured affine spectrum, formal fibres along `Z`

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `X = Spec A`, `Z = V(I)`, `U = X ∖ Z` and
`j : U → X` the inclusion. Let `M` be a finite `A`-module and `ℱ = M̃|_U`.
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.CutoffCriterionAffine` proves
the affine case of Stacks 0BJY in the cutoff form: if `A` is universally catenary and the formal
fibres of *every* local ring of `A` satisfy Serre's condition `(Sₙ)`, then `R^pj_*ℱ` is coherent
for all `0 ≤ p < n` exactly when `n` is strictly below the cutoff `s_{A,I}(M)` of Stacks 0BJR.
This file proves the same equivalence with the formal-fibres hypothesis imposed only at the
primes of `Z`, which is what Stacks 0BJY itself assumes.

## Main results

* `lt_localCohomologyCutoff_iff_forall_isCoherent_rightDerivedZeroLocus`: the cutoff criterion
  for coherence of the higher direct images, formal fibres along `Z` only.

## Implementation notes

Clause (3) of Stacks 0BK0, in the form
`Stacks.LocalCohomologySequence.isCoherent_rightDerived_iff_finite_localCohomology`, needs no
hypothesis on the formal fibres at all; only the cutoff criterion itself,
`Stacks.LocalCohomology.lt_localCohomologyCutoff_iff_forall_finite_succZeroLocus`, does, and it
is already stated with the hypothesis restricted along `V(I)`. The combination is otherwise the
proof of `lt_localCohomologyCutoff_iff_forall_isCoherent_rightDerived` verbatim.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.LocalCohomologyTilde

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-- **The affine case of Stacks 0BJY, in cutoff form, formal fibres along `Z` only.** Let `A`
be a universally catenary Noetherian ring, `I ⊆ A` an ideal, `U = Spec A ∖ V(I)`,
`j : U → Spec A` the inclusion and `M` a finite `A`-module. If the formal fibres of
`𝒪_{Spec A, q}` satisfy Serre's condition `(Sₙ)` for every `q ∈ V(I)`, then `R^pj_*(M̃|_U)` is
coherent for every `0 ≤ p < n` exactly when `n` is strictly below the local cohomology
finiteness cutoff `s_{A,I}(M)` of Stacks 0BJR. -/
public theorem lt_localCohomologyCutoff_iff_forall_isCoherent_rightDerivedZeroLocus
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hA : Ring.IsUniversallyCatenary (ToType A)) (n : ℕ)
    (hformal : ∀ q : PrimeSpectrum (ToType A), I ≤ q.asIdeal →
      Stacks.LocalCohomology.FormalFibersHavePropertySk (Localization.AtPrime q.asIdeal) n) :
    (n : ℕ∞) < Stacks.LocalCohomology.localCohomologyCutoff (ToType A) I M ↔
      ∀ p : ℕ, p < n →
        (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj
          ((tilde M).restrict (zeroLocusCompl I).ι)).IsCoherent :=
  (Stacks.LocalCohomology.lt_localCohomologyCutoff_iff_forall_finite_succZeroLocus
      (ToType A) I M hA n hformal).trans
    (forall_congr' fun p => forall_congr' fun _ =>
      (isCoherent_rightDerived_iff_finite_localCohomology I M p).symm)

end Stacks.LocalCohomologySequence

end
