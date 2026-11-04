module

public import StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.LocalRings
public import StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.FieldIso

/-!
# Stacks 0EJA is false: the unconditional statement

The criterion of Stacks 0EJA, at its published hypotheses (Situation 0EHC, `A` local with
`𝔞 = 𝔪`, `cd(A, I) = 1`), fails for the non-catenary local ring `A''` of
`StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.Counterexample`, over the
field `K = ℚ(t₀, t₁, …)` (lifted to the universe `u`), with `(ℱₙ)` the completion of `𝒪_U`. The
mathematics is recorded in the module docstring of that file. The ring `A''/I` is not catenary,
so the corrected form of 0EJA, which assumes `A/I` catenary, is not contradicted.

## Main results

* `Stacks.NonCatenaryExample.not_stacks0EJA` — the negation of the published statement.

## References

* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA)
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.Algebraization

universe u

namespace Stacks.NonCatenaryExample

/-- **Stacks 0EJA is false as published.** There is an algebraization situation (Situation 0EHC)
with `A` Noetherian local, `𝔞 = 𝔪`, `cd(A, I) = 1`, and an object `(ℱₙ)` of `Coh(U, I𝒪_U)` such
that `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2` for every `y ∈ U ∩ Y` with `dim({y}‾) = 1` and every
`𝔭 ∉ V(I𝒪_{X,y}^∧)`, but `(ℱₙ)` does not satisfy the `(2, 3)`-inequalities. -/
@[stacks 0EJA "refutation of the published 'if' direction: at hypotheses (1) and (2) alone, the \
depth inequality at the points of U ∩ Y of dimension one does not imply the (2, 3)-inequalities; \
in the example A/I is not catenary"]
theorem not_stacks0EJA :
    ¬ ∀ (S : AlgebraizationSituation.{u}) [IsLocalRing S.A], S.a = maximalIdeal S.A →
      Stacks.LocalCohomology.cohomologicalDimension S.A S.I (IsNoetherian.noetherian S.I) = 1 →
      ∀ F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S),
        (SatisfiesDepthInequalities S F 2 3 ↔
          ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
            Order.height (S.U.ι.base y) = 1 →
            ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
              ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
              ((2 : ℤ) : EInt) <
                enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
                  krullDimToEInt
                    (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal))) := by
  intro h
  let k : Type u := ULift.{u} ℚ
  let K : Type u := BigField k
  let e : K ≃+* FractionRing (MvPolynomial (Fin 3) K) := fieldEquiv k
  exact not_iff_of_local K e (exists_annihilatedPrime_primePpp K e)
    (localization_eq_zero_or_regular K e)
    (h (situation K e) rfl (cohomologicalDimension_situation K e) (formalModule K e))

end Stacks.NonCatenaryExample

end
