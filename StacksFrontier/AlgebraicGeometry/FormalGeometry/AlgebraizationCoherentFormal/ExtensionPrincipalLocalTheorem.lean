module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.AlgebraizationCdOneTheorem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NilpotentIdealExtension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusDimensionCriterion

/-!
# Extending a coherent formal module over a principal ideal of a local ring

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)`, its closed subschemes `Y = V(I)` and `Z = V(𝔞)`, and the open complement
`U = X ∖ Z`. Let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`. [Stacks, Tag 0EJ9] asserts that `(ℱₙ)`
extends to `X` in the sense of [Stacks, Tag 0EIM] as soon as

1. `A` is local and `𝔞 = 𝔪` is the maximal ideal,
2. `A` has a dualizing complex,
3. `I = (f)` is a principal ideal,
4. `(ℱₙ)` satisfies the `(2, 3)`-inequalities of [Stacks, Tag 0EJ3];

and that, in particular, over an `I`-adically complete `A` the system is then the completion of a
coherent `𝒪_U`-module.

## Proof

A principal ideal has cohomological dimension `cd(A, (f)) ≤ 1` ([Stacks, Tag 0DX9]). There are two
cases.

* `cd(A, I) = 1`. Then hypotheses (2) and (4) are those of [Stacks, Tag 0EJJ]
  (`Stacks.Algebraization.extendsToX_of_cd_one_of_satisfiesDepthInequalities`), which gives the
  extension. Tag 0EJJ is the later and more general form of this lemma in the source
  ("algebraization in cohomological dimension 1"); its proof replaces the obstruction-theoretic
  Mittag-Leffler argument of the source's proof of 0EJ9 by the improvement of [Stacks, Tag 0EJG]
  and the canonical extension of [Stacks, Tag 0EJI].
* `cd(A, I) ≤ 0`. Then `V(I)` is open and closed in the connected spectrum of the local ring `A`
  and contains the closed point, so `I` is nilpotent
  (`Stacks.LocalCohomology.exists_pow_eq_bot_of_cohomologicalDimension_le_zero`); over a nilpotent
  ideal every object of `Coh(U, I𝒪_U)` extends to `X`
  (`Stacks.Algebraization.extendsToX_of_pow_eq_bot`, by [Stacks, Tag 0EIU] against the zero
  system).

The in-particular clause is condition (2) of [Stacks, Tag 0EIL] — the system lies in the essential
image of the completion functor of `U` — reached from extendability over an `I`-adically complete
base along the chain of conditions (6), (5) and (2) of that tag.

## Main results

* `Stacks.Algebraization.extendsToX_of_isLocalRing_of_eq_span_singleton` — the first assertion of
  [Stacks, Tag 0EJ9].
* `Stacks.Algebraization.essImage_completionFunctor_of_isLocalRing_of_eq_span_singleton` — its
  in-particular clause.

## Implementation notes

The conclusion is `Stacks.Algebraization.ExtendsToX` of [Stacks, Tag 0EIM] for
`Stacks.Algebraization.toKerSystem S F`, the system read along the kernel ideal sheaf of `Y ⟶ X`,
which is the spelling the carrier of Tag 0EJJ uses; the underlying inverse system is that of
`(ℱₙ)` (`Stacks.Algebraization.toKerSystem_obj`).

## References

* [Stacks Project, Tag 0EJ9](https://stacks.math.columbia.edu/tag/0EJ9)
* [Stacks Project, Tag 0EJJ](https://stacks.math.columbia.edu/tag/0EJJ)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EIM](https://stacks.math.columbia.edu/tag/0EIM), the conclusion.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0EIL](https://stacks.math.columbia.edu/tag/0EIL)
* [Stacks Project, Tag 0EIU](https://stacks.math.columbia.edu/tag/0EIU)
* [Stacks Project, Tag 0DX9](https://stacks.math.columbia.edu/tag/0DX9)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance high] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **Stacks Project, Tag 0EJ9.** In Situation 0EHC let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`.
Assume (1) `A` is local and `𝔞 = 𝔪` is the maximal ideal, (2) `A` has a dualizing complex,
(3) `I = (f)` is a principal ideal, and (4) `(ℱₙ)` satisfies the `(2, 3)`-inequalities. Then
`(ℱₙ)` extends to `X`. -/
@[stacks 0EJ9 "first assertion: (ℱₙ) extends to X"]
public theorem extendsToX_of_isLocalRing_of_eq_span_singleton
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (ha : S.a = IsLocalRing.maximalIdeal S.A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hI : S.I = Ideal.span {f})
    (hineq : SatisfiesDepthInequalities S F 2 3) :
    ExtendsToX S (toKerSystem S F) := by
  have hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) ≤ 1 := by
    have h := Stacks.LocalCohomology.cohomologicalDimension_span_singleton_le_one S.A f
    rw [← hI] at h
    exact h
  rcases Int.le_iff_lt_or_eq.mp hcd with hlt | heq
  · obtain ⟨t, ht⟩ := Stacks.LocalCohomology.exists_pow_eq_bot_of_cohomologicalDimension_le_zero
      S.A S.I (ha ▸ S.I_le_a) _ (Int.lt_add_one_iff.mp hlt)
    exact extendsToX_of_pow_eq_bot S ht (toKerSystem S F)
  · exact extendsToX_of_cd_one_of_satisfiesDepthInequalities S F hdual heq hineq

/-- **Stacks Project, Tag 0EJ9, in-particular clause.** In the situation of
`Stacks.Algebraization.extendsToX_of_isLocalRing_of_eq_span_singleton`, if moreover `A` is
`I`-adically complete then `(ℱₙ)` is the completion of a coherent `𝒪_U`-module.

The system extends to `X`, and over an `I`-adically complete base an extendable system is the
restriction of a completion on `X`, hence the completion of a module restricted from `X`, hence a
completion on `U` ([Stacks, Tag 0EIL]). -/
@[stacks 0EJ9 "in-particular clause: over an I-adically complete A, (ℱₙ) is the completion of a \
coherent 𝒪_U-module"]
public theorem essImage_completionFunctor_of_isLocalRing_of_eq_span_singleton
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] [IsAdicComplete S.I S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (ha : S.a = IsLocalRing.maximalIdeal S.A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hI : S.I = Ideal.span {f})
    (hineq : SatisfiesDepthInequalities S F 2 3) :
    (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage (toKerSystem S F) :=
  (isCompletion_iff_ofRestriction S (toKerSystem S F)).mpr
    ((isCompletionOfRestriction_iff_isRestrictionOfCompletion S (toKerSystem S F)).mpr
      (isRestrictionOfCompletion_of_extendsToX S (toKerSystem S F)
        (extendsToX_of_isLocalRing_of_eq_span_singleton S F f ha hdual hI hineq)))

end Stacks.Algebraization

end
