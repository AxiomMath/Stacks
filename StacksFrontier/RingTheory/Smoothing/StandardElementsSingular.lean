module

public import StacksFrontier.RingTheory.Smoothing.SingularIdealFactorization
public import StacksFrontier.RingTheory.Smoothing.StandardnessConditions
public import StacksFrontier.RingTheory.Smoothing.PresentationRelabel

/-!
# Standard elements lie in the singular ideal

Let `R → A` be a ring map of finite presentation. The singular ideal `H_{A/R}`
(Stacks 07C5) is the radical ideal cutting out the locus where `Spec(A) → Spec(R)`
is not smooth. This file proves that both the elementary standard and the strictly
standard elements of `A` over `R` lie in `H_{A/R}`, and deduces that the
localization at a strictly standard element is smooth.

For an elementary standard element `a` this is immediate from the implication
(6) ⇒ (4) ⇒ (1) of Stacks 16.3.7, which makes `A_a` smooth over `R`, so
`a` itself witnesses smoothness at every prime it avoids. For a strictly
standard element `a` the argument is the one of Stacks 16.2.4: if `a`
were outside a prime `q`, then one of the Jacobian minors occurring in the
expression of `a` would be outside `q` as well, and multiplying `a` by it produces
an elementary standard element outside `q`, so `R → A` is smooth at `q`.

## Main definitions

None.

## Main results

* `Stacks.Smoothing.mem_singularIdeal_of_isElementaryStandard`: an elementary
  standard element lies in the singular ideal.
* `Stacks.Smoothing.mem_singularIdeal_of_isStrictlyStandard`: a strictly standard
  element lies in the singular ideal.
* `Stacks.Smoothing.smooth_localizationAway_of_isStrictlyStandard`: the
  localization of `A` away from a strictly standard element is smooth over `R`,
  i.e. the implication (5) ⇒ (1) of Stacks 16.3.7.

## Implementation notes

The singular ideal is `Stacks.Smoothing.singularIdeal`, the vanishing ideal of the set of
primes at which `R → A` is not smooth in the sense of `Algebra.SmoothAt`; membership in it is
therefore unfolded through `PrimeSpectrum.mem_vanishingIdeal`, and exhibiting smoothness at a
prime means naming an element outside it whose localization is smooth.

## References

* [Stacks Project, Tag 07C5](https://stacks.math.columbia.edu/tag/07C5)
* [Stacks Project, Tag 07CA](https://stacks.math.columbia.edu/tag/07CA)
* [Stacks Project, Tag 07EZ](https://stacks.math.columbia.edu/tag/07EZ)
-/

@[expose] public section

namespace Stacks.Smoothing

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- An element whose localization is smooth lies in the singular ideal: the
non-smooth locus is contained in `V(a)`. -/
theorem mem_singularIdeal_of_smooth_localizationAway
    [Algebra.FinitePresentation R A] {a : A}
    (h : Algebra.Smooth R (Localization.Away a)) : a ∈ singularIdeal R A := by
  refine (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun q hq ↦ ?_
  by_contra hqa
  exact hq ⟨a, hqa, h⟩

/-- An elementary standard element lies in the singular ideal. This is the
implication (6) ⇒ (4) ⇒ (1) of Stacks 16.3.7, read as a statement about the
singular ideal. -/
theorem mem_singularIdeal_of_isElementaryStandard
    [Algebra.FinitePresentation R A] {a : A}
    (ha : IsElementaryStandard (R := R) (A := A) a) : a ∈ singularIdeal R A := by
  have hstd : Algebra.IsStandardSmooth R (Localization.Away a) :=
    isStandardSmooth_localizationAway_of_isElementaryStandard
      ({ R := R, A := A, a := a } : SixStandardnessConditions) ha
  have := hstd
  exact mem_singularIdeal_of_smooth_localizationAway ⟨inferInstance, inferInstance⟩

/-- The localization of `A` away from an elementary standard element is smooth
over `R`. -/
theorem smooth_localizationAway_of_isElementaryStandard
    [Algebra.FinitePresentation R A] {a : A}
    (ha : IsElementaryStandard (R := R) (A := A) a) :
    Algebra.Smooth R (Localization.Away a) :=
  smooth_localization_away_of_mem_singularIdeal R A
    (mem_singularIdeal_of_isElementaryStandard ha)

/-- **Stacks 16.2.4 for one prime.** A strictly standard element lies in the
singular ideal: if it were outside a prime `q`, one of the Jacobian minors in its
expression would be outside `q` too, and their product is an elementary standard
element outside `q`, so `R → A` is smooth at `q`. -/
theorem mem_singularIdeal_of_isStrictlyStandard
    [Algebra.FinitePresentation R A] {a : A}
    (ha : IsStrictlyStandard (R := R) (A := A) a) : a ∈ singularIdeal R A := by
  classical
  obtain ⟨P, c, hcn, hcm, ⟨⟨aI, haeq⟩, hcond⟩⟩ := ha
  refine (PrimeSpectrum.mem_vanishingIdeal _ _).2 fun q hq ↦ ?_
  by_contra hqa
  -- Some Jacobian minor on `c` columns is invertible at `q`.
  obtain ⟨U, hU, hminor⟩ : ∃ U : Finset (Fin P.n), ∃ hU : U.card = c,
      P.lift (P.jacobianMinor c hcm U hU) ∉ q.asIdeal := by
    by_contra hno
    refine hqa ?_
    rw [haeq]
    refine Ideal.sum_mem _ fun s hs ↦ ?_
    have hsCard : s.card = c := (Finset.mem_powersetCard.mp hs).2
    have hmem : P.lift (P.jacobianMinor c hcm s hsCard) ∈ q.asIdeal := by
      by_contra hmem
      exact hno ⟨s, hsCard, hmem⟩
    have hdite : (if h : s.card = c then P.jacobianMinor c hcm s h else 0) =
        P.jacobianMinor c hcm s hsCard := by
      split
      · rfl
      · rename_i hne
        exact absurd hsCard hne
    rw [hdite]
    exact q.asIdeal.mul_mem_left (aI s) hmem
  -- Its product with `a` is elementary standard and still invertible at `q`.
  have helem := isElementaryStandard_mul_lift_jacobianMinor P a c hcn hcm hcond U hU
  have hprod : a * P.lift (P.jacobianMinor c hcm U hU) ∉ q.asIdeal := by
    intro hprod
    rcases q.isPrime.mul_mem_iff_mem_or_mem.mp hprod with h | h
    · exact hqa h
    · exact hminor h
  exact hq ⟨a * P.lift (P.jacobianMinor c hcm U hU), hprod,
    smooth_localizationAway_of_isElementaryStandard helem⟩

/-- **Stacks 16.3.7, (5) ⇒ (1).** The localization of `A` away from a strictly
standard element is smooth over `R`. -/
theorem smooth_localizationAway_of_isStrictlyStandard
    [Algebra.FinitePresentation R A] {a : A}
    (ha : IsStrictlyStandard (R := R) (A := A) a) :
    Algebra.Smooth R (Localization.Away a) :=
  smooth_localization_away_of_mem_singularIdeal R A
    (mem_singularIdeal_of_isStrictlyStandard ha)

end Stacks.Smoothing

end
