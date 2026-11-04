module

public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Existence of K-injective resolutions in a Grothendieck abelian category

Every cochain complex in a Grothendieck abelian category admits a quasi-isomorphism into a
K-injective complex. This is the existential shadow of the *functorial* resolution
`Stacks.Injectives.kInjectiveResolutionInclusion`, and it is the shape in which the hypothesis
is consumed: the pointwise criterion
`Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective`
(and its relatives) asks for a function producing, for each complex, *some* K-injective complex
receiving a quasi-isomorphism from it, with no functoriality attached. Stating it once here
keeps the several derived-functor developments that need it from each repeating the witness.

## Main results

* `Stacks.Cohomology.moduleExistsKInjectiveResolution`: every cochain complex in a Grothendieck
  abelian category receives a quasi-isomorphism into a K-injective complex.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Cohomology

/-- Every cochain complex in a Grothendieck abelian category admits a quasi-isomorphism into a
`K`-injective complex. -/
theorem moduleExistsKInjectiveResolution (A : Type*) [Category A] [Abelian A]
    [IsGrothendieckAbelian A] (K : CochainComplex A ℤ) :
    ∃ (I : CochainComplex A ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor A).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion A).app K, inferInstance, inferInstance⟩

end Stacks.Cohomology
