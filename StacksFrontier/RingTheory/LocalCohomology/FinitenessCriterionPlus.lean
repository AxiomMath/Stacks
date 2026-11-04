module

public import StacksFrontier.RingTheory.LocalCohomology.FinitenessAnnihilatorCriterionPlus
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCriterion

/-!
# Finiteness of the local cohomology of a bounded-below complex and depth

Let `A` be a Noetherian ring admitting a dualizing complex, let `T ⊆ Spec(A)` be stable under
specialization, let `s ∈ ℤ` and let `K` be an object of the bounded-below derived category of
`A`-modules whose cohomology modules are all finite. The local cohomology modules `H^i_T(K)` are
finite for every `i ≤ s` exactly when
$$ \operatorname{depth}_{A_p}(K_p) + \dim((A/p)_q) > s $$
for every pair of primes `p ∉ T`, `q ∈ T` with `p ⊆ q`.

This is the complex-level companion of the module-level criterion in
`StacksFrontier/RingTheory/LocalCohomology/FinitenessCriterion.lean`, and the source proves it as a
formal consequence of two earlier results:

* the annihilator criterion for a bounded-below complex, which relates the depth-dimension
  inequality to uniform annihilation of `H^i_T(K)` by one ideal supported in `T`, written here as
  the predicate `Stacks.LocalCohomology.AnnihilatorDepthCriterionPlus`, and
* the finiteness criterion for a bounded-below complex, which relates that uniform annihilation to
  finiteness, written here as the predicate
  `Stacks.LocalCohomology.FinitenessAnnihilatorCriterionPlus`.

Composing the two at `T' = T` gives the equivalence above, and that composition is what this file
carries out.

## What is proved and what is assumed

The implication from finiteness to the depth-dimension inequality needs only the first of the two
inputs: the step from finiteness to a uniform annihilator is
`Stacks.LocalCohomology.exists_annihilator_localCohomologyWithSupportInPlus_of_finite`, which is
proved in `StacksFrontier/RingTheory/LocalCohomology/FinitenessAnnihilatorCriterionPlus.lean`. So
`depth_add_dim_gt_of_finite_localCohomologyWithSupportInPlus` below assumes only
`AnnihilatorDepthCriterionPlus`.

That predicate is itself proved elsewhere in this library, by
`Stacks.LocalCohomology.annihilatorDepthCriterionPlus` in
`StacksFrontier/RingTheory/LocalCohomology/FaltingsAnnihilator.lean`, at the universe instance where
the modules live in the ring's own universe. Supplying it as the hypothesis `hEHZ` therefore makes
the first theorem below unconditional at that instance; it is kept as a hypothesis here so that
the statements hold in the generality of the predicates, and so that this file does not depend on
the dualizing-complex machinery that the proof of that predicate needs.

The converse implication additionally needs `FinitenessAnnihilatorCriterionPlus`, the step from a
uniform annihilator back to finiteness. Only one of its two directions is available: the direction
from finiteness to the annihilator is proved, and the direction used here is the one the source
proves by a descending induction on a degree bounding `K` below. That direction is **not** proved
in this library, so the full equivalence below carries the predicate as an explicit hypothesis and
its label records this.

The hypothesis is not a restatement of the conclusion it helps prove: the predicate mentions
neither depth nor the dualizing complex, and speaks only about annihilating ideals, while the
conclusion is the depth-dimension inequality.

## Main results

* `Stacks.LocalCohomology.depth_add_dim_gt_of_finite_localCohomologyWithSupportInPlus` — the
  implication from finiteness to the depth-dimension inequality, assuming only the annihilator
  criterion.
* `Stacks.LocalCohomology.localCohomologyWithSupportInPlus_finite_iff_depth_add_dim` — the full
  equivalence, assuming both criteria.

## Implementation notes

The two criteria are stated for nested specialization-closed subsets `T ⊆ T'`; here both are
taken to be `T`, which is the shape in which the source states this result. The dimension of
`(A/p)_q` is the Krull dimension of the localization of `A ⧸ p` at the image of `q`, compared
against the integer degree in the extended integers through
`Stacks.Algebraization.krullDimToEInt`, exactly as in the two criteria; the derived depth of the
localization `K_p` is `DerivedCategory.Plus.depth` of
`Stacks.LocalCohomology.localizedComplex`.

Membership in `D⁺_{Coh}(A)` is expressed as a bounded-below object together with finiteness of
every cohomology module, which is the hypothesis `hK`.

## References

* [Stacks Project, Tag 0EI2](https://stacks.math.columbia.edu/tag/0EI2)
* [Stacks Project, Tag 0EI1](https://stacks.math.columbia.edu/tag/0EI1)
* [Stacks Project, Tag 0EHZ](https://stacks.math.columbia.edu/tag/0EHZ)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.LocalCohomology

/-- **Stacks 0EI2, the implication (1) ⟹ (2).** Let `A` be a Noetherian ring with a dualizing
complex, let `T ⊆ Spec(A)` be stable under specialization, let `s ∈ ℤ` and let `K` be a
bounded-below complex with finite cohomology modules. If `H^i_T(K)` is finite for every `i ≤ s`,
then `depth_{A_p}(K_p) + dim((A/p)_q) > s` for every `p ∉ T` and `q ∈ T` with `p ⊆ q`.

Finiteness gives one ideal supported in `T` annihilating all of `H^i_T(K)` for `i ≤ s`, by
`exists_annihilator_localCohomologyWithSupportInPlus_of_finite`; the annihilator criterion of
Tag 0EHZ at `T' = T` turns that ideal into the depth-dimension inequality. -/
@[stacks 0EI2 "the implication (1) ⟹ (2), assuming only Tag 0EHZ's annihilator criterion
  (`AnnihilatorDepthCriterionPlus`), which is proved in `FaltingsAnnihilator.lean`; the step from
  finiteness to a uniform annihilator is proved"]
theorem depth_add_dim_gt_of_finite_localCohomologyWithSupportInPlus
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hEHZ : AnnihilatorDepthCriterionPlus.{u, v, w} A)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (homega : Dualizing.IsDualizingComplex omega)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (s : ℤ) (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (hfin : ∀ i : ℤ, i ≤ s →
      Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A T K i)) :
    ∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → (hpq : p.asIdeal ≤ q.asIdeal) →
      letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
        Ideal.isPrime_map_quotientMk_of_isPrime hpq
      (DerivedCategory.Plus.depth.{u, v} (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (localizedComplex.{u, v} p K) : EInt) +
        Stacks.Algebraization.krullDimToEInt
          (ringKrullDim (Localization.AtPrime
            (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) > (s : EInt) :=
  (hEHZ omega homega T T Set.Subset.rfl hT hT s K hK).mp
    (exists_annihilator_localCohomologyWithSupportInPlus_of_finite.{u, v} A T K s hfin)

/-- **Stacks 0EI2, Proposition 51.14.2: finiteness of local cohomology, III.** Let `A` be a
Noetherian ring with a dualizing complex, let `T ⊆ Spec(A)` be stable under specialization, let
`s ∈ ℤ` and let `K` be a bounded-below complex with finite cohomology modules. Then `H^i_T(K)` is
finite for every `i ≤ s` if and only if `depth_{A_p}(K_p) + dim((A/p)_q) > s` for every `p ∉ T`
and `q ∈ T` with `p ⊆ q`.

This is the composition the source performs: the finiteness criterion of Tag 0EI1 replaces
finiteness through degree `s` by uniform annihilation by one ideal supported in `T`, and the
annihilator criterion of Tag 0EHZ at `T' = T` replaces that uniform annihilation by the
depth-dimension inequality. -/
@[stacks 0EI2 "the full equivalence (1) ⟺ (2), assuming Tag 0EI1's finiteness criterion
  (`FinitenessAnnihilatorCriterionPlus`), whose direction from an annihilator to finiteness is not
  proved in this library, and Tag 0EHZ's annihilator criterion
  (`AnnihilatorDepthCriterionPlus`), which is proved in `FaltingsAnnihilator.lean`"]
theorem localCohomologyWithSupportInPlus_finite_iff_depth_add_dim
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hEI1 : FinitenessAnnihilatorCriterionPlus.{u, v} A)
    (hEHZ : AnnihilatorDepthCriterionPlus.{u, v, w} A)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (homega : Dualizing.IsDualizingComplex omega)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (s : ℤ) (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :
    (∀ i : ℤ, i ≤ s →
      Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A T K i)) ↔
      (∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → (hpq : p.asIdeal ≤ q.asIdeal) →
        letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
          Ideal.isPrime_map_quotientMk_of_isPrime hpq
        (DerivedCategory.Plus.depth.{u, v} (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (localizedComplex.{u, v} p K) : EInt) +
          Stacks.Algebraization.krullDimToEInt
            (ringKrullDim (Localization.AtPrime
              (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) > (s : EInt)) :=
  (hEI1 T hT K hK s).trans (hEHZ omega homega T T Set.Subset.rfl hT hT s K hK)

end Stacks.LocalCohomology

end
