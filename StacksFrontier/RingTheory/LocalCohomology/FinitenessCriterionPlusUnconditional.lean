module

public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessAnnihilatorCriterionPlusConverse
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCriterionPlus

/-!
# Finiteness of the local cohomology of a bounded-below complex and depth, unconditionally

`StacksFrontier/RingTheory/LocalCohomology/FinitenessCriterionPlus.lean` states Tag 0EI2 relative to
two predicates on the base ring:

* `Stacks.LocalCohomology.AnnihilatorDepthCriterionPlus`, which is Tag 0EHZ, the equivalence
  between uniform annihilation of `H^i_T(K)` for `i ≤ s` by one ideal supported in `T` and the
  depth-dimension inequality, and
* `Stacks.LocalCohomology.FinitenessAnnihilatorCriterionPlus`, which is Tag 0EI1, the equivalence
  between that uniform annihilation and finiteness of the same modules.

Both are now available. The first is
`Stacks.LocalCohomology.annihilatorDepthCriterionPlus` in
`StacksFrontier/RingTheory/LocalCohomology/FaltingsAnnihilator.lean`, at the universe instance where
the modules and the dualizing complex live in the ring's own universe. The second is assembled in
`StacksFrontier/RingTheory/LocalCohomology/FinitenessAnnihilatorCriterionPlusConverse.lean`, whose
`Stacks.LocalCohomology.localCohomologyWithSupportInPlus_finite_iff_exists_annihilator` combines
the implication from finiteness to an annihilator, proved in
`StacksFrontier/RingTheory/LocalCohomology/FinitenessAnnihilatorCriterionPlus.lean`, with the
converse proved there. This file feeds both in, so that Tag 0EI2 holds with no hypothesis beyond
the existence of a dualizing complex.

## Main results

* `Stacks.LocalCohomology.finitenessAnnihilatorCriterionPlus` — Tag 0EI1 in the predicate form in
  which Tag 0EI2 consumes it.
* `Stacks.LocalCohomology.localCohomologyWithSupportInPlus_finite_iff_depth_add_dim_sameUniverse`
  — **Stacks 0EI2**, the equivalence between finiteness of `H^i_T(K)` for `i ≤ s` and the
  depth-dimension inequality, with nothing assumed beyond the hypotheses the source assumes.
* `Stacks.LocalCohomology.depth_add_dim_gt_of_finite_localCohomologyWithSupportInPlus_sameUniverse`
  — its implication from finiteness to the depth-dimension inequality, recorded separately
  because that half needs Tag 0EHZ alone.

## Implementation notes

The universes are the ones at which Tag 0EHZ is available: the modules of `K` and those of the
dualizing complex all live in the ring's universe. Tag 0EI1 is available in the two-universe
generality of the predicate, so it is the dualizing-complex input that fixes this.

As in `FinitenessCriterionPlus.lean`, the two criteria are applied at `T' = T`, which is the
shape in which the source states this result; the dimension of `(A/p)_q` is the Krull dimension
of the localization of `A ⧸ p` at the image of `q`, compared against the integer degree in the
extended integers through `Stacks.Algebraization.krullDimToEInt`; and membership in `D⁺_{Coh}(A)`
is expressed as a bounded-below object together with finiteness of every cohomology module.

## References

* [Stacks Project, Tag 0EI2](https://stacks.math.columbia.edu/tag/0EI2)
* [Stacks Project, Tag 0EI1](https://stacks.math.columbia.edu/tag/0EI1)
* [Stacks Project, Tag 0EHZ](https://stacks.math.columbia.edu/tag/0EHZ)
-/
@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- **Stacks 0EI2, the implication (1) ⟹ (2).** Let `A` be a Noetherian ring with a dualizing
complex, let `T ⊆ Spec(A)` be stable under specialization, let `s ∈ ℤ` and let `K` be a
bounded-below complex with finite cohomology modules. If `H^i_T(K)` is finite for every `i ≤ s`,
then `depth_{A_p}(K_p) + dim((A/p)_q) > s` for every `p ∉ T` and `q ∈ T` with `p ⊆ q`.

This is `depth_add_dim_gt_of_finite_localCohomologyWithSupportInPlus` with its hypothesis
`AnnihilatorDepthCriterionPlus` supplied by `annihilatorDepthCriterionPlus`, Tag 0EHZ. -/
theorem depth_add_dim_gt_of_finite_localCohomologyWithSupportInPlus_sameUniverse
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex omega)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (s : ℤ) (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hfin : ∀ i : ℤ, i ≤ s →
      Module.Finite A (localCohomologyWithSupportInPlus.{u, u} A T K i)) :
    ∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → (hpq : p.asIdeal ≤ q.asIdeal) →
      letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
        Ideal.isPrime_map_quotientMk_of_isPrime hpq
      (DerivedCategory.Plus.depth.{u, u} (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (localizedComplex.{u, u} p K) : EInt) +
        Stacks.Algebraization.krullDimToEInt
          (ringKrullDim (Localization.AtPrime
            (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) > (s : EInt) :=
  depth_add_dim_gt_of_finite_localCohomologyWithSupportInPlus.{u, u, u} A
    (annihilatorDepthCriterionPlus A) omega homega T hT s K hK hfin

/-- **Stacks 0EI1, as the predicate Tag 0EI2 consumes.** For every specialization-closed `T` and
every bounded-below complex `K` with finite cohomology, the local cohomology `H^i_T(K)` is finite
for all `i ≤ n` exactly when one ideal whose zero locus lies in `T` annihilates all of them.

This is `localCohomologyWithSupportInPlus_finite_iff_exists_annihilator`, with the arguments
reordered to match the predicate. -/
theorem finitenessAnnihilatorCriterionPlus (A : Type u) [CommRing A] [IsNoetherianRing A] :
    FinitenessAnnihilatorCriterionPlus.{u, v} A :=
  fun T hT K hK n ↦
    localCohomologyWithSupportInPlus_finite_iff_exists_annihilator.{u, v} A T hT K hK n

/-- **Stacks 0EI2, Proposition 51.14.2: finiteness of local cohomology, III.** Let `A` be a
Noetherian ring admitting a dualizing complex, let `T ⊆ Spec(A)` be stable under specialization,
let `s ∈ ℤ` and let `K` be an object of the bounded-below derived category of `A`-modules whose
cohomology modules are all finite. Then `H^i_T(K)` is finite for every `i ≤ s` if and only if
`depth_{A_p}(K_p) + dim((A/p)_q) > s` for every pair of primes `p ∉ T`, `q ∈ T` with `p ⊆ q`.

This is the composition the source performs: the finiteness criterion of Tag 0EI1 replaces
finiteness through degree `s` by uniform annihilation by one ideal supported in `T`, and the
annihilator criterion of Tag 0EHZ at `T' = T` replaces that uniform annihilation by the
depth-dimension inequality. Both criteria are proved in this library, so nothing is assumed here
beyond the hypotheses of the source. -/
@[stacks 0EI2]
theorem localCohomologyWithSupportInPlus_finite_iff_depth_add_dim_sameUniverse
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex omega)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (s : ℤ) (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    (∀ i : ℤ, i ≤ s →
      Module.Finite A (localCohomologyWithSupportInPlus.{u, u} A T K i)) ↔
      (∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → (hpq : p.asIdeal ≤ q.asIdeal) →
        letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
          Ideal.isPrime_map_quotientMk_of_isPrime hpq
        (DerivedCategory.Plus.depth.{u, u} (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (localizedComplex.{u, u} p K) : EInt) +
          Stacks.Algebraization.krullDimToEInt
            (ringKrullDim (Localization.AtPrime
              (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) > (s : EInt)) :=
  localCohomologyWithSupportInPlus_finite_iff_depth_add_dim.{u, u, u} A
    (finitenessAnnihilatorCriterionPlus.{u, u} A) (annihilatorDepthCriterionPlus A)
    omega homega T hT s K hK

end Stacks.LocalCohomology

end
