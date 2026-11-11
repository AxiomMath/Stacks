module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplement
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionFromNeighborhoods
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Finite étale covers near a hypersurface on a punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`. Write `U = Spec(A) ∖ {𝔪}` for the punctured
spectrum of `A` and `U₀ = U ∩ V(f)` for the zero locus of `f` on it, which is the punctured
spectrum of `A/fA` viewed as a closed subscheme of `U`. This is Situation
[Stacks, Tag 0BLF]. [Stacks, Tag 0BLP] asserts that if

1. `A` is `f`-adically complete,
2. `f` is a nonzerodivisor, and
3. `H¹_𝔪(A/fA)` is a finite `A`-module,

then the restriction functor `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}` is fully faithful.

The source deduces this from [Stacks, Tag 0ELA] — full faithfulness of the restriction functor
from the neighbourhoods of a closed subscheme, granted full faithfulness of the completion
functor on finite locally free objects — applied to the output of [Stacks, Tag 0EKV], which
supplies that completion hypothesis from the three hypotheses above.

## Main results

* `Stacks.FundamentalGroup.complementZeroLocus_maximalIdeal_eq_puncturedSpectrum` — the
  complement of the zero locus of `𝔪` is the punctured spectrum, so the scheme `U` of
  Situation [Stacks, Tag 0BLF] is the one over which the neighbourhoods of `U₀` and the ideal
  sheaf `f 𝒪_U` are already available.
* `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_puncturedSpectrum_principal` —
  the conclusion of [Stacks, Tag 0BLP] from the section-extension property. The tag itself is
  registered on
  `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_isAdicComplete`
  (`StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumFiniteEtaleFullyFaithful`),
  which proves it from the three hypotheses alone.

## Implementation notes

**How the statement is spelled.** The neighbourhoods `𝒱 = {U' : U₀ ⊆ U' ⊆ U}` and the colimit
`colim_𝒱 FÉt_{U'}` are those of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionFromNeighborhoods`: the index poset is
`Stacks.FundamentalGroup.Neighborhood U Y` for `Y` an ideal sheaf on `U`, and full faithfulness
of the restriction functor out of the directed colimit of the categories `FÉt_{U'}` is
`Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful U Y`, which spells out the two
shrinking conditions that colimit description amounts to. The ideal sheaf is
`Stacks.Algebraization.idealSheafNearVanishing A (Ideal.span {f}) 𝔪`, that is `f 𝒪_U`, whose
closed subscheme is `Stacks.Algebraization.principalFormalLocus`, the zero locus `U₀` of `f` on
`U`. So `U₀` enters as a closed subscheme of `U` rather than as `Spec(A/fA) ∖ {𝔪}`; the two are
the same closed subscheme of `U`, and the first description is the one the colimit over the
intermediate opens is stated with.

**The section-extension hypothesis.** The declaration here consumes
`Stacks.FundamentalGroup.SectionsExtendNearSubscheme`, the shrinking form of the conclusion of
[Stacks, Tag 0EL8], through
`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme`; the
three hypotheses of the tag are recorded but not consumed. The library does prove that input from
the three hypotheses: [Stacks, Tag 0EKV] is
`Stacks.Algebraization.completionFullyFaithfulComplete_principal` and [Stacks, Tag 0ELA] is
`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete`;
their composite, the complete statement of [Stacks, Tag 0BLP], lives in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumFiniteEtaleFullyFaithful`, which
imports this module.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0BLP](https://stacks.math.columbia.edu/tag/0BLP)
* [Stacks Project, Tag 0EKV](https://stacks.math.columbia.edu/tag/0EKV)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

open Stacks.Algebraization Stacks.LocalCohomology

/-- **The punctured spectrum is the complement of the zero locus of the maximal ideal.** A prime
of a local ring contains the maximal ideal exactly when it is the closed point. -/
theorem complementZeroLocus_maximalIdeal_eq_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A] :
    complementZeroLocus A (IsLocalRing.maximalIdeal A) = Stacks.Divisors.puncturedSpectrum A := by
  have hzero : PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A) =
      {IsLocalRing.closedPoint A} := by
    ext p
    change IsLocalRing.maximalIdeal A ≤ p.asIdeal ↔ p = IsLocalRing.closedPoint A
    refine ⟨fun h => PrimeSpectrum.ext (le_antisymm
      (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) h), ?_⟩
    rintro rfl
    exact le_rfl
  refine TopologicalSpace.Opens.ext ?_
  change (PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A))ᶜ =
    ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))ᶜ
  rw [hzero]

/-- **The conclusion of [Stacks, Tag 0BLP] from the section-extension property.** In Situation
[Stacks, Tag 0BLF] — a Noetherian local ring `(A, 𝔪)` and an element `f ∈ 𝔪`, with
`U = Spec(A) ∖ {𝔪}` the punctured spectrum and `U₀ = U ∩ V(f)` the zero locus of `f` on it —
if sections of finite étale covers of neighbourhoods of `U₀` extend and are determined after
shrinking (`Stacks.FundamentalGroup.SectionsExtendNearSubscheme`), then the restriction functor
`colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}` is fully faithful.

The hypotheses (1)–(3) of the tag (`A` is `f`-adically complete, `f` is a nonzerodivisor,
`H¹_𝔪(A/fA)` is a finite `A`-module) are recorded but not consumed. This declaration is not the
registration of the tag: [Stacks, Tag 0BLP] itself, proved from (1)–(3) alone through
[Stacks, Tag 0EKV] and [Stacks, Tag 0ELA], is
`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_isAdicComplete`. -/
theorem finiteEtaleColimitFullyFaithful_puncturedSpectrum_principal
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
    (_hf : f ∈ IsLocalRing.maximalIdeal A)
    (_hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (_hnzd : f ∈ nonZeroDivisors A)
    (_hfinite : Module.Finite A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      (ModuleCat.of A (A ⧸ Ideal.span {f})) 1))
    (hsections : SectionsExtendNearSubscheme
      (complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme)
      (idealSheafNearVanishing A (Ideal.span {f}) (IsLocalRing.maximalIdeal A))) :
    FiniteEtaleColimitFullyFaithful
      (complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme)
      (idealSheafNearVanishing A (Ideal.span {f}) (IsLocalRing.maximalIdeal A)) :=
  finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme _ _ hsections

end Stacks.FundamentalGroup

end
