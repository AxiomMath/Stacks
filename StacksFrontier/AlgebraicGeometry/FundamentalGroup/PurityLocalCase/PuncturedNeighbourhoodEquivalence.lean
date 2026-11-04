module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.FiniteLocallyFreeAdicFreeStalks
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementQuotientTower
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleNeighbourhoodExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumFiniteEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionFromPuncturedSpectrumNeighborhoods
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison

/-!
# Finite étale covers of the neighbourhoods of the punctured closed fibre

Situation [Stacks, Tag 0BLF]: `(A, 𝔪)` is a Noetherian local ring and `f ∈ 𝔪`.
`U = Spec(A) ∖ {𝔪}` is the punctured spectrum of `A` and `U₀ = U ∩ V(f)` is the punctured
spectrum of `A/fA`, viewed as the closed subscheme of `U` cut out by `f 𝒪_U`. [Stacks, Tag 0BLV]
asserts that if

1. `A` is `f`-adically complete,
2. `f` is a nonzerodivisor, and
3. `H¹_𝔪(A/fA)` and `H²_𝔪(A/fA)` are finite `A`-modules,

then the restriction functor `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}` is an equivalence.

The source's proof is [Stacks, Tag 0EK1] applied to the closed subscheme `U₀ ⊆ U`, with the
completion equivalence of [Stacks, Tag 0EKZ] as its input. This file does the same. Full
faithfulness is [Stacks, Tag 0BLP]
(`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_isAdicComplete`).
The essential image is the extension step of [Stacks, Tag 0EK1]
(`Stacks.FundamentalGroup.exists_finiteEtale_neighbourhood_extension_of_completion`). It is fed
by two inputs. The full faithfulness of completion is [Stacks, Tag 0EKV]. The essential
surjectivity of completion on finite locally free objects is the third conjunct of
[Stacks, Tag 0EKZ], `Stacks.Algebraization.isCompletionNearClosedFiniteLocallyFree_of_principal`.

## Main results

* `Stacks.FundamentalGroup.finite_specialFibreLocalCohomology_of_finite_localCohomologyModule` —
  the two spellings of the finiteness of `H^i_𝔪(A/fA)` agree.
* `Stacks.FundamentalGroup.exists_finiteLocallyFree_completion_puncturedSpectrum_principal` —
  every finite locally free object of `Coh(U, f𝒪_U)` is the completion of a finite locally free
  module on an open neighbourhood of `U₀` in `U`.
* `Stacks.FundamentalGroup.finiteEtaleColimitEquivalence_puncturedSpectrum_of_isAdicComplete` —
  [Stacks, Tag 0BLV].

## Implementation notes

The colimit `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'}` is a directed colimit of categories ([Stacks, Tag
04AX]). Its objects are covers of the individual neighbourhoods `U'`, and its morphisms are
morphisms over some smaller neighbourhood, two of which are identified when they agree after
further shrinking. The restriction functor out of it is fully faithful exactly when
`Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful` holds. It is essentially surjective
exactly when every finite étale cover of `U₀` is isomorphic to the restriction of a finite étale
cover of some neighbourhood. The equivalence is stated as the conjunction of the two, the
vocabulary of [Stacks, Tag 0ELA] and [Stacks, Tag 0BLP].

## References

* [Stacks Project, Tag 0BLV](https://stacks.math.columbia.edu/tag/0BLV)
* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0BLP](https://stacks.math.columbia.edu/tag/0BLP)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0EKZ](https://stacks.math.columbia.edu/tag/0EKZ)
* [Stacks Project, Tag 0EKV](https://stacks.math.columbia.edu/tag/0EKV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

open Stacks.Algebraization Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)

/-- The standing situation of [Stacks, Tag 0EHC] attached to Situation [Stacks, Tag 0BLF]: the
ring `A`, the ideal `I = (f)` and the ideal `𝔞 = 𝔪`. -/
abbrev puncturedAlgebraizationSituation (hf : f ∈ IsLocalRing.maximalIdeal A) :
    AlgebraizationSituation.{u} where
  A := A
  I := Ideal.span {f}
  a := IsLocalRing.maximalIdeal A
  I_le_a := (Ideal.span_singleton_le_iff_mem _).mpr hf

/-- In Situation [Stacks, Tag 0BLF] the finiteness of `H^i_𝔪(A/fA)` in the vocabulary of
[Stacks, Tag 0BLP] is the finiteness of the special-fibre local cohomology of
[Stacks, Tag 0EKZ]. -/
theorem finite_specialFibreLocalCohomology_of_finite_localCohomologyModule
    (hf : f ∈ IsLocalRing.maximalIdeal A) (i : ℤ)
    (h : Module.Finite A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      (ModuleCat.of A (A ⧸ Ideal.span {f})) i)) :
    Module.Finite A (specialFibreLocalCohomology (puncturedAlgebraizationSituation A f hf) f i) :=
  (Module.finite_iff_of_moduleCat_iso
    (localCohomologyWithSupportInIsoLocalCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      (ModuleCat.of A (A ⧸ Ideal.span {f})) i)).mpr h

/-- **The completion functor of [Stacks, Tag 0EKZ] reaches every finite locally free object of
`Coh(U, f𝒪_U)`.** In Situation [Stacks, Tag 0BLF], assume `A` is `f`-adically complete, `f` is a
nonzerodivisor and `H¹_𝔪(A/fA)`, `H²_𝔪(A/fA)` are finite. Then every finite locally free object
of `Coh(U, f𝒪_U)` is the completion of a finite locally free module on an open neighbourhood of
`U₀` in `U`. -/
theorem exists_finiteLocallyFree_completion_puncturedSpectrum_principal
    (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A) (hnzd : f ∈ nonZeroDivisors A)
    (hH1 : Module.Finite A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      (ModuleCat.of A (A ⧸ Ideal.span {f})) 1))
    (hH2 : Module.Finite A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      (ModuleCat.of A (A ⧸ Ideal.span {f})) 2))
    (F : Stacks.Coherent.CoherentAdicSystems
      (idealSheafNearVanishing A (Ideal.span {f}) (IsLocalRing.maximalIdeal A)))
    (hF : IsFiniteLocallyFreeAdic
      (idealSheafNearVanishing A (Ideal.span {f}) (IsLocalRing.maximalIdeal A)) F) :
    IsNeighbourhoodCompletionFiniteLocallyFree
      (idealSheafNearVanishing A (Ideal.span {f}) (IsLocalRing.maximalIdeal A)) F := by
  let S := puncturedAlgebraizationSituation A f hf
  have h : idealSheafNearVanishing A (Ideal.span {f}) (IsLocalRing.maximalIdeal A) =
      idealOnOpen S := idealSheafNearVanishing_eq_idealOnOpen S
  revert F
  rw [h]
  intro F hF
  obtain ⟨V, hV, G, hG, e⟩ := isCompletionNearClosedFiniteLocallyFree_of_principal S F rfl
    hcomplete hnzd
    (finite_specialFibreLocalCohomology_of_finite_localCohomologyModule A f hf 1 hH1)
    (finite_specialFibreLocalCohomology_of_finite_localCohomologyModule A f hf 2 hH2)
    (hasFiniteFreeStalks_of_isFiniteLocallyFreeAdic S F hF)
  exact ⟨V, (support_idealOnOpen_subset S).trans hV, G, hG, e⟩

/-- **[Stacks, Tag 0BLV].** In Situation [Stacks, Tag 0BLF] — `(A, 𝔪)` a Noetherian local ring,
`f ∈ 𝔪`, `U = Spec(A) ∖ {𝔪}` the punctured spectrum of `A` and `U₀ = U ∩ V(f)` the punctured
spectrum of `A/fA` — assume

1. `A` is `f`-adically complete,
2. `f` is a nonzerodivisor, and
3. `H¹_𝔪(A/fA)` and `H²_𝔪(A/fA)` are finite `A`-modules.

Then the restriction functor `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}` is an equivalence.

The colimit is directed, so the functor is an equivalence exactly when the two conjuncts below
hold. The first is that it is fully faithful, in the form
`Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful`: morphisms between restrictions to
`U₀` come from a smaller neighbourhood, and morphisms agreeing on `U₀` agree on a smaller
neighbourhood. The second is that it is essentially surjective: every finite étale cover of `U₀`
is the restriction of a finite étale cover of some open `U'` with `U₀ ⊆ U' ⊆ U`. -/
@[stacks 0BLV "the restriction functor colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} → FÉt_{U₀} is an \
equivalence: fully faithful, and every finite étale cover of U₀ extends to a neighbourhood"]
theorem finiteEtaleColimitEquivalence_puncturedSpectrum_of_isAdicComplete
    (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A) (hnzd : f ∈ nonZeroDivisors A)
    (hH1 : Module.Finite A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      (ModuleCat.of A (A ⧸ Ideal.span {f})) 1))
    (hH2 : Module.Finite A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      (ModuleCat.of A (A ⧸ Ideal.span {f})) 2)) :
    FiniteEtaleColimitFullyFaithful (complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme)
        (idealSheafNearVanishing A (Ideal.span {f}) (IsLocalRing.maximalIdeal A)) ∧
      ∀ C : FiniteEtaleOver
        (idealSheafNearVanishing A (Ideal.span {f}) (IsLocalRing.maximalIdeal A)).subscheme,
      ∃ (W : Neighborhood (complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme)
          (idealSheafNearVanishing A (Ideal.span {f}) (IsLocalRing.maximalIdeal A)))
        (V : FiniteEtaleOver (Neighborhood.open _ _ W).toScheme),
        Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom _ _ W)).obj V ≅ C) :=
  ⟨finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_isAdicComplete A f hf hcomplete hnzd hH1,
    exists_finiteEtale_neighbourhood_extension_of_completion _
      (completionFullyFaithfulComplete_puncturedSpectrum_principal A f hf hcomplete hnzd hH1)
      (exists_finiteLocallyFree_completion_puncturedSpectrum_principal A f hf hcomplete hnzd
        hH1 hH2)⟩

end Stacks.FundamentalGroup

end
