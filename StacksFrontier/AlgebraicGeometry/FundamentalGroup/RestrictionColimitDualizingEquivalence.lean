module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementQuotientTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.FiniteLocallyFreeAdicFreeStalks
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.LocalPrincipalEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsAssociatedPointInduction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumFormalSections
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PullbackMultiplicationLaws
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionColimitEquivalenceOfCompletion

/-!
# Finite étale covers near a hypersurface of a punctured spectrum, over a ring with a dualizing
complex

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`. Write `X = Spec(A)`, `X₀ = Spec(A/fA)`,
`U = X ∖ {𝔪}` for the punctured spectrum and `U₀ = U ∩ V(f)` for the zero locus of `f` on it.
[Stacks, Tag 0DXY] asserts that if

1. `A` has a dualizing complex and is `f`-adically complete, and
2. one of
   * (a) `A_f` is `(S₂)` and every irreducible component of `X` not contained in `X₀` has
     dimension `≥ 4`, or
   * (b) `depth(A_𝔭) + dim(A/𝔭) > 3` for every prime `𝔭 ∉ V(f)` with `V(𝔭) ∩ V(f) ≠ {𝔪}`,

then the restriction functor `colim_{U₀ ⊆ U' ⊆ U open} FÉt_{U'} ⟶ FÉt_{U₀}` is an equivalence.

The source's proof is [Stacks, Tag 0EK1] for the closed subscheme `U₀ ⊆ U`, fed by the completion
equivalence of [Stacks, Tag 0EKY]. This file does the same, in two halves.

* **Full faithfulness.** [Stacks, Tag 0ELA] turns full faithfulness of the completion functor
  `colim_{U'} Coh(𝒪_{U'}) ⟶ Coh(U, f𝒪_U)` on finite locally free objects — condition (4) of
  [Stacks, Tag 0EK2] — into the conclusion. That condition is reached from condition (1) of the
  same tag: `U` is quasi-affine, and `colim_{U'} Γ(U', 𝒪_{U'}) = lim_n Γ(U, 𝒪_U/fⁿ𝒪_U)` by
  [Stacks, Tag 0EG2], whose hypothesis is the dimension bound at the associated points of
  `𝒪_U`. Those points have associated primes of `A` for their primes, and at such a prime `𝔭`
  outside `V(f)` whose closure meets `V(f)` away from `𝔪` the hypothesis (2) of the tag gives
  `dim(A/𝔭) ≥ 3`, which is the bound because `cd(A, (f)) ≤ 1`.
* **The essential image.** Every finite locally free object of `Coh(U, f𝒪_U)` is the completion
  of a finite locally free module on a neighbourhood of `U₀`, which is the
  essential-surjectivity half of [Stacks, Tag 0EKY]; the algebraization step of
  [Stacks, Tag 0EK1] then extends every finite étale cover of `U₀` to a neighbourhood.

## Main definitions

* `Stacks.FundamentalGroup.DepthDimensionCondition` — hypothesis (2) above, as a condition on `A`
  and `f`.
* `Stacks.FundamentalGroup.puncturedSpectrumSituation` — the standing situation of
  [Stacks, Tag 0EHC] with the ideals `(f) ⊆ 𝔪`.

## Main results

* `Stacks.FundamentalGroup.three_le_ringKrullDim_quotient_of_depthDimension` — hypothesis (2)
  bounds `dim(A/𝔭)` below by `3` at an associated prime `𝔭` of `A` outside `V(f)` whose closure
  meets `V(f)` away from `𝔪`.
* `Stacks.FundamentalGroup.associatedPointsClosureDimensionBound_unit_of_depthDimension` — the
  hypothesis of [Stacks, Tag 0EG2] for the structure sheaf of `U`.
* `Stacks.FundamentalGroup.completionFullyFaithfulComplete_puncturedSpectrum_of_dualizing` —
  condition (4) of [Stacks, Tag 0EK2] at the closed subscheme `U₀ ⊆ U`.
* `Stacks.FundamentalGroup.exists_finiteLocallyFree_completion_puncturedSpectrum_of_dualizing` —
  the essential-surjectivity half of [Stacks, Tag 0EKY], in the vocabulary of
  `Stacks.Algebraization.IsNeighbourhoodCompletionFiniteLocallyFree`.
* `Stacks.FundamentalGroup.finiteEtaleColimitEquivalence_puncturedSpectrum_of_dualizing` —
  **[Stacks, Tag 0DXY]**.

## Implementation notes

`U` is `Stacks.LocalCohomology.complementZeroLocus A 𝔪`, the punctured spectrum by
`Stacks.FundamentalGroup.complementZeroLocus_maximalIdeal_eq_puncturedSpectrum`, and `U₀` is the
closed subscheme of `U` cut out by `f 𝒪_U` (`Stacks.Algebraization.idealSheafNearVanishing`).

The colimit `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'}` is a directed colimit of categories,
[Stacks, Tag 04AX]: its objects are covers of the individual neighbourhoods `U'`, and a morphism
between two of them is a morphism over some smaller neighbourhood, two such being identified when
they agree after shrinking further. A functor out of it is an equivalence exactly when it is
fully faithful in that sense — `Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful` — and
essentially surjective, which says that every finite étale cover of `U₀` is isomorphic to the
restriction of a finite étale cover of some neighbourhood. The conclusion is the conjunction of
the two, the same shape as for [Stacks, Tag 0BLV].

Hypothesis (2)(a) reads "`A_f` is `(S₂)`" as `PropertySkRing (Localization.Away f) 2`, Serre's
condition of [Stacks, Tag 031P] for the ring `A_f`, and the dimension condition on the
irreducible components of `X` not contained in `X₀` as a condition on the minimal primes `𝔭` of
`A` with `f ∉ 𝔭`. In (2)(b), `V(f)` is the set of primes containing `f`.

The dualizing complex is asked for in an arbitrary model `[HasDerivedCategory (ModuleCat A)]` of
the derived category, and moved to the standard model — the one the cited results are stated in —
by `Stacks.Dualizing.exists_isDualizingComplex_iff_of_models`.

## References

* [Stacks Project, Tag 0DXY](https://stacks.math.columbia.edu/tag/0DXY)
* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0EKY](https://stacks.math.columbia.edu/tag/0EKY)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open Stacks.LocalCohomology (complementZeroLocus cohomologicalDimension)

universe u w

namespace Stacks.FundamentalGroup

open Stacks.Algebraization

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)

/-- **Hypothesis (2) of [Stacks, Tag 0DXY]**, as a disjunction of its two branches: either `A_f`
satisfies Serre's condition `(S₂)` and `dim(A/𝔭) ≥ 4` for every minimal prime `𝔭` of `A` with
`f ∉ 𝔭`, or `depth(A_𝔭) + dim(A/𝔭) > 3` for every prime `𝔭` with `f ∉ 𝔭` whose closure meets
`V(f)` in more than the closed point. -/
public def DepthDimensionCondition : Prop :=
  (PropertySkRing (Localization.Away f) 2 ∧
      ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal → f ∉ p.asIdeal →
        (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
    (∀ p : PrimeSpectrum A, f ∉ p.asIdeal →
      ({q : PrimeSpectrum A | p.asIdeal ≤ q.asIdeal} ∩
        {q : PrimeSpectrum A | f ∈ q.asIdeal}) ≠
        {⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩} →
      (3 : WithBot ℕ∞) <
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
          ringKrullDim (A ⧸ p.asIdeal))

/-- **Hypothesis (2) of [Stacks, Tag 0DXY] bounds the dimension at an associated prime.** Let `𝔭`
be an associated prime of `A` with `f ∉ 𝔭` whose closure meets `V(f)` in more than the closed
point. Then `dim(A/𝔭) ≥ 3`.

An associated prime has `depth(A_𝔭) = 0`, so branch (b) gives `dim(A/𝔭) > 3` outright. Under
branch (a) the Serre condition `(S₂)` at `A_𝔭` reads `min(2, dim(A_𝔭)) ≤ depth(A_𝔭) = 0`, which
forces the height of `𝔭` to vanish; so `𝔭` is a minimal prime and `dim(A/𝔭) ≥ 4`. -/
public theorem three_le_ringKrullDim_quotient_of_depthDimension
    (hcond : DepthDimensionCondition A f) (p : PrimeSpectrum A)
    (hpass : IsAssociatedPrimeStacks A A p.asIdeal) (hf : f ∉ p.asIdeal)
    (hne : ({q : PrimeSpectrum A | p.asIdeal ≤ q.asIdeal} ∩
      {q : PrimeSpectrum A | f ∈ q.asIdeal}) ≠
        {⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩}) :
    (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal) := by
  have hdepth0 : Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal) = 0 := by
    rw [← Module.depth_eq_depth_of_linearEquiv _
      ((LocalizedModule.equivTensorProduct p.asIdeal.primeCompl A).trans
        (Algebra.TensorProduct.rid A (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toLinearEquiv)]
    exact depth_localization_eq_zero_of_mem_associatedPrimes p
      ((Stacks.Depth.isAssociatedPrimeStacks_iff_mem_associatedPrimes p.asIdeal).1 hpass)
  rcases hcond with ⟨hS2, hcomp⟩ | hb
  · have hS2p : PropertySkRing (Localization.AtPrime p.asIdeal) 2 :=
      propertySkRing_localizationAtPrime_of_away A f 2 hS2 p hf
    let m := maximalIdeal (Localization.AtPrime p.asIdeal)
    have hm := hS2p m
    let e : Localization.AtPrime m ≃+* Localization.AtPrime p.asIdeal :=
      (IsLocalization.atUnits (Localization.AtPrime p.asIdeal) m.primeCompl
        (S := Localization.AtPrime m) fun x hx => notMem_maximalIdeal.mp hx).symm.toRingEquiv
    rw [e.ringKrullDim, _root_.ringDepth_eq_of_ringEquiv e, ringDepth_eq_depth_maximalIdeal,
      hdepth0, IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal, WithBot.unbotD_coe] at hm
    have hh : p.asIdeal.height = 0 := by
      rcases min_le_iff.mp hm with h2 | h0
      · exact absurd h2 (by norm_num)
      · exact nonpos_iff_eq_zero.mp h0
    exact le_trans (by norm_num) (hcomp p (Ideal.height_eq_zero_iff.mp hh) hf)
  · simpa [hdepth0] using (hb p hf hne).le

/-- **The hypothesis of [Stacks, Tag 0EG2] for the structure sheaf of the punctured spectrum.**
Under hypothesis (2) of [Stacks, Tag 0DXY], whenever `x` is an associated point of `𝒪_U` outside
`V(f)` whose closure meets `V(f)` away from the closed point, every point `z` of
`closure {x} ∩ {𝔪}` has `dim(𝒪_{closure {x}, z}) > cd(A, (f)) + 1`.

The structure sheaf is finite locally free, so the prime of such an `x` is an associated prime of
`A`; the only `z` as above is the closed point, where the local dimension of the closure is
`dim(A/𝔭)`; and `cd(A, (f)) ≤ 1`, a principal ideal needing one Koszul step. So the bound is
`dim(A/𝔭) ≥ 3`, which is
`Stacks.FundamentalGroup.three_le_ringKrullDim_quotient_of_depthDimension`. -/
public theorem associatedPointsClosureDimensionBound_unit_of_depthDimension
    (hcond : DepthDimensionCondition A f) :
    AssociatedPointsClosureDimensionBound A (Ideal.span {f}) (maximalIdeal A)
      (SheafOfModules.unit (complementZeroLocus A (maximalIdeal A) : Scheme).ringCatSheaf) := by
  rintro x hx hxI ⟨y, hxy, hyI, hya⟩ z hxz haz
  have hpass : IsAssociatedPrimeStacks A A x.1.asIdeal :=
    Stacks.Divisors.isAssociatedPrimeStacks_of_mem_associatedPoints_complementZeroLocus
      A (maximalIdeal A) _ ((Scheme.Modules.isFiniteLocallyFree_iff _).2
        (Stacks.Algebraization.isFiniteLocallyFree_unit
          (complementZeroLocus A (maximalIdeal A) : Scheme))) hx
  have hf : f ∉ x.1.asIdeal := fun h => hxI ((Ideal.span_singleton_le_iff_mem _).2 h)
  have hne : ({q : PrimeSpectrum A | x.1.asIdeal ≤ q.asIdeal} ∩
      {q : PrimeSpectrum A | f ∈ q.asIdeal}) ≠
        {⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩} := by
    intro h
    have hy : y ∈ ({q : PrimeSpectrum A | x.1.asIdeal ≤ q.asIdeal} ∩
        {q : PrimeSpectrum A | f ∈ q.asIdeal}) :=
      ⟨hxy, (Ideal.span_singleton_le_iff_mem _).1 hyI⟩
    rw [h, Set.mem_singleton_iff] at hy
    exact hya (by rw [hy])
  have hdim := three_le_ringKrullDim_quotient_of_depthDimension A f hcond x.1 hpass hf hne
  obtain rfl : z = closedPoint A := by
    ext1
    exact ((maximalIdeal.isMaximal A).eq_of_le z.isPrime.ne_top haz).symm
  have hcd : cohomologicalDimension A (Ideal.span {f})
      (Ideal.span {f}).fg_of_isNoetherianRing ≤ 1 :=
    Stacks.LocalCohomology.cohomologicalDimension_span_singleton_le_one A f
  have hthree : ((3 : ℤ) : EInt) ≤ krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal)) := by
    refine le_trans (le_of_eq ?_) (krullDimToEInt_mono hdim)
    exact (krullDimToEInt_natCast 3).symm
  exact lt_of_lt_of_le (WithBotTop.coe_lt_coe.mpr (by omega))
    (hthree.trans_eq (congrArg krullDimToEInt (closureLocalDimension_closedPoint A _).symm))

/-- **Completion near `U₀` is fully faithful on finite locally free objects.** In Situation
[Stacks, Tag 0BLF] assume `A` has a dualizing complex, is `f`-adically complete, and satisfies
hypothesis (2) of [Stacks, Tag 0DXY]. Then the completion functor
`colim_{U₀ ⊆ U' ⊆ U} Coh(𝒪_{U'}) ⟶ Coh(U, f𝒪_U)` is fully faithful on the finite locally free
objects, in the form of condition (4) of [Stacks, Tag 0EK2].

The route is condition (1) of [Stacks, Tag 0EK2] followed by the chain `(1) ⇒ (2) ⇒ (3) ⇒ (4)` of
that tag. Condition (1) has two clauses. The first, that `U` is quasi-affine, is
`Stacks.Algebraization.isQuasiAffine_complementZeroLocus`. The second, that
`colim_{U'} Γ(U', 𝒪_{U'})` is the inverse limit of the sections of the structure sheaves of the
infinitesimal neighbourhoods of `U₀`, is [Stacks, Tag 0EG2],
`Stacks.Algebraization.isIso_comparisonMap_of_associatedPointsClosureDimensionBound`, read through
`Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_isIso_comparisonMap`: the comparison map
of that tag compares the same colimit with the sections of the quotients `𝒪_U / fⁿ𝒪_U` on all of
`U`, and those are the sections on the infinitesimal neighbourhoods. Its hypothesis is
`Stacks.FundamentalGroup.associatedPointsClosureDimensionBound_unit_of_depthDimension`.

This is the input the proof of [Stacks, Tag 0DXY] feeds to [Stacks, Tag 0ELA]. -/
public theorem completionFullyFaithfulComplete_puncturedSpectrum_of_dualizing
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hcond : DepthDimensionCondition A f) :
    NeighbourhoodCompletion.CompletionFullyFaithfulComplete
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)).subschemeι := by
  have : IsNoetherian (complementZeroLocus A (maximalIdeal A) : Scheme) := ⟨⟩
  have hdual' := (Dualizing.exists_isDualizingComplex_iff_of_models (A := A) inferInstance
    (HasDerivedCategory.standard (ModuleCat.{u} A))).mp hdual
  have h1 : NeighbourhoodCompletion.IsQuasiAffineComplete
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)).subschemeι := by
    refine ⟨isQuasiAffine_complementZeroLocus A (maximalIdeal A), ?_⟩
    refine (infTower_isSectionsComplete_iff
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)).subschemeι _).2
        (isNeighbourhoodSectionsComplete_of_isIso_comparisonMap A (Ideal.span {f})
          (maximalIdeal A) _ ?_)
    exact isIso_comparisonMap_of_associatedPointsClosureDimensionBound (Ideal.span {f})
      (maximalIdeal A) ((Ideal.span_singleton_le_iff_mem _).2
        (le_maximalIdeal_of_isAdicComplete A (Ideal.span {f}) hcomplete
          (Ideal.mem_span_singleton_self f)))
      hcomplete hdual' _
      (associatedPointsClosureDimensionBound_unit_of_depthDimension A f hcond)
  have hc := NeighbourhoodCompletion.implications_among_conditions
    (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)).subschemeι
  exact hc.2.2.1 (hc.2.1 (hc.1 h1))

/-- The standing situation of [Stacks, Tag 0EHC] attached to Situation [Stacks, Tag 0BLF] over a
ring with a dualizing complex: the ring `A`, the ideal `I = (f)` and the ideal `𝔞 = 𝔪`. -/
public abbrev puncturedSpectrumSituation (hf : f ∈ maximalIdeal A) :
    AlgebraizationSituation.{u} where
  A := A
  I := Ideal.span {f}
  a := maximalIdeal A
  I_le_a := (Ideal.span_singleton_le_iff_mem _).2 hf

/-- **The completion functor of [Stacks, Tag 0EKY] reaches every finite locally free object of
`Coh(U, f𝒪_U)`.** In Situation [Stacks, Tag 0BLF] assume `A` has a dualizing complex, is
`f`-adically complete, and satisfies hypothesis (2) of [Stacks, Tag 0DXY]. Then every finite
locally free object of `Coh(U, f𝒪_U)` is the completion of a finite locally free module on an
open neighbourhood of `U₀` in `U`.

This is the essential-surjectivity half of [Stacks, Tag 0EKY]; compare
`Stacks.Algebraization.isCompletionNearClosedFiniteLocallyFree_of_isLocalRing_of_eq_span_singleton`
whose hypothesis on the terms of the object is their stalkwise freeness. -/
public theorem exists_finiteLocallyFree_completion_puncturedSpectrum_of_dualizing
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (hf : f ∈ maximalIdeal A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hcond : DepthDimensionCondition A f)
    (F : Stacks.Coherent.CoherentAdicSystems
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)))
    (hF : IsFiniteLocallyFreeAdic
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)) F) :
    IsNeighbourhoodCompletionFiniteLocallyFree
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)) F := by
  set S := puncturedSpectrumSituation A f hf
  have h : idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A) = idealOnOpen S :=
    idealSheafNearVanishing_eq_idealOnOpen S
  revert F
  rw [h]
  intro F hF
  obtain ⟨V, hV, G, hG, e⟩ :=
    isCompletionNearClosedFiniteLocallyFree_of_isLocalRing_of_eq_span_singleton S hdual
      hcomplete rfl rfl hcond F (hasFiniteFreeStalks_of_isFiniteLocallyFreeAdic S F hF)
  exact ⟨V, (support_idealOnOpen_subset S).trans hV, G, hG, e⟩

/-- **[Stacks, Tag 0DXY].** In Situation [Stacks, Tag 0BLF] — `(A, 𝔪)` a Noetherian local ring,
`f ∈ 𝔪`, `U = Spec(A) ∖ {𝔪}` the punctured spectrum of `A` and `U₀ = U ∩ V(f)` the punctured
spectrum of `A/fA`, as the closed subscheme of `U` cut out by `f 𝒪_U` — assume

1. `A` has a dualizing complex and is `f`-adically complete, and
2. one of
   * (a) `A_f` is `(S₂)` and `dim(A/𝔭) ≥ 4` for every minimal prime `𝔭` of `A` with `f ∉ 𝔭`, or
   * (b) `depth(A_𝔭) + dim(A/𝔭) > 3` for every prime `𝔭 ∉ V(f)` with `V(𝔭) ∩ V(f) ≠ {𝔪}`.

Then the restriction functor `colim_{U₀ ⊆ U' ⊆ U open} FÉt_{U'} ⟶ FÉt_{U₀}` is an equivalence.

The colimit is directed, so the functor is an equivalence exactly when the two conjuncts below
hold. The first is that it is fully faithful, in the form
`Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful`: morphisms between restrictions to `U₀`
come from a smaller neighbourhood, and morphisms agreeing on `U₀` agree on a smaller
neighbourhood. The second is that it is essentially surjective: every finite étale cover of `U₀`
is the restriction of a finite étale cover of some open `U'` with `U₀ ⊆ U' ⊆ U`.

As in the source, this is [Stacks, Tag 0EK1] for the closed subscheme `U₀` of `U`, with the
completion equivalence of [Stacks, Tag 0EKY] as input. Full faithfulness is [Stacks, Tag 0ELA]
applied to
`Stacks.FundamentalGroup.completionFullyFaithfulComplete_puncturedSpectrum_of_dualizing`, and the
essential image is the algebraization step of [Stacks, Tag 0EK1] fed by that same input together
with
`Stacks.FundamentalGroup.exists_finiteLocallyFree_completion_puncturedSpectrum_of_dualizing`. -/
@[stacks 0DXY "the restriction functor colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} → FÉt_{U₀} is an \
equivalence: fully faithful, and every finite étale cover of U₀ extends to a neighbourhood"]
public theorem finiteEtaleColimitEquivalence_puncturedSpectrum_of_dualizing
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (hf : f ∈ maximalIdeal A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hcond :
      (PropertySkRing (Localization.Away f) 2 ∧
          ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal → f ∉ p.asIdeal →
            (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
        (∀ p : PrimeSpectrum A, f ∉ p.asIdeal →
          ({q : PrimeSpectrum A | p.asIdeal ≤ q.asIdeal} ∩
            {q : PrimeSpectrum A | f ∈ q.asIdeal}) ≠
            {⟨maximalIdeal A, (maximalIdeal.isMaximal A).isPrime⟩} →
          (3 : WithBot ℕ∞) <
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
              ringKrullDim (A ⧸ p.asIdeal))) :
    FiniteEtaleColimitFullyFaithful (complementZeroLocus A (maximalIdeal A) : Scheme)
        (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)) ∧
      ∀ C : FiniteEtaleOver
        (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)).subscheme,
      ∃ (W : Neighborhood (complementZeroLocus A (maximalIdeal A) : Scheme)
          (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)))
        (V : FiniteEtaleOver (Neighborhood.open _ _ W).toScheme),
        Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom _ _ W)).obj V ≅ C) :=
  have : IsNoetherian (complementZeroLocus A (maximalIdeal A) : Scheme) := ⟨⟩
  have hff := completionFullyFaithfulComplete_puncturedSpectrum_of_dualizing.{u, w} A f hdual
    hcomplete hcond
  ⟨finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete _ _ hff,
    exists_finiteEtale_neighbourhood_extension_of_completion _ hff
      (exists_finiteLocallyFree_completion_puncturedSpectrum_of_dualizing.{u, w} A f hf hdual
        hcomplete hcond)⟩

end Stacks.FundamentalGroup

end
