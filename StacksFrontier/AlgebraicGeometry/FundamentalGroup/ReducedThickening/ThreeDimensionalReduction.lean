module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ReducedThickening.PuncturedSpectrumThickening
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ReducedThickening.ReducedQuotient
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionColimitDualizingEquivalence
public import StacksFrontier.RingTheory.AdicCompletion.AnalyticallyUnramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale covers near a hypersurface of a punctured spectrum, under a dimension bound on the
components

Let `(A, 𝔪)` be a Noetherian local ring, `f ∈ 𝔪`, and write `X = Spec A`, `X₀ = V(f)`,
`U = X ∖ {𝔪}` for the punctured spectrum and `U₀ = U ∩ V(f)`.  Assume `A` has a dualizing complex,
is `f`-adically complete, and that every irreducible component of `X` not contained in `X₀` has
dimension at least `3`.  This file proves that the restriction functor
`colim_{U₀ ⊆ U' ⊆ U open} FÉt_{U'} ⟶ FÉt_{U₀}` is fully faithful.

The dimension hypothesis is a bound at the *minimal* primes of `A`, while the completion theorems
that produce full faithfulness ask for a bound at the *associated* primes.  The two agree when `A`
is reduced, so the proof first replaces `A` by its reduction `A_red = A / nil(A)`:

* over `A_red` the bound at the minimal primes is a bound at the associated primes, which gives
  the hypothesis of the formal-sections theorem for the structure sheaf of the punctured spectrum
  of `A_red`, hence full faithfulness of the completion functor near the closed subscheme of that
  punctured spectrum cut out by the image of `f`;
* the punctured spectrum of `A_red` is a thickening of the punctured spectrum of `A` compatibly
  with those closed subschemes, and full faithfulness of restriction of finite étale covers is
  insensitive to a thickening.

A dualizing complex, `f`-adic completeness and the dimension bound all pass from `A` to `A_red`,
the last because the minimal primes of `A_red` are the images of those of `A` and the dimensions
of the corresponding quotients agree.

## Main results

* `Stacks.FundamentalGroup.associatedPointsClosureDimensionBound_unit_of_three_le_ringKrullDim` —
  for a reduced `A` the dimension bound at the minimal primes is the dimension hypothesis of
  [Stacks, Tag 0EG2] for the structure sheaf of the punctured spectrum.
* `completionFullyFaithfulComplete_puncturedSpectrum_of_three_le_ringKrullDim` — for a reduced
  `A`, full faithfulness of the completion functor `colim_{U'} Coh(𝒪_{U'}) ⟶ Coh(U, f𝒪_U)` on
  the finite locally free objects, which is condition (4) of [Stacks, Tag 0EK2].
* `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_isReduced` — the
  restriction functor `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}` is fully faithful for a reduced
  `A`.
* `finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_three_le_ringKrullDim` — the restriction
  functor `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}` is fully faithful, with no reducedness
  assumption on `A`.
* `Stacks.FundamentalGroup.three_le_ringKrullDim_quotient_nilradical` and
  `Stacks.FundamentalGroup.map_maximalIdeal_quotientMk` — the two transfers along
  `A ⟶ A / nil(A)` that the passage to the reduction needs.

## Implementation notes

The quotient `A / nil(A)` is reduced because `nil(A)` is a radical ideal, and local because the
quotient of a local ring by a proper ideal is local; neither is a global instance, so both are
produced on the spot.

Two transfers along `A ⟶ A / nil(A)` are needed and are proved here.  The maximal ideal of
`A / I` is the image of the maximal ideal of `A` whenever the quotient is again local — without
this the punctured spectrum of `A_red` coming from the thickening, which is cut out by the image
of `𝔪`, is not the one the completion theorem speaks about.  And a minimal prime `𝔮` of
`A / nil(A)` contracts to a minimal prime `𝔭` of `A` with `(A / nil(A)) / 𝔮 ≅ A / 𝔭`: minimal
primes contract to minimal primes along a surjection, the minimal primes over `nil(A)` are the
minimal primes of `A` because `nil(A)` is the radical of `(0)`, and the isomorphism of the double
quotient with `A / 𝔭` holds because `nil(A) ⊆ 𝔭`.

The route to the completion statement is condition (1) of [Stacks, Tag 0EK2] — the punctured
spectrum is quasi-affine, and the colimit of the sections of the structure sheaf over the
neighbourhoods of `U₀` is the limit of the sections on the infinitesimal neighbourhoods — followed
by the chain `(1) ⇒ (2) ⇒ (3) ⇒ (4)` of that tag.  The second clause of condition (1) is
[Stacks, Tag 0EG2], whose dimension hypothesis is the one supplied by reducedness.

The derived category of `A`-modules is read in the standard model
`CategoryTheory.HasDerivedCategory.standard`, the model the dualizing-complex results cited here
are stated in; a dualizing complex in another model is carried to this one by
`Stacks.Dualizing.exists_isDualizingComplex_iff_of_models`.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0BQB](https://stacks.math.columbia.edu/tag/0BQB)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open Stacks.LocalCohomology (complementZeroLocus cohomologicalDimension)

universe u w

namespace Stacks.FundamentalGroup

open Stacks.Algebraization

/-! ### The reduction of a local ring -/

/-- **The quotient by the nilradical is reduced.**  The nilradical is the radical of the zero
ideal, and a quotient by a radical ideal is reduced. -/
@[ega "0 1.1.1"]
theorem isReduced_quotient_nilradical (A : Type u) [CommRing A] : IsReduced (A ⧸ nilradical A) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical 0)

/-- **The nilradical of a local ring is a proper ideal.**  It is contained in every prime, in
particular in the maximal ideal, which is proper. -/
theorem nilradical_ne_top_of_isLocalRing (A : Type u) [CommRing A] [IsLocalRing A] :
    nilradical A ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ nilradical_le_prime (maximalIdeal A)))

/-- **The reduction of a local ring is local.**  A quotient of a local ring by a proper ideal is
local, and the nilradical is proper. -/
theorem isLocalRing_quotient_nilradical (A : Type u) [CommRing A] [IsLocalRing A] :
    IsLocalRing (A ⧸ nilradical A) :=
  have : Nontrivial (A ⧸ nilradical A) :=
    Ideal.Quotient.nontrivial_iff.mpr (nilradical_ne_top_of_isLocalRing A)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- **The maximal ideal of a local quotient is the image of the maximal ideal.**  If `R` is local
and `R / I` is local, then `I` is proper, hence contained in the maximal ideal of `R`, and the
quotient map is a local homomorphism; so an element of `R` is a unit exactly when its image is,
which is the asserted equality of ideals. -/
theorem map_maximalIdeal_quotientMk (R : Type u) [CommRing R] [IsLocalRing R] (I : Ideal R)
    [IsLocalRing (R ⧸ I)] :
    (maximalIdeal R).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [sup_eq_left.mpr (le_maximalIdeal hI)]

/-- **A prime of `A` containing the nilradical has the same quotient read over the reduction.**
For a prime `𝔭` of `A` the nilradical is contained in `𝔭`, so the double quotient
`(A / nil(A)) / 𝔭(A / nil(A))` is `A / 𝔭`. -/
theorem ringKrullDim_quotient_map_quotientMk_nilradical (A : Type u) [CommRing A] (p : Ideal A)
    [p.IsPrime] :
    ringKrullDim ((A ⧸ nilradical A) ⧸ p.map (Ideal.Quotient.mk (nilradical A))) =
      ringKrullDim (A ⧸ p) :=
  ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE (nilradical_le_prime p))

/-- **The minimal primes over the nilradical are the minimal primes.**  The nilradical is the
radical of the zero ideal, and an ideal and its radical have the same minimal primes. -/
theorem minimalPrimes_nilradical (A : Type u) [CommRing A] :
    (nilradical A).minimalPrimes = minimalPrimes A := by
  rw [show nilradical A = (⊥ : Ideal A).radical by simp [nilradical], Ideal.radical_minimalPrimes]

/-- **The dimension bound on the components of `Spec A` missing `V(f)` passes to the reduction.**
Let `𝔮` be a minimal prime of `A / nil(A)` not containing the image of `f`.  Then `𝔮` contracts
to a minimal prime `𝔭` of `A` with `f ∉ 𝔭`, and `(A / nil(A)) / 𝔮` is `A / 𝔭`, so the bound
`dim (A / 𝔭) ≥ 3` is the bound `dim ((A / nil(A)) / 𝔮) ≥ 3`. -/
theorem three_le_ringKrullDim_quotient_nilradical (A : Type u) [CommRing A] (f : A)
    (hdim : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal → f ∉ p.asIdeal →
      (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal))
    (q : PrimeSpectrum (A ⧸ nilradical A)) (hq : IsMinimalPrime q.asIdeal)
    (hqf : Ideal.Quotient.mk (nilradical A) f ∉ q.asIdeal) :
    (3 : WithBot ℕ∞) ≤ ringKrullDim ((A ⧸ nilradical A) ⧸ q.asIdeal) := by
  have hmin := Ideal.minimalPrimes_comap_of_surjective
    (f := Ideal.Quotient.mk (nilradical A)) Ideal.Quotient.mk_surjective hq
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker, minimalPrimes_nilradical] at hmin
  have hp : (q.asIdeal.comap (Ideal.Quotient.mk (nilradical A))).IsPrime := hmin.isPrime
  have hmap : (q.asIdeal.comap (Ideal.Quotient.mk (nilradical A))).map
      (Ideal.Quotient.mk (nilradical A)) = q.asIdeal :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q.asIdeal
  rw [← hmap, ringKrullDim_quotient_map_quotientMk_nilradical]
  exact hdim ⟨_, hp⟩ hmin fun h => hqf (Ideal.mem_comap.mp h)

/-! ### Completion near `U₀` over a reduced ring -/

section StandardModel

attribute [local instance] HasDerivedCategory.standard

/-- **The dimension bound on the components of `Spec A` missing `V(f)` is the hypothesis of
[Stacks, Tag 0EG2] for a reduced ring.**  Let `A` be a reduced Noetherian local ring and suppose
every minimal prime `𝔭` of `A` with `f ∉ 𝔭` has `dim (A/𝔭) ≥ 3`.  Then whenever `x` is an
associated point of `𝒪_U` outside `V(f)`, every point `z` of `closure {x} ∩ {𝔪}` has
`dim(𝒪_{closure {x}, z}) > cd(A, (f)) + 1`.

The structure sheaf is finite locally free, so the prime of such an `x` is an associated prime of
`A`, hence a minimal prime because `A` is reduced, and the bound applies to it.  The only `z` as
above is the closed point, where the local dimension of the closure is `dim(A/𝔭)`; and
`cd(A, (f)) ≤ 1`, a principal ideal needing one Koszul step.  So the required inequality is
`dim(A/𝔭) ≥ 3`. -/
theorem associatedPointsClosureDimensionBound_unit_of_three_le_ringKrullDim (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A] (f : A)
    (hdim : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal → f ∉ p.asIdeal →
      (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) :
    AssociatedPointsClosureDimensionBound A (Ideal.span {f}) (maximalIdeal A)
      (SheafOfModules.unit (complementZeroLocus A (maximalIdeal A) : Scheme).ringCatSheaf) := by
  rintro x hx hxI - z hxz haz
  have hpass : IsAssociatedPrimeStacks A A x.1.asIdeal :=
    Stacks.Divisors.isAssociatedPrimeStacks_of_mem_associatedPoints_complementZeroLocus
      A (maximalIdeal A) _ ((Scheme.Modules.isFiniteLocallyFree_iff _).2
        (Stacks.Algebraization.isFiniteLocallyFree_unit
          (complementZeroLocus A (maximalIdeal A) : Scheme))) hx
  have hf : f ∉ x.1.asIdeal := fun h => hxI ((Ideal.span_singleton_le_iff_mem _).2 h)
  have hbound : (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ x.1.asIdeal) :=
    hdim x.1 (assoc_prime_mem_minimalPrimes_of_isReduced
      ((Stacks.Depth.isAssociatedPrimeStacks_iff_mem_associatedPrimes x.1.asIdeal).1 hpass)) hf
  have hz : z = closedPoint A := by
    ext1
    exact ((maximalIdeal.isMaximal A).eq_of_le z.isPrime.ne_top haz).symm
  subst hz
  have hcd : cohomologicalDimension A (Ideal.span {f})
      (Ideal.span {f}).fg_of_isNoetherianRing ≤ 1 :=
    Stacks.LocalCohomology.cohomologicalDimension_span_singleton_le_one A f
  have hthree : ((3 : ℤ) : EInt) ≤ krullDimToEInt (ringKrullDim (A ⧸ x.1.asIdeal)) := by
    refine le_trans (le_of_eq ?_) (krullDimToEInt_mono hbound)
    exact (krullDimToEInt_natCast 3).symm
  exact lt_of_lt_of_le (WithBotTop.coe_lt_coe.mpr (by omega))
    (le_trans hthree (le_of_eq (congrArg krullDimToEInt
      (closureLocalDimension_closedPoint A _).symm)))

/-- **Completion near `U₀` is fully faithful on finite locally free objects over a reduced ring.**
Let `A` be a reduced Noetherian local ring with a dualizing complex which is `f`-adically
complete, and assume every minimal prime `𝔭` of `A` with `f ∉ 𝔭` has `dim (A/𝔭) ≥ 3`.  Then the
completion functor `colim_{U₀ ⊆ U' ⊆ U} Coh(𝒪_{U'}) ⟶ Coh(U, f𝒪_U)` is fully faithful on the
finite locally free objects, which is condition (4) of [Stacks, Tag 0EK2].

The route is condition (1) of [Stacks, Tag 0EK2] followed by the chain `(1) ⇒ (2) ⇒ (3) ⇒ (4)` of
that tag.  Condition (1) has two clauses: that `U` is quasi-affine, and that
`colim_{U'} Γ(U', 𝒪_{U'})` is the inverse limit of the sections of the structure sheaves of the
infinitesimal neighbourhoods of `U₀`.  The second is [Stacks, Tag 0EG2], whose hypothesis is
`Stacks.FundamentalGroup.associatedPointsClosureDimensionBound_unit_of_three_le_ringKrullDim`. -/
theorem completionFullyFaithfulComplete_puncturedSpectrum_of_three_le_ringKrullDim (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A] (f : A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hdim : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal → f ∉ p.asIdeal →
      (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) :
    NeighbourhoodCompletion.CompletionFullyFaithfulComplete
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)).subschemeι := by
  have : IsNoetherian (complementZeroLocus A (maximalIdeal A) : Scheme) := ⟨⟩
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
      hcomplete hdual _
      (associatedPointsClosureDimensionBound_unit_of_three_le_ringKrullDim A f hdim)
  have hc := NeighbourhoodCompletion.implications_among_conditions
    (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)).subschemeι
  exact hc.2.2.1 (hc.2.1 (hc.1 h1))

/-- **Full faithfulness of restriction of finite étale covers from the neighbourhoods of `U₀`,
over a reduced ring.**  The reduced case of
`finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_three_le_ringKrullDim`, obtained from full
faithfulness of the completion functor near `U₀`. -/
theorem finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_isReduced (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsReduced A] (f : A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hdim : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal → f ∉ p.asIdeal →
      (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) :
    FiniteEtaleColimitFullyFaithful (complementZeroLocus A (maximalIdeal A) : Scheme.{u})
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)) :=
  have : IsNoetherian (complementZeroLocus A (maximalIdeal A) : Scheme) := ⟨⟩
  finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete _ _
    (completionFullyFaithfulComplete_puncturedSpectrum_of_three_le_ringKrullDim A f hdual
      hcomplete hdim)

/-- **Full faithfulness of restriction descends from the reduction.**  The dimension bound is a
bound at the minimal primes of `A`, which pass to the reduction, so the reduced case above
applies to `A / nil(A)`; the punctured spectrum of the reduction is a thickening of that of `A`
carrying the closed subscheme cut out by the image of `f` to `U₀`, and full faithfulness of
restriction of finite étale covers is insensitive to such a thickening. -/
theorem finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_three_le_ringKrullDim_standard
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hdim : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal → f ∉ p.asIdeal →
      (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) :
    FiniteEtaleColimitFullyFaithful (complementZeroLocus A (maximalIdeal A) : Scheme.{u})
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)) := by
  have := isReduced_quotient_nilradical A
  have := isLocalRing_quotient_nilradical A
  refine finiteEtaleColimitFullyFaithful_of_completionComplete_nilradical A (maximalIdeal A) f ?_
  rw [map_maximalIdeal_quotientMk A (nilradical A)]
  exact completionFullyFaithfulComplete_puncturedSpectrum_of_three_le_ringKrullDim
    (A ⧸ nilradical A) (Ideal.Quotient.mk (nilradical A) f)
    (exists_isDualizingComplex_quotient_nilradical A hdual)
    (isAdicComplete_span_singleton_quotient_nilradical A f hcomplete)
    (three_le_ringKrullDim_quotient_nilradical A f hdim)

end StandardModel

/-! ### Full faithfulness of restriction, with no reducedness assumption -/

/-- **Restriction of finite étale covers from the neighbourhoods of `U₀` in `U` is fully
faithful.**  Let `(A, 𝔪)` be a Noetherian local ring, `f ∈ A`, `X = Spec A`, `X₀ = V(f)`,
`U = X ∖ {𝔪}` and `U₀ = U ∩ V(f)`.  Assume `A` has a dualizing complex, is `f`-adically complete,
and that every irreducible component of `X` not contained in `X₀` has dimension at least `3` —
that is, `dim (A/𝔭) ≥ 3` for every minimal prime `𝔭` of `A` with `f ∉ 𝔭`.  Then the restriction
functor `colim_{U₀ ⊆ U' ⊆ U open} FÉt_{U'} ⟶ FÉt_{U₀}` is fully faithful.

The dimension hypothesis is a bound at the minimal primes, whereas the completion theorem behind
full faithfulness needs one at the associated primes; so `A` is first replaced by its reduction,
where the associated primes are the minimal primes.  The punctured spectrum of the reduction is a
thickening of `U` carrying its closed subscheme cut out by the image of `f` to `U₀`, and full
faithfulness of restriction is insensitive to such a thickening; a dualizing complex, `f`-adic
completeness and the dimension bound all survive the passage to the reduction.

The dualizing complex is asked for in an arbitrary model of the derived category of `A`-modules,
and moved to the standard model — the one the completion results are stated in — by
`Stacks.Dualizing.exists_isDualizingComplex_iff_of_models`. -/
@[stacks 0DXX "the whole statement, under the source's hypotheses only: a dualizing complex and \
f-adic completeness, and dimension at least three for every irreducible component of X not \
contained in the zero locus of f"]
theorem finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_three_le_ringKrullDim (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (f : A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (hdim : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal → f ∉ p.asIdeal →
      (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) :
    FiniteEtaleColimitFullyFaithful (complementZeroLocus A (maximalIdeal A) : Scheme.{u})
      (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)) :=
  finiteEtaleColimitFullyFaithful_puncturedSpectrum_of_three_le_ringKrullDim_standard A f
    ((Dualizing.exists_isDualizingComplex_iff_of_models (A := A) inferInstance
      (HasDerivedCategory.standard (ModuleCat.{u} A))).mp hdual)
    hcomplete hdim

end Stacks.FundamentalGroup

end
