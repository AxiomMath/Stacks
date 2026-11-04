module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionColimitDualizingEquivalence
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
public import StacksFrontier.RingTheory.Serre.Criterion

/-!
# Finite étale covers near a hypersurface in a complete local ring of dimension at least four

Let `(A, 𝔪)` be a complete local Noetherian ring and let `f ∈ 𝔪` be nonzero.  Write
`X = Spec A`, `U = X ∖ {𝔪}` for the punctured spectrum and `U₀ = U ∩ V(f)` for the punctured
spectrum of `A / fA`, the closed subscheme of `U` cut out by `f 𝒪_U`.  Suppose `A_f` satisfies
Serre's condition `(S₂)` and every irreducible component of `X` has dimension at least `4`.  Then
the restriction functor

```
colim_{U₀ ⊆ U' ⊆ U open} FÉt_{U'} ⟶ FÉt_{U₀}
```

is an equivalence of categories.

All three hypotheses of the equivalence are available.  A complete local Noetherian ring has a
dualizing complex, and it is `f`-adically complete because `f 𝒪` is contained in the maximal
ideal; and the dimension bound on every irreducible component of `X` is in particular a bound on
those components not contained in `V(f)`, which together with `(S₂)` for `A_f` is the first of
the two alternative hypotheses.

## Main results

* `AlgebraicGeometry.finiteEtaleColimitEquivalence_puncturedSpectrum_of_propertySk` — the
  equivalence, under the hypotheses above.

## Implementation notes

Serre's condition `(S₂)` for `A_f` is `PropertySkRing (Localization.Away f) 2`, and the dimension
condition on the irreducible components of `X` is a condition on the minimal primes `𝔭` of `A`:
the component is `V(𝔭)` and its dimension is the Krull dimension of `A / 𝔭`.

The dualizing complex is produced in the standard model of the derived category of `A`-modules
and transported to the ambient model by
`Stacks.Dualizing.exists_isDualizingComplex_iff_of_models`.

## References

* [Stacks Project, Tag 0BLW](https://stacks.math.columbia.edu/tag/0BLW)
* [Stacks Project, Tag 0DXY](https://stacks.math.columbia.edu/tag/0DXY)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (idealSheafNearVanishing)
open Stacks.FundamentalGroup (DepthDimensionCondition FiniteEtaleColimitFullyFaithful Neighborhood
  finiteEtaleColimitEquivalence_puncturedSpectrum_of_dualizing)
open Stacks.LocalCohomology (complementZeroLocus)

universe u w

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (f : A)

/-- **Stacks Project, Tag 0BLW.**  Let `(A, 𝔪)` be a complete local Noetherian ring and let
`f ∈ 𝔪` be nonzero.  Assume `A_f` satisfies Serre's condition `(S₂)` and every irreducible
component of `Spec A` has dimension at least `4`.  Then the restriction functor

```
colim_{U₀ ⊆ U' ⊆ U open} FÉt_{U'} ⟶ FÉt_{U₀}
```

is an equivalence, where `U = Spec A ∖ {𝔪}` and `U₀ = U ∩ V(f)`.

This is Stacks 0DXY under its hypothesis (2)(a).  Its hypothesis (1) is available: a complete
local Noetherian ring has a dualizing complex by Stacks 0BFR, and it is `f`-adically complete
because `f A` is contained in the maximal ideal, with respect to which it is complete.  The
dimension bound of (2)(a) is on the components of `Spec A` not contained in `V(f)`, so the bound
on all of them is more than enough. -/
@[stacks 0BLW "the equivalence of the remark, from the tag's own hypotheses: `A` complete local \
Noetherian, `f ∈ 𝔪` nonzero, `A_f` satisfying `(S₂)`, and every irreducible component of \
`Spec A` of dimension at least 4; nothing beyond them is assumed"]
theorem finiteEtaleColimitEquivalence_puncturedSpectrum_of_propertySk
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [IsAdicComplete (maximalIdeal A) A]
    (hf : f ∈ maximalIdeal A) (_hfne : f ≠ 0)
    (hS2 : PropertySkRing (Localization.Away f) 2)
    (hdim : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) :
    FiniteEtaleColimitFullyFaithful (complementZeroLocus A (maximalIdeal A) : Scheme)
        (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)) ∧
      ∀ C : FiniteEtaleOver
        (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)).subscheme,
      ∃ (W : Neighborhood (complementZeroLocus A (maximalIdeal A) : Scheme)
          (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)))
        (V : FiniteEtaleOver (Neighborhood.open _ _ W).toScheme),
        Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom _ _ W)).obj V ≅ C) := by
  have hdual : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K :=
    (Dualizing.exists_isDualizingComplex_iff_of_models (A := A)
      (HasDerivedCategory.standard (ModuleCat.{u} A)) inferInstance).mp
      (Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal A)
  have hcomplete : IsAdicComplete (Ideal.span {f}) A :=
    isAdicComplete_of_le_of_fg_of_isAdicComplete
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 hf))
      (inferInstance : IsAdicComplete (maximalIdeal A) A)
      (Ideal.fg_of_isNoetherianRing _)
  exact finiteEtaleColimitEquivalence_puncturedSpectrum_of_dualizing.{u, w} A f hf hdual hcomplete
    (Or.inl ⟨hS2, fun p hp _ => hdim p hp⟩)

/-- **A normal Noetherian ring satisfies Serre's condition `(S₂)`.**  This is the easy direction
of Serre's criterion for normality, with the depth inequality transported from `WithBot ℕ∞` to
`ℕ∞`: the Krull dimension of a localization at a prime is not `⊥`, so the two readings of
`min(2, dim R_𝔭) ≤ depth(R_𝔭)` agree. -/
@[sga "2 XI 3.11" "necessity: (ii)"]
private theorem propertySkRing_two_of_isDomain_and_isIntegrallyClosed_atPrime
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    PropertySkRing R 2 := by
  have hd := (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth
    (R := R)).mp h |>.2
  intro p hp
  have hdp := hd p
  rw [ringDepth_eq_depth_maximalIdeal]
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp
    (ringKrullDim_ne_bot (R := Localization.AtPrime p))
  rw [← he] at hdp ⊢
  simp only [WithBot.unbotD_coe]
  have h2 : ((2 : ℕ∞) : WithBot ℕ∞) = 2 := rfl
  refine min_le_iff.mpr ?_
  rcases min_le_iff.mp hdp with hc | hc
  · rw [← h2, WithBot.coe_le_coe] at hc
    exact Or.inl hc
  · rw [WithBot.coe_le_coe] at hc
    exact Or.inr hc

/-- A localization of an integrally closed domain at a submonoid avoiding `0` is an integrally
closed domain. -/
private theorem isDomain_and_isIntegrallyClosed_localization
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsDomain R] [IsIntegrallyClosed R]
    (M : Submonoid R) [IsLocalization M S] (h0 : (0 : R) ∉ M) :
    IsDomain S ∧ IsIntegrallyClosed S := by
  have hM : M ≤ nonZeroDivisors R := fun a ha =>
    mem_nonZeroDivisors_of_ne_zero fun hz => h0 (hz ▸ ha)
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors (M := M) S hM,
    isIntegrallyClosed_of_isLocalization S M hM⟩

/-- **Stacks Project, Tag 0BLW, the example at the end of the remark.**  The hypotheses of
`AlgebraicGeometry.finiteEtaleColimitEquivalence_puncturedSpectrum_of_propertySk` hold when `A`
is a complete local normal domain of dimension at least `4` and `f ∈ 𝔪` is nonzero, so the
restriction functor `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}` is an equivalence in that case.

A localization of a normal domain at a set of nonzero elements is again a normal domain, so `A_f`
and each of its local rings is an integrally closed domain; Serre's criterion then gives `(S₂)`
for `A_f`.  The only minimal prime of a domain is `(0)`, and `A / (0) = A` has dimension at
least `4`, which is the dimension bound on the irreducible components of `Spec A`. -/
@[stacks 0BLW "the example at the end of the remark: a complete local normal domain of dimension \
at least 4, with `f ∈ 𝔪` nonzero, satisfies the remark's hypotheses, so the equivalence holds \
for it; normality is `IsDomain` together with `IsIntegrallyClosed` and nothing beyond the \
remark's own hypotheses is assumed"]
theorem finiteEtaleColimitEquivalence_puncturedSpectrum_of_isIntegrallyClosed
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [IsAdicComplete (maximalIdeal A) A]
    [IsDomain A] [IsIntegrallyClosed A]
    (hdim : (4 : WithBot ℕ∞) ≤ ringKrullDim A) (hf : f ∈ maximalIdeal A) (hfne : f ≠ 0) :
    FiniteEtaleColimitFullyFaithful (complementZeroLocus A (maximalIdeal A) : Scheme)
        (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)) ∧
      ∀ C : FiniteEtaleOver
        (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)).subscheme,
      ∃ (W : Neighborhood (complementZeroLocus A (maximalIdeal A) : Scheme)
          (idealSheafNearVanishing A (Ideal.span {f}) (maximalIdeal A)))
        (V : FiniteEtaleOver (Neighborhood.open _ _ W).toScheme),
        Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom _ _ W)).obj V ≅ C) := by
  have hnzd : (0 : A) ∉ Submonoid.powers f := fun ⟨n, hn⟩ => pow_ne_zero n hfne hn
  obtain ⟨hdom, hic⟩ := isDomain_and_isIntegrallyClosed_localization A (Localization.Away f) _ hnzd
  refine finiteEtaleColimitEquivalence_puncturedSpectrum_of_propertySk.{u, w} A f hf hfne ?_ ?_
  · exact propertySkRing_two_of_isDomain_and_isIntegrallyClosed_atPrime
      (Localization.Away f) fun p hp =>
      isDomain_and_isIntegrallyClosed_localization (Localization.Away f) (Localization.AtPrime p)
        p.primeCompl fun h => h p.zero_mem
  · intro q hq
    have hbot : q.asIdeal = ⊥ := le_antisymm (hq.2 ⟨inferInstance, bot_le⟩ bot_le) bot_le
    rw [hbot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
    exact hdim

end AlgebraicGeometry

end
