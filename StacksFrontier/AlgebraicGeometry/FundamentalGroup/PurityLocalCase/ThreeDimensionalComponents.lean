module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHomsOnBijective
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ConnectednessApplication
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusDimensionCriterion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.FaithfulRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.FullyFaithfulComplete
public import StacksFrontier.RingTheory.AdicCompletion.AnalyticallyUnramified

/-!
# Three-dimensional missing components in the local Lefschetz situation

Let `(A, 𝔪)` be a Noetherian local ring, let `f ∈ 𝔪`, and write `X = Spec A`, `X₀ = Spec (A/fA)`
and `U`, `U₀` for the two punctured spectra.  This file is about the hypothesis that every
irreducible component of `X` not contained in `X₀` has dimension at least `3`, and extracts the
two consequences of it that are about the opens `U'` with `U₀ ⊆ U' ⊆ U`.

An irreducible component of `X` is the closed set cut out by a minimal prime `𝔭` of `A`, it fails
to be contained in `X₀ = V(f)` exactly when `f ∉ 𝔭`, and its dimension is `dim (A/𝔭)`.

## Main definitions

* `AlgebraicGeometry.LocalLefschetzSituation.HasThreeDimensionalMissingComponents` — the
  dimension hypothesis.

## Main results

* `…HasThreeDimensionalMissingComponents.hasLargeMissingComponents` — the hypothesis implies the
  two-dimensionality condition of
  `AlgebraicGeometry.LocalLefschetzSituation.HasLargeMissingComponents` on every open of `X`, so
  no shrinking of `U` is needed to make restriction faithful.
* `…faithful_finiteEtaleBaseChange_of_threeDimensional` and
  `…finiteEtaleBaseChange_map_eq_of_threeDimensional` — restriction of finite étale covers from
  any open `U'` with `U₀ ⊆ U' ⊆ U` to `U₀` is faithful, and two morphisms of covers of `U'` that
  agree over `U₀` are already equal.
* `…three_le_ringKrullDim_quotient_of_isAssociatedPrime` — for a reduced `A` the dimension bound
  holds at every associated prime of `A`, not only at the minimal ones.
* `…completionFullyFaithful_finiteLocallyFree_on_of_threeDimensional` — for a reduced `A` with a
  dualizing complex which is `f`-adically complete, the completion functor
  `colim_{U₀ ⊆ U' ⊆ U} Coh(𝒪_{U'}) ⟶ Coh(U, f𝒪_U)` is fully faithful on the finite locally free
  objects.

## Implementation notes

The dimension condition is phrased through `IsMinimalPrime` on ideals of `A` rather than through
`irreducibleComponents (Spec A)`, matching
`AlgebraicGeometry.LocalLefschetzSituation.HasLargeMissingComponents`, whose one-dimensional
components are described the same way.

The completion statement is the one of Algebraic and Formal Geometry,
[Stacks, Tag 0EKU] at the ideals `f A ⊆ 𝔪`: its target `V(𝔞)` is the single closed point, so the
dimension `dim((A/𝔭)_𝔮)` of its hypothesis is taken at `𝔮 = 𝔪` and is `dim (A/𝔭)`, and the
cohomological dimension of the principal ideal `f A` is at most one, so the required strict
inequality `cd(A, fA) + 1 < dim (A/𝔭)` is exactly `dim (A/𝔭) ≥ 3`.  Reducedness enters only
through the identification of the associated primes of `A` with its minimal primes.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0BLN](https://stacks.math.columbia.edu/tag/0BLN)
* [Stacks Project, Tag 0EKU](https://stacks.math.columbia.edu/tag/0EKU)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (closureLocalDimension krullDimToEInt nbhdHomComparisonOn
  OpensNearVanishing)
open Stacks.LocalCohomology (cohomologicalDimension)

universe u

namespace AlgebraicGeometry.LocalLefschetzSituation

/-- **Every irreducible component of `X` not contained in `X₀` has dimension at least `3`.**
The irreducible components of `X = Spec A` are the closed sets `V(𝔭)` for `𝔭` a minimal prime of
`A`; such a component is contained in `X₀ = V(f)` exactly when `f ∈ 𝔭`, and its dimension is the
Krull dimension of `A/𝔭`. -/
def HasThreeDimensionalMissingComponents (S : LocalLefschetzSituation.{u}) : Prop :=
  ∀ p : PrimeSpectrum S.A, IsMinimalPrime p.asIdeal → S.f ∉ p.asIdeal →
    3 ≤ ringKrullDim (S.A ⧸ p.asIdeal)

/-- A component of dimension at least `3` has dimension at least `2`, so the dimension
hypothesis holds on every open of `X` with nothing removed. -/
theorem HasThreeDimensionalMissingComponents.hasLargeMissingComponents
    {S : LocalLefschetzSituation.{u}} (h : S.HasThreeDimensionalMissingComponents)
    (W : S.X.Opens) : S.HasLargeMissingComponents W := fun p hp _ hpf =>
  le_trans (by norm_num) (h p hp hpf)

/-- Restriction of finite étale covers from an open `U'` with `U₀ ⊆ U' ⊆ U` to `U₀` is faithful
once every irreducible component of `X` not contained in `X₀` has dimension at least `3`: such a
component meets `X₀` away from the closed point already, so no open has to be discarded. -/
theorem faithful_finiteEtaleBaseChange_of_threeDimensional
    (S : LocalLefschetzSituation.{u}) (h : S.HasThreeDimensionalMissingComponents)
    {W : S.X.Opens} (hW : W ≤ S.UOpen) (r : S.U₀ ⟶ W.toScheme)
    (hr : r ≫ W.ι = S.U₀ToU ≫ S.UOpen.ι) :
    (finiteEtaleBaseChange r).Faithful :=
  S.faithful_finiteEtaleBaseChange_of_hasLargeMissingComponents hW r hr
    (h.hasLargeMissingComponents W)

/-- Two morphisms of finite étale covers of an open `U'` with `U₀ ⊆ U' ⊆ U` which agree after
restriction to `U₀` are equal, with no shrinking of `U'`.  This is the faithfulness half of full
faithfulness of `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}`, written on representatives. -/
theorem finiteEtaleBaseChange_map_eq_of_threeDimensional
    (S : LocalLefschetzSituation.{u}) (h : S.HasThreeDimensionalMissingComponents)
    {V : S.X.Opens} (hV : V ≤ S.UOpen) (hVU₀ : S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ V)
    {A B : FiniteEtaleOver V.toScheme} (a b : A ⟶ B)
    (hab : (finiteEtaleBaseChange (S.homToOpen hVU₀)).map a =
      (finiteEtaleBaseChange (S.homToOpen hVU₀)).map b) :
    a = b :=
  (S.faithful_finiteEtaleBaseChange_of_threeDimensional h hV (S.homToOpen hVU₀)
    (S.homToOpen_comp_ι hVU₀)).map_injective hab

/-- In a reduced Noetherian ring the associated primes are the minimal primes, so the dimension
bound on the irreducible components of `X` missing `X₀` is a bound at every associated prime of
`A` outside `V(f)`. -/
theorem three_le_ringKrullDim_quotient_of_isAssociatedPrime
    {S : LocalLefschetzSituation.{u}} [_root_.IsReduced S.A]
    (h : S.HasThreeDimensionalMissingComponents) (p : PrimeSpectrum S.A)
    (hp : IsAssociatedPrimeStacks S.A S.A p.asIdeal) (hpf : S.f ∉ p.asIdeal) :
    3 ≤ ringKrullDim (S.A ⧸ p.asIdeal) :=
  h p (assoc_prime_mem_minimalPrimes_of_isReduced
    ((isAssociatedPrimeStacks_iff_mem_associatedPrimes p.asIdeal).mp hp)) hpf

/-- **The completion functor on the neighbourhoods of `U₀` in `U` is fully faithful on vector
bundles.** Let `A` be a reduced Noetherian local ring with a dualizing complex which is
`f`-adically complete, and assume every irreducible component of `X` not contained in `X₀` has
dimension at least `3`.  Then for every open `U'` with `U₀ ⊆ U' ⊆ U` and all finite locally free
coherent `𝒪_{U'}`-modules `G`, `F`, the canonical map
`colim_{U'' ⊆ U'} Hom_{U''}(G|_{U''}, F|_{U''}) ⟶ Hom_{Coh(U', f𝒪_{U'})}(G^∧, F^∧)` is bijective.

This is Algebraic and Formal Geometry, [Stacks, Tag 0EKU] at the pair of ideals `f A ⊆ 𝔪`: the
closed set `V(𝔪)` is the closed point, so the dimension in its hypothesis is `dim (A/𝔭)` at an
associated prime `𝔭` of `A` with `f ∉ 𝔭`, and the cohomological dimension of `f A` is at most
one. -/
theorem completionFullyFaithful_finiteLocallyFree_on_of_threeDimensional
    (S : LocalLefschetzSituation.{u}) [_root_.IsReduced S.A]
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (h : S.HasThreeDimensionalMissingComponents)
    (V : OpensNearVanishing S.A (Ideal.span {S.f}) (maximalIdeal S.A))
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules V.openSet.toScheme.ringCatSheaf)
    (hG : Scheme.Modules.IsFiniteLocallyFree G.obj)
    (hF : Scheme.Modules.IsFiniteLocallyFree F.obj) :
    Function.Bijective (nbhdHomComparisonOn V G F) := by
  refine Stacks.Algebraization.completionFullyFaithful_finiteLocallyFree_on
    (Ideal.span_le.mpr (by simpa using S.f_mem_maximalIdeal)) hcomplete hdualizing
    ?_ V G F hG hF
  intro p hp hpI _ z hpz hz
  have hpf : S.f ∉ p.asIdeal := fun hf =>
    hpI (Ideal.span_le.mpr (by simpa using hf))
  have hdim : 3 ≤ ringKrullDim (S.A ⧸ p.asIdeal) :=
    three_le_ringKrullDim_quotient_of_isAssociatedPrime h p hp hpf
  have hclosure : closureLocalDimension S.A p z = ringKrullDim (S.A ⧸ p.asIdeal) :=
    (Stacks.Algebraization.closureLocalDimension_eq_ringKrullDim_quotient_localizationAtPrime
      p z).trans (ringKrullDim_quotient_localization_of_maximalIdeal_le S.A z hz p.asIdeal)
  have hcd : cohomologicalDimension S.A (Ideal.span {S.f})
      (Ideal.span {S.f}).fg_of_isNoetherianRing ≤ 1 :=
    Stacks.LocalCohomology.cohomologicalDimension_span_singleton_le_one S.A S.f
  have hthree : ((3 : ℤ) : EInt) ≤ krullDimToEInt (ringKrullDim (S.A ⧸ p.asIdeal)) := by
    refine le_trans (le_of_eq ?_) (Stacks.Algebraization.krullDimToEInt_mono hdim)
    exact (Stacks.Algebraization.krullDimToEInt_natCast 3).symm
  rw [hclosure]
  exact lt_of_lt_of_le (WithBotTop.coe_lt_coe.mpr (by omega)) hthree

end AlgebraicGeometry.LocalLefschetzSituation

end
