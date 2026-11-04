module

public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayConcentration
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
public import StacksFrontier.RingTheory.Depth.Ext
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
import StacksCore.Tactic.StacksAttribute

/-!
# A dualizing module with the maximal ideal associated lives on a zero-dimensional ring

Let `(A, 𝔪)` be a Noetherian local ring and let `N` be an `A`-module whose degree-zero complex
`N[0]` is a dualizing complex ([Stacks, Tag 0A7B]). If `𝔪` is an associated prime of `N`, then
`A` is zero-dimensional, `𝔪` is an associated prime of `A` itself, and consequently no element
of `𝔪` is a nonzerodivisor on `A`.

This is the local input to the statement that the local equation of an effective Cartier divisor
is a nonzerodivisor on a dualizing module: a dualizing module with an associated point on the
divisor would force the local ring there to be zero-dimensional, and there the local equation
cannot be regular.

## Main results

* `Dualizing.mem_associatedPrimes_self_of_mem_associatedPrimes_maximalIdeal`: `𝔪 ∈ Ass(A)`, and
  along the way `dim(A) = 0`.
* `Dualizing.not_isSMulRegular_of_mem_associatedPrimes_maximalIdeal`: no element of `𝔪` is a
  nonzerodivisor on `A`.

## Implementation notes

The proof is the chain of [Stacks, Tag 0AWS]. Some shift `N[0]⟦-m⟧` of the dualizing complex is
normalized (`Dualizing.exists_isNormalizedDualizingComplex_shift`); that shift has its cohomology
in the single degree `m`, so by the equivalent conditions of [Stacks, Tag 0AWS] the ring is
Cohen--Macaulay and the normalized complex is its dualizing module placed in degree `-dim(A)`.
Comparing the two concentration degrees identifies `N` with that dualizing module, which is
maximal Cohen--Macaulay by the final assertion of the same tag, so `depth(N) = dim(A)`. The
hypothesis makes `depth(N) = 0` ([Stacks, Tag 00LL]), whence `dim(A) = 0`; Cohen--Macaulayness
then reads `depth(A) = 0`, which is `𝔪 ∈ Ass(A)` by the same lemma, and an element of an
associated prime is a zerodivisor.

Universes: `Dualizing.IsNormalizedDualizingComplex` is pinned at `HasDerivedCategory.standard`
and the equivalent conditions of [Stacks, Tag 0AWS] are stated for `ModuleCat.{u} A`, so
everything below is read at the module universe of the ring and at the standard model of the
derived category.

## References

* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 00LL](https://stacks.math.columbia.edu/tag/00LL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- The degree-zero cohomology of the degree-zero complex on `N` is `N`. -/
private noncomputable def homologyZeroSingleZeroIso (N : ModuleCat.{u} A) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ≅ N :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app N

/-- Reindexing the cohomology of a fixed object along an equality of degrees. -/
private noncomputable def homologyCongr (K : DerivedCategory (ModuleCat.{u} A)) {a b : ℤ}
    (h : a = b) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) a).obj K ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).obj K :=
  eqToIso (congrArg (fun j : ℤ => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K) h)

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- A module with an associated prime is nonzero. -/
private theorem nontrivial_of_mem_associatedPrimes {N : Type*} [AddCommGroup N] [Module A N]
    {p : Ideal A} (hass : p ∈ associatedPrimes A N) : Nontrivial N := by
  rcases subsingleton_or_nontrivial N with hsub | hnt
  · obtain ⟨hp, x, hx⟩ := hass
    refine absurd (Ideal.eq_top_iff_one p |>.mpr ?_) hp.ne_top
    rw [hx]
    refine Ideal.le_radical ?_
    rw [Submodule.mem_colon_singleton, one_smul, Submodule.mem_bot]
    exact Subsingleton.elim _ _
  · exact hnt

/-- **A dualizing module whose associated primes contain the maximal ideal forces the maximal
ideal to be an associated prime of the ring**, the ring being zero-dimensional and
Cohen--Macaulay. -/
theorem mem_associatedPrimes_self_of_mem_associatedPrimes_maximalIdeal (N : ModuleCat.{u} A)
    (hN : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))
    (hass : IsLocalRing.maximalIdeal A ∈ associatedPrimes A N) :
    IsLocalRing.maximalIdeal A ∈ associatedPrimes A A := by
  set K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N with hKdef
  -- `N` is a finite module, being the only cohomology of a dualizing complex.
  have hfin : Module.Finite A N := by
    have := hN.finiteCohomology 0
    exact Module.Finite.equiv (homologyZeroSingleZeroIso N).toLinearEquiv
  have hnt : Nontrivial N := nontrivial_of_mem_associatedPrimes hass
  -- Normalize the dualizing complex.
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, 0} K hN
  -- `H^i(K⟦-m⟧) ≅ H^{-m + i}(K)`, so the shift has cohomology only in degree `m`.
  have hshift : ∀ i : ℤ,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (K⟦-m⟧) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-m + i)).obj K :=
    fun i => homologyShiftIso K (-m) i
  have hconc : IsCohomologicallyConcentratedInOneDegree (K⟦-m⟧) := by
    refine ⟨m, fun i hi => ?_⟩
    refine IsZero.of_iso ?_ (hshift i)
    exact isZero_homology_of_iso_single.{u, 0} K 0 N ⟨Iso.refl _⟩ (-m + i) (by omega)
  -- The equivalent conditions of Tag 0AWS.
  have htfae := isCohenMacaulay_tfae_dualizingComplex (K⟦-m⟧) hm
  have hCM : IsCohenMacaulayLocalRing A := (htfae.out 2 1).mp hconc
  obtain ⟨e⟩ := (htfae.out 2 3).mp hconc
  -- `H^m(K⟦-m⟧) ≅ N` is nonzero, so the concentration degree of the shift is `-dim(A)`.
  have hiso : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj (K⟦-m⟧) ≅ N :=
    hshift m ≪≫ homologyCongr K (show -m + m = (0 : ℤ) by ring) ≪≫
      homologyZeroSingleZeroIso N
  have hNm : Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj (K⟦-m⟧)) :=
    (Equiv.nontrivial_congr hiso.toLinearEquiv.toEquiv).mpr hnt
  have hmd : m = -(localRingDimension A : ℤ) := by
    by_contra hne
    exact (not_subsingleton_iff_nontrivial.mpr hNm)
      (ModuleCat.subsingleton_of_isZero
        (isZero_homology_of_iso_single.{u, 0} (K⟦-m⟧) _ _ ⟨e⟩ m hne))
  -- `N` is the dualizing module of the normalized complex, hence maximal Cohen--Macaulay.
  have hdual : dualizingModule (K⟦-m⟧) ≅ N :=
    homologyCongr (K⟦-m⟧) (show -(localRingDimension A : ℤ) = m by rw [hmd]) ≪≫ hiso
  have hmax := dualizingModule_isMaximalCohenMacaulay (K⟦-m⟧) hm hCM
  rw [Module.IsMaximalCohenMacaulay,
    Module.depth_eq_depth_of_linearEquiv _ hdual.toLinearEquiv] at hmax
  -- The hypothesis says `depth(N) = 0`, so the ring is zero-dimensional.
  have hdepth : Module.depth A (IsLocalRing.maximalIdeal A) N = 0 :=
    Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes.mpr hass
  rw [hdepth] at hmax
  have hdim : ringKrullDim A = 0 := hmax.symm.trans (by norm_num)
  -- Cohen--Macaulayness now reads `depth(A) = 0`.
  have hself : Module.IsMaximalCohenMacaulay A A :=
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A).mp hCM
  rw [Module.IsMaximalCohenMacaulay, hdim] at hself
  refine Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes.mp ?_
  exact_mod_cast hself

/-- **No element of the maximal ideal is a nonzerodivisor**, when a dualizing module has the
maximal ideal among its associated primes. -/
theorem not_isSMulRegular_of_mem_associatedPrimes_maximalIdeal (N : ModuleCat.{u} A)
    (hN : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))
    (hass : IsLocalRing.maximalIdeal A ∈ associatedPrimes A N)
    {t : A} (ht : t ∈ IsLocalRing.maximalIdeal A) :
    ¬ IsSMulRegular A t := fun hreg =>
  (isSMulRegular_iff_forall_notMem_associatedPrimes t).mp hreg _
    (mem_associatedPrimes_self_of_mem_associatedPrimes_maximalIdeal N hN hass) ht

end Dualizing

end
