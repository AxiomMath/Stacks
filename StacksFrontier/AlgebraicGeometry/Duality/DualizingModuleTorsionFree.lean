module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleStalk
public import StacksFrontier.RingTheory.Dualizing.AssociatedPrimeRegular
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
import all StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# A dualizing module over a Noetherian domain is torsion free

Let `A` be a Noetherian domain and let `ω` be a dualizing module over `A`: an `A`-module whose
complex `ω[n]` in some degree is a dualizing complex ([Stacks, Remark 0B4R]). Then `ω` is
torsion free. This is the property of the dualizing module that the last step of the proof of
[Stacks, Tag 0BBV] quotes from [Stacks, Tag 0AWK], read at a local ring of a normal surface.

## Main results

* `Dualizing.isTorsionFree_of_isDualizingComplex_single` — the statement for `ω[n]` dualizing.
* `Stacks.Duality.IsDualizingRingModule.isTorsionFree` — the same for a dualizing module in the
  sense of [Stacks, Remark 0B4R].
* `Stacks.Duality.IsDualizingModule.isTorsionFree_stalk` — the stalks of a dualizing module on a
  locally Noetherian scheme are torsion free wherever the local ring is a domain.

## The argument

Suppose `r • m = 0` with `r ≠ 0` and `m ≠ 0`. Then `r` is a zerodivisor on `ω`, so it lies in an
associated prime `p` of `ω`. Localizing at `p`, the maximal ideal of `A_p` is an associated prime
of `ω_p`, and `ω_p[0]` is a dualizing complex over `A_p` by [Stacks, Tag 0A7G]. A dualizing
module whose maximal ideal is associated lives on a zero-dimensional ring whose maximal ideal is
associated to the ring itself
(`Dualizing.mem_associatedPrimes_self_of_mem_associatedPrimes_maximalIdeal`, the argument of
[Stacks, Tag 0AWS]). But `A_p` is a domain, so its only associated prime is `0`; hence `p A_p = 0`,
and `r / 1 ∈ p A_p` forces `r = 0`.

Neither normality nor locality of `A` is needed.

## References

* [Stacks Project, Tag 0AWK](https://stacks.math.columbia.edu/tag/0AWK)
* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The only associated prime of a domain is the zero ideal. -/
private theorem eq_bot_of_mem_associatedPrimes_self {B : Type u} [CommRing B] [IsDomain B]
    {q : Ideal B} (hq : q ∈ associatedPrimes B B) : q = ⊥ := by
  obtain ⟨hprime, x, hx⟩ := hq
  have hx0 : x ≠ 0 := by
    rintro rfl
    refine hprime.ne_top (eq_top_iff.mpr fun y _ => ?_)
    rw [hx]
    exact Ideal.le_radical (by simp [Submodule.mem_colon_singleton])
  refine eq_bot_iff.mpr fun y hy => ?_
  rw [hx] at hy
  obtain ⟨k, hk⟩ := hy
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at hk
  exact (Submodule.mem_bot B).mpr (IsNilpotent.eq_zero ⟨k, (mul_eq_zero.mp hk).resolve_right hx0⟩)

/-- **A dualizing module over a Noetherian domain, in degree zero, is torsion free.** -/
theorem isTorsionFree_of_isDualizingComplex_singleZero [IsDomain A] (M : ModuleCat.{u} A)
    (hM : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) :
    Module.IsTorsionFree A M := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r m hrm
  by_contra! h
  -- `r` is a zerodivisor on `M`, hence lies in an associated prime `p`.
  have hreg : ¬ IsSMulRegular M r := fun hr => h.2 (hr (by simp [hrm]))
  have hmem : r ∈ ⋃ p ∈ associatedPrimes A M, (p : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_regular A M]
    exact hreg
  obtain ⟨p, hp, hrp⟩ := Set.mem_iUnion₂.mp hmem
  have : p.IsPrime := hp.isPrime
  let B := Localization.AtPrime p
  -- The maximal ideal of `A_p` is associated to `M_p`.
  have hass : maximalIdeal B ∈ associatedPrimes B (LocalizedModule.AtPrime p M) :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp
  -- `M_p` in degree zero is a dualizing complex over `A_p`.
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  have hflat : (algebraMap A B).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B p.primeCompl)
  let : (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).Additive :=
    extendScalars_additive.{u, u} _
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hflat
  let : PreservesColimitsOfSize.{u, u} (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} _).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have hext := isDualizingComplex_extendScalars_of_isLocalization (B := B) p.primeCompl _ hM
  have hMp : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
      (ModuleCat.of B (LocalizedModule.AtPrime p M))) :=
    isDualizingComplex_of_iso
      (Stacks.Duality.mapDerivedCategorySingleZeroIso _ M ≪≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso
          (extensionLocalizationIso.{u, u} p.primeCompl M)) hext
  -- Hence `p A_p` is associated to the domain `A_p`, so it is zero.
  have hbot : maximalIdeal B = ⊥ := eq_bot_of_mem_associatedPrimes_self
    (mem_associatedPrimes_self_of_mem_associatedPrimes_maximalIdeal
      (ModuleCat.of B (LocalizedModule.AtPrime p M)) hMp hass)
  have hr : algebraMap A B r ∈ maximalIdeal B := by
    rw [← Localization.AtPrime.under_maximalIdeal (I := p)] at hrp
    exact hrp
  rw [hbot, Ideal.mem_bot] at hr
  exact h.1 ((IsLocalization.injective B p.primeCompl_le_nonZeroDivisors) (by simpa using hr))

/-- **A dualizing module over a Noetherian domain is torsion free.** If `M[n]` is a dualizing
complex over the Noetherian domain `A` for some `n`, then `M` is a torsion free `A`-module. -/
theorem isTorsionFree_of_isDualizingComplex_single [IsDomain A] (M : ModuleCat.{u} A) (n : ℤ)
    (hM : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M)) :
    Module.IsTorsionFree A M :=
  isTorsionFree_of_isDualizingComplex_singleZero M
    (isDualizingComplex_of_iso
      (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso n 0 n (add_zero n)).app M)
      (isDualizingComplex_shift _ hM n))

end Dualizing

namespace Stacks.Duality

/-- **A dualizing module of a Noetherian domain is torsion free** ([Stacks, Remark 0B4R] for the
terminology). -/
theorem IsDualizingRingModule.isTorsionFree {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {M : Type u} [AddCommGroup M] [Module A M]
    (hM : IsDualizingRingModule A M) : Module.IsTorsionFree A M :=
  have ⟨n, hn⟩ := hM.2
  Dualizing.isTorsionFree_of_isDualizingComplex_single (ModuleCat.of A M) n hn

/-- **The stalks of a dualizing module are torsion free** at every point whose local ring is a
domain — at every point of a normal or integral scheme, for instance. -/
theorem IsDualizingModule.isTorsionFree_stalk {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {ω : X.Modules} (hω : IsDualizingModule ω) (x : X)
    [IsDomain (X.presheaf.stalk x)] :
    letI := Stacks.ModuleStalkSpecialization.stalkModule ω x
    Module.IsTorsionFree (X.presheaf.stalk x) (ω.presheaf.stalk x) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule ω x
  have : ω.IsCoherent := hω.1
  have : ω.IsQuasicoherent := isQuasicoherent_of_isCoherent ω
  obtain ⟨n, hn⟩ := hω.2
  exact Dualizing.isTorsionFree_of_isDualizingComplex_singleZero _
    (isDualizingComplex_single_stalk ω n hn x)

end Stacks.Duality

end
