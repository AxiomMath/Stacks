module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalitiesUnwinding
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Dualizing.CanonicalModule
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange

/-!
# The normalizing shift of a base-changed normalized dualizing complex

Let `A → R` be a flat map of Noetherian local rings, let `p ⊆ A` be the prime under the maximal
ideal of `R`, and assume `p R = 𝔪_R`. If `ω` is a normalized dualizing complex over `A`, then
`(ω ⊗^L_A R)⟦-dim(A/p)⟧` is a normalized dualizing complex over `R`.

The map `A → R` factors as `A → A_p → R`, the second map is a flat local homomorphism whose
maximal ideal extends to the maximal ideal of `R`, so the statement is [Stacks, Tag 0A7Z]
(the localization `ω_p⟦-dim(A/p)⟧` is normalized over `A_p`) followed by [Stacks, Tag 0AWD]
(flat local base change preserves normalized dualizing complexes), transported along the
composition isomorphism of derived extension of scalars and the commutation with shifts.

As an input for the algebraization statements, in the local algebraization situation with
`𝔞 = 𝔪` the distance `δ^Y_Z(z)` at a point `z ∈ Y` lying under a point `y ∈ U` is bounded by
`dim(A/p)`, where `p` is the prime of `A` under `y`.

## Main results

* `Dualizing.isNormalizedDualizingComplex_totalDerivedExtensionScalars_shift` — the shifted
  derived base change is normalized.
* `Stacks.Algebraization.distanceToZ_le_ringKrullDim_quotient` — `δ^Y_Z(z) ≤ dim(A/p)`.
* `Stacks.Algebraization.exists_ringKrullDim_quotient_underlyingPrime_eq` — `dim(A/p)` is a
  natural number.

## References

* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- Derived base change along a flat map of Noetherian local rings `A → R`, with `p` the prime
under `𝔪_R` and `p R = 𝔪_R`, sends a normalized dualizing complex `ω` over `A` to a complex whose
shift by `-dim(A/p)` is a normalized dualizing complex over `R`: factor `A → A_p → R`, apply
[Stacks, Tag 0A7Z] to `A → A_p` and [Stacks, Tag 0AWD] to `A_p → R`. -/
public theorem isNormalizedDualizingComplex_totalDerivedExtensionScalars_shift
    {A R : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R] [Module.Flat A R]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsNormalizedDualizingComplex.{u, u} ω)
    (p : Ideal A) [p.IsPrime]
    (hp : (IsLocalRing.maximalIdeal R).comap (algebraMap A R) = p)
    (hmax : p.map (algebraMap A R) = IsLocalRing.maximalIdeal R)
    (e : ℕ) (he : ringKrullDim (A ⧸ p) = (e : WithBot ℕ∞)) :
    IsNormalizedDualizingComplex.{u, u}
      (((totalDerivedExtensionScalars.{u, u, u} (algebraMap A R)).functor.obj ω)⟦-(e : ℤ)⟧) := by
  let Ap := Localization.AtPrime p
  have : IsNoetherianRing Ap := IsLocalization.isNoetherianRing p.primeCompl Ap inferInstance
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap A R s) := fun s => by
    by_contra hs
    exact s.2 (hp ▸ ((mem_maximalIdeal (algebraMap A R s)).mpr hs :
      (s : A) ∈ (maximalIdeal R).comap (algebraMap A R)))
  let g : Ap →+* R := IsLocalization.lift hunit
  have hg : g.comp (algebraMap A Ap) = algebraMap A R := IsLocalization.lift_comp hunit
  let : Algebra Ap R := g.toAlgebra
  have : IsScalarTower A Ap R := IsScalarTower.of_algebraMap_eq' hg.symm
  have : Module.Flat Ap R :=
    (Module.flat_iff_of_isLocalization Ap p.primeCompl R).mpr inferInstance
  have hmaxAp : (maximalIdeal Ap).map (algebraMap Ap R) = maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    change p.map (g.comp (algebraMap A Ap)) = _
    rw [hg, hmax]
  have : IsLocalHom (algebraMap Ap R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm' := Ideal.mem_map_of_mem (algebraMap Ap R) ((mem_maximalIdeal a).mpr hna)
    rw [hmaxAp] at hm'
    exact (mem_maximalIdeal _).mp hm' ha
  have h2 := isNormalizedDualizingComplex_extendScalars_of_flat.{u, u, u} hmaxAp _
    (isNormalizedDualizingComplex_localizationAtPrime_shift ω hω p e he)
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap Ap R)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [← hg]
  refine (isNormalizedDualizingComplex_congr ?_).mp h2
  exact ((ModuleCat.extendScalars (algebraMap Ap R)).mapDerivedCategory.commShiftIso
      (-(e : ℤ))).app _ ≪≫
    (shiftFunctor _ (-(e : ℤ))).mapIso
      (((totalDerivedExtensionScalarsIsoExtendScalars (algebraMap Ap R)).app _).symm ≪≫
        (totalDerivedExtensionScalars.{u, u, u} g).functor.mapIso
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A Ap)).functor.mapIso
            ((uliftDerivedSelfIso A).app ω)) ≪≫
        (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A Ap) g).app ω)

end Dualizing

namespace Stacks.Algebraization

/-- The coheight of a prime, as an element of `WithBot ℕ∞`, is the Krull dimension of the
quotient by it. -/
private theorem coheight_eq_ringKrullDim_quotient' {R : Type u} [CommRing R]
    (q : PrimeSpectrum R) :
    (Order.coheight q : WithBot ℕ∞) = ringKrullDim (R ⧸ q.asIdeal) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  rfl

/-- For `z` a point of `Y = Spec(A/I)` the height of `z` in the specialization order is the
dimension of `(A/I)/z`. -/
private theorem height_Y_eq_ringKrullDim (S : AlgebraizationSituation.{u}) (z : S.Y) :
    ((Order.height z : ℕ∞) : WithBot ℕ∞) = ringKrullDim ((S.A ⧸ S.I) ⧸ z.asIdeal) := by
  have h : Order.height z = Order.coheight (α := PrimeSpectrum (S.A ⧸ S.I)) z :=
    (Order.height_orderIso
      (AlgebraicGeometry.specOrderIsoPrimeSpectrum (.of (S.A ⧸ S.I))) z).symm
  rw [h]
  exact coheight_eq_ringKrullDim_quotient' (R := S.A ⧸ S.I) z

/-- In the local algebraization situation with `𝔞 = 𝔪`, the distance `δ^Y_Z(z)` at a point
`z ∈ Y` lying under `y ∈ U` is at most `dim(A/p)`, for `p` the prime of `A` under `y`. -/
public theorem distanceToZ_le_ringKrullDim_quotient (S : AlgebraizationSituation.{u})
    [IsLocalRing S.A] (ha : S.a = IsLocalRing.maximalIdeal S.A) (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) :
    ((S.distanceToZ z : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (S.A ⧸ (underlyingPrime S y).asIdeal) := by
  have hdim : ringKrullDim ((S.A ⧸ S.I) ⧸ z.asIdeal) =
      ringKrullDim (S.A ⧸ (underlyingPrime S y).asIdeal) := by
    have hcomap : (underlyingPrime S y).asIdeal = z.asIdeal.comap (Ideal.Quotient.mk S.I) :=
      congrArg PrimeSpectrum.asIdeal hyz
    have hIle : S.I ≤ (underlyingPrime S y).asIdeal := by
      rw [hcomap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact z.asIdeal.zero_mem
    have hmap : (underlyingPrime S y).asIdeal.map (Ideal.Quotient.mk S.I) = z.asIdeal := by
      rw [hcomap, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [← hmap]
    exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIle)
  rw [← hdim, ← height_Y_eq_ringKrullDim S z]
  exact WithBot.coe_le_coe.mpr (distanceToZ_le_height S ha z)

/-- Over a Noetherian local ring the dimension of `A/p`, for `p` the prime under a point of `U`,
is a natural number. -/
public theorem exists_ringKrullDim_quotient_underlyingPrime_eq
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] (y : S.U.toScheme) :
    ∃ e : ℕ, ringKrullDim (S.A ⧸ (underlyingPrime S y).asIdeal) = e := by
  have : IsLocalRing (S.A ⧸ (underlyingPrime S y).asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp
    (ringKrullDim_ne_bot (R := S.A ⧸ (underlyingPrime S y).asIdeal))
  have hne : n ≠ ⊤ := by
    rintro rfl
    exact ringKrullDim_ne_top hn.symm
  obtain ⟨e, rfl⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨e, hn.symm⟩

end Stacks.Algebraization

end
