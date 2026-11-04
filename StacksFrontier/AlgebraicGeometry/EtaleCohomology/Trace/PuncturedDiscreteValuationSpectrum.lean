module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Pulling an open subscheme back to the spectrum of a discrete valuation ring

Let `R` be a discrete valuation ring with uniformizer `ϖ`, let `f : Spec R ⟶ X` and let
`j : U ⟶ X` be an open immersion such that `f` sends the generic point into `U` and the closed
point outside `U`. Then `U ×_X Spec R` is the punctured spectrum of `R`, which is
`Spec R[1/ϖ] = Spec K`, `K` the fraction field: the spectrum of `R` has exactly two points, the
preimage of `U` is the generic point alone, and that is the basic open set `D(ϖ)`.

This is the geometric step in the description of the local invariants `H⁰_loc` of Weil II 1.8:
for an open immersion `j : U ⟶ X̄` of curves and a boundary point `y ∉ U`, the strict
henselization `Spec 𝒪^{sh}_{X̄,ȳ}` is the spectrum of a discrete valuation ring whose generic
point maps into `U`, so `U ×_X̄ Spec 𝒪^{sh}_{X̄,ȳ}` is the spectrum of its fraction field `K^{sh}`,
and the stalk of `j_* F` at `ȳ` is the set of sections of `F` over `Spec K^{sh}`
(`Stacks.EtaleCohomology.nonempty_directImageStalkIsoStrictHenselizationGamma`).

## Main results

* `AlgebraicGeometry.exists_pullback_iso_spec_away_of_isDiscreteValuationRing` — the iso
  `U ×_X Spec R ≅ Spec R[1/ϖ]` over `Spec R`.
* `AlgebraicGeometry.isFractionRing_localizationAway_of_irreducible` — `R[1/ϖ]` is the fraction
  field of `R`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

/-- In a discrete valuation ring a prime ideal avoids a uniformizer exactly when it is zero. -/
theorem notMem_prime_iff_eq_bot_of_irreducible (hϖ : Irreducible ϖ) (p : Ideal R)
    [p.IsPrime] : ϖ ∉ p ↔ p = ⊥ := by
  constructor
  · intro h
    by_contra hp
    rw [IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hp),
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ] at h
    exact h (Ideal.mem_span_singleton_self ϖ)
  · rintro rfl h
    exact hϖ.ne_zero ((Submodule.mem_bot R).1 h)

/-- **The spectrum of a localization away from a uniformizer is the fraction field**: inverting a
uniformizer of a discrete valuation ring inverts every nonzero element. -/
theorem isFractionRing_localizationAway_of_irreducible (hϖ : Irreducible ϖ) :
    IsFractionRing R (Localization.Away ϖ) := by
  refine IsLocalization.of_le (Submonoid.powers ϖ) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun x hx => ?_
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hx) hϖ
  rw [map_mul, map_pow]
  exact (v.isUnit.map _).mul ((IsLocalization.Away.algebraMap_isUnit ϖ).pow n)

/-- **The preimage of an open subscheme in the spectrum of a discrete valuation ring.** If `f`
sends the generic point of `Spec R` into the open subscheme `j : U ⟶ X` and the closed point
outside it, then `U ×_X Spec R` is isomorphic over `Spec R` to `Spec R[1/ϖ]`. -/
theorem exists_pullback_iso_spec_away_of_isDiscreteValuationRing (hϖ : Irreducible ϖ)
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (f : Spec (.of R) ⟶ X)
    (hgen : f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range j)
    (hcl : f (IsLocalRing.closedPoint R) ∉ Set.range j) :
    ∃ e : pullback j f ≅ Spec (.of (Localization.Away ϖ)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away ϖ))) =
        pullback.snd j f := by
  have hrange : Set.range (pullback.snd j f) =
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away ϖ)))) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    change _ = Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away ϖ)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away ϖ) ϖ]
    ext (p : PrimeSpectrum R)
    change f p ∈ Set.range j ↔ ϖ ∉ p.asIdeal
    rw [notMem_prime_iff_eq_bot_of_irreducible R hϖ p.asIdeal]
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · by_contra hne
      obtain rfl : p = IsLocalRing.closedPoint R :=
        PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne))
      exact hcl hp
    · obtain rfl : p = ⟨⊥, Ideal.isPrime_bot⟩ := PrimeSpectrum.ext hp
      exact hgen
  exact ⟨IsOpenImmersion.isoOfRangeEq _ _ hrange, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

end AlgebraicGeometry
