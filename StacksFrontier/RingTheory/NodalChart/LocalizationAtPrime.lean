module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.MvPolynomial.Localization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChangePullback
public import StacksFrontier.RingTheory.NodalChart.CompletedLocalRing

/-!
# The nodal chart at the origin over a prime of a non-local base

`Stacks.NodalChart.exists_ringEquiv_adicCompletion_localization_chartOrigin` computes the
completed local ring of the nodal chart `R[x, y]/(xy - h)` at the origin of the chart over the
closed point, for `R` Noetherian *local*. The base `R` of the chart of Tag 0CBY is an affine
étale neighbourhood of a point of the base scheme, hence of finite type over it, and so is not
local: what is needed there is the same computation at the origin of the chart over an arbitrary
prime `𝔭` of `R`. This file supplies it by comparing the chart over `R` with the chart over the
localization `R_𝔭`.

The comparison is that the nodal chart over `R_𝔭` is a localization of the nodal chart over `R`:
`R_𝔭[x, y]` is the localization of `R[x, y]` at the image of `R ∖ 𝔭`
(`MvPolynomial.isLocalization`), and taking the quotient by the nodal equation on both sides
preserves that (`IsLocalization.of_surjective`, the nodal equation over `R_𝔭` being the image of
the nodal equation over `R`). The origin over the maximal ideal of `R_𝔭` is then the image of the
origin over `𝔭`, the latter is prime and disjoint from the localizing submonoid, so the two
correspond and the local rings of the two charts at the two origins agree.

## Main results

* `Stacks.NodalChart.isLocalization_nodalChartRing_localizationAtPrime` — **the nodal chart over
  `R_𝔭` is the localization of the nodal chart over `R` at the image of `R ∖ 𝔭`.**
* `Stacks.NodalChart.map_chartOrigin` — the origin over `𝔭` maps onto the origin over the maximal
  ideal of `R_𝔭`.
* `Stacks.NodalChart.comap_chartOrigin_maximalIdeal` — and pulls back from it.
* `Stacks.NodalChart.exists_ringEquiv_localizationAtPrime_chartOrigin` — **the local ring of the
  chart over `R` at the origin over `𝔭` is the local ring of the chart over `R_𝔭` at its
  origin.**
* `Stacks.NodalChart.exists_ringEquiv_adicCompletion_localizationAtPrime_chartOrigin` — **the
  completed local ring of the nodal chart at the origin over a prime `𝔭` of an arbitrary
  Noetherian base is `A⟦x, y⟧/(xy - h)`**, where `A` is the completion of `R_𝔭`. This is the
  non-local form of `exists_ringEquiv_adicCompletion_localization_chartOrigin`.

## Implementation notes

The algebra structure of `R_𝔭[x, y]/(xy - h)` over `R[x, y]/(xy - h)` is the one induced by
`Stacks.nodalChartMap`, declared as an instance here: the two types determine `R`, `h` and `𝔭`,
so instance resolution has nothing to guess.

The last result transports the computation over the local base along the isomorphism of local
rings using `StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv`, which matches the
maximal ideals of two isomorphic local rings and therefore their completions.
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.MixedCompletion

universe u

namespace Stacks.NodalChart

attribute [local instance] MvPolynomial.algebraMvPolynomial

section Localization

variable {R : Type u} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (h : R)

/-- The nodal equation over the localized base is the image of the nodal equation over the
base. -/
public theorem map_span_nodalEquation :
    Ideal.map (algebraMap (MvPolynomial (Fin 2) R)
          (MvPolynomial (Fin 2) (Localization.AtPrime 𝔭)))
        (Ideal.span {nodalEquation R h}) =
      Ideal.span {nodalEquation (Localization.AtPrime 𝔭)
        (algebraMap R (Localization.AtPrime 𝔭) h)} := by
  rw [Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def, map_nodalEquation]

/-- The nodal chart over the localized base is an algebra over the nodal chart, through
`Stacks.nodalChartMap`. -/
public instance algebraNodalChartRingLocalizationAtPrime :
    Algebra (nodalChartRing R h)
      (nodalChartRing (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭) h)) :=
  (nodalChartMap (algebraMap R (Localization.AtPrime 𝔭)) h).toAlgebra

public theorem algebraMap_nodalChartRing_localizationAtPrime_eq :
    algebraMap (nodalChartRing R h)
        (nodalChartRing (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭) h)) =
      nodalChartMap (algebraMap R (Localization.AtPrime 𝔭)) h :=
  rfl

/-- **The nodal chart over the localization of the base is a localization of the nodal chart.**
The chart `R_𝔭[x, y]/(xy - h)` is the localization of `R[x, y]/(xy - h)` at the image of the
multiplicative set `R ∖ 𝔭`. -/
public instance isLocalization_nodalChartRing_localizationAtPrime :
    IsLocalization (Algebra.algebraMapSubmonoid (nodalChartRing R h) 𝔭.primeCompl)
      (nodalChartRing (Localization.AtPrime 𝔭)
        (algebraMap R (Localization.AtPrime 𝔭) h)) := by
  have hsub : (𝔭.primeCompl.map (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)).map
        (algebraMap (MvPolynomial (Fin 2) R) (nodalChartRing R h)) =
      Algebra.algebraMapSubmonoid (nodalChartRing R h) 𝔭.primeCompl := by
    ext x
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
    constructor
    · rintro ⟨p, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, by rw [algebraMap_nodalChartRing_eq]⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨MvPolynomial.C s, ⟨s, hs, rfl⟩, by rw [algebraMap_nodalChartRing_eq]⟩
  rw [← hsub]
  refine IsLocalization.of_surjective _ _
    (algebraMap (MvPolynomial (Fin 2) R) (nodalChartRing R h)) Ideal.Quotient.mk_surjective
    (algebraMap (MvPolynomial (Fin 2) (Localization.AtPrime 𝔭))
      (nodalChartRing (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭) h)))
    Ideal.Quotient.mk_surjective ?_ ?_
  · rw [algebraMap_nodalChartRing_localizationAtPrime_eq, nodalChartMap_comp_quotientMk,
      MvPolynomial.algebraMap_def]
  · rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, Ideal.mk_ker]
    exact (map_span_nodalEquation 𝔭 h).ge

/-! ### The origin over a prime of the base -/

/-- **The origin over `𝔭` maps onto the origin over the maximal ideal of `R_𝔭`.** -/
public theorem map_chartOrigin :
    (chartOrigin 𝔭 h).map (algebraMap (nodalChartRing R h)
        (nodalChartRing (Localization.AtPrime 𝔭)
          (algebraMap R (Localization.AtPrime 𝔭) h))) =
      chartOrigin (𝔭.map (algebraMap R (Localization.AtPrime 𝔭)))
        (algebraMap R (Localization.AtPrime 𝔭) h) := by
  rw [chartOrigin, chartOrigin, Ideal.map_map, algebraMap_nodalChartRing_localizationAtPrime_eq,
    nodalChartMap_comp_quotientMk, ← Ideal.map_map, map_polyMixed]

/-- The parameter of the chart lies in the maximal ideal of the localized base. -/
public theorem algebraMap_mem_maximalIdeal_localizationAtPrime (hh : h ∈ 𝔭) :
    algebraMap R (Localization.AtPrime 𝔭) h ∈ maximalIdeal (Localization.AtPrime 𝔭) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ hh

/-- The localizing submonoid misses the origin over `𝔭`: a constant coming from outside `𝔭`
does not vanish at the origin. -/
public theorem disjoint_algebraMapSubmonoid_chartOrigin (hh : h ∈ 𝔭) :
    Disjoint ((Algebra.algebraMapSubmonoid (nodalChartRing R h) 𝔭.primeCompl :
        Submonoid (nodalChartRing R h)) : Set (nodalChartRing R h))
      (chartOrigin 𝔭 h : Set (nodalChartRing R h)) := by
  rw [Set.disjoint_left]
  intro x hx hmem
  obtain ⟨s, hs, rfl⟩ := hx
  have hs𝔭 : s ∈ 𝔭 := by
    rw [← C_mem_polyMixed_iff (n := 2), ← comap_chartOrigin (I := 𝔭) (h := h) hh,
      Ideal.mem_comap, ← algebraMap_nodalChartRing_eq]
    exact hmem
  exact absurd hs𝔭 hs

/-- **The origin over the maximal ideal of `R_𝔭` pulls back to the origin over `𝔭`.** -/
public theorem comap_chartOrigin_maximalIdeal (hh : h ∈ 𝔭) :
    (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
          (algebraMap R (Localization.AtPrime 𝔭) h)).comap
        (algebraMap (nodalChartRing R h)
          (nodalChartRing (Localization.AtPrime 𝔭)
            (algebraMap R (Localization.AtPrime 𝔭) h))) =
      chartOrigin 𝔭 h := by
  have hp : (chartOrigin 𝔭 h).IsPrime := chartOrigin_isPrime (I := 𝔭) hh
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← map_chartOrigin]
  exact IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid (nodalChartRing R h) 𝔭.primeCompl) _ hp
    (disjoint_algebraMapSubmonoid_chartOrigin 𝔭 h hh)

/-- **The local ring of the chart at the origin over `𝔭` is the local ring of the chart over the
localized base at its origin**, compatibly with the maps from the chart over `R`. -/
public theorem exists_ringEquiv_localizationAtPrime_chartOrigin (hh : h ∈ 𝔭) :
    letI := chartOrigin_isPrime (I := 𝔭) hh
    letI := chartOrigin_isMaximal (I := maximalIdeal (Localization.AtPrime 𝔭))
      (algebraMap_mem_maximalIdeal_localizationAtPrime 𝔭 h hh)
    ∃ E : Localization.AtPrime (chartOrigin 𝔭 h) ≃+*
        Localization.AtPrime (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
          (algebraMap R (Localization.AtPrime 𝔭) h)),
      ∀ c : nodalChartRing R h,
        E (algebraMap (nodalChartRing R h) (Localization.AtPrime (chartOrigin 𝔭 h)) c) =
          algebraMap _ _ (nodalChartMap (algebraMap R (Localization.AtPrime 𝔭)) h c) := by
  let := chartOrigin_isPrime (I := 𝔭) hh
  let := chartOrigin_isMaximal (I := maximalIdeal (Localization.AtPrime 𝔭))
    (algebraMap_mem_maximalIdeal_localizationAtPrime 𝔭 h hh)
  let : IsScalarTower (nodalChartRing R h)
      (nodalChartRing (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭) h))
      (Localization.AtPrime (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
        (algebraMap R (Localization.AtPrime 𝔭) h))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hloc := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid (nodalChartRing R h) 𝔭.primeCompl)
    (Localization.AtPrime (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
      (algebraMap R (Localization.AtPrime 𝔭) h)))
    (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
      (algebraMap R (Localization.AtPrime 𝔭) h))
  have hsub : (chartOrigin 𝔭 h).primeCompl =
      (Ideal.comap (algebraMap (nodalChartRing R h)
            (nodalChartRing (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭) h)))
          (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
            (algebraMap R (Localization.AtPrime 𝔭) h))).primeCompl :=
    Submonoid.ext fun c => by
      show c ∉ chartOrigin 𝔭 h ↔ c ∉ _
      rw [comap_chartOrigin_maximalIdeal 𝔭 h hh]
      simp
  have hloc' : IsLocalization (chartOrigin 𝔭 h).primeCompl
      (Localization.AtPrime (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
        (algebraMap R (Localization.AtPrime 𝔭) h))) := by
    rw [hsub]
    exact hloc
  let := hloc'
  refine ⟨(IsLocalization.algEquiv (chartOrigin 𝔭 h).primeCompl
    (Localization.AtPrime (chartOrigin 𝔭 h))
    (Localization.AtPrime (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
      (algebraMap R (Localization.AtPrime 𝔭) h)))).toRingEquiv, fun c => ?_⟩
  exact ((IsLocalization.algEquiv (chartOrigin 𝔭 h).primeCompl
    (Localization.AtPrime (chartOrigin 𝔭 h))
    (Localization.AtPrime (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
      (algebraMap R (Localization.AtPrime 𝔭) h)))).commutes c).trans
    (IsScalarTower.algebraMap_apply (nodalChartRing R h)
      (nodalChartRing (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭) h))
      (Localization.AtPrime (chartOrigin (maximalIdeal (Localization.AtPrime 𝔭))
        (algebraMap R (Localization.AtPrime 𝔭) h))) c)

/-! ### The completed local ring at the origin over a prime -/

/-- **The completed local ring of a nodal chart at the origin over a prime of an arbitrary
Noetherian base.** For `R` Noetherian, `𝔭` a prime of `R` and `h ∈ 𝔭`, the completion of the
local ring of `R[x, y]/(xy - h)` at the origin of the chart over `𝔭` is `A⟦x, y⟧/(xy - h)`,
where `A` is the completion of the local ring `R_𝔭`.

This is the non-local form of
`Stacks.NodalChart.exists_ringEquiv_adicCompletion_localization_chartOrigin`, and it is the shape
Tag 0CAV consumes for a chart whose base is an affine étale neighbourhood of a point of the base
scheme. The isomorphism is compatible with the maps from `R`. -/
public theorem exists_ringEquiv_adicCompletion_localizationAtPrime_chartOrigin
    [IsNoetherianRing R] (hh : h ∈ 𝔭) :
    letI := chartOrigin_isPrime (I := 𝔭) hh
    letI := IsLocalization.isNoetherianRing 𝔭.primeCompl (Localization.AtPrime 𝔭)
      inferInstance
    ∃ E : AdicCompletion (maximalIdeal (Localization.AtPrime (chartOrigin 𝔭 h)))
          (Localization.AtPrime (chartOrigin 𝔭 h)) ≃+*
        (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔭))
            (Localization.AtPrime 𝔭)) ⧸
          nodalSeriesIdeal (Localization.AtPrime 𝔭)
            (algebraMap R (Localization.AtPrime 𝔭) h)),
      ∀ r : R, E (algebraMap (Localization.AtPrime (chartOrigin 𝔭 h)) _
          (algebraMap (nodalChartRing R h) (Localization.AtPrime (chartOrigin 𝔭 h))
            (algebraMap R (nodalChartRing R h) r))) =
        algebraMap (Localization.AtPrime 𝔭) _ (algebraMap R (Localization.AtPrime 𝔭) r) := by
  let := chartOrigin_isPrime (I := 𝔭) hh
  let := IsLocalization.isNoetherianRing 𝔭.primeCompl (Localization.AtPrime 𝔭) inferInstance
  have hh' : algebraMap R (Localization.AtPrime 𝔭) h ∈ maximalIdeal (Localization.AtPrime 𝔭) :=
    algebraMap_mem_maximalIdeal_localizationAtPrime 𝔭 h hh
  let := chartOrigin_isMaximal (I := maximalIdeal (Localization.AtPrime 𝔭)) hh'
  obtain ⟨L, hL⟩ := exists_ringEquiv_localizationAtPrime_chartOrigin 𝔭 h hh
  obtain ⟨E₀, hE₀⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv L
  obtain ⟨E₁, hE₁⟩ := exists_ringEquiv_adicCompletion_localization_chartOrigin
    (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭) h) hh'
  refine ⟨E₀.trans E₁, fun r => ?_⟩
  rw [RingEquiv.trans_apply, hE₀, hL, nodalChartMap_algebraMap, hE₁]

end Localization

end Stacks.NodalChart

end
