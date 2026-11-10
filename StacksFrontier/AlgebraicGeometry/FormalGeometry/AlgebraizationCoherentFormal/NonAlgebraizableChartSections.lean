module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelTransition

/-!
# The chart rings as sections on the punctured spectrum, and their restriction to the overlap

`Stacks.Algebraization.NonAlgebraizableExample.levelOverlapRingEquiv` reads the chart ring
`A_{xy}/tⁿA_{xy}` as the sections of `𝒪` over the overlap of the two charts of the punctured
spectrum of `A/tⁿA`. This file does the same for a single chart — the equivalence
`A_r/tⁿA_r ≅ Γ(D(r̄))` with `D(r̄)` read as an open of the punctured spectrum rather than of
`Spec(A/tⁿA)` — and records that restricting from a chart to the overlap of the two charts is the
ring map `Stacks.Algebraization.NonAlgebraizableExample.chartRestrict`, which is what
`Stacks.Algebraization.NonAlgebraizableExample.gluedSections` is cut out by.

That dictionary is what turns a sheaf-theoretic trivialization of the glued module `𝓛ₙ` into the
ring-theoretic statement `Stacks.Algebraization.NonAlgebraizableExample.gluedSections` speaks
about: a pair of chart functions matched by the transition element.

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.levelChartRingEquiv` — the chart ring
  `A_r/tⁿA_r` is the ring of sections of `𝒪` on the chart `D(r̄)` of the punctured spectrum of
  `A/tⁿA`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.image_levelChart` — the image in
  `Spec(A/tⁿA)` of a chart of the punctured spectrum is the basic open it was pulled back from.
* `Stacks.Algebraization.NonAlgebraizableExample.map_chartOpenEquiv` — restriction of sections
  from `D(r̄)` to a smaller basic open `D(q̄)` of `Spec(A/tⁿA)` is `chartRestrict`.
* `Stacks.Algebraization.NonAlgebraizableExample.map_levelChartRingEquiv_overlap` — restriction
  from a chart of the punctured spectrum to the overlap of the two charts is `chartRestrict`.

## Implementation notes

`map_chartOpenEquiv` is proved by uniqueness of maps out of a localization: both sides are ring
maps from `A_r/tⁿA_r`, which is the localization of `A/tⁿA` away from the image of `r`
(`isLocalization_away_levelToChart`), and they agree on the image of `A/tⁿA` because
`chartOpenEquiv` is an `A/tⁿA`-algebra map, `chartRestrict` carries the image of `A/tⁿA` in one
chart ring to its image in the other, and restriction of sections of the structure sheaf fixes
`AlgebraicGeometry.StructureSheaf.algebraMap_self_map`.

The transport from `Spec(A/tⁿA)` to its punctured spectrum is the same two steps as in
`levelOverlapRingEquiv`: sections of an open subscheme are sections of the ambient scheme on the
image open by `rfl`, so only the identification of that image is needed.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- The image in `Spec(A/tⁿA)` of the chart `D(r̄)` of the punctured spectrum is the basic open
`D(r̄)` itself. -/
public theorem image_levelChart (r : AmbientRing k) (n : ℕ)
    (hle : chartOpen k r n ≤ levelOpen k n) :
    (levelOpen k n).ι ''ᵁ levelChart k r n = chartOpen k r n := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hle]

/-- **Restriction of chart functions along a divisibility.** On the sections of `𝒪` over the
basic opens of `Spec(A/tⁿA)`, restriction from `D(r̄)` to the smaller `D(q̄)` is the map
`A_r/tⁿA_r → A_q/tⁿA_q`. -/
@[stacks 0EHE "restriction from D(r) to D(q) is A_r/t^n A_r -> A_q/t^n A_q"]
public theorem map_chartOpenEquiv (r q : AmbientRing k) (hdvd : r ∣ q) (n : ℕ)
    (hle : chartOpen k q n ≤ chartOpen k r n) (v : chartRing k r n) :
    ((levelScheme k n).presheaf.map (homOfLE hle).op).hom (chartOpenEquiv k r n v) =
      chartOpenEquiv k q n (chartRestrict k r q hdvd n v) := by
  have : IsLocalization.Away (levelElt k r n) (chartRing k r n) :=
    isLocalization_away_levelToChart k r n
  have hrestrict (z : levelRing k n) :
      chartRestrict k r q hdvd n (levelToChart k r n z) = levelToChart k q n z := by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [levelToChart_mk, chartRestrict_mk, localizationRestrict_algebraMap, levelToChart_mk]
  have hext : ((levelScheme k n).presheaf.map (homOfLE hle).op).hom.comp
      (chartOpenEquiv k r n).toRingEquiv.toRingHom =
      (chartOpenEquiv k q n).toRingEquiv.toRingHom.comp
        (chartRestrict k r q hdvd n).toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (levelElt k r n))
      (RingHom.ext fun z => ?_)
    have h1 : chartOpenEquiv k r n (levelToChart k r n z) =
        algebraMap (levelRing k n) Γ(levelScheme k n, chartOpen k r n) z :=
      (chartOpenEquiv k r n).commutes z
    have h2 : chartOpenEquiv k q n (chartRestrict k r q hdvd n (levelToChart k r n z)) =
        algebraMap (levelRing k n) Γ(levelScheme k n, chartOpen k q n) z := by
      rw [hrestrict]
      exact (chartOpenEquiv k q n).commutes z
    change ((levelScheme k n).presheaf.map (homOfLE hle).op).hom
        (chartOpenEquiv k r n (levelToChart k r n z)) =
      chartOpenEquiv k q n (chartRestrict k r q hdvd n (levelToChart k r n z))
    rw [h1, h2]
    exact ConcreteCategory.congr_hom (StructureSheaf.algebraMap_self_map (R := levelRing k n)
      (op (chartOpen k q n)) (op (chartOpen k r n)) (homOfLE hle).op) z
  exact DFunLike.congr_fun hext v

/-- **Stacks Project, Tag 0EHE (a chart ring is the ring of sections on the chart).** The chart
ring `A_r/tⁿA_r` is the ring of sections of `𝒪` on the chart `D(r̄)` of the punctured spectrum of
`A/tⁿA`; compare `levelOverlapRingEquiv` for the overlap of the two charts. -/
@[stacks 0EHE "A_r/t^n A_r is the ring of sections of O on the chart D(r)"]
public def levelChartRingEquiv (r : AmbientRing k) (n : ℕ)
    (hle : chartOpen k r n ≤ levelOpen k n) :
    chartRing k r n ≃+* Γ((levelOpen k n).toScheme, levelChart k r n) :=
  (chartOpenEquiv k r n).toRingEquiv.trans
    ((levelScheme k n).presheaf.mapIso
      (eqToIso (image_levelChart k r n hle)).op).commRingCatIsoToRingEquiv

/-- `levelChartRingEquiv` is `chartOpenEquiv` followed by restriction of sections along the
identification `image_levelChart` of the image of the chart. -/
public theorem levelChartRingEquiv_apply (r : AmbientRing k) (n : ℕ)
    (hle : chartOpen k r n ≤ levelOpen k n) (v : chartRing k r n) :
    levelChartRingEquiv k r n hle v =
      ((levelScheme k n).presheaf.map (eqToIso (image_levelChart k r n hle)).op.hom).hom
        (chartOpenEquiv k r n v) := rfl

/-- **Stacks Project, Tag 0EHE (restriction from a chart to the overlap).** Restriction of
sections of `𝒪` from a chart of the punctured spectrum of `A/tⁿA` to the overlap of the two
charts is the map `chartRestrict` of chart rings. This is the dictionary between the sheaf-level
and the ring-level description of the glued module: a global section of `𝓛ₙ` is a pair of chart
functions matched on the overlap, and this is what matching means. -/
@[stacks 0EHE "restriction from a chart to the overlap is A_r/t^n A_r -> A_xy/t^n A_xy"]
public theorem map_levelChartRingEquiv_overlap (r : AmbientRing k) (n : ℕ)
    (hdvd : r ∣ xVar k * yVar k) (hle : chartOpen k r n ≤ levelOpen k n)
    (hq : chartOpen k (xVar k * yVar k) n ≤ chartOpen k r n)
    (h : levelOverlap k n ≤ levelChart k r n) (v : chartRing k r n) :
    ((levelOpen k n).toScheme.presheaf.map (homOfLE h).op).hom
        (levelChartRingEquiv k r n hle v) =
      levelOverlapRingEquiv k n (chartRestrict k r (xVar k * yVar k) hdvd n v) := by
  have hcomp := (levelScheme k n).presheaf.map_comp
    (eqToIso (image_levelChart k r n hle)).op.hom
    ((levelOpen k n).ι.opensFunctor.map (homOfLE h)).op
  have hcomp' := (levelScheme k n).presheaf.map_comp (homOfLE hq).op
    (homOfLE (image_levelOverlap k n).le).op
  rw [levelChartRingEquiv_apply, levelOverlapRingEquiv_apply,
    ← map_chartOpenEquiv k r (xVar k * yVar k) hdvd n hq v]
  rw [show (eqToIso (image_levelChart k r n hle)).op.hom ≫
        ((levelOpen k n).ι.opensFunctor.map (homOfLE h)).op =
      (homOfLE hq).op ≫ (homOfLE (image_levelOverlap k n).le).op from
    Subsingleton.elim _ _] at hcomp
  exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hcomp.trans hcomp'.symm))
    (chartOpenEquiv k r n v)).symm

end Stacks.Algebraization.NonAlgebraizableExample

end
