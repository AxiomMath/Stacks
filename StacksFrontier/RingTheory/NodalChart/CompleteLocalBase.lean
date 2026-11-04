module

public import StacksFrontier.RingTheory.NodalChart.CompletedLocalRing

/-!
# The completed local ring of a nodal chart over a complete base

`Stacks.NodalChart.exists_ringEquiv_adicCompletion_localization_chartOrigin` computes the
completed local ring of the nodal chart `R[x, y]/(xy - h)` at the origin of the chart over the
closed point as `A⟦x, y⟧/(xy - h)`, where `A` is the completion of the Noetherian local ring `R`
and the parameter is read in `A`. When `R` is already complete for its maximal-adic topology
there is nothing to complete, and the answer is `R⟦x, y⟧/(xy - h)` with the parameter `h` itself.

That is the shape in which Tag 0CBX states the completed local ring of a nodal family — a
quotient of a power series ring over the completed local ring of the base, by `xy` minus a
parameter of that same ring — so it is the shape in which the two must be compared.

## Main results

* `Stacks.NodalChart.exists_ringEquiv_adicCompletion_localization_chartOrigin_of_isAdicComplete`
  — **the completed local ring of a nodal chart over a complete Noetherian local base `A` is
  `A⟦x, y⟧/(xy - h)`**, compatibly with the maps from `A`.

## Implementation notes

The identification of `A` with its own completion is `AdicCompletion.ofAlgEquiv`, available
because `A` is `𝔪`-adically complete; it is carried to the power series ring by
`MvPowerSeries.map` and to the quotient by `Ideal.quotientEquiv`.

## References

* [Stacks Project, Tag 0CBX](https://stacks.math.columbia.edu/tag/0CBX)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Stacks.NodalChart

/-- **The completed local ring of a nodal chart over a complete Noetherian local base.** For `A`
Noetherian local and complete for its maximal-adic topology and `h` in the maximal ideal, the
completion of the local ring of `A[x, y]/(xy - h)` at the origin of the chart over the closed
point is `A⟦x, y⟧/(xy - h)`, compatibly with the two maps from `A`.

This is `Stacks.NodalChart.exists_ringEquiv_adicCompletion_localization_chartOrigin` read
through the canonical identification of a complete ring with its own completion. -/
public theorem exists_ringEquiv_adicCompletion_localization_chartOrigin_of_isAdicComplete
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (h : A) (hh : h ∈ maximalIdeal A) :
    letI := chartOrigin_isMaximal (I := maximalIdeal A) hh
    ∃ E : AdicCompletion (maximalIdeal (Localization.AtPrime (chartOrigin (maximalIdeal A) h)))
          (Localization.AtPrime (chartOrigin (maximalIdeal A) h)) ≃+*
        (MvPowerSeries (Fin 2) A ⧸ Ideal.span
          {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}),
      ∀ a : A, E (algebraMap (Localization.AtPrime (chartOrigin (maximalIdeal A) h)) _
          (algebraMap (nodalChartRing A h) (Localization.AtPrime (chartOrigin (maximalIdeal A) h))
            (algebraMap A (nodalChartRing A h) a))) =
        algebraMap A (MvPowerSeries (Fin 2) A ⧸ Ideal.span
          {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) a := by
  let := chartOrigin_isMaximal (I := maximalIdeal A) hh
  obtain ⟨E₀, hE₀⟩ := exists_ringEquiv_adicCompletion_localization_chartOrigin A h hh
  let ε : AdicCompletion (maximalIdeal A) A ≃+* A :=
    (AdicCompletion.ofAlgEquiv (maximalIdeal A)).symm.toRingEquiv
  have hε : ∀ a : A, ε (algebraMap A (AdicCompletion (maximalIdeal A) A) a) = a := fun a => by
    show (AdicCompletion.ofAlgEquiv (maximalIdeal A)).symm
      (algebraMap A (AdicCompletion (maximalIdeal A) A) a) = a
    rw [← (AdicCompletion.ofAlgEquiv (maximalIdeal A)).commutes a,
      AlgEquiv.symm_apply_apply]
    rfl
  let F : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ≃+*
      MvPowerSeries (Fin 2) A :=
    RingEquiv.ofRingHom (MvPowerSeries.map ε.toRingHom) (MvPowerSeries.map ε.symm.toRingHom)
      (by rw [← MvPowerSeries.map_comp]
          simp only [RingEquiv.toRingHom_eq_coe, ε.comp_symm, MvPowerSeries.map_id])
      (by rw [← MvPowerSeries.map_comp]
          simp only [RingEquiv.toRingHom_eq_coe, ε.symm_comp, MvPowerSeries.map_id])
  have hFC : ∀ c, F (MvPowerSeries.C c) = MvPowerSeries.C (ε c) := fun c => by
    show MvPowerSeries.map ε.toRingHom (MvPowerSeries.C c) = _
    rw [MvPowerSeries.map_C]
    rfl
  have hgen : (F : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) →+*
        MvPowerSeries (Fin 2) A)
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 -
        MvPowerSeries.C (algebraMap A (AdicCompletion (maximalIdeal A) A) h)) =
      MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h := by
    rw [map_sub, map_mul, RingEquiv.coe_toRingHom, hFC, hε]
    simp [F]
  have hI : Ideal.span ({MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h} :
        Set (MvPowerSeries (Fin 2) A)) =
      Ideal.map (F : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) →+*
        MvPowerSeries (Fin 2) A) (nodalSeriesIdeal A h) := by
    rw [nodalSeriesIdeal, Ideal.map_span, Set.image_singleton, hgen]
  refine ⟨E₀.trans (Ideal.quotientEquiv (nodalSeriesIdeal A h) _ F hI), fun a => ?_⟩
  rw [RingEquiv.trans_apply, hE₀]
  show (Ideal.quotientEquiv (nodalSeriesIdeal A h) _ F hI)
    (algebraMap A (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸
      nodalSeriesIdeal A h) a) = _
  rw [show algebraMap A (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A) ⧸
        nodalSeriesIdeal A h) a =
      Ideal.Quotient.mk _ (algebraMap A
        (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A) A)) a) from rfl,
    Ideal.quotientEquiv_mk, MvPowerSeries.algebraMap_apply, hFC, hε,
    show algebraMap A (MvPowerSeries (Fin 2) A ⧸ Ideal.span
        ({MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h} :
          Set (MvPowerSeries (Fin 2) A))) a =
      Ideal.Quotient.mk _ (algebraMap A (MvPowerSeries (Fin 2) A) a) from rfl,
    MvPowerSeries.algebraMap_apply]
  rfl

end Stacks.NodalChart

end
