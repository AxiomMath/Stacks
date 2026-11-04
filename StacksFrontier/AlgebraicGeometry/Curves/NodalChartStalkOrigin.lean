module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation
public import StacksFrontier.RingTheory.AdicCompletion.CohenMacaulayFibreUniverse
public import StacksFrontier.RingTheory.NodalChart.CompleteLocalBase

/-!
# The completed local ring of the spectrum of a nodal chart at its origin

`Stacks.NodalChart.exists_ringEquiv_adicCompletion_localization_chartOrigin_of_isAdicComplete`
computes the completion of the *ring* `(R[x, y]/(xy - h))_{𝔫}` localized at the origin `𝔫` of
the chart. This file reads that computation on the *scheme* `Spec R[x, y]/(xy - h)`, at the point
of its spectrum given by the origin: the local ring of a spectrum at a prime is the localization
there, so the two differ only by the canonical identification, and the identification is
compatible with the maps from the coordinate ring.

That is the form in which the completed local ring of the chart is compared with the completed
local ring of a nodal family, which is where Tag 0CBX leaves it.

## Main results

* `Stacks.NodalChart.toStalk_comp_stalkHomAt_specMap` — **the map of local rings of `Spec φ` at a
  prime is `φ`**, read through the germ maps from the global sections.
* `Stacks.NodalChart.chartOriginPt` — the origin of the chart over the closed point, as a point
  of the spectrum of the chart.
* `Stacks.NodalChart.comap_chartOrigin_algebraMap` — the origin of the chart over a point of the
  base pulls back to that point along the structure map of the chart.
* `Stacks.NodalChart.specMap_algebraMap_chartOriginPt` — hence the origin over the closed point
  lies over the closed point.
* `Stacks.NodalChart.exists_ringEquiv_adicCompletion_stalk_chartOriginPt` — **the completed local
  ring of `Spec A[x, y]/(xy - h)` at the origin over the closed point is `A⟦x, y⟧/(xy - h)`**, for
  `A` a complete Noetherian local ring, compatibly with the maps from `A`.

## Implementation notes

The identification of the local ring of `Spec B` at a prime `𝔭` with `B_𝔭` is Mathlib's
`AlgebraicGeometry.StructureSheaf.stalkIso`, an isomorphism of `B`-algebras whose structure map
on the stalk side is `AlgebraicGeometry.StructureSheaf.toStalk`; the completions are matched by
`StacksDraft.exists_adicCompletion_ringEquiv_of_map_eq`, the maximal ideals of two isomorphic
local rings corresponding.

The compatibility of the whole chain with the maps from `A` rests on
`Stacks.NodalChart.toStalk_comp_stalkHomAt_specMap`, which is the naturality of the germ at the
whole space together with the naturality of `AlgebraicGeometry.Scheme.ΓSpecIso`.

## References

* [Stacks Project, Tag 0CBX](https://stacks.math.columbia.edu/tag/0CBX)
* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Stacks.MixedCompletion

universe u

namespace Stacks.NodalChart

/-- **The map of local rings of `Spec φ` at a prime is `φ`.** Read through the maps from the
global sections to the two local rings, the map of local rings that `Spec φ` induces at a prime
`𝔭` of the target ring is the ring map `φ` itself. -/
public theorem toStalk_comp_stalkHomAt_specMap {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {q : PrimeSpectrum A} {p : PrimeSpectrum B}
    (hp : (Spec.map (CommRingCat.ofHom φ)) p = q) :
    StructureSheaf.toStalk A q ≫
        CommRingCat.ofHom ((Spec.map (CommRingCat.ofHom φ)).stalkHomAt hp) =
      CommRingCat.ofHom φ ≫ StructureSheaf.toStalk B p := by
  have htop : ∀ (C : Type u) [CommRing C] (r : PrimeSpectrum C), StructureSheaf.toStalk C r =
      (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫
        (Spec (CommRingCat.of C)).presheaf.germ ⊤ r trivial := fun C _ r => by
    rw [StructureSheaf.toStalk]
    rfl
  have hnat : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Spec.map (CommRingCat.ofHom φ)).appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have hgerm : (Spec (CommRingCat.of A)).presheaf.germ ⊤ q trivial ≫
      CommRingCat.ofHom ((Spec.map (CommRingCat.ofHom φ)).stalkHomAt hp) =
      (Spec.map (CommRingCat.ofHom φ)).appTop ≫
        (Spec (CommRingCat.of B)).presheaf.germ ⊤ p trivial := by
    subst hp
    have hid : CommRingCat.ofHom ((Spec.map (CommRingCat.ofHom φ)).stalkHomAt
        (rfl : (Spec.map (CommRingCat.ofHom φ)) p = (Spec.map (CommRingCat.ofHom φ)) p)) =
        (Spec.map (CommRingCat.ofHom φ)).stalkMap p := by
      simp only [Scheme.Hom.stalkHomAt, TopCat.Presheaf.stalkCongr_hom,
        TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, CommRingCat.ofHom_hom]
    exact (congrArg (fun z => (Spec (CommRingCat.of A)).presheaf.germ ⊤
        ((Spec.map (CommRingCat.ofHom φ)) p) trivial ≫ z) hid).trans
      (Scheme.Hom.germ_stalkMap (Spec.map (CommRingCat.ofHom φ)) ⊤ p trivial)
  rw [htop A q, htop B p]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ z) hgerm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (Spec (CommRingCat.of B)).presheaf.germ ⊤ p trivial) hnat).trans
          (Category.assoc _ _ _))))

/-- **The local ring of a spectrum at a prime is the localization there**, compatibly with the
maps from the coordinate ring. The ideal of the prime is taken as a separate argument so that
the localization may be named by an ideal the consumer already has in hand. -/
public theorem exists_ringEquiv_stalk_localizationAtPrime (B : Type u) [CommRing B]
    (p : PrimeSpectrum B) (I : Ideal B) [I.IsPrime] (hp : p.asIdeal = I) :
    ∃ Θ : ((Spec (.of B)).presheaf.stalk p) ≃+* Localization.AtPrime I,
      ∀ b : B, Θ ((StructureSheaf.toStalk B p).hom b) =
        algebraMap B (Localization.AtPrime I) b := by
  subst hp
  exact ⟨(IsLocalization.algEquiv p.asIdeal.primeCompl
      ((structurePresheafInCommRingCat B).stalk p) (Localization.AtPrime p.asIdeal)).toRingEquiv,
    fun b => (IsLocalization.algEquiv p.asIdeal.primeCompl
      ((structurePresheafInCommRingCat B).stalk p)
      (Localization.AtPrime p.asIdeal)).commutes b⟩

/-- The origin of the nodal chart over the closed point of a local base, as a point of the
spectrum of the chart. -/
public def chartOriginPt (A : Type u) [CommRing A] [IsLocalRing A] {h : A}
    (hh : h ∈ maximalIdeal A) : ↥(Spec (.of (nodalChartRing A h))) :=
  (⟨chartOrigin (maximalIdeal A) h, (chartOrigin_isMaximal hh).isPrime⟩ :
    PrimeSpectrum (nodalChartRing A h))

/-- **The origin of the chart over a point of the base pulls back to that point** along the
structure map of the chart: a constant lies in the ideal of the origin exactly when it lies in
the ideal of the point. -/
public theorem comap_chartOrigin_algebraMap {R : Type u} [CommRing R] {I : Ideal R} {h : R}
    (hh : h ∈ I) :
    (chartOrigin I h).comap (algebraMap R (nodalChartRing R h)) = I := by
  ext r
  rw [Ideal.mem_comap, algebraMap_nodalChartRing_eq, ← Ideal.mem_comap, comap_chartOrigin hh,
    C_mem_polyMixed_iff]

/-- **The origin of the chart over the closed point lies over the closed point.** -/
public theorem specMap_algebraMap_chartOriginPt (A : Type u) [CommRing A] [IsLocalRing A]
    {h : A} (hh : h ∈ maximalIdeal A) :
    (Spec.map (CommRingCat.ofHom (algebraMap A (nodalChartRing A h)))) (chartOriginPt A hh) =
      closedPoint A :=
  PrimeSpectrum.ext (comap_chartOrigin_algebraMap hh)

/-- **The completed local ring of the spectrum of a nodal chart at the origin over the closed
point.** For `A` Noetherian local and complete for its maximal-adic topology and `h` in the
maximal ideal, the completion of the local ring of `Spec A[x, y]/(xy - h)` at the origin of the
chart over the closed point is `A⟦x, y⟧/(xy - h)`, compatibly with the two maps from `A` — the
one induced by the structure morphism of the chart and the one making the power series quotient
an `A`-algebra. -/
public theorem exists_ringEquiv_adicCompletion_stalk_chartOriginPt
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (h : A) (hh : h ∈ maximalIdeal A) :
    ∃ EP : AdicCompletion (maximalIdeal ((Spec (.of (nodalChartRing A h))).presheaf.stalk
            (chartOriginPt A hh)))
          ((Spec (.of (nodalChartRing A h))).presheaf.stalk (chartOriginPt A hh)) ≃+*
        (MvPowerSeries (Fin 2) A ⧸ Ideal.span
          {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}),
      ∀ a : A, EP (algebraMap _ _
          (((Spec.map (CommRingCat.ofHom (algebraMap A (nodalChartRing A h)))).stalkHomAt
              (specMap_algebraMap_chartOriginPt A hh))
            ((stalkClosedPointIso (CommRingCat.of A)).inv.hom a))) =
        algebraMap A (MvPowerSeries (Fin 2) A ⧸ Ideal.span
          {MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C h}) a := by
  let := chartOrigin_isMaximal (I := maximalIdeal A) hh
  obtain ⟨E₁, hE₁⟩ :=
    exists_ringEquiv_adicCompletion_localization_chartOrigin_of_isAdicComplete A h hh
  obtain ⟨Θ, hΘ⟩ := exists_ringEquiv_stalk_localizationAtPrime (nodalChartRing A h)
    (chartOriginPt A hh) (chartOrigin (maximalIdeal A) h) rfl
  obtain ⟨Θc, hΘc⟩ :=
    Stacks.AdicCompletionFibreUniverse.exists_adicCompletion_ringEquiv_of_map_eq Θ
      (maximalIdeal ((Spec (.of (nodalChartRing A h))).presheaf.stalk (chartOriginPt A hh)))
      (maximalIdeal (Localization.AtPrime (chartOrigin (maximalIdeal A) h)))
      (IsLocalRing.map_ringEquiv_maximalIdeal Θ)
  refine ⟨Θc.trans E₁, fun a => ?_⟩
  have hkey : Θ
      (((Spec.map (CommRingCat.ofHom (algebraMap A (nodalChartRing A h)))).stalkHomAt
          (specMap_algebraMap_chartOriginPt A hh))
        ((stalkClosedPointIso (CommRingCat.of A)).inv.hom a)) =
      algebraMap (nodalChartRing A h) (Localization.AtPrime (chartOrigin (maximalIdeal A) h))
        (algebraMap A (nodalChartRing A h) a) := by
    have h2 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (toStalk_comp_stalkHomAt_specMap (algebraMap A (nodalChartRing A h))
        (specMap_algebraMap_chartOriginPt A hh))) a
    refine Eq.trans (congrArg Θ ?_) (hΘ (algebraMap A (nodalChartRing A h) a))
    rw [stalkClosedPointIso_inv]
    exact h2
  rw [RingEquiv.trans_apply, hΘc, hkey, hE₁]

end Stacks.NodalChart

end
