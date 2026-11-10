module

public import StacksFrontier.RingTheory.GeometricallyIntegral.FibrewiseDensity
public import StacksFrontier.RingTheory.GeometricallyIntegral.OpenLocus

/-!
# A scheme-theoretically dense family of reduced standard opens makes the fibres reduced

`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedLocus` and
`StacksFrontier.RingTheory.GeometricallyIntegral.GoodReduced` reduce the affine case of Stacks 0579
to
one statement, the *good half* of the generic-fibre dichotomy: over a Noetherian domain `D` with a
finite type algebra `T` whose generic fibre is geometrically reduced, some nonempty basic open of
`Spec D` lies inside `Algebra.geometricallyReducedFibreLocus D T`. That is the affine case of
Stacks 0578, and its proof in the source runs through the smooth locus: the generic fibre has a
dense open which is smooth over the fraction field, that open is scheme-theoretically dense because
the generic fibre is reduced, Stacks 0573 spreads the scheme-theoretic density to all nearby
fibres, and Stacks 056E concludes that those fibres are geometrically reduced because the dense
open has geometrically reduced fibres.

**This file proves the last two of those four steps**, in the affine, ring-theoretic form, taking
the dense family as a hypothesis. Given a finite family `g₁, …, gₙ` in `T` such that

* the union `⋃ⱼ D(1 ⊗ gⱼ)` is scheme-theoretically dense in the generic fibre — equivalently, by
  Stacks 056C and Stacks 0565, the multiplication map of the family `1 ⊗ gⱼ` is injective over
  `K ⊗[D] T` — and
* every `T_{gⱼ}` has geometrically reduced fibres over `D`,

there is a nonzero `f : D` with `D(f) ⊆ Algebra.geometricallyReducedFibreLocus D T`. So the good
half of the dichotomy is reduced to producing such a family, which is what generic flatness, the
density of the smooth locus of a geometrically reduced fibre (Stacks 056V) and the base-change
description of the smooth locus (Stacks 02V4) supply.

The second step, Stacks 056E for reducedness, is short over a fixed field and needs no flatness:
an element of `T ⊗[D] L` which is nilpotent is nilpotent in each localization
`(T ⊗[D] L)_{1 ⊗ gⱼ}`, hence zero there, hence annihilated by a power of `1 ⊗ gⱼ`; and injectivity
of the multiplication map says exactly that an element annihilated by a power of each member of the
family is zero (Stacks 0565). Nothing is tensored, so no flatness enters.

## Main results

* `Algebra.isReduced_of_injective_bigPhi`: **Stacks 056E for reducedness, affine case.** A ring
  with a finite family whose multiplication map is injective and whose localizations are all
  reduced is reduced.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily`: from a
  family which is scheme-theoretically dense in the generic fibre and has reduced localizations
  after every field-valued base change, a nonempty basic open inside the geometrically reduced
  fibre locus.
* `Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily'`: the
  same with the hypothesis on the localizations stated as geometric reducedness of the fibres of
  `D → T_{gⱼ}`, which is the form in which smoothness of `T_{gⱼ}` over `D` delivers it.

## Implementation notes

The hypothesis on the members of the family is stated once as reducedness of
`Localization.Away ((1 : L) ⊗ₜ gⱼ)`, a localization of the fibre, and once as reducedness of
`L ⊗[D] Localization.Away (gⱼ)`, a fibre of a localization. The two agree by
`IsLocalization.Away.tensorProductEquivTMulRight`, localization commuting with base change; the
second form is the one a consumer has, since it is a statement about the `D`-algebra `T_{gⱼ}`.

The generic point is given by a field `K` over `D` with `D → K` injective rather than by the
fraction field, and the conclusion quantifies over all fields `L` over `D` in which `f` stays
nonzero, which is how `Algebra.geometricallyReducedFibreLocus` reads membership of a basic open.
No Noetherian hypothesis is used: the Noetherian hypothesis of Stacks 0579 enters only through the
constructibility criterion of Stacks 053Z, not here.

## References

* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 0573](https://stacks.math.columbia.edu/tag/0573)
* [Stacks Project, Tag 056E](https://stacks.math.columbia.edu/tag/056E)
* [Stacks Project, Tag 0565](https://stacks.math.columbia.edu/tag/0565)
* [Stacks Project, Tag 056C](https://stacks.math.columbia.edu/tag/056C)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Algebra

/-- **The affine case of Stacks 056E for reducedness.** A commutative ring `R` is reduced as soon
as it carries a finite family `g` whose multiplication map `r ↦ (gⱼ r)ⱼ` is injective and all of
whose localizations `R_{gⱼ}` are reduced.

Geometrically: if the standard opens `D(gⱼ)` are reduced and their union is scheme-theoretically
dense in `Spec R`, then `Spec R` is reduced. A nilpotent element of `R` is nilpotent, hence zero,
in each `R_{gⱼ}`, so some power of each `gⱼ` annihilates it; by Stacks 0565 injectivity of the
multiplication map says precisely that such an element vanishes. -/
theorem isReduced_of_injective_bigPhi {R : Type u} [CommRing R] {n : ℕ} (g : Fin n → R)
    (hinj : Function.Injective (bigPhi (M := R) n g))
    (hred : ∀ j, IsReduced (Localization.Away (g j))) : IsReduced R := by
  rw [← bigLambda_injective_iff_bigPhi_injective, bigLambda_injective_iff_powerTorsion] at hinj
  refine ⟨fun x hx => hinj x fun j => ?_⟩
  have hzero : algebraMap R (Localization.Away (g j)) x = 0 :=
    (hred j).eq_zero _ (hx.map (algebraMap R (Localization.Away (g j))))
  obtain ⟨⟨m, k, hmk⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (g j))
    (Localization.Away (g j)) x).mp hzero
  exact ⟨k, by simpa [smul_eq_mul, ← hmk] using hm⟩

/-- **The good half of the generic-fibre dichotomy for reducedness, from a dense family.** Let `D`
be a domain, `T` a finite type `D`-algebra, `K` a field over `D` with `D → K` injective — the
generic point of `Spec D` — and `g` a finite family in `T`. Assume

* the multiplication map of the family `1 ⊗ gⱼ` is injective over `K ⊗[D] T`, i.e. by Stacks 056C
  and Stacks 0565 that `⋃ⱼ D(1 ⊗ gⱼ)` is scheme-theoretically dense in the generic fibre, and
* for every field `L` over `D` each localization `(L ⊗[D] T)_{1 ⊗ gⱼ}` is reduced.

Then some nonempty basic open of `Spec D` is contained in
`Algebra.geometricallyReducedFibreLocus D T`.

Stacks 0573, in the form `Algebra.exists_ne_zero_injective_bigPhi_tmul_of_algebraMap_ne_zero`,
spreads the injectivity from `K` to every field in which the element it produces stays nonzero, and
`Algebra.isReduced_of_injective_bigPhi` — Stacks 056E — turns that into reducedness of the
fibre. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily
    {D T : Type u} [CommRing D] [IsDomain D] [CommRing T] [Algebra D T] [Algebra.FiniteType D T]
    {n : ℕ} (g : Fin n → T) (K : Type u) [Field K] [Algebra D K]
    (hDK : Function.Injective (algebraMap D K))
    (hdense : Function.Injective (bigPhi (M := K ⊗[D] T) n fun j => (1 : K) ⊗ₜ[D] g j))
    (hred : ∀ (L : Type u) [Field L] [Algebra D L] (j : Fin n),
      IsReduced (Localization.Away ((1 : L) ⊗ₜ[D] g j))) :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyReducedFibreLocus D T := by
  obtain ⟨f, hne, hmain⟩ :=
    exists_ne_zero_injective_bigPhi_tmul_of_algebraMap_ne_zero g K hDK hdense
  refine ⟨f, hne, fun p hp L _ _ hker => ?_⟩
  have hf : algebraMap D L f ≠ 0 := fun h0 =>
    (PrimeSpectrum.mem_basicOpen f p).mp hp (hker ▸ RingHom.mem_ker.mpr h0)
  have : IsReduced (L ⊗[D] T) := isReduced_of_injective_bigPhi _ (hmain L hf) (hred L)
  exact isReduced_of_injective (Algebra.TensorProduct.comm D T L).toRingEquiv
    (Algebra.TensorProduct.comm D T L).injective

/-- **The good half of the generic-fibre dichotomy for reducedness, from a dense family with
geometrically reduced members.** The form of
`Algebra.exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily` in which
the hypothesis on the members of the family is that every fibre of `D → T_{gⱼ}` be geometrically
reduced, rather than that every localization of a fibre of `D → T` be reduced.

The two hypotheses agree because localization commutes with base change,
`IsLocalization.Away.tensorProductEquivTMulRight` giving
`L ⊗[D] T_{gⱼ} ≃ (L ⊗[D] T)_{1 ⊗ gⱼ}`. This is the form delivered by smoothness of `T_{gⱼ}` over
`D`, which is how the proof of Stacks 0578 produces it: the family is chosen inside the smooth
locus. -/
theorem exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily'
    {D T : Type u} [CommRing D] [IsDomain D] [CommRing T] [Algebra D T] [Algebra.FiniteType D T]
    {n : ℕ} (g : Fin n → T) (K : Type u) [Field K] [Algebra D K]
    (hDK : Function.Injective (algebraMap D K))
    (hdense : Function.Injective (bigPhi (M := K ⊗[D] T) n fun j => (1 : K) ⊗ₜ[D] g j))
    (hred : ∀ (L : Type u) [Field L] [Algebra D L] (j : Fin n),
      IsReduced (L ⊗[D] Localization.Away (g j))) :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyReducedFibreLocus D T := by
  refine exists_ne_zero_basicOpen_subset_geometricallyReducedFibreLocus_of_denseFamily g K hDK
    hdense fun L _ _ j => ?_
  have := hred L j
  exact isReduced_of_injective
    (IsLocalization.Away.tensorProductEquivTMulRight D L (g j)
      (Localization.Away (g j))).symm.toRingEquiv
    (IsLocalization.Away.tensorProductEquivTMulRight D L (g j)
      (Localization.Away (g j))).symm.injective

end Algebra

end
