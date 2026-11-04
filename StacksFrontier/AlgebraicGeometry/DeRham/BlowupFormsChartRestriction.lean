module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.Modules.MonoRestrictLocality
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupChartPresentation

/-!
# The first canonical map on forms, restricted to a standard chart of the coordinate blowup

In the situation of `StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison` —
a ring `R`, `S = Spec(R)`, the coordinate closed immersion `Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X`, the
blowup `b : L ⟶ X` of `X` along `Z` and its exceptional divisor `E ⊆ L` — the first of the two
canonical maps of [Stacks, Tag 0G5G] is

`b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}`,

namely `Stacks.DeRham.blowupFormsPullbackMap`. The proof of the source checks the statement on
the standard affine charts of `L`, which are the spectra of the affine blowup algebras
`A[I/y_i]`. This file performs the first step of that reduction: it identifies the restriction of
the first canonical map to the `i`-th standard chart `j_i : L_i ⟶ L` with the canonical map on
forms of the *affine* morphism `j_i ≫ b : L_i ⟶ X`, for which the chart computation of
`StacksFrontier.RingTheory.Kaehler.BlowupChartFormsPoleBound` is available on global sections.

The identification is the composition law
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_comp` for the two horizontally
composable squares

```
L_i ⟶ L ⟶ X
 ↓     ↓    ↓
 S  =  S  = S
```

together with the fact that the comparison attached to the left-hand square is an isomorphism:
`j_i` is an open immersion, hence étale, so
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale` applies.

## Main definitions

* `Stacks.DeRham.coordinateBlowupChart`, `Stacks.DeRham.coordinateBlowupChartι`: the `i`-th
  standard affine chart `L_i` of the coordinate blowup and its open immersion into `L`.
* `Stacks.DeRham.coordinateBlowupChartToAmbient`, `Stacks.DeRham.coordinateBlowupChartToBase`:
  the two structure morphisms `L_i ⟶ X` and `L_i ⟶ S` of the chart.
* `Stacks.DeRham.chartFormsEtaleComparison`: the comparison `j_i^*Ω^a_{L/S} ⟶ Ω^a_{L_i/S}` of
  the left-hand square, an isomorphism.
* `Stacks.DeRham.chartFormsPullbackMap`: the canonical map
  `(j_i ≫ b)^*Ω^a_{X/S} ⟶ Ω^a_{L_i/S}` of the outer square — the chart-level first canonical
  map.

## Main results

* `Stacks.DeRham.chartFormsPullbackMap_eq` and
  `Stacks.DeRham.pullback_blowupFormsPullbackMap_eq`: **the chart-level first canonical map is
  the restriction of the global one**, read through the coherence isomorphism of the two
  pullbacks and the étale comparison of the chart, and the same identity solved for the
  restriction.
* `Stacks.DeRham.mono_pullback_blowupFormsPullbackMap_iff`: consequently the restriction of the
  first canonical map to the chart is a monomorphism exactly when the chart-level map is.
* `Stacks.DeRham.pullback_blowupFormsPullbackMap_eq_zero_iff`: and it vanishes exactly when the
  chart-level map does.
* `Stacks.DeRham.mono_blowupFormsPullbackMap_of_chart`: **the first canonical map is a
  monomorphism as soon as each chart-level one is** — the reduction to charts of the injectivity
  half of the source's proof, by locality of monomorphy
  (`Stacks.AlgebraicGeometry.Modules.mono_of_mono_pullback_cover`).

## Implementation notes

The chart is indexed by a section of the ideal sheaf of the centre, and the section used here is
`Stacks.MoreMorphisms.coordinateIdealSection`, the `i`-th of the last `n` coordinates. Those are
the sections for which `Stacks.MoreMorphisms.exists_coordinateBlowupChartPresentation` identifies
the chart with affine space; and the `n` charts so obtained already cover `L`, which is
`Stacks.MoreMorphisms.exists_mem_range_coordinateBlowupChart`.

The commutativity hypotheses of the three squares are discharged by `simp`, and the resulting
proof terms are irrelevant: `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap` depends
on its commutativity argument only through a proof of a proposition, so any two spellings give
the same morphism.

No `@[stacks]` attribute is attached: this is one step of the reduction to charts in the proof
of Tag 0G5G, not one of its assertions.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ) (i : Fin n)

/-- The `i`-th standard affine chart `L_i` of the coordinate blowup: the spectrum of the affine
blowup algebra of the ideal of the centre at the `i`-th of the last `n` coordinates. -/
noncomputable abbrev coordinateBlowupChart : Scheme.{u} :=
  Spec (.of (Stacks.MoreMorphisms.coordinateBlowupChartRing R m n i))

/-- The open immersion `j_i : L_i ⟶ L` of the `i`-th standard affine chart into the coordinate
blowup. -/
noncomputable abbrev coordinateBlowupChartι :
    coordinateBlowupChart R m n i ⟶ coordinateBlowup R m n :=
  blowupChartι (Stacks.MoreMorphisms.coordinateIdeal R m n)
    (Stacks.MoreMorphisms.topAffineOpen R m n)
    (Stacks.MoreMorphisms.coordinateIdealSection R m n i)

/-- The structure morphism `L_i ⟶ X` of the `i`-th standard chart over the ambient affine
space: the chart's open immersion followed by the blowing-up morphism. -/
noncomputable abbrev coordinateBlowupChartToAmbient :
    coordinateBlowupChart R m n i ⟶ coordinateAmbient R m n :=
  coordinateBlowupChartι R m n i ≫ coordinateBlowupToAmbient R m n

/-- The structure morphism `L_i ⟶ S` of the `i`-th standard chart over the base. -/
noncomputable abbrev coordinateBlowupChartToBase :
    coordinateBlowupChart R m n i ⟶ coordinateBase R :=
  coordinateBlowupChartι R m n i ≫ coordinateBlowupToBase R m n

/-- The square expressing that the chart's structure morphism over the base factors through the
blowup. -/
theorem coordinateBlowupChartι_comm :
    coordinateBlowupChartι R m n i ≫ coordinateBlowupToBase R m n =
      coordinateBlowupChartToBase R m n i ≫ 𝟙 (coordinateBase R) := by
  simp

/-- The square expressing that the chart's structure morphism over the base factors through the
ambient affine space. -/
theorem coordinateBlowupChartToAmbient_comm :
    coordinateBlowupChartToAmbient R m n i ≫ coordinateAmbientToBase R m n =
      coordinateBlowupChartToBase R m n i ≫ 𝟙 (coordinateBase R) := by
  simp [coordinateBlowupChartToAmbient, coordinateBlowupChartToBase, coordinateBlowupToBase,
    Category.assoc]

/-- The comparison `j_i^*Ω^a_{L/S} ⟶ Ω^a_{L_i/S}` of the square cut out by the chart's open
immersion. -/
noncomputable def chartFormsEtaleComparison (a : ℕ) :
    (Scheme.Modules.pullback (coordinateBlowupChartι R m n i)).obj
        (Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) a) ⟶
      Scheme.Hom.relativeDifferentialForms (coordinateBlowupChartToBase R m n i) a :=
  Scheme.Hom.relativeDifferentialFormsMap (coordinateBlowupChartι R m n i)
    (coordinateBlowupToBase R m n) (coordinateBlowupChartToBase R m n i)
    (𝟙 (coordinateBase R)) (coordinateBlowupChartι_comm R m n i) a

/-- **The comparison of forms along a standard chart of the coordinate blowup is an
isomorphism**: the chart's inclusion is an open immersion, hence étale, and the base morphism of
its square is the identity, so [Stacks, Tag 0FLV] applies. -/
instance isIso_chartFormsEtaleComparison (a : ℕ) :
    IsIso (chartFormsEtaleComparison R m n i a) :=
  Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale _ _ _ _
    (coordinateBlowupChartι_comm R m n i) a

/-- The chart-level first canonical map `(j_i ≫ b)^*Ω^a_{X/S} ⟶ Ω^a_{L_i/S}`: the canonical map
on relative differential forms of the outer square, whose upper edge `j_i ≫ b : L_i ⟶ X` is a
morphism of affine schemes. -/
noncomputable def chartFormsPullbackMap (a : ℕ) :
    (Scheme.Modules.pullback (coordinateBlowupChartToAmbient R m n i)).obj
        (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) a) ⟶
      Scheme.Hom.relativeDifferentialForms (coordinateBlowupChartToBase R m n i) a :=
  Scheme.Hom.relativeDifferentialFormsMap (coordinateBlowupChartToAmbient R m n i)
    (coordinateAmbientToBase R m n) (coordinateBlowupChartToBase R m n i)
    (𝟙 (coordinateBase R)) (coordinateBlowupChartToAmbient_comm R m n i) a

/-- **The chart-level first canonical map is the restriction of the global one.** The canonical
map on `a`-forms of the outer square `L_i ⟶ X` over `S` is the coherence isomorphism
`(j_i ≫ b)^* ≅ j_i^* ∘ b^*`, followed by the restriction along `j_i` of the first canonical map
`b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}` of [Stacks, Tag 0G5G], followed by the étale comparison of the
chart. -/
theorem chartFormsPullbackMap_eq (a : ℕ) :
    chartFormsPullbackMap R m n i a =
      (Scheme.Modules.pullbackComp (coordinateBlowupChartι R m n i)
            (coordinateBlowupToAmbient R m n)).inv.app
          (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) a) ≫
        (Scheme.Modules.pullback (coordinateBlowupChartι R m n i)).map
            (blowupFormsPullbackMap R m n a) ≫
          chartFormsEtaleComparison R m n i a :=
  Scheme.Hom.relativeDifferentialFormsMap_comp (coordinateBlowupToAmbient R m n)
    (coordinateBlowupChartι R m n i) (coordinateAmbientToBase R m n)
    (coordinateBlowupToBase R m n) (coordinateBlowupChartToBase R m n i)
    (𝟙 (coordinateBase R)) (𝟙 (coordinateBase R)) (𝟙 (coordinateBase R)) (by simp)
    (coordinateBlowupChartι_comm R m n i) (coordinateBlowupChartToAmbient_comm R m n i) a

/-- **`Stacks.DeRham.chartFormsPullbackMap_eq`, solved for the restriction of the global map.**
The restriction along the chart of the first canonical map of [Stacks, Tag 0G5G] is the
chart-level first canonical map, conjugated by the coherence isomorphism of the two pullbacks and
by the étale comparison of the chart. -/
theorem pullback_blowupFormsPullbackMap_eq (a : ℕ) :
    (Scheme.Modules.pullback (coordinateBlowupChartι R m n i)).map
        (blowupFormsPullbackMap R m n a) =
      (Scheme.Modules.pullbackComp (coordinateBlowupChartι R m n i)
            (coordinateBlowupToAmbient R m n)).hom.app
          (Scheme.Hom.relativeDifferentialForms (coordinateAmbientToBase R m n) a) ≫
        chartFormsPullbackMap R m n i a ≫ inv (chartFormsEtaleComparison R m n i a) := by
  rw [chartFormsPullbackMap_eq]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- **The restriction of the first canonical map to a standard chart is a monomorphism exactly
when the chart-level first canonical map is.** The two differ by the coherence isomorphism of the
two pullbacks and by the étale comparison of the chart, both isomorphisms. -/
theorem mono_pullback_blowupFormsPullbackMap_iff (a : ℕ) :
    Mono ((Scheme.Modules.pullback (coordinateBlowupChartι R m n i)).map
        (blowupFormsPullbackMap R m n a)) ↔ Mono (chartFormsPullbackMap R m n i a) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [chartFormsPullbackMap_eq]; infer_instance
  · rw [pullback_blowupFormsPullbackMap_eq]; infer_instance

/-- **The restriction of the first canonical map to a standard chart vanishes exactly when the
chart-level first canonical map does.** -/
theorem pullback_blowupFormsPullbackMap_eq_zero_iff (a : ℕ) :
    (Scheme.Modules.pullback (coordinateBlowupChartι R m n i)).map
        (blowupFormsPullbackMap R m n a) = 0 ↔ chartFormsPullbackMap R m n i a = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [chartFormsPullbackMap_eq, h]; simp
  · rw [pullback_blowupFormsPullbackMap_eq, h]; simp

/-- **The first canonical map of [Stacks, Tag 0G5G] is a monomorphism as soon as each of its
chart-level versions is.** The `n` standard charts cover `L`, monomorphy of a morphism of
`𝒪_L`-modules is local on `L`
(`Stacks.AlgebraicGeometry.Modules.mono_of_mono_pullback_cover`), and the restriction of the
first canonical map to the `i`-th chart is the `i`-th chart-level map up to isomorphism.

This is the reduction of the injectivity half of the source's proof to its chart computation:
what remains is monomorphy of `Stacks.DeRham.chartFormsPullbackMap`, the canonical map on forms
of the morphism of *affine* schemes `L_i ⟶ X`, which on global sections is the `a`-th exterior
power of `KaehlerDifferential.mapBaseChange` along the chart morphism — injective by
`Stacks.Kaehler.injective_exteriorPower_map_blowupChartMapBaseChange`. -/
theorem mono_blowupFormsPullbackMap_of_chart (a : ℕ)
    (h : ∀ i : Fin n, Mono (chartFormsPullbackMap R m n i a)) :
    Mono (blowupFormsPullbackMap R m n a) :=
  Stacks.AlgebraicGeometry.Modules.mono_of_mono_pullback_cover _
    (fun i => coordinateBlowupChartι R m n i)
    (Stacks.MoreMorphisms.exists_mem_range_coordinateBlowupChart R m n)
    fun i => (mono_pullback_blowupFormsPullbackMap_iff R m n i a).2 (h i)

end Stacks.DeRham

end
