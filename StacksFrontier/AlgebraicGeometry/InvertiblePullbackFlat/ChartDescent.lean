module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.Submersive
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.StarCover
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.InjectivityOfUnit

/-!
# Descending an invertible module from transition units chosen on the target

Let `f : X ⟶ Y` be a morphism of schemes and `ℒ` a sheaf of `𝒪_X`-modules. Suppose given a
cover of `Y` by opens `chart y ∋ y`, a generator of `ℒ` over each `f ⁻¹ᵁ chart y`, and, for
every open `A` inside two charts, *some* unit of `Γ(Y, A)` pulling back to the ratio of the two
chart generators. Then `ℒ` is the pullback of an invertible `𝒪_Y`-module.

This is the last paragraph of [Stacks, Tag 0BD7] read as an assembly step, and it is the shape
in which that tag's proof produces its data: the generators there are `φ^*(g_y) s` for one
meromorphic section `s` and meromorphic functions `g_y` on `Y`, so the ratio of two of them is
`φ^*(g_i/g_j)` — visibly a pullback from the base, with no cocycle condition established.

## Why this is not already available

`Stacks.PicFinite.LiftedChartData f ℒ` is exactly the input of the comparison with `ℒ`, and its
docstring says that transition units from any source will do. Both existing suppliers, however,
impose a combinatorial hypothesis on the cover that Tag 0BD7 cannot satisfy:
`Stacks.PicFinite.ChartData.toLiftedChartData` needs `f` to be an isomorphism over an open
containing every overlap of two distinct charts (Tag 0C0T), and
`Stacks.LiftInvertible.StarLiftData` extends `Stacks.PicFinite.ChartData`, hence also asks that
two distinct charts meet only inside a centre. What is supplied here instead is the
**cocycle laws for free**: the chosen units are *not* assumed to satisfy them, and they are
derived from the corresponding laws upstairs by injectivity of `f^#` on sections, which for a
flat morphism with nonempty fibres is
  `Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.injective_app_of_flat_of_surjective`.

## Main definitions

* `Stacks.InvertiblePullback.chartGen`: a chart generator restricted to the preimage of a
  smaller open.
* `Stacks.InvertiblePullback.chartRatio`: the transition unit of two chart generators upstairs.
* `Stacks.InvertiblePullback.liftedChartDataOfTargetUnits`: the lifted chart data built from
  chosen units on the target.

## Main results

* `Stacks.InvertiblePullback.injective_appUnits`: `f^#` injective on sections is `f^#` injective
  on units.
* `Stacks.InvertiblePullback.chartRatio_restrict`, `chartRatio_symm`, `chartRatio_comp`: the
  transition units upstairs restrict, invert and compose.
* `Stacks.InvertiblePullback.targetUnits_of_inf`: the datum need only be given over the
  intersection of two charts; it restricts to every smaller open.
* `Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_targetUnits`: the conclusion of
  Tag 0BD7 from the datum.
* `Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_flat` and
  `exists_isInvertible_pullback_iso_of_flat_of_inf`: the same with the injectivity hypothesis
  discharged from flatness and nonemptiness of the fibres, which are hypotheses (3) of Tag 0BD7.

## Implementation notes

The tag is **withheld**: these statements carry a hypothesis Tag 0BD7 does not, namely the chart
and unit datum, which is what the first four paragraphs of that proof construct. What remains of
the tag after this file is exactly the production of `chart`, the generators, and the units —
the source's "`φ^*(g)s` is a generator for `ℒ` on an open neighbourhood of `φ^{-1}(y)`" together
with "`g` and `g'` differ by an element of `𝒪_{Y, y}^*`".

The ratio convention is the one the structure fixes: `chartRatio gen i j A` is the unit carrying
the `j`-th generator to the `i`-th, so `chartRatio_comp` composes in the order `i → j → k` while
the cocycle field of `Stacks.SheafOfModules.UnitTransitionCocycle` asks for the opposite order.
The two are reconciled by commutativity, which is available on `Γ(Y, A)` — a `CommRingCat`
object — but *not* upstairs, where the sections of `Stacks.SheafOfModules.structureSheaf` are a
`RingCat` object and `mul_comm` does not typecheck. So the commutation is done on the target
side, after transporting along the chosen units.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules

universe u

namespace Stacks.InvertiblePullback

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-! ### Injectivity of `f^#` on units -/

/-- If `f^#` is injective on the sections over every open, it is injective on their units. -/
theorem injective_appUnits
    (hinj : ∀ A : Y.Opens, Function.Injective (Stacks.PicFinite.pull f A)) (A : Y.Opens) :
    Function.Injective (Stacks.LiftInvertible.appUnits f A) := fun _a _b hab =>
  Units.ext (hinj A (congrArg Units.val hab))

/-- `f^#` on units commutes with restriction. -/
theorem appUnits_restrict {A A' : Y.Opens} (h : A' ≤ A) (v : (Γ(Y, A))ˣ) :
    Stacks.LiftInvertible.appUnits f A'
        (Units.map (Y.presheaf.map (homOfLE h).op).hom v) =
      Units.map ((_root_.structureSheaf X.toRingedSpace.sheaf).obj.map
          ((Opens.map f.base).map (homOfLE h)).op).hom
        (Stacks.LiftInvertible.appUnits f A v) :=
  Units.ext (Stacks.PicFinite.pull_restrict f h v.val).symm

/-! ### The chart generators and their ratios -/

variable {L : X.Modules} {chart : Y → Y.Opens}
  (gen : ∀ y, GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ chart y))

/-- A chart generator, restricted to the preimage of a smaller open. -/
def chartGen (i : Y) {W : Y.Opens} (hW : W ≤ chart i) :
    GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W) :=
  generatorRestrict (X := X.toRingedSpace) L
    ((Opens.map f.base).map (homOfLE hW)).le (gen i)

/-- Restricting a restricted chart generator again restricts the chart generator. -/
theorem chartGen_restrict (i : Y) {W W' : Y.Opens} (hW : W ≤ chart i) (h : W' ≤ W) :
    generatorRestrict (X := X.toRingedSpace) L
        ((Opens.map f.base).map (homOfLE h)).le (chartGen gen i hW) =
      chartGen gen i (h.trans hW) :=
  generatorRestrict_trans (X := X.toRingedSpace) L
    ((Opens.map f.base).map (homOfLE hW)).le
    ((Opens.map f.base).map (homOfLE h)).le (gen i)

/-- **The transition unit of two chart generators**, over an open inside both charts: the unit
carrying the `j`-th chart generator to the `i`-th. -/
def chartRatio (i j : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j) :
    ((_root_.structureSheaf X.toRingedSpace.sheaf).obj.obj (op (f ⁻¹ᵁ A)))ˣ :=
  generatorRatioUnit (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
    (chartGen gen j hj) (chartGen gen i hi)

/-- The underlying section of `chartRatio` is the `generatorRatio` of the two chart generators. -/
theorem chartRatio_val (i j : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j) :
    (chartRatio gen i j A hi hj).val =
      generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
        (chartGen gen j hj) (chartGen gen i hi) :=
  generatorRatioUnit_val (X := X.toRingedSpace) L (f ⁻¹ᵁ A) _ _

/-- The transition scalar of two chart generators commutes with restriction. -/
theorem chartRatio_restrict_val (i j : Y) {A A' : Y.Opens} (hi : A ≤ chart i)
    (hj : A ≤ chart j) (h : A' ≤ A) :
    (_root_.structureSheaf X.toRingedSpace.sheaf).obj.map
          ((Opens.map f.base).map (homOfLE h)).op
        (generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
          (chartGen gen j hj) (chartGen gen i hi)) =
      generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ A')
        (chartGen gen j (h.trans hj)) (chartGen gen i (h.trans hi)) := by
  rw [← chartGen_restrict gen i hi h, ← chartGen_restrict gen j hj h,
    generatorRatio_restrict (X := X.toRingedSpace) L
      ((Opens.map f.base).map (homOfLE h)).le]
  rfl

/-- The transition unit of two chart generators commutes with restriction. -/
theorem chartRatio_restrict (i j : Y) {A A' : Y.Opens} (hi : A ≤ chart i) (hj : A ≤ chart j)
    (h : A' ≤ A) :
    Units.map ((_root_.structureSheaf X.toRingedSpace.sheaf).obj.map
          ((Opens.map f.base).map (homOfLE h)).op).hom (chartRatio gen i j A hi hj) =
      chartRatio gen i j A' (h.trans hi) (h.trans hj) :=
  Units.ext <| by
    rw [Units.coe_map, chartRatio_val, chartRatio_val]
    exact chartRatio_restrict_val gen i j hi hj h

/-- Reversing a transition inverts its unit. -/
theorem chartRatio_symm (i j : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j) :
    chartRatio gen j i A hj hi = (chartRatio gen i j A hi hj)⁻¹ :=
  generatorRatioUnit_symm (X := X.toRingedSpace) L (f ⁻¹ᵁ A) _ _

/-- The transition units of three charts compose, in the order `i → j → k`. -/
theorem chartRatio_comp (i j k : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j)
    (hk : A ≤ chart k) :
    chartRatio gen i j A hi hj * chartRatio gen j k A hj hk = chartRatio gen i k A hi hk :=
  generatorRatioUnit_comp (X := X.toRingedSpace) L (f ⁻¹ᵁ A) _ _ _

/-! ### The datum, and the lifted chart data it produces -/

/-- The datum restated on units: a unit of `Γ(Y, A)` pulling back to the transition scalar is a
unit of `Γ(Y, A)` pulling back to the transition unit. -/
theorem appUnits_eq_of_pull_eq
    (hu : ∀ (i j : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j),
      ∃ w : (Γ(Y, A))ˣ, Stacks.PicFinite.pull f A w.val =
        generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
          (chartGen gen j hj) (chartGen gen i hi))
    (i j : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j) :
    ∃ w : (Γ(Y, A))ˣ,
      Stacks.LiftInvertible.appUnits f A w = chartRatio gen i j A hi hj := by
  obtain ⟨w, hw⟩ := hu i j A hi hj
  exact ⟨w, Units.ext (hw.trans (chartRatio_val gen i j A hi hj).symm)⟩

/-- **The datum need only be given over the intersection of two charts.** A unit on
`chart i ⊓ chart j` pulling back to the transition scalar there restricts to one on every open
inside both charts. -/
theorem targetUnits_of_inf
    (hu : ∀ i j : Y, ∃ w : (Γ(Y, chart i ⊓ chart j))ˣ,
      Stacks.PicFinite.pull f (chart i ⊓ chart j) w.val =
        generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ (chart i ⊓ chart j))
          (chartGen gen j inf_le_right) (chartGen gen i inf_le_left))
    (i j : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j) :
    ∃ w : (Γ(Y, A))ˣ, Stacks.PicFinite.pull f A w.val =
      generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
        (chartGen gen j hj) (chartGen gen i hi) := by
  obtain ⟨w, hw⟩ := hu i j
  refine ⟨Units.map (Y.presheaf.map (homOfLE (le_inf hi hj)).op).hom w, ?_⟩
  refine Eq.trans ?_ (chartRatio_restrict_val gen i j inf_le_left inf_le_right (le_inf hi hj))
  exact (Stacks.PicFinite.pull_restrict f (le_inf hi hj) w.val).symm.trans (congrArg _ hw)

/-- **Lifted chart data from units chosen on the target.** The cocycle laws are *not* assumed of
the chosen units: they are forced, because `f^#` is injective on sections and the corresponding
laws hold for the transition units upstairs. -/
def liftedChartDataOfTargetUnits
    (hinj : ∀ A : Y.Opens, Function.Injective (Stacks.PicFinite.pull f A))
    (hmem : ∀ y, y ∈ chart y)
    (hu : ∀ (i j : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j),
      ∃ w : (Γ(Y, A))ˣ, Stacks.PicFinite.pull f A w.val =
        generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
          (chartGen gen j hj) (chartGen gen i hi)) :
    Stacks.PicFinite.LiftedChartData f L := by
  classical
  choose w hw using appUnits_eq_of_pull_eq gen hu
  refine
    { chart := chart
      mem_chart := hmem
      generator := gen
      cocycle :=
        { transition := w
          restrict := ?_
          symm := ?_
          cocycle := ?_ }
      pull_transition := ?_ }
  · intro i j A A' hi hj h
    refine injective_appUnits hinj A' ?_
    rw [appUnits_restrict h, hw, hw, chartRatio_restrict]
  · intro i j A hi hj
    refine injective_appUnits hinj A ?_
    rw [map_inv, hw, hw, chartRatio_symm]
  · intro i j k A hi hj hk
    refine injective_appUnits hinj A ?_
    rw [mul_comm, map_mul, hw, hw, hw, chartRatio_comp]
  · intro i j A hi hj
    have hval := congrArg Units.val (hw i j A hi hj)
    rw [chartRatio_val] at hval
    exact hval

/-! ### The conclusion of Tag 0BD7 from the datum -/

/-- **The conclusion of Stacks Tag 0BD7, from a chart cover with transition units chosen on the
target.** The tag is withheld: Tag 0BD7 has no hypothesis on the cover, and producing this datum
from its hypotheses is the content of the first four paragraphs of its proof. -/
theorem exists_isInvertible_pullback_iso_of_targetUnits
    (hinj : ∀ A : Y.Opens, Function.Injective (Stacks.PicFinite.pull f A))
    (hmem : ∀ y, y ∈ chart y)
    (hu : ∀ (i j : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j),
      ∃ w : (Γ(Y, A))ˣ, Stacks.PicFinite.pull f A w.val =
        generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
          (chartGen gen j hj) (chartGen gen i hi)) :
    ∃ N : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat)).mp Y.IsSheaf) N ∧
        Nonempty ((Scheme.Modules.pullback f).obj N ≅ L) :=
  let D := liftedChartDataOfTargetUnits gen hinj hmem hu
  ⟨D.descend,
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry Y.presheaf _ _).mp
      D.isInvertible_descend,
    ⟨D.pullbackIso⟩⟩

/-- **The same with the injectivity hypothesis discharged**, from flatness of `f` and
nonemptiness of its fibres — hypothesis (3) of Stacks Tag 0BD7. -/
theorem exists_isInvertible_pullback_iso_of_flat [Flat f]
    (hfiber : ∀ y : Y, Nonempty (f.fiber y)) (hmem : ∀ y, y ∈ chart y)
    (hu : ∀ (i j : Y) (A : Y.Opens) (hi : A ≤ chart i) (hj : A ≤ chart j),
      ∃ w : (Γ(Y, A))ˣ, Stacks.PicFinite.pull f A w.val =
        generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ A)
          (chartGen gen j hj) (chartGen gen i hi)) :
    ∃ N : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat)).mp Y.IsSheaf) N ∧
        Nonempty ((Scheme.Modules.pullback f).obj N ≅ L) :=
  have : Surjective f := Surjective.of_nonempty_fiber f hfiber
  exists_isInvertible_pullback_iso_of_targetUnits gen
    (fun A => Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.injective_app_of_flat_of_surjective f A)
      hmem hu

/-- **The form in which Stacks Tag 0BD7 supplies its datum**: the unit is produced once, over
the intersection of two charts. -/
theorem exists_isInvertible_pullback_iso_of_flat_of_inf [Flat f]
    (hfiber : ∀ y : Y, Nonempty (f.fiber y)) (hmem : ∀ y, y ∈ chart y)
    (hu : ∀ i j : Y, ∃ w : (Γ(Y, chart i ⊓ chart j))ˣ,
      Stacks.PicFinite.pull f (chart i ⊓ chart j) w.val =
        generatorRatio (X := X.toRingedSpace) L (f ⁻¹ᵁ (chart i ⊓ chart j))
          (chartGen gen j inf_le_right) (chartGen gen i inf_le_left)) :
    ∃ N : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat)).mp Y.IsSheaf) N ∧
        Nonempty ((Scheme.Modules.pullback f).obj N ≅ L) :=
  exists_isInvertible_pullback_iso_of_flat gen hfiber hmem (targetUnits_of_inf gen hu)

end Stacks.InvertiblePullback

end
