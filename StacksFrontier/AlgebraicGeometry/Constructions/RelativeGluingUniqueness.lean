module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import StacksCore.Tactic.StacksAttribute

/-!
# Uniqueness of the scheme glued from a relative gluing datum

Fix a locally directed open cover `𝒰` of a scheme `S` and a relative gluing datum `d` over it, so
that `d` consists of schemes `Xᵢ` over the members `Uᵢ` of `𝒰` with cartesian transition squares.
A *gluing* of `d` is a scheme `X` over `S` together with morphisms `Xᵢ ⟶ X` commuting with the
transition maps and exhibiting each `Xᵢ` as the part of `X` over `Uᵢ`, i.e. making every square
```
Xᵢ  ⟶  X
 |      |
 v      v
Uᵢ  ⟶  S
```
cartesian. This is the conclusion of Tag 01LH, whose existence half is the canonical colimit
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued` with its structure map
`RelativeGluingData.toBase`. This file proves the other half: **a gluing of `d` is unique up to a
unique isomorphism over `S` compatible with the morphisms from the `Xᵢ`** — uniqueness of the
total space together with its charts, across different total spaces, and not merely of a second
chart structure on one fixed total space. No quasi-coherent module appears here; Tag 01LI's
uniqueness of the pair `(X, F)` also needs the module half, and the combination of the two is
`Stacks.AlgebraicGeometry.RelativeSheafGluing.RelativeSheafGluingData.existsUnique_pairIso`.

## Main definitions

* `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.Gluing`: a scheme over `S` glued from the
  datum, i.e. a witness of the conclusion of Tag 01LH.
* `RelativeGluingData.gluingGlued`: the canonical gluing, on the colimit of the `Xᵢ`.

## Main results

* `RelativeGluingData.existsUnique_iso`: **two gluings of one relative gluing datum are related
  by exactly one isomorphism over `S` carrying the one family of morphisms from the `Xᵢ` to the
  other.**

## Implementation notes

The morphisms `Xᵢ ⟶ X` of a gluing are open immersions, being base changes of the members of
`𝒰` along the structure map, and they cover `X`, because `𝒰` covers `S` and the cartesian squares
produce a preimage of every point. So they form an open cover of `X`, and that cover is locally
directed: the argument is the one Mathlib uses for the canonical gluing, reading a point of an
overlap `Xᵢ ×_X Xⱼ` through the base and pulling the resulting member of `𝒰` back along a
cartesian square. Both the isomorphism and its uniqueness are then formal: a morphism out of `X`
is determined by its restrictions to the cover, and a compatible family of morphisms out of the
`Xᵢ` glues, by `AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOfLocallyDirected`.

The hypotheses `[Small.{u} 𝒰.I₀]` and `[Quiver.IsThin 𝒰.I₀]` are needed only to form the
canonical gluing, and so are not assumed for the uniqueness statement itself.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 01LI](https://stacks.math.columbia.edu/tag/01LI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Cover.RelativeGluingData

variable {S : Scheme.{u}} {𝒰 : S.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
  {d : RelativeGluingData 𝒰}

/-- A **gluing** of a relative gluing datum `d` over a locally directed open cover `𝒰` of `S`: a
scheme over `S` whose part over the `i`-th member of `𝒰` is the `i`-th scheme of `d`, compatibly
with the transition maps. This is the conclusion of [Stacks, Tag 01LH]. -/
structure Gluing (d : RelativeGluingData 𝒰) where
  /-- The total space. -/
  pt : Scheme.{u}
  /-- The structure morphism to the base. -/
  toBase : pt ⟶ S
  /-- The morphism from the `i`-th scheme of the datum to the total space. -/
  chart : ∀ i, d.functor.obj i ⟶ pt
  /-- The morphisms from the datum commute with its transition maps. -/
  chart_trans : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), d.functor.map hij ≫ chart j = chart i
  /-- The `i`-th scheme of the datum is the part of the total space over the `i`-th member of the
  cover. -/
  isPullback_chart : ∀ i, IsPullback (d.natTrans.app i) (chart i) (𝒰.f i) toBase

namespace Gluing

variable (G : Gluing d)

/-- Each chart of a gluing is an open immersion. -/
instance (i : 𝒰.I₀) : IsOpenImmersion (G.chart i) :=
  MorphismProperty.of_isPullback (G.isPullback_chart i) (𝒰.map_prop i)

/-- The charts of a gluing cover its total space: a point of the total space lies over a member
of `𝒰`, and the cartesian square over that member produces a preimage. -/
lemma exists_chart_eq (x : G.pt) : ∃ (i : 𝒰.I₀) (y : d.functor.obj i), G.chart i y = x := by
  obtain ⟨i, u, hu⟩ := 𝒰.isOpenCover_opensRange.exists_mem (G.toBase.base x)
  obtain ⟨y, -, hy⟩ := exists_preimage_of_isPullback (G.isPullback_chart i) u x hu
  exact ⟨i, y, hy⟩

/-- Two charts of a gluing meet over the base: the two projections of their intersection agree
after passing to the base. -/
lemma fst_natTrans_f_eq (i j : 𝒰.I₀) :
    pullback.fst (G.chart i) (G.chart j) ≫ d.natTrans.app i ≫ 𝒰.f i =
      pullback.snd (G.chart i) (G.chart j) ≫ d.natTrans.app j ≫ 𝒰.f j := by
  rw [(G.isPullback_chart i).w, (G.isPullback_chart j).w, ← Category.assoc, ← Category.assoc,
    pullback.condition]

/-- **The charts of a gluing are locally directed.**  A point of the intersection of the `i`-th
and the `j`-th chart lies over a member of `𝒰` mapping to both the `i`-th and the `j`-th, and the
cartesian square over that member produces a point of the corresponding chart. -/
lemma exists_lift_eq {i j : 𝒰.I₀}
    (x : (pullback (G.chart i) (G.chart j)).carrier) :
    ∃ (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : d.functor.obj k),
      pullback.lift (d.functor.map hki) (d.functor.map hkj)
        (by rw [G.chart_trans, G.chart_trans]) y = x := by
  have hbase := congrArg (fun φ : pullback (G.chart i) (G.chart j) ⟶ S => φ.base x)
    (G.fst_natTrans_f_eq i j)
  simp only [Scheme.Hom.comp_apply] at hbase
  obtain ⟨k, fi, fj, uk, -, h2⟩ := 𝒰.exists_of_f_eq_f
    ((d.natTrans.app i).base ((pullback.fst (G.chart i) (G.chart j)).base x))
    ((d.natTrans.app j).base ((pullback.snd (G.chart i) (G.chart j)).base x)) hbase
  obtain ⟨xk, hk1, -⟩ := exists_preimage_of_isPullback (d.equifibered fj) _ uk h2.symm
  refine ⟨k, fi, fj, xk, ?_⟩
  apply (pullback.snd (G.chart i) (G.chart j)).injective
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd, hk1]

/-- The open cover of the total space of a gluing by its charts. -/
def cover : G.pt.OpenCover where
  I₀ := 𝒰.I₀
  X i := d.functor.obj i
  f := G.chart
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨fun x => by simpa using G.exists_chart_eq x, inferInstance⟩

/-- The index category of the chart cover of a gluing is that of `𝒰`. -/
instance : Category G.cover.I₀ := inferInstanceAs <| Category 𝒰.I₀

/-- The chart cover of a gluing is locally directed, with transition maps those of the datum. -/
instance : G.cover.LocallyDirected where
  trans hij := d.functor.map hij
  trans_id i := d.functor.map_id i
  trans_comp hij hjk := d.functor.map_comp hij hjk
  w hij := G.chart_trans hij
  directed x := exists_lift_eq G x
  property_trans hij :=
    MorphismProperty.of_isPullback (d.equifibered hij).flip (𝒰.property_trans hij)

/-- **A morphism out of the total space of a gluing is determined by its charts.** -/
lemma hom_ext {Y : Scheme.{u}} (a b : G.pt ⟶ Y)
    (h : ∀ i : 𝒰.I₀, G.chart i ≫ a = G.chart i ≫ b) : a = b :=
  G.cover.hom_ext a b h

end Gluing

section Canonical

variable [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

/-- **The canonical gluing of a relative gluing datum**, on the colimit of its schemes: the
existence half of [Stacks, Tag 01LH], assembled from Mathlib's relative gluing. -/
def gluingGlued (d : RelativeGluingData 𝒰) : Gluing d where
  pt := d.glued
  toBase := d.toBase
  chart i := colimit.ι d.functor i
  chart_trans hij := colimit.w d.functor hij
  isPullback_chart := d.isPullback_natTrans_ι_toBase

end Canonical

namespace Gluing

/-- The morphism between the total spaces of two gluings obtained by gluing the charts. -/
def glue (G G' : Gluing d) : G.pt ⟶ G'.pt :=
  G.cover.glueMorphismsOfLocallyDirected (fun i => G'.chart i) fun hij => G'.chart_trans hij

/-- The glued morphism between two gluings carries each chart of the first to the corresponding
chart of the second. -/
@[reassoc (attr := simp)]
lemma chart_glue (G G' : Gluing d) (i : 𝒰.I₀) : G.chart i ≫ G.glue G' = G'.chart i :=
  G.cover.map_glueMorphismsOfLocallyDirected _ _ i

/-- The glued morphism from `G` to `G'` followed by the one from `G'` to `G` is the identity. -/
lemma glue_glue (G G' : Gluing d) : G.glue G' ≫ G'.glue G = 𝟙 G.pt :=
  G.hom_ext _ _ fun i => by simp

/-- The glued morphism between two gluings commutes with their structure morphisms to `S`. -/
lemma glue_toBase (G G' : Gluing d) : G.glue G' ≫ G'.toBase = G.toBase :=
  G.hom_ext _ _ fun i => by
    rw [← Category.assoc, chart_glue, ← (G'.isPullback_chart i).w, ← (G.isPullback_chart i).w]

/-- The isomorphism between the total spaces of two gluings. -/
def iso (G G' : Gluing d) : G.pt ≅ G'.pt where
  hom := G.glue G'
  inv := G'.glue G
  hom_inv_id := G.glue_glue G'
  inv_hom_id := G'.glue_glue G

end Gluing

/-- **Stacks Project, Tag 01LI.**  *Uniqueness of the total space.*  Let `𝒰` be a locally directed
open cover of a scheme `S` and let `d` be a relative gluing datum over it.  Two schemes over `S`
glued from `d` — each with its own total space and its own morphisms from the schemes of `d`,
exhibiting them as the parts over the members of `𝒰` — are related by exactly one isomorphism over
`S` carrying the one family of morphisms to the other.

This is the total-space half of the uniqueness assertion of [Stacks, Tag 01LH], which Tag 01LI
quotes for the relatively glued scheme carrying a glued quasi-coherent module.  The module half
and the combination of the two halves are `existsUnique_iso_realizationOn` and
`existsUnique_pairIso` in the namespace
`Stacks.AlgebraicGeometry.RelativeSheafGluing.RelativeSheafGluingData`; the latter is Tag 01LI's
"moreover" sentence, that the *pair* `(X, F)` is unique up to unique isomorphism over `S`.  The
canonical gluing, on the colimit of the schemes of `d`, is
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.gluingGlued`. -/
theorem existsUnique_iso (G G' : Gluing d) :
    ∃! e : G.pt ≅ G'.pt,
      e.hom ≫ G'.toBase = G.toBase ∧ ∀ i, G.chart i ≫ e.hom = G'.chart i :=
  ⟨G.iso G', ⟨G.glue_toBase G', fun i => G.chart_glue G' i⟩, fun _ he =>
    Iso.ext (G.hom_ext _ _ fun i => (he.2 i).trans (G.chart_glue G' i).symm)⟩

end AlgebraicGeometry.Scheme.Cover.RelativeGluingData

end
