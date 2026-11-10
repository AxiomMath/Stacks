module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat

/-!
# The flat locus of a morphism of algebraic spaces

The set of points of the source at which a morphism of algebraic spaces locally of finite
presentation is flat is open in the point space of Stacks 03BU. This is the openness
assertion of Stacks 05X3, whose two finiteness hypotheses on a common base make the morphism
itself locally of finite presentation by Stacks 05WT. The second assertion of Stacks 05X3,
that forming this locus commutes with an arbitrary base change on the common base, is not
proved here.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isFlatAt_chart_iff`: flatness at a point is unchanged on passing
  between a morphism of algebraic spaces and the morphism of charts in a commuting square of
  étale charts over it.
* `AlgebraicGeometry.Space.isFlatAt_yoneda_iff`: for a morphism of represented presheaves,
  flatness at a point of the source is flatness of the underlying morphism of schemes at the
  corresponding scheme point.
* `AlgebraicGeometry.Space.isOpen_setOf_isFlatAt`: the flat locus of a morphism of algebraic
  spaces locally of finite presentation is open.

## Implementation notes

Flatness at a point of an algebraic space is `AlgebraicGeometry.Space.IsFlatAt`, part (2) of
Stacks 03ML: the germ condition on every pointed étale chart. Unlike unramifiedness or
quasi-finiteness at a point, it does not quantify over open neighbourhoods, so openness is
not formal and has to be transported from the scheme-level statement Stacks 0399,
`AlgebraicGeometry.isOpen_setOf_isFlatAt`.

The transport is through one surjective étale chart of the source rather than through the
union over all commuting squares of charts: a surjective étale chart is open and surjective on
points, so the locus is the image of the chart-level locus, and the chart-level locus is cut
out by an open subset of the chart scheme by Stacks 03BX clause (1). This is the route taken
for the Cohen–Macaulay locus in
`StacksFrontier/AlgebraicGeometry/Spaces/CohenMacaulay/Locus.lean`.

The base-change assertion of Stacks 05X3 is of a different nature: its scheme-level
counterpart, `AlgebraicGeometry.setOf_isFlatAt_baseChange`, is stated for a pair of stacked
cartesian squares over the common base, so reading it on charts asks for a configuration of
étale charts of all six spaces in which the chart of the target and the chart of the source
are each a fibre product over the chart of the base. Only the single-square case is available
(`AlgebraicGeometry.Space.exists_compatible_etale_charts`), and that assertion is therefore
left open.

## References

* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 05X3](https://stacks.math.columbia.edu/tag/05X3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Germ flatness at a point of a scheme -/

/-- The germ morphism induced by a morphism of schemes at a point of its source is flat, in
the sense of Stacks 04ND, as soon as the induced homomorphism of local rings at that point is
flat: the germ is represented on the whole source scheme, and composing with the canonical
isomorphism from the top open subscheme does not change flatness of the stalk map.

This is one direction of `AlgebraicGeometry.MorphismOfGerms.isFlat_ofSchemeHom_iff`, reproved
here so that this file does not import the strict henselization theory on which the converse
direction of that equivalence rests; the same statement already appears privately in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Flat.lean`. -/
private theorem isFlat_ofSchemeHom_of_isFlatAt {U V : Scheme.{u}} (g : U ⟶ V) (x : U)
    (hg : _root_.AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom x) :
    MorphismOfGerms.IsFlat (MorphismOfGerms.ofSchemeHom g x) := by
  refine ⟨⟨⊤, by simp, U.topIso.hom ≫ g, rfl⟩, rfl, ?_⟩
  change ((U.topIso.hom ≫ g).stalkMap ⟨x, by simp⟩).hom.Flat
  exact (congrArg (fun k => k.hom.Flat)
    (Scheme.Hom.stalkMap_comp U.topIso.hom g ⟨x, by simp⟩)).mpr
      (hg.comp (Flat.stalkMap U.topIso.hom ⟨x, by simp⟩))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Flatness at a point, read on charts -/

/-- Flatness at a point is flatness of the germ of the chart morphism at the chart's source
point, for any given pointed étale chart. -/
private theorem isFlatAt_iff_of_chart {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (x : points B S hS F) (c : EtaleChartAtPoint B S hS f x) :
    IsFlatAt B S hS f x ↔
      MorphismOfGerms.IsFlat (MorphismOfGerms.ofSchemeHom
        ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)) :=
  holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@MorphismOfGerms.IsFlat.{u})
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat f x c

/-- Flatness at a point is unchanged on passing between a morphism of algebraic spaces and the
morphism of charts in a commuting square of étale charts over it. -/
theorem isFlatAt_chart_iff {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (comm : a ≫ f = yoneda.map h ≫ b)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) (t : Spec (.of p.carrier)) :
    IsFlatAt B S hS (yoneda.map h) (p.class B S hS (yoneda.obj U)) ↔
      IsFlatAt B S hS f
        (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) := by
  let cf : EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) :=
    { U := U, V := V, a := a, b := b, h := h, a_etale := ha, b_etale := hb
      comm := comm.symm, representative := p, point := t, maps_to := rfl }
  let ch := etaleChartAtPointOfId B S hS U V h p t
  exact (isFlatAt_iff_of_chart B S hS _ _ ch).trans (isFlatAt_iff_of_chart B S hS f _ cf).symm

/-- For a morphism of represented presheaves, flatness at a point of the source is flatness
of the underlying morphism of schemes at the corresponding scheme point. -/
theorem isFlatAt_yoneda_iff (U V : BigFppfOver B S hS) (h : U ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsFlatAt B S hS (yoneda.map h) (p.class B S hS (yoneda.obj U)) ↔
      _root_.AlgebraicGeometry.IsFlatAt
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom (schemePoint B S hS U p) := by
  let c := etaleChartAtPointOfId B S hS U V h p (IsLocalRing.closedPoint p.carrier)
  exact (isFlatAt_iff_of_chart B S hS _ _ c).trans
    ⟨flatAt_of_isFlat_germ _ _, isFlat_ofSchemeHom_of_isFlatAt _ _⟩

/-- For a morphism of represented presheaves locally of finite presentation, the set of
points of the source at which it is flat is open in the point topology of Stacks 03BX. -/
theorem isOpen_setOf_isFlatAt_yoneda (U V : BigFppfOver B S hS) (h : U ⟶ V)
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h)] :
    IsOpen {u : points B S hS (yoneda.obj U) | IsFlatAt B S hS (yoneda.map h) u} :=
  (isOpen_yoneda_iff_isSchemeOpen B S hS U _).mpr
    ⟨{z | _root_.AlgebraicGeometry.IsFlatAt
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom z},
      _root_.AlgebraicGeometry.isOpen_setOf_isFlatAt _,
      fun p => isFlatAt_yoneda_iff B S hS U V h p⟩

/-! ### Openness of the flat locus -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Openness of the flat locus of a morphism of algebraic spaces.** For a morphism of
algebraic spaces over `S` locally of finite presentation, the set of points of the source at
which it is flat is open.

This is the scheme-level theorem Stacks 0399 transported along one surjective étale chart of
the source, which is open and surjective on points. -/
@[sga "3 VIB 1.3" "more general", sga "3 X 4.4" "partial"]
theorem isOpen_setOf_isFlatAt (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsOpen {x : points B S hS X | IsFlatAt B S hS f x} := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, α, hcomm, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  have _ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map α) :=
    hf U V a b α haEtale hbEtale hcomm.symm
  have hpre : {z : points B S hS (yoneda.obj U) | IsFlatAt B S hS (yoneda.map α) z} =
      pointsMap B S hS (yoneda.obj U) a ⁻¹' {x : points B S hS X | IsFlatAt B S hS f x} := by
    refine Set.ext fun z => ?_
    induction z using Quot.ind with
    | _ p =>
      exact isFlatAt_chart_iff B S hS f U V a b α haEtale hbEtale hcomm p
        (IsLocalRing.closedPoint p.carrier)
  have := isOpenMap_pointsMap_of_presheafEtale B S hS a haEtale _
    (isOpen_setOf_isFlatAt_yoneda B S hS U V α)
  rwa [hpre, Set.image_preimage_eq _
    ((surjective_iff_surjective_pointsMap B S hS X hX U a).mp haSurj)] at this

/-! ### Stacks 05X3, the openness assertion -/

/-- **Stacks 05X3, the openness assertion.** Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` whose source and target are given over a third algebraic space `Z` by morphisms
`p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`. If `p` is locally of finite presentation and `q`
is locally of finite type, then the set of points of `|X|` at which `f` is flat is open.

Flatness of `p`, which the source assumes, is not needed here: the two finiteness hypotheses
already make `f` locally of finite presentation by Stacks 05WT, so the openness of the flat
locus of a morphism locally of finite presentation applies to `f` itself. The same reduction
is how the scheme-level assertion of Stacks 05VK is proved. -/
@[stacks 05X3 "openness of the flat locus", sga "3 VIB 1.3" "more general", sga "3 X 4.4" "partial"]
theorem isOpen_setOf_isFlatAt_of_isLocallyOfFinitePresentation_comp
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hp : IsLocallyOfFinitePresentation B S hS p)
    (hq : IsLocallyOfFiniteType B S hS q) :
    IsOpen {x : points B S hS X | IsFlatAt B S hS f x} :=
  isOpen_setOf_isFlatAt B S hS hX hY f
    (isLocallyOfFinitePresentation_of_comp B S hS hX hY hZ f q (hfq ▸ hp) hq)

end AlgebraicGeometry.Space

end
