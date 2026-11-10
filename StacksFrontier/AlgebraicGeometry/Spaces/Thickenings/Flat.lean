module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Thickenings.Flatness

/-!
# Flatness across a thickening of algebraic spaces

Consider a morphism of thickenings of algebraic spaces over a scheme `S`,

```
(X ⊂ X') --(f, f')--> (Y ⊂ Y')
         ↘                ↙
            (B ⊂ B')
```

with `B ⊂ B'` of finite order, `X'` flat over `B'`, and both unprimed spaces the base changes
of their primed counterparts. If `f` is flat then so is `f'`, and `Y'` is flat over `B'` at
every point in the image of `f'`.

## Main results

* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isFlatAt_g'_of_isFlat_f`: the
  ambient target is flat over the ambient base at every point in the image of the ambient
  morphism.
* `AlgebraicGeometry.Space.isFlat_of_isFlat_restriction`: **Stacks 0CG5**, flatness of the
  ambient morphism.
* `AlgebraicGeometry.Space.isFlatAt_base_of_isFlat_restriction`: **Stacks 0CG5**, flatness of
  the ambient target over the base along the image.

## Implementation notes

Flatness of `f'` is the forward implication of
`AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isFlat_iff`, part 0CG8 of Tag 0CG6,
applied to the cartesian finite-order deformation assembled from the hypotheses; no second
proof is given here.

Flatness of `Y'` over `B'` at the image points is not an every-chart condition but a
pointed-chart condition, Tag 03ML part (2) at the germ-level flatness predicate of Tag 04ND,
so it is not an instance of the every-chart transport of Tag 0CG6 and the compatible charts
have to be named. They are produced exactly as in
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation`: an
atlas of the ambient base lifts to an atlas of the ambient target and then to one of the
ambient source, the three thickenings pull back along those charts to thickenings of schemes
by Tag 09ZX with the base one of finite order, and the two unprimed charts are cartesian over
the unprimed base chart by pasting, so the whole square of charts is a
`Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram`. On that diagram Tag 06AF gives
flatness of the stalk map of the chart of `g'` at every point of the chart of `X'`, and a
point of the chart of `X'` over the given point of `X'` exists because the chart is surjective
(Tag 03H5). The square of charts of `g'` together with that point is a pointed étale chart at
the image point, so Tag 04NC turns the single germ into the every-chart condition.

## References

* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 04R7](https://stacks.math.columbia.edu/tag/04R7)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 06AF](https://stacks.math.columbia.edu/tag/06AF)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 0CG5](https://stacks.math.columbia.edu/tag/0CG5)
* [Stacks Project, Tag 0CG6](https://stacks.math.columbia.edu/tag/0CG6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

/-- The germ morphism induced by a morphism of schemes at a point of its source is flat, in the
sense of [Stacks Project, Tag 04ND], as soon as the induced homomorphism of local rings at that
point is flat: the germ is represented on the whole source scheme, and composing with the
canonical isomorphism from the top open subscheme does not change flatness of the stalk map. -/
private theorem isFlat_ofSchemeHom_of_flat_stalkMap {U V : Scheme.{u}} (g : U ⟶ V) (x : U)
    (hg : (g.stalkMap x).hom.Flat) :
    MorphismOfGerms.IsFlat (MorphismOfGerms.ofSchemeHom g x) := by
  refine ⟨⟨⊤, by simp, U.topIso.hom ≫ g, by change g x = g x; rfl⟩, rfl, ?_⟩
  change ((U.topIso.hom ≫ g).stalkMap ⟨x, by simp⟩).hom.Flat
  exact (congrArg (fun k => k.hom.Flat)
    (Scheme.Hom.stalkMap_comp U.topIso.hom g ⟨x, by simp⟩)).mpr
      (hg.comp (Flat.stalkMap U.topIso.hom ⟨x, by simp⟩))

/-- Lifting a map out of a chart along a pullback square of charts. -/
private theorem exists_chart_lift {C : Type*} [Category.{u} C] {F F' : Cᵒᵖ ⥤ Type u}
    {V₀ V' W : C} {pV : yoneda.obj V₀ ⟶ F} {j : V₀ ⟶ V'} {ι : F ⟶ F'} {q : yoneda.obj V' ⟶ F'}
    (hpb : IsPullback pV (yoneda.map j) ι q) (a : yoneda.obj W ⟶ F) (b : W ⟶ V')
    (h : a ≫ ι = yoneda.map b ≫ q) :
    ∃ g : W ⟶ V₀, yoneda.map g ≫ pV = a ∧ g ≫ j = b :=
  ⟨yoneda.preimage (hpb.lift a (yoneda.map b) h),
    by rw [yoneda.map_preimage]; exact hpb.lift_fst a (yoneda.map b) h,
    yoneda.map_injective (by
      rw [yoneda.map_comp, yoneda.map_preimage]; exact hpb.lift_snd a (yoneda.map b) h)⟩

/-- A chart over a chart of the ambient corner lies over the chart of the next ambient corner. -/
private theorem chart_comp_eq {C : Type*} [Category.{u} C] {F F' G G' : Cᵒᵖ ⥤ Type u}
    {V₀ V' V'' : C} {p : yoneda.obj V₀ ⟶ F} {j : V₀ ⟶ V'} {α : V' ⟶ V''} {ι : F ⟶ F'}
    {q : yoneda.obj V' ⟶ F'} {g : F ⟶ G} {g' : F' ⟶ G'} {ιG : G ⟶ G'}
    {qG : yoneda.obj V'' ⟶ G'} (hw : p ≫ ι = yoneda.map j ≫ q) (hc : g ≫ ιG = ι ≫ g')
    (hq : yoneda.map α ≫ qG = q ≫ g') : p ≫ g ≫ ιG = yoneda.map (j ≫ α) ≫ qG := by
  rw [hc, ← Category.assoc, hw, Functor.map_comp, Category.assoc,
    Category.assoc, hq]

/-- Pasting an outer cartesian square of charts with the cartesian square of the base charts
gives a cartesian square of the underlying objects. -/
private theorem isPullback_chart_of_paste {C : Type*} [Category.{u} C] {F F' : Cᵒᵖ ⥤ Type u}
    {U₀ U' V₀ V' : C} {pB : yoneda.obj U₀ ⟶ F} {jB : U₀ ⟶ U'} {ι : F ⟶ F'}
    {qB : yoneda.obj U' ⟶ F'} (hpb : IsPullback pB (yoneda.map jB) ι qB) {j : V₀ ⟶ V'}
    {g₀ : V₀ ⟶ U₀} {α : V' ⟶ U'} {a : yoneda.obj V₀ ⟶ F} {b : yoneda.obj V' ⟶ F'}
    (houter : IsPullback (yoneda.map j) a b ι) (ha : yoneda.map g₀ ≫ pB = a)
    (hb : yoneda.map α ≫ qB = b) (hcomm : g₀ ≫ jB = j ≫ α) : IsPullback j g₀ α jB := by
  subst ha hb
  exact IsPullback.of_map_of_faithful yoneda (houter.of_bot (by
    simpa only [Functor.map_comp] using congrArg yoneda.map hcomm.symm) hpb.flip)

namespace CartesianFiniteOrderDeformation

variable {T : BigFppfSite.{u}} {S : Scheme.{u}} {hS : T.Contains S}
    (D : CartesianFiniteOrderDeformation T S hS)

/-- **The ambient target of a cartesian finite-order deformation is flat over the ambient base
along the image of the ambient morphism.** If the morphism of special fibres is flat then, for
every point `x'` of the ambient source, the structure morphism `g'` of the ambient target is
flat at the image of `x'` under the ambient morphism. -/
theorem isFlatAt_g'_of_isFlat_f (hf : IsFlat T S hS D.f)
    (x' : points T S hS D.X'.1) :
    IsFlatAt T S hS D.g' (pointsMap T S hS D.X'.1 D.f' x') := by
  classical
  let Tscheme := BigFppfOver.toScheme T S hS
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      Tscheme).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange T S hS inferInstance
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      Tscheme).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange T S hS inferInstance
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      Tscheme).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      Tscheme).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  -- Compatible charts of the three ambient corners.
  obtain ⟨U', qB', hqB'surj, hqB'etale⟩ := D.B'.property.exists_atlas
  obtain ⟨V', qY', α, hqYcomm, hqYsurj, hqYetale⟩ :=
    exists_surjective_etale_presentation_lift T S hS D.Y'.property D.B'.property D.g'
      U' qB' hqB'surj hqB'etale
  obtain ⟨W', qX', β, hqXcomm, hqXsurj, hqXetale⟩ :=
    exists_surjective_etale_presentation_lift T S hS D.X'.property D.Y'.property D.f'
      V' qY' hqYsurj hqYetale
  -- The three thickenings pull back to thickenings of schemes on those charts.
  obtain ⟨U₀, jB, pB, hpbB, hBfinite⟩ :=
    exists_finiteOrderThickening_chart_pullback T S hS D.base_finiteOrder U' qB' hqB'etale
  obtain ⟨V₀, jY, pY, hpbY, hYthick⟩ :=
    exists_thickening_chart_pullback_subfunctor T S hS D.target_thickening V' qY'
  obtain ⟨W₀, jX, pX, hpbX, hXthick⟩ :=
    exists_thickening_chart_pullback_subfunctor T S hS D.source_thickening W' qX'
  have hqY₀etale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pY :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbY.flip hqYetale
  have hqX₀etale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pX :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbX.flip hqXetale
  -- The charts of the unprimed corners lie over the chart of the unprimed base.
  have hgcompat : pY ≫ D.g ≫ D.B.ι = yoneda.map (jY ≫ α) ≫ qB' :=
    chart_comp_eq hpbY.w D.comm_g hqYcomm.symm
  have hfcompat : pX ≫ D.f ≫ D.Y.ι = yoneda.map (jX ≫ β) ≫ qY' :=
    chart_comp_eq hpbX.w D.comm_f hqXcomm.symm
  obtain ⟨g₀, hg₀pB, hg₀jB⟩ := exists_chart_lift hpbB (pY ≫ D.g) (jY ≫ α) hgcompat
  obtain ⟨f₀, hf₀pY, hf₀jY⟩ := exists_chart_lift hpbY (pX ≫ D.f) (jX ≫ β) hfcompat
  -- Both unprimed charts are cartesian over the unprimed base chart.
  have hβaQ : yoneda.map (β ≫ α) ≫ qB' = qX' ≫ D.f' ≫ D.g' := by
    rw [Functor.map_comp, Category.assoc, ← hqYcomm, ← Category.assoc, ← hqXcomm,
      Category.assoc]
  have hpbYchartSite : IsPullback jY g₀ α jB :=
    isPullback_chart_of_paste hpbB (hpbY.flip.paste_vert D.isPullback_Y) hg₀pB hqYcomm.symm
      hg₀jB
  have hpbXchartSite : IsPullback jX (f₀ ≫ g₀) (β ≫ α) jB :=
    isPullback_chart_of_paste hpbB (hpbX.flip.paste_vert D.isPullback_X)
      (by rw [Functor.map_comp, Category.assoc, hg₀pB, ← Category.assoc, hf₀pY, Category.assoc])
      hβaQ (by rw [Category.assoc, hg₀jB, ← Category.assoc, hf₀jY, Category.assoc])
  have hqX'flat : Flat (Tscheme.map (β ≫ α)) :=
    D.flat_X' W' U' qX' qB' (β ≫ α) hqXetale hqB'etale hβaQ
  -- The resulting cartesian finite-order deformation diagram of schemes.
  let E : Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.{u} :=
    { S := Tscheme.obj U₀
      S' := Tscheme.obj U'
      iS := Tscheme.map jB
      iS_finiteOrder := hBfinite
      X := Tscheme.obj W₀
      X' := Tscheme.obj W'
      iX := Tscheme.map jX
      iX_thickening := hXthick
      Y := Tscheme.obj V₀
      Y' := Tscheme.obj V'
      iY := Tscheme.map jY
      iY_thickening := hYthick
      pX := Tscheme.map (f₀ ≫ g₀)
      pX' := Tscheme.map (β ≫ α)
      pY := Tscheme.map g₀
      pY' := Tscheme.map α
      f := Tscheme.map f₀
      f' := Tscheme.map β
      f_over_S := by simp
      f'_over_S' := by simp
      f_thickening_comm := by
        simpa only [Functor.map_comp] using congrArg Tscheme.map hf₀jY
      X_cartesian := hpbXchartSite.map Tscheme
      Y_cartesian := hpbYchartSite.map Tscheme
      X'_flat := hqX'flat }
  have hfChart : Flat (Tscheme.map f₀) := hf W₀ V₀ pX pY f₀ hqX₀etale hqY₀etale hf₀pY
  -- A point of the chart of the ambient source over the given point.
  obtain ⟨z, hz⟩ := (surjective_iff_pointsMap_surjective T S hS
    (isAlgebraicSpace_yoneda T S hS W') D.X'.property qX' hqXsurj.1).mp hqXsurj x'
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  -- The square of charts of `g'`, pointed at the image of that point.
  let c : EtaleChartAtPoint T S hS D.g' (pointsMap T S hS D.X'.1 D.f' x') :=
    { U := V'
      V := U'
      a := qY'
      b := qB'
      h := α
      a_etale := hqYetale
      b_etale := hqB'etale
      comm := hqYcomm.symm
      representative := FieldValuedPoint.map T S hS (yoneda.obj W') (yoneda.map β) p
      point := ⟨⊥, inferInstance⟩
      maps_to := by
        have h1 : pointsMap T S hS (yoneda.obj V') qY'
            ((FieldValuedPoint.map T S hS (yoneda.obj W') (yoneda.map β) p).class T S hS
              (yoneda.obj V')) =
            pointsMap T S hS (yoneda.obj W') (yoneda.map β ≫ qY')
              (p.class T S hS (yoneda.obj W')) := by
          rw [pointsMap_comp]
          rfl
        rw [h1, ← hqXcomm, pointsMap_comp]
        exact congrArg (pointsMap T S hS D.X'.1 D.f') hz }
  refine (holdsOnEveryEtaleChartAtPoint_iff_some T S hS (@MorphismOfGerms.IsFlat.{u})
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat D.Y'.property D.B'.property
    D.g' _).mpr ⟨c, ?_⟩
  have hpoint : c.sourcePoint T S hS =
      (Tscheme.map β) ((Tscheme.map p.value) (⟨⊥, inferInstance⟩ :
        Spec (.of p.carrier))) := by
    change (Tscheme.map (p.value ≫ β)) _ = _
    rw [Tscheme.map_comp]
    rfl
  rw [hpoint]
  exact isFlat_ofSchemeHom_of_flat_stalkMap _ _
    (AlgebraicGeometry.flatAt_target_of_flat_reduction E.iX_thickening E.iY_thickening
      E.iS_finiteOrder E.X_cartesian E.Y_cartesian E.f_thickening_comm.symm E.f_over_S
      E.f'_over_S' E.X'_flat hfChart ((Tscheme.map p.value) ⟨⊥, inferInstance⟩))

end CartesianFiniteOrderDeformation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X' Y' B' : AlgebraicSpaces B S hS}
variable {X : Subfunctor X'.1} {Y : Subfunctor Y'.1} {B₀ : Subfunctor B'.1}
variable (f : X.toFunctor ⟶ Y.toFunctor) (f' : X'.1 ⟶ Y'.1)
variable (pX : X.toFunctor ⟶ B₀.toFunctor) (pX' : X'.1 ⟶ B'.1)
  (pY : Y.toFunctor ⟶ B₀.toFunctor) (pY' : Y'.1 ⟶ B'.1)

/-- The cartesian finite-order deformation of algebraic spaces presented by a commuting
diagram of thickenings with the structure morphisms of the sources given separately. -/
noncomputable def cartesianFiniteOrderDeformationOfDiagram
    (hiX : IsThickening B S hS X' X) (hiY : IsThickening B S hS Y' Y)
    (hiB : IsFiniteOrderThickening B S hS B' B₀)
    (hcartX : IsPullback X.ι pX pX' B₀.ι) (hcartY : IsPullback Y.ι pY pY' B₀.ι)
    (hinner : f ≫ pY = pX) (houter : f' ≫ pY' = pX')
    (hrestrict : X.ι ≫ f' = f ≫ Y.ι)
    (hXflat : IsFlat B S hS pX') :
    CartesianFiniteOrderDeformation B S hS where
  X' := X'
  Y' := Y'
  B' := B'
  X := X
  Y := Y
  B := B₀
  base_finiteOrder := hiB
  source_thickening := hiX
  target_thickening := hiY
  f := f
  f' := f'
  g := pY
  g' := pY'
  comm_f := hrestrict.symm
  comm_g := hcartY.w.symm
  isPullback_X := by rw [hinner, houter]; exact hcartX
  isPullback_Y := hcartY
  flat_X' := by rw [houter]; exact hXflat

/-- **Stacks 0CG5, flatness of the ambient morphism.** In a commuting diagram of thickenings
of algebraic spaces over `S` with the base thickening of finite order, the ambient source flat
over the ambient base and both unprimed spaces the base changes of their primed counterparts,
flatness of the morphism of special fibres implies flatness of its ambient deformation.

This is the forward implication of part 0CG8 of Tag 0CG6, which is
`AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isFlat_iff`. -/
@[stacks 0CG5 "flatness of the upper morphism"]
theorem isFlat_of_isFlat_restriction
    (hiX : IsThickening B S hS X' X) (hiY : IsThickening B S hS Y' Y)
    (hiB : IsFiniteOrderThickening B S hS B' B₀)
    (hcartX : IsPullback X.ι pX pX' B₀.ι) (hcartY : IsPullback Y.ι pY pY' B₀.ι)
    (hinner : f ≫ pY = pX) (houter : f' ≫ pY' = pX')
    (hrestrict : X.ι ≫ f' = f ≫ Y.ι)
    (hXflat : IsFlat B S hS pX') (hfflat : IsFlat B S hS f) :
    IsFlat B S hS f' :=
  (CartesianFiniteOrderDeformation.isFlat_iff
    (cartesianFiniteOrderDeformationOfDiagram B S hS f f' pX pX' pY pY' hiX hiY hiB hcartX
      hcartY hinner houter hrestrict hXflat)).mp hfflat

/-- **Stacks 0CG5, flatness of the ambient target along the image.** In the situation of
`AlgebraicGeometry.Space.isFlat_of_isFlat_restriction` the ambient target is flat over the
ambient base at every point in the image of the ambient morphism. -/
@[stacks 0CG5 "flatness of the upper target at image points"]
theorem isFlatAt_base_of_isFlat_restriction
    (hiX : IsThickening B S hS X' X) (hiY : IsThickening B S hS Y' Y)
    (hiB : IsFiniteOrderThickening B S hS B' B₀)
    (hcartX : IsPullback X.ι pX pX' B₀.ι) (hcartY : IsPullback Y.ι pY pY' B₀.ι)
    (hinner : f ≫ pY = pX) (houter : f' ≫ pY' = pX')
    (hrestrict : X.ι ≫ f' = f ≫ Y.ι)
    (hXflat : IsFlat B S hS pX') (hfflat : IsFlat B S hS f)
    (x' : points B S hS X'.1) :
    IsFlatAt B S hS pY' (pointsMap B S hS X'.1 f' x') :=
  CartesianFiniteOrderDeformation.isFlatAt_g'_of_isFlat_f
    (cartesianFiniteOrderDeformationOfDiagram B S hS f f' pX pX' pY pY' hiX hiY hiB hcartX
      hcartY hinner houter hrestrict hXflat) hfflat x'

end AlgebraicGeometry.Space

end
