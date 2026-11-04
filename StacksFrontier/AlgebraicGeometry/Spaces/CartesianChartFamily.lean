module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecPullbackChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# Glueing a cartesian family of schemes over the étale charts of an algebraic space

Let `X` be an algebraic space over a scheme `S`.  A *cartesian chart family* over `X` is the
datum of a scheme `F(V)` over every étale scheme chart `V` of `X`, together with a morphism
`F(h) : F(V') ⟶ F(V)` over every morphism `h : V' ⟶ V` of charts, functorially in `h`, such that
every square

```
F(V')  ⟶  F(V)
  |          |
  V'   ⟶    V
```

is cartesian.  This is the shape in which the relative constructions of Stacks 084C (relative
`Proj`), 081V (relative `Spec`) and their special cases are glued from the case of schemes: over a
surjective étale chart `V₂ ⟶ X` with relation `V' = V₂ ×_X V₂`, the two morphisms
`F(V') ⇉ F(V₂)` attached to the two projections form an étale equivalence relation, whose quotient
is an algebraic space `F_X` over `X` with `F(V₂) = F_X ×_X V₂`.

This file develops that glueing once, for an arbitrary cartesian chart family.  It is the
argument `StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecEquivalenceRelation`,
`…ChartRelativeSpecQuotient` and `…ChartRelativeSpecPullbackChart` carry out for the relative
spectrum of a quasi-coherent algebra, with the relative spectrum over a chart replaced by the
family: none of those arguments uses anything about the relative spectrum beyond its
functoriality in the chart and its cartesian squares.

## Main definitions

* `AlgebraicGeometry.Space.CartesianChartFamily`: the datum.
* `AlgebraicGeometry.Space.CartesianChartFamily.site`,
  `AlgebraicGeometry.Space.CartesianChartFamily.siteToChart` and
  `AlgebraicGeometry.Space.CartesianChartFamily.siteMap`: the family read in the big fppf site
  over `S`.
* `AlgebraicGeometry.Space.CartesianChartFamily.quotient`: **the glued algebraic space** `F_X`,
  the quotient of the relation of the family over a relation of charts, and
  `AlgebraicGeometry.Space.CartesianChartFamily.quotientHom` its structure morphism to `X`.

## Main results

* `AlgebraicGeometry.Space.CartesianChartFamily.map_id`: the identity law, derived from the
  composition law and the cartesian squares.
* `AlgebraicGeometry.Space.CartesianChartFamily.equivalenceRelation`: the two morphisms
  `F(V') ⇉ F(V₂)` form an internal equivalence relation.
* `AlgebraicGeometry.Space.CartesianChartFamily.isAlgebraicSpace_quotientPresheaf`: the quotient
  is an algebraic space (Stacks 02WW).
* `AlgebraicGeometry.Space.CartesianChartFamily.isPullback_quotientHom`: **the cartesian square
  at the chart**, `F(V₂) = F_X ×_X V₂`, for a surjective chart `V₂`.

## References

* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A cartesian family of schemes over the étale charts of an algebraic space `X`**: a scheme
`F(V)` over every étale scheme chart `V` of `X`, contained in the site, and a morphism
`F(V') ⟶ F(V)` over every morphism of charts `V' ⟶ V`, functorially, with every square over a
morphism of charts cartesian. -/
structure CartesianChartFamily (X : AlgebraicSpaces B S hS) where
  /-- The scheme over a chart. -/
  obj : SmallEtale B S hS X.1 → Scheme.{u}
  /-- Its structure morphism to the scheme of the chart. -/
  toChart : ∀ V, obj V ⟶ chartScheme V
  /-- The morphism over a morphism of charts. -/
  map : ∀ {V V' : SmallEtale B S hS X.1}, (V' ⟶ V) → (obj V' ⟶ obj V)
  /-- The square over a morphism of charts is cartesian. -/
  isPullback : ∀ {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V),
    IsPullback (map h) (toChart V') (toChart V) (chartSchemeMap h)
  /-- The composition law. -/
  map_comp : ∀ {V V' V'' : SmallEtale B S hS X.1} (h : V' ⟶ V) (h' : V'' ⟶ V'),
    map (h' ≫ h) = map h' ≫ map h
  /-- Every scheme of the family is an object of the site. -/
  contains : ∀ V, B.Contains (obj V)

namespace CartesianChartFamily

variable {X : AlgebraicSpaces B S hS} (F : CartesianChartFamily X)

/-- The morphism over a morphism of charts lies over it. -/
@[reassoc]
theorem map_comp_toChart {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    F.map h ≫ F.toChart V = F.toChart V' ≫ chartSchemeMap h :=
  (F.isPullback h).w

/-- **The identity law.**  The morphism over the identity is idempotent by the composition law
and invertible as a base change of an isomorphism, hence the identity. -/
theorem map_id (V : SmallEtale B S hS X.1) : F.map (𝟙 V) = 𝟙 (F.obj V) := by
  have : IsIso (F.map (𝟙 V)) :=
    (F.isPullback (𝟙 V)).isIso_fst_of_isIso
      (show IsIso (𝟙 (chartScheme V)) from inferInstance)
  refine ((cancel_epi (F.map (𝟙 V))).mp ?_).symm
  rw [Category.comp_id, ← F.map_comp, Category.comp_id]

/-- The morphism over a morphism of charts inherits every base-change-stable property of the
morphism of chart schemes. -/
theorem map_of_isStableUnderBaseChange {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (hP : P (chartSchemeMap h)) :
    P (F.map h) :=
  MorphismProperty.of_isPullback (F.isPullback h).flip hP

/-- The morphism over a morphism of charts is étale. -/
theorem etale_map {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) : Etale (F.map h) :=
  have : MorphismProperty.IsStableUnderBaseChange
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    Etale.etale_isStableUnderBaseChange
  F.map_of_isStableUnderBaseChange h (@Etale.{u} : MorphismProperty Scheme.{u})
    (etale_chartSchemeMap h)

/-! ### The family read in the big fppf site -/

/-- The scheme over a chart as an object of the big fppf site over `S`, with structure morphism
its structure morphism to the chart followed by that of the chart. -/
def site (V : SmallEtale B S hS X.1) : BigFppfOver B S hS :=
  BigFppfOver.siteObjectOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) (F.contains V)
    (F.toChart V)

/-- The scheme underlying the site object over a chart is the scheme over that chart. -/
@[simp]
theorem toScheme_obj_site (V : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).obj (F.site V) = F.obj V :=
  rfl

/-- The structure morphism to the chart, as a morphism of the site. -/
def siteToChart (V : SmallEtale B S hS X.1) :
    F.site V ⟶ (SmallEtale.toOver B S hS X.1).obj V :=
  BigFppfOver.siteMapOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) (F.contains V)
    (F.toChart V)

/-- The scheme morphism underlying `siteToChart` is the structure morphism to the chart. -/
@[simp]
theorem toScheme_map_siteToChart (V : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).map (F.siteToChart V) = F.toChart V :=
  rfl

/-- The morphism over a morphism of charts, as a morphism of the site. -/
def siteMap {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) : F.site V' ⟶ F.site V :=
  Over.homMk (ObjectProperty.homMk (F.map h)) (by
    apply ObjectProperty.hom_ext
    change F.map h ≫ F.toChart V ≫ B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V).hom =
      F.toChart V' ≫ B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj V').hom
    rw [← Category.assoc, F.map_comp_toChart, Category.assoc,
      chartSchemeMap_comp_inclusion_map_hom])

/-- The scheme morphism underlying `siteMap h` is the morphism over `h`. -/
@[simp]
theorem toScheme_map_siteMap {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    (BigFppfOver.toScheme B S hS).map (F.siteMap h) = F.map h :=
  rfl

/-- The composition law, read in the site. -/
theorem siteMap_comp {V V' V'' : SmallEtale B S hS X.1} (h : V' ⟶ V) (h' : V'' ⟶ V') :
    F.siteMap (h' ≫ h) = F.siteMap h' ≫ F.siteMap h :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (F.map_comp h h'))

/-- The identity law, read in the site. -/
theorem siteMap_id (V : SmallEtale B S hS X.1) : F.siteMap (𝟙 V) = 𝟙 (F.site V) :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (F.map_id V))

/-- **The cartesian square over a morphism of charts, read in the site.** -/
theorem isPullback_siteMap {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    IsPullback (F.siteMap h) (F.siteToChart V') (F.siteToChart V)
      ((SmallEtale.toOver B S hS X.1).map h) :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) (F.isPullback h)

/-- The morphism of site objects is étale, in the form the étale equivalence relations of the
big fppf site consume. -/
theorem inverseImage_etale_siteMap {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F.siteMap h) :=
  F.etale_map h

/-! ### The morphism to the algebraic space -/

/-- The morphism `F(V) ⟶ X` attached to a chart: the structure morphism to the chart followed by
the chart. -/
def siteToSpace (V : SmallEtale B S hS X.1) : yoneda.obj (F.site V) ⟶ X.1 :=
  yoneda.map (F.siteToChart V) ≫ V.obj.hom

/-- The morphisms to `X` attached to the charts are compatible with the morphisms of the
family. -/
theorem siteMap_comp_siteToSpace {V V' : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    yoneda.map (F.siteMap h) ≫ F.siteToSpace V = F.siteToSpace V' := by
  rw [siteToSpace, siteToSpace, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    (F.isPullback_siteMap h).w, CategoryTheory.Functor.map_comp, Category.assoc,
    yoneda_map_toOver_map_comp_hom]

/-! ### The equivalence relation over a relation of charts -/

/-- The source of `relation B S hS tR sR` is the image of `tR` in schemes over `S`. -/
private theorem relation_source_eq_post_map {Ro Wo : BigFppfOver B S hS} (sR tR : Ro ⟶ Wo) :
    (relation B S hS tR sR).source = (Over.post (X := B.obj hS) B.inclusion).map tR :=
  prod.lift_snd _ _

/-- The target of `relation B S hS tR sR` is the image of `sR` in schemes over `S`. -/
private theorem relation_target_eq_post_map {Ro Wo : BigFppfOver B S hS} (sR tR : Ro ⟶ Wo) :
    (relation B S hS tR sR).target = (Over.post (X := B.obj hS) B.inclusion).map sR :=
  prod.lift_fst _ _

section Relation

variable {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)

include hsq in
/-- The two morphisms of the family over a relation of charts are jointly monic. -/
theorem jointlyMono₂_siteMap :
    JointlyMono₂ (yoneda.map (F.siteMap pr₁)) (yoneda.map (F.siteMap pr₂)) := by
  have hA₁ := (F.isPullback_siteMap pr₁).map yoneda
  have hA₂ := (F.isPullback_siteMap pr₂).map yoneda
  refine ⟨fun Z a b h₁ h₂ => hA₂.hom_ext h₂ (hsq.hom_ext ?_ ?_)⟩
  · rw [Category.assoc, Category.assoc, ← hA₁.w, ← Category.assoc, ← Category.assoc, h₁]
  · rw [Category.assoc, Category.assoc, ← hA₂.w, ← Category.assoc, ← Category.assoc, h₂]

/-- The composition identity of the triple fibre product of charts, read on the family. -/
theorem siteMap_pullbackSnd_comp :
    F.siteMap (Limits.pullback.snd pr₁ pr₂) ≫ F.siteMap pr₂ =
      F.siteMap (Limits.pullback.fst pr₁ pr₂) ≫ F.siteMap pr₁ := by
  rw [← F.siteMap_comp, ← F.siteMap_comp, Limits.pullback.condition]

/-- **The family over the triple fibre product of charts is the fibre product of two copies of
the family over `V'`**, the limiting cone transitivity needs. -/
theorem isPullback_siteMap₂ :
    IsPullback (F.siteMap (Limits.pullback.snd pr₁ pr₂)) (F.siteMap (Limits.pullback.fst pr₁ pr₂))
      (F.siteMap pr₂) (F.siteMap pr₁) := by
  have hbase : IsPullback
      ((SmallEtale.toOver B S hS X.1).map (Limits.pullback.snd pr₁ pr₂))
      ((SmallEtale.toOver B S hS X.1).map (Limits.pullback.fst pr₁ pr₂))
      ((SmallEtale.toOver B S hS X.1).map pr₂)
      ((SmallEtale.toOver B S hS X.1).map pr₁) :=
    (IsPullback.of_hasPullback pr₁ pr₂).flip.map (SmallEtale.toOver B S hS X.1)
  have houter := (F.isPullback_siteMap (Limits.pullback.snd pr₁ pr₂)).paste_vert hbase
  rw [← (F.isPullback_siteMap (Limits.pullback.fst pr₁ pr₂)).w,
    ← (F.isPullback_siteMap pr₂).w] at houter
  exact houter.of_bot (F.siteMap_pullbackSnd_comp pr₁ pr₂) (F.isPullback_siteMap pr₁)

include hsq in
/-- **The two morphisms of the family over a relation of charts form an internal equivalence
relation of presheaves.**  All conditions are instances of the functoriality of the family,
applied to the diagonal, the swap and the composition of the relation of charts. -/
def equivalenceRelation :
    EquivalenceRelation (yoneda.map (F.siteMap pr₁)) (yoneda.map (F.siteMap pr₂)) where
  __ := F.jointlyMono₂_siteMap pr₁ pr₂ hsq
  r := yoneda.map (F.siteMap (chartRelationDiag pr₁ pr₂ hsq))
  reflexivity₁ := by
    rw [← CategoryTheory.Functor.map_comp, ← F.siteMap_comp, chartRelationDiag_comp_fst,
      F.siteMap_id, CategoryTheory.Functor.map_id]
  reflexivity₂ := by
    rw [← CategoryTheory.Functor.map_comp, ← F.siteMap_comp, chartRelationDiag_comp_snd,
      F.siteMap_id, CategoryTheory.Functor.map_id]
  s := yoneda.map (F.siteMap (chartRelationSwap pr₁ pr₂ hsq))
  symmetry₁ := by
    rw [← CategoryTheory.Functor.map_comp, ← F.siteMap_comp, chartRelationSwap_comp_fst]
  symmetry₂ := by
    rw [← CategoryTheory.Functor.map_comp, ← F.siteMap_comp, chartRelationSwap_comp_snd]
  c := ((F.isPullback_siteMap₂ pr₁ pr₂).map yoneda).cone
  isLimit := ((F.isPullback_siteMap₂ pr₁ pr₂).map yoneda).isLimit
  t := yoneda.map (F.siteMap (chartRelationOuter pr₁ pr₂ hsq))
  transitivity₁ := by
    change yoneda.map (F.siteMap (chartRelationOuter pr₁ pr₂ hsq)) ≫ yoneda.map (F.siteMap pr₁) =
      yoneda.map (F.siteMap (Limits.pullback.snd pr₁ pr₂)) ≫ yoneda.map (F.siteMap pr₁)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← F.siteMap_comp, ← F.siteMap_comp, chartRelationOuter_comp_fst]
  transitivity₂ := by
    change yoneda.map (F.siteMap (chartRelationOuter pr₁ pr₂ hsq)) ≫ yoneda.map (F.siteMap pr₂) =
      yoneda.map (F.siteMap (Limits.pullback.fst pr₁ pr₂)) ≫ yoneda.map (F.siteMap pr₂)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← F.siteMap_comp, ← F.siteMap_comp, chartRelationOuter_comp_snd]

include hsq in
/-- **The two morphisms of the family over a relation of charts form an étale equivalence
relation over `S`**, in the sense of Tag 02WS. -/
theorem isEtaleEquivalenceRelation :
    IsEtaleEquivalenceRelation (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) := by
  refine isEtaleEquivalenceRelation_of_yoneda B S hS _ _ (Iso.refl _) ?_
    (F.inverseImage_etale_siteMap pr₁) (F.inverseImage_etale_siteMap pr₂)
  simpa only [Iso.refl_hom, Category.id_comp] using
    (F.equivalenceRelation pr₁ pr₂ hsq).isEquivalenceRelation

/-! ### The quotient -/

/-- The quotient sheaf of the étale equivalence relation of the family, as a presheaf. -/
abbrev quotientPresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁))).obj

include hsq in
/-- **The quotient of the family is an algebraic space over `S`**, by Tag 02WW. -/
theorem isAlgebraicSpace_quotientPresheaf :
    IsAlgebraicSpace B S hS (F.quotientPresheaf pr₁ pr₂) :=
  have := F.isEtaleEquivalenceRelation pr₁ pr₂ hsq
  isAlgebraicSpace_quotient_unconditional B S hS _ _

/-- **The glued algebraic space** `F_X`: the quotient of the étale equivalence relation of the
family over a relation of étale charts. -/
def quotient : AlgebraicSpaces B S hS :=
  ⟨F.quotientPresheaf pr₁ pr₂, F.isAlgebraicSpace_quotientPresheaf pr₁ pr₂ hsq⟩

include hsq in
/-- The chart's morphism to `X`, read on the restricted functor of points, identifies the two
projections of the relation. -/
theorem sourceMap_comp_siteToSpace :
    Stacks.Groupoids.sourceMap (Over.post B.inclusion)
          (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫
        ((pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ F.siteToSpace V₂) =
      Stacks.Groupoids.targetMap (Over.post B.inclusion)
          (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫
        ((pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ F.siteToSpace V₂) := by
  rw [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap, relation_source_eq_post_map,
    relation_target_eq_post_map, ← Category.assoc, ← Category.assoc,
    whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom,
    whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom, Category.assoc, Category.assoc,
    F.siteMap_comp_siteToSpace, F.siteMap_comp_siteToSpace]

/-- **The structure morphism `F_X ⟶ X`**, which the chart's morphism `F(V₂) ⟶ V₂ ⟶ X` descends
to along the quotient map. -/
def quotientHom : F.quotient pr₁ pr₂ hsq ⟶ X :=
  ObjectProperty.homMk
    (Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ⟨X.1, X.property.isSheaf⟩
      ((pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ F.siteToSpace V₂)
      (F.sourceMap_comp_siteToSpace pr₁ pr₂ hsq)).hom

/-- The structure morphism restricts on the chart to the chart's own morphism to `X`. -/
theorem toQuotientSheaf_comp_quotientHom :
    Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫
        (F.quotientHom pr₁ pr₂ hsq).hom =
      (pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ F.siteToSpace V₂ :=
  Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc _ _ _ _ _ _

/-- The structure morphism is the only morphism to `X` restricting on the chart to the chart's
own morphism. -/
theorem quotientHom_unique (d : F.quotient pr₁ pr₂ hsq ⟶ X)
    (hd : Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫ d.hom =
      (pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ F.siteToSpace V₂) :
    d = F.quotientHom pr₁ pr₂ hsq := by
  refine ObjectProperty.hom_ext _ ?_
  exact congrArg (·.hom) (Stacks.Groupoids.quotientSheafDesc_unique (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁))
    ⟨X.1, X.property.isSheaf⟩
    ((pointsYonedaIso (Over.post B.inclusion) (F.site V₂)).hom ≫ F.siteToSpace V₂)
    (F.sourceMap_comp_siteToSpace pr₁ pr₂ hsq) ⟨d.hom⟩ hd)

/-! ### The chart of the glued space -/

/-- The chart `F(V₂) ⟶ F_X` of the glued space. -/
abbrev quotientChart : yoneda.obj (F.site V₂) ⟶ (F.quotient pr₁ pr₂ hsq).1 :=
  Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) (F.site V₂)
    (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁))

/-- The chart of the glued space is the quotient map of the étale equivalence relation. -/
theorem quotientChart_eq_quotientMap :
    F.quotientChart pr₁ pr₂ hsq = quotientMap B S hS (F.siteMap pr₂) (F.siteMap pr₁) :=
  (yonedaEquiv_symm_app_toQuotientSheaf _ _ _ _).symm

/-- **The chart of the glued space is étale**, after every representable base change. -/
theorem etale_quotientChart :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (F.quotientChart pr₁ pr₂ hsq) := by
  have := F.isEtaleEquivalenceRelation pr₁ pr₂ hsq
  rw [quotientChart_eq_quotientMap]
  exact quotientMap_etale_unconditional B S hS _ _

/-- **The chart of the glued space is surjective**, after every representable base change. -/
theorem surjective_quotientChart :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
      (F.quotientChart pr₁ pr₂ hsq) := by
  have := F.isEtaleEquivalenceRelation pr₁ pr₂ hsq
  rw [quotientChart_eq_quotientMap]
  exact quotientMap_surjective_unconditional B S hS _ _

/-! ### The cartesian square at the chart -/

/-- The structure morphisms of the family over `V'` and `V₂` commute with the source maps of the
two relations. -/
theorem post_siteToChart_comp_source :
    (Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V') ≫
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁)).source =
      (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)).source ≫
        (Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V₂) := by
  rw [relation_source_eq_post_map, relation_source_eq_post_map, ← Functor.map_comp,
    ← Functor.map_comp, (F.isPullback_siteMap pr₂).w]

/-- The structure morphisms of the family over `V'` and `V₂` commute with the target maps of the
two relations. -/
theorem post_siteToChart_comp_target :
    (Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V') ≫
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁)).target =
      (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)).target ≫
        (Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V₂) := by
  rw [relation_target_eq_post_map, relation_target_eq_post_map, ← Functor.map_comp,
    ← Functor.map_comp, (F.isPullback_siteMap pr₁).w]

/-- The square over the second projection, read in the schemes over `S`. -/
theorem isPullback_post_siteToChart :
    IsPullback ((Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V'))
      (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)).source
      (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
        ((SmallEtale.toOver B S hS X.1).map pr₁)).source
      ((Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V₂)) := by
  rw [relation_source_eq_post_map, relation_source_eq_post_map]
  exact ((F.isPullback_siteMap pr₂).flip).map (Over.post (X := B.obj hS) B.inclusion)

include hsq in
/-- **The glued space restricts on a surjective chart to the family over the chart**:
`F(V₂) = F_X ×_X V₂`.  This is Stacks 07S3 at the morphism of equivalence relations given by the
structure morphisms of the family over `V'` and `V₂`, composed with the identification
`V₂/V' ≅ X` of `AlgebraicGeometry.Space.exists_iso_chartQuotientSheaf`. -/
theorem isPullback_quotientHom
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      V₂.obj.hom) :
    IsPullback
      (Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (F.site V₂)
        (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)))
      (yoneda.map (F.siteToChart V₂)) (F.quotientHom pr₁ pr₂ hsq).hom V₂.obj.hom := by
  have := F.isEtaleEquivalenceRelation pr₁ pr₂ hsq
  have := isEquivalenceRelation_chartRelation B S hS X pr₁ pr₂ hsq
  obtain ⟨e, he⟩ := exists_iso_chartQuotientSheaf B S hS X pr₁ pr₂ hsq hsurj
  have hbase : Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) ((SmallEtale.toOver B S hS X.1).obj V₂)
        (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
          ((SmallEtale.toOver B S hS X.1).map pr₁)) ≫ e.inv = V₂.obj.hom := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have htqs := toQuotientSheaf_comp_of_quotientChart_comp (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion) ((SmallEtale.toOver B S hS X.1).obj V₂)
    (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
      ((SmallEtale.toOver B S hS X.1).map pr₁)) e.inv V₂.obj.hom hbase
  have h07S3 := Stacks.Groupoids.isPullback_toQuotientSheaf_of_subcanonical
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
    (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁))
    (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
      ((SmallEtale.toOver B S hS X.1).map pr₁))
    ((Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V'))
    ((Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V₂))
    (F.post_siteToChart_comp_source pr₁ pr₂) (F.post_siteToChart_comp_target pr₁ pr₂)
    (F.isPullback_post_siteToChart pr₁ pr₂)
  have hnu : (Stacks.Groupoids.quotientSheafMap (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁))
          (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
            ((SmallEtale.toOver B S hS X.1).map pr₁))
          ((Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V'))
          ((Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V₂))
          (F.post_siteToChart_comp_source pr₁ pr₂)
          (F.post_siteToChart_comp_target pr₁ pr₂)).hom ≫ e.inv =
      (F.quotientHom pr₁ pr₂ hsq).hom := by
    have key : Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
            (Over.post (X := B.obj hS) B.inclusion)
            (relation B S hS (F.siteMap pr₂) (F.siteMap pr₁)) ≫
          ((Stacks.Groupoids.quotientSheafMap (BigFppfOver.topology B S hS)
              (Over.post (X := B.obj hS) B.inclusion) _ _ _ _
              (F.post_siteToChart_comp_source pr₁ pr₂)
              (F.post_siteToChart_comp_target pr₁ pr₂)).hom ≫ e.inv) =
        (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) (F.site V₂)).hom ≫
          F.siteToSpace V₂ := by
      rw [← Category.assoc, Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafMap,
        Category.assoc, htqs, ← Category.assoc,
        whiskerLeft_yoneda_map_comp_pointsYonedaIso_hom, Category.assoc]
      rfl
    exact congrArg (fun m => m.hom) (F.quotientHom_unique pr₁ pr₂ hsq
      (ObjectProperty.homMk _) key)
  have hleft : IsPullback
      (Stacks.Groupoids.yonedaToPoints (Over.post (X := B.obj hS) B.inclusion) (F.site V₂))
      (yoneda.map (F.siteToChart V₂))
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft (yoneda.map
        ((Over.post (X := B.obj hS) B.inclusion).map (F.siteToChart V₂))))
      (Stacks.Groupoids.yonedaToPoints (Over.post (X := B.obj hS) B.inclusion)
        ((SmallEtale.toOver B S hS X.1).obj V₂)) :=
    IsPullback.of_horiz_isIso ⟨Stacks.Groupoids.yonedaToPoints_naturality
      (Over.post (X := B.obj hS) B.inclusion) (F.siteToChart V₂)⟩
  have hbot : IsPullback
      (Stacks.Groupoids.yonedaToPoints (Over.post (X := B.obj hS) B.inclusion)
          ((SmallEtale.toOver B S hS X.1).obj V₂) ≫
        Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion)
          (relation B S hS ((SmallEtale.toOver B S hS X.1).map pr₂)
            ((SmallEtale.toOver B S hS X.1).map pr₁)))
      (𝟙 (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V₂))) e.inv V₂.obj.hom :=
    IsPullback.of_vert_isIso ⟨by rwa [Category.id_comp]⟩
  have hpaste := (hleft.paste_horiz h07S3).paste_vert hbot
  rwa [Category.comp_id, hnu] at hpaste

end Relation

end CartesianChartFamily

end AlgebraicGeometry.Space

end
