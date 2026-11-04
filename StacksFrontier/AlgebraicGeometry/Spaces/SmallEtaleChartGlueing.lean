module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheaves
public import StacksFrontier.CategoryTheory.Sites.Glueing.AbsoluteGlueingAnySite

/-!
# Chartwise glueing data for sheaves on an algebraic space

Stacks 03LS describes a sheaf of sets on the small étale site of an algebraic space `X` by its
restrictions to the étale scheme charts of `X`, together with the comparison isomorphisms between
successive restrictions.  This file provides the two halves of that description that do not need
the identification of a chart's small étale site with a slice of `X`'s:

* the glueing description of Stacks 0GWK at the small étale site itself, where the sheaves are
  carried by the *slices* `X_étale/U` rather than by the small étale sites of the charts, and
* the category `AlgebraicGeometry.Space.ChartGlueingData` in which Stacks 03LS states its
  equivalence, whose objects carry a sheaf on the small étale site of each chart together with
  the transition isomorphisms along `AlgebraicGeometry.Space.chartInverseImage` and the cocycle
  condition expressed by `AlgebraicGeometry.Space.chartInverseImageComp`.

## Main definitions

* `AlgebraicGeometry.Space.ChartGlueingData`: a sheaf of sets on the small étale site of every
  étale scheme chart of `X`, transition isomorphisms along the chartwise inverse images, and the
  cocycle condition relating them to
  `AlgebraicGeometry.Space.chartInverseImageComp`.
* `AlgebraicGeometry.Space.ChartGlueingData.Hom`: a morphism of chartwise glueing data, and the
  category structure it defines.

## Main results

* `AlgebraicGeometry.Space.smallEtaleGlueingEquivalence`: sheaves of sets on the small étale site
  of an algebraic space are equivalent to absolute glueing data on that site, i.e. to a sheaf on
  each slice `X_étale/U` together with transition isomorphisms satisfying the cocycle condition.
* `AlgebraicGeometry.Space.smallEtaleGlueingEquivalence_functor_obj_sheaf` and
  `AlgebraicGeometry.Space.smallEtaleGlueingEquivalence_functor_map_app`: the equivalence is the
  canonical one, sending a sheaf to the family of its restrictions to the slices, by `rfl`.

## Implementation notes

`AlgebraicGeometry.Space.smallEtaleGlueingEquivalence` is an instance of
`CategoryTheory.SiteGlueing.canonicalEquivalence`, Stacks 0GWK.  Its generality is needed here
and is not a universe accident that a transport would repair: the small étale site of an
algebraic space over a scheme of universe `u` is a `CategoryTheory.Category.{u, u + 1}` whose
sheaves of sets are valued in `Type (u + 1)`, so neither of the two coincidences that
`CategoryTheory.SmallCategory` asserts holds.

What is *not* proved here is the equivalence of Stacks 03LS itself, between sheaves on the small
étale site of `X` and `AlgebraicGeometry.Space.ChartGlueingData`; it is
`AlgebraicGeometry.Space.chartGlueingEquivalence`, downstream.  Two inputs were missing when
this file was written, and both are now supplied downstream:

* that `AlgebraicGeometry.Space.chartRestriction U` agrees, through the equivalence of
  Stacks 04M0, with restriction `j_U^{-1}` to the slice `X_étale/U`, and likewise that
  `AlgebraicGeometry.Space.chartInverseImage f` agrees with
  `CategoryTheory.GrothendieckTopology.overMapPullback` along `f`.  This is
  `AlgebraicGeometry.Space.chartRestriction_overPullbackIso` and
  `AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure`;
* that the canonical chartwise datum of a sheaf satisfies the cocycle condition
  `AlgebraicGeometry.Space.ChartGlueingData.transition_comp`.  That condition is stated through
  `AlgebraicGeometry.Space.chartInverseImageComp`, which is an
  `CategoryTheory.Adjunction.leftAdjointUniq`, so it is the adjoint mate of an associativity
  statement about `AlgebraicGeometry.Space.smallToposMorphism_comp`.  That associativity is
  `AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_assoc`, and the cocycle is
  `AlgebraicGeometry.Space.chartRestrictionComp_cocycle`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCanonicalGlueing`.

What the equivalence further needed is neither of those but their *compatibility*: that the two
comparisons of the first item carry the composition isomorphisms
`AlgebraicGeometry.Space.chartRestrictionComp` and
`AlgebraicGeometry.Space.chartInverseImageComp` to `CategoryTheory.Sheaf.pushforwardOverMapIso`
and `CategoryTheory.GrothendieckTopology.overMapPullbackComp`.  That is what transports a
chartwise datum, or a morphism of chartwise data, to the slice-indexed form below, and it is a
separate pair of theorems — the associativity above does not supply them —
`AlgebraicGeometry.Space.chartInverseImage_overMapPullbackIso_comp` and
`AlgebraicGeometry.Space.chartRestriction_overPullbackIso_comp` in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartDictionaryCoherence`.  With them the
equivalence of Stacks 03LS is proved,
`AlgebraicGeometry.Space.chartGlueingEquivalence` in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartGlueingEquivalence`.

No part of this is a universe obstruction, and none of it is supplied by the glueing equivalence
below:
`CategoryTheory.SiteGlueing.GlueingData` of the small étale site of `X` is the slice-indexed
form of the datum, and the content that remains is exactly the comparison of the two readings of
restriction to a chart.

## References

* [Stacks Project, Tag 03LS](https://stacks.math.columbia.edu/tag/03LS)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Glueing along the slices of the small étale site -/

/-- Sheaves of sets on the small étale site of an algebraic space are equivalent to absolute
glueing data on that site: a sheaf on each slice `X_étale/U` at an étale scheme chart `U`,
together with transition isomorphisms along the slice restrictions satisfying the cocycle
condition.

This is Stacks 0GWK applied to the small étale site, which is possible because
`CategoryTheory.SiteGlueing.canonicalEquivalence` carries no smallness hypothesis. -/
noncomputable def smallEtaleGlueingEquivalence :
    Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ≌
      SiteGlueing.GlueingData.{u + 1} (SmallEtale.topology B S hS X.1) :=
  SiteGlueing.canonicalEquivalence (SmallEtale.topology B S hS X.1)

/-- The glueing equivalence of the small étale site is the canonical one: the datum attached to a
sheaf carries, on the slice at a chart `U`, the restriction of that sheaf to the slice. -/
theorem smallEtaleGlueingEquivalence_functor_obj_sheaf
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (U : SmallEtale B S hS X.1) :
    ((smallEtaleGlueingEquivalence B S hS X).functor.obj F).sheaf U = F.over U := rfl

/-- On morphisms, the glueing equivalence of the small étale site is restriction to the slices. -/
theorem smallEtaleGlueingEquivalence_functor_map_app
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))} (ψ : F ⟶ G)
    (U : SmallEtale B S hS X.1) :
    ((smallEtaleGlueingEquivalence B S hS X).functor.map ψ).app U =
      ((SmallEtale.topology B S hS X.1).overPullback (Type (u + 1)) U).map ψ := rfl

/-! ### Chartwise glueing data -/

/-- **Chartwise glueing data for sheaves of sets on an algebraic space** (Stacks 03LS): a sheaf
of sets on the small étale site of every étale scheme chart of `X`, an isomorphism
`c_f : f^{-1}F_U ≅ F_V` for every morphism `f : V ⟶ U` of charts, where `f^{-1}` is the small
étale inverse image of Stacks 03G2, part (3), along the represented morphism of algebraic spaces,
subject to the cocycle condition `c_g ∘ g^{-1}c_f = c_{g ≫ f}` read through the canonical
comparison `AlgebraicGeometry.Space.chartInverseImageComp`. -/
structure ChartGlueingData where
  /-- the sheaf on the small étale site of the chart `U` -/
  sheaf (U : SmallEtale B S hS X.1) :
    Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X U).1) (Type (u + 1))
  /-- the transition isomorphism `f^{-1}F_U ≅ F_V` for a morphism of charts `f : V ⟶ U` -/
  transition {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartInverseImage B S hS X f).obj (sheaf U) ≅ sheaf V
  /-- the cocycle condition, stated through the canonical comparison of successive chartwise
  inverse images with the inverse image along the composite -/
  transition_comp {W V U : SmallEtale B S hS X.1} (f : V ⟶ U) (g : W ⟶ V) :
    (chartInverseImage B S hS X g).map (transition f).hom ≫ (transition g).hom =
      (chartInverseImageComp B S hS X f g).hom.app (sheaf U) ≫ (transition (g ≫ f)).hom

namespace ChartGlueingData

/-- A morphism of chartwise glueing data: a family of morphisms of the chart sheaves commuting
with the transition isomorphisms. -/
@[ext]
structure Hom (D E : ChartGlueingData B S hS X) where
  /-- the morphism `F_U ⟶ G_U` on the small étale site of the chart `U` -/
  app (U : SmallEtale B S hS X.1) : D.sheaf U ⟶ E.sheaf U
  /-- compatibility with the transition isomorphisms -/
  w {V U : SmallEtale B S hS X.1} (f : V ⟶ U) :
    (chartInverseImage B S hS X f).map (app U) ≫ (E.transition f).hom =
      (D.transition f).hom ≫ app V

attribute [reassoc] Hom.w

/-- Chartwise glueing data form a category, a morphism being a family of morphisms of the chart
sheaves compatible with the transition isomorphisms. -/
instance : Category (ChartGlueingData B S hS X) where
  Hom := Hom B S hS X
  id D := { app := fun _ => 𝟙 _, w := fun _ => by simp }
  comp α β :=
    { app := fun U => α.app U ≫ β.app U
      w := fun f => by
        rw [Functor.map_comp, Category.assoc, Hom.w, ← Category.assoc, Hom.w, Category.assoc] }

/-- The identity morphism of a chartwise glueing datum is the identity on every chart. -/
@[simp] lemma id_app (D : ChartGlueingData B S hS X) (U : SmallEtale B S hS X.1) :
    Hom.app (𝟙 D) U = 𝟙 (D.sheaf U) := rfl

/-- Morphisms of chartwise glueing data compose chart by chart. -/
@[simp] lemma comp_app {D E F : ChartGlueingData B S hS X} (α : D ⟶ E) (β : E ⟶ F)
    (U : SmallEtale B S hS X.1) :
    Hom.app (α ≫ β) U = α.app U ≫ β.app U := rfl

/-- Two morphisms of chartwise glueing data that agree on every chart are equal. -/
@[ext] lemma hom_ext {D E : ChartGlueingData B S hS X} {α β : D ⟶ E}
    (h : ∀ U, α.app U = β.app U) : α = β :=
  Hom.ext (funext h)

/-- A morphism of chartwise glueing data all of whose components are isomorphisms is an
isomorphism. -/
lemma isIso_of_isIso_app {D E : ChartGlueingData B S hS X} (α : D ⟶ E)
    (h : ∀ U, IsIso (α.app U)) : IsIso α := by
  refine ⟨⟨{ app := fun U => inv (α.app U), w := fun {V U} f => ?_ }, ?_, ?_⟩⟩
  · have hα := α.w f
    rw [IsIso.eq_comp_inv, Category.assoc, ← hα, ← Category.assoc, ← Functor.map_comp,
      IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · exact hom_ext B S hS X fun U => IsIso.hom_inv_id (α.app U)
  · exact hom_ext B S hS X fun U => IsIso.inv_hom_id (α.app U)

end ChartGlueingData

end AlgebraicGeometry.Space

end
