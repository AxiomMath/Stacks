module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModulePushforwardComparison

/-!
# The direct image of modules at abelian coefficients is base change of charts

Let `f : X ⟶ Y` be a *representable* morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  `AlgebraicGeometry.Space.modulePushforwardChartIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean` identifies the
direct image of modules of Stacks 03LU along `f` with the concrete direct image taken along base
change of étale scheme charts.  This file reads that identification through the forgetful functor
to sheaves of **abelian groups**:
```
  f_*M, forgotten  =  (M, forgotten) restricted along chart base change.
```

## Why the abelian reading is wanted

Stacks 04E5, part (2) — full faithfulness of the direct image along a closed immersion — is
proved in this tree as
`AlgebraicGeometry.Space.fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion`
(`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionChartBaseChangeDense.lean`), and it is
proved for *restriction along chart base change*, `CategoryTheory.Functor.`
`sheafPushforwardContinuous` of `AlgebraicGeometry.Space.smallBaseChange` at
`AddCommGrpCat`.  Every statement about the conormal sequence is about
`AlgebraicGeometry.Space.modulePushforward` instead, which is built from the right Kan extension
`AlgebraicGeometry.Space.smallEtaleDirectImageRan`.  The comparison of the two is available
elsewhere at sheaves of sets, at sheaves of commutative rings and at sheaves of modules; this
file supplies it at sheaves of abelian groups — which is the one category 04E5, part (2) is
stated in.  `AlgebraicGeometry.Space.abelianPushforwardPreimage` is the resulting application of
04E5, part (2).

## Main definitions

* `AlgebraicGeometry.Space.abelianPushforwardChartIso`: **the direct image of modules along a
  representable morphism, read in sheaves of abelian groups, is restriction along base change of
  étale scheme charts.**
* `AlgebraicGeometry.Space.abelianPushforwardPreimage`: **Stacks 04E5, part (2) transported to
  `AlgebraicGeometry.Space.modulePushforward`.**  For a closed immersion `f : X ⟶ Y` and
  `𝒪_X`-modules `M`, `N`, every morphism `f_*M ⟶ f_*N` of sheaves of abelian groups on the small
  étale site of `Y` is the direct image of a morphism `M ⟶ N` of sheaves of abelian groups on the
  small étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.abelianPushforwardChartIso_hom_app`: the comparison is the
  module-level comparison forgotten to abelian groups, by `rfl`; it adds no transport of its own.
* `AlgebraicGeometry.Space.abelianPushforward_map_abelianPushforwardPreimage` and
  `AlgebraicGeometry.Space.abelianPushforwardPreimage_unique`: the transported morphism does push
  forward to the given one, and is the only morphism that does.

## Implementation notes

**The general comparison is not restated here.**  Pushing a sheaf of modules forward and then
forgetting to abelian groups *is* forgetting and then restricting, by `Iso.refl`:
`CategoryTheory.SheafOfModules.pushforward` is the restriction of the underlying presheaf
followed by a restriction of scalars, and restriction of scalars does not change the underlying
abelian group.  That is
`Stacks.Cohomology.SiteModulePushforward.AnySite.pushforwardCompToSheafIso'` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/ModulePushforwardComparison.lean`,
which was stated with the ring and module universes both pinned to `max u₁ v₁`, the universe its
derived-functor consumers need.  Nothing in its proof uses that; it has been generalized in
place to free universes, which is what makes it applicable at the small étale site, where the
objects live one universe above the morphisms while the structure sheaf and its modules live at
the lower one.  No second copy of the statement exists.

**The continuity instance.** `CategoryTheory.Functor.IsContinuous` is a `Prop`, so the instance
installed here as a local instance and the one
`AlgebraicGeometry.Space.fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion` carries in
a `letI` are equal by proof irrelevance; the two spellings of the restriction functor are
therefore the same functor and no comparison between them is needed.

## No tag is registered

Stacks 03LU is registered on `AlgebraicGeometry.Space.modulePushforward`, Stacks 03G2, part (4)
on `AlgebraicGeometry.Space.smallBaseChange`, and Stacks 04E5, part (2) on
`AlgebraicGeometry.Space.fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion`.  Reading
a known identification of functors in a larger category of coefficients, and conjugating a
known full-faithfulness statement by it, are proof steps rather than clauses of a tag — exactly
as for `AlgebraicGeometry.Space.modulePushforwardChartIso` itself, which carries no tag for the
reason its own implementation notes give.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (4), base change
  of étale scheme charts.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the direct image of
  modules.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (2), full
  faithfulness of the direct image along a closed immersion on sheaves of abelian groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The direct image of modules along a representable morphism of algebraic spaces, read in
sheaves of abelian groups, is restriction along base change of étale scheme charts.**

This is `AlgebraicGeometry.Space.modulePushforwardChartIso` followed by the general fact that the
direct image of sheaves of modules forgets to the restriction of the underlying abelian sheaf. -/
noncomputable def abelianPushforwardChartIso (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    modulePushforward B S hS f ⋙ SheafOfModules.toSheaf (structureRingSheaf B S hS Y) ≅
      SheafOfModules.toSheaf (structureRingSheaf B S hS X) ⋙
        (smallBaseChange B S hS f hf).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  Functor.isoWhiskerRight (modulePushforwardChartIso B S hS f hf) _ ≪≫
    Stacks.Cohomology.SiteModulePushforward.AnySite.pushforwardCompToSheafIso' _ _ _ _ _
      (smallBaseChangeSharp B S hS f hf)

/-- **The abelian comparison is the module-level comparison, forgotten.**  Its component at a
module is `CategoryTheory.SheafOfModules.toSheaf` applied to the component of
`AlgebraicGeometry.Space.modulePushforwardChartIso`; forgetting the module structure adds no
transport of its own, so a consumer reads the abelian comparison on sections through the
module-level one.

This holds by `rfl`, unlike the corresponding equation for the module-level comparison itself,
whose implementation notes record that spelling it out does not fit the default heartbeat
budget: the two sides here are compared in `Sheaf _ AddCommGrpCat`, where the underlying
presheaf of the direct image of a module is the restricted presheaf on the nose. -/
theorem abelianPushforwardChartIso_hom_app (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    (abelianPushforwardChartIso B S hS f hf).hom.app M =
      (SheafOfModules.toSheaf (structureRingSheaf B S hS Y)).map
        ((modulePushforwardChartIso B S hS f hf).hom.app M) :=
  rfl

/-! ### Stacks 04E5, part (2), for the direct image of modules -/

section ClosedImmersion

variable (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
  (M N : Modules.{u, u} B S hS X.1 X.2)

/-- **Stacks 04E5, part (2), transported to `AlgebraicGeometry.Space.modulePushforward`.**  For a
closed immersion `f : X ⟶ Y` of algebraic spaces, a morphism `f_*M ⟶ f_*N` of sheaves of abelian
groups between the direct images of two `𝒪_X`-modules comes from a morphism `M ⟶ N` of sheaves of
abelian groups on the small étale site of `X`.

The direct image here is the one of Stacks 03LU; 04E5, part (2) is proved for restriction along
chart base change, and `AlgebraicGeometry.Space.abelianPushforwardChartIso` is what carries it
over.  `AlgebraicGeometry.Space.abelianPushforward_map_abelianPushforwardPreimage` is the
factorization and `AlgebraicGeometry.Space.abelianPushforwardPreimage_unique` its uniqueness. -/
noncomputable def abelianPushforwardPreimage
    (g : (SheafOfModules.toSheaf (structureRingSheaf B S hS Y)).obj
        ((modulePushforward B S hS f).obj M) ⟶
      (SheafOfModules.toSheaf (structureRingSheaf B S hS Y)).obj
        ((modulePushforward B S hS f).obj N)) :
    (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj M ⟶
      (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj N :=
  (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u} B S hS f hf).preimage
    ((abelianPushforwardChartIso B S hS f hf.rep).inv.app M ≫ g ≫
      (abelianPushforwardChartIso B S hS f hf.rep).hom.app N)

/-- The morphism produced by `AlgebraicGeometry.Space.abelianPushforwardPreimage` does push
forward to the given one. -/
theorem abelianPushforward_map_abelianPushforwardPreimage
    (g : (SheafOfModules.toSheaf (structureRingSheaf B S hS Y)).obj
        ((modulePushforward B S hS f).obj M) ⟶
      (SheafOfModules.toSheaf (structureRingSheaf B S hS Y)).obj
        ((modulePushforward B S hS f).obj N)) :
    (abelianPushforwardChartIso B S hS f hf.rep).hom.app M ≫
        ((smallBaseChange B S hS f hf.rep).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).map
          (abelianPushforwardPreimage B S hS f hf M N g) =
      g ≫ (abelianPushforwardChartIso B S hS f hf.rep).hom.app N := by
  rw [abelianPushforwardPreimage,
    (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u} B S hS f hf).map_preimage]
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- `AlgebraicGeometry.Space.abelianPushforwardPreimage` is the only morphism whose direct image
is the given one: the direct image along a closed immersion is faithful on abelian sheaves. -/
theorem abelianPushforwardPreimage_unique
    (g : (SheafOfModules.toSheaf (structureRingSheaf B S hS Y)).obj
        ((modulePushforward B S hS f).obj M) ⟶
      (SheafOfModules.toSheaf (structureRingSheaf B S hS Y)).obj
        ((modulePushforward B S hS f).obj N))
    (χ : (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj M ⟶
      (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj N)
    (hχ : (abelianPushforwardChartIso B S hS f hf.rep).hom.app M ≫
        ((smallBaseChange B S hS f hf.rep).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).map χ =
      g ≫ (abelianPushforwardChartIso B S hS f hf.rep).hom.app N) :
    χ = abelianPushforwardPreimage B S hS f hf M N g := by
  exact (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u}
    B S hS f hf).map_injective ((cancel_epi _).1 (hχ.trans
      (abelianPushforward_map_abelianPushforwardPreimage B S hS f hf M N g).symm))

end ClosedImmersion

end AlgebraicGeometry.Space

end
