module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.DerivedPushforwardSheafify
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSiteFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Higher direct images on the lisse-étale site of an algebraic stack

Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks over a scheme `S` in a big fppf site
`B`. It restricts to a continuous and cocontinuous functor of the lisse-étale sites, hence
induces a morphism of topoi whose direct image is `Functor.sheafPushforwardCocontinuous` along
that restriction. This file identifies its higher direct images: `Rᵖ f'_* ℋ` is the sheaf
associated to the `p`-th right derived *presheaf* direct image of `ℋ`, naturally in `ℋ`. That is
the lisse-étale case of **Stacks 0GR2**.

The mathematics is not specific to these sites and is proved for an arbitrary cocontinuous
functor of sites in
`CategoryTheory.Functor.rightDerivedSheafPushforwardCocontinuousIso`; what this file supplies is
that the lisse-étale site of an algebraic stack satisfies that result's hypotheses, and the
instantiation.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.rightDerived_sheafPushforward_iso_sheafify_derivedPresheaf`:
  the lisse-étale case of Stacks 0GR2.

## Implementation notes

The lisse-étale site of an algebraic stack is a category of type `Type (u + 1)` whose morphisms
live in `Type u`, so it is essentially small at every coefficient universe `max (u + 1) a`.
Abelian sheaves on it then form a Grothendieck abelian category and in particular have enough
injectives, which is what makes the right derived functors available; those are the hypotheses
the general result leaves open.

This is the lisse-étale twin of
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfHigherDirectImage.lean`. Every instance it needs is
already available for an arbitrary site — sheafification from
`Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp` and Grothendieck abelianness from
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall` — so the only input specific to
the smooth case is the cocontinuity of the restriction,
`AlgebraicGeometry.Stack.LisseEtale.siteFunctor_isCocontinuous`.

`StacksCore.Tactic.StacksAttribute` is reachable transitively and is retained deliberately: it
supplies the attribute this file applies, so importing it directly records the dependency.

The coefficient universe `a` is free, and because it occurs only inside `max (u + 1) a` it is
not determined by the explicit arguments. Three of the applications below therefore write their
universe lists out; for the rest unification fixes every universe from the explicit arguments
and no list is written.

## References

* [Stacks Project, Tag 0GR2](https://stacks.math.columbia.edu/tag/0GR2)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace AlgebraicGeometry.Stack.LisseEtale

open CategoryTheory AlgebraicGeometry.Stack

universe u w a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
  (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- **Stacks 0GR2, the lisse-étale case.** The `p`-th higher direct image along the morphism of
lisse-étale topoi induced by a smooth 1-morphism of algebraic stacks is the sheaf associated to
the `p`-th right derived presheaf direct image, naturally in the abelian sheaf of coefficients.

The lisse-étale site of an algebraic stack is a category of type `Type (u + 1)` with morphisms in
`Type u`, so it is essentially small at any coefficient universe `max (u + 1) a`; abelian
sheaves on it then form a Grothendieck abelian category and in particular have enough
injectives, which is what makes the right derived functors available. -/
@[stacks 0GR2 "lisse-étale sheafification formula"]
public theorem rightDerived_sheafPushforward_iso_sheafify_derivedPresheaf (p : ℕ) :
    letI : (siteFunctor.{u, w} B S hS f hf).1.IsCocontinuous
        (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) :=
      siteFunctor_isCocontinuous.{u, w} B S hS f hf
    letI : HasSheafify (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a} :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
    letI : HasSheafify (topology.{u, w} B S hS 𝒴) AddCommGrpCat.{max (u + 1) a} :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
    letI : EssentiallySmall.{max (u + 1) a} (LisseEtale.{u, w} B S hS 𝒳) :=
      essentiallySmallSelf (LisseEtale.{u, w} B S hS 𝒳)
    letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall
      (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a}
    letI := IsGrothendieckAbelian.enoughInjectives
      (C := Sheaf (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a})
    letI := Functor.sheafPushforwardCocontinuous_additive.{u + 1, u + 1, u, u, a}
      (siteFunctor.{u, w} B S hS f hf).1
      (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴)
    Nonempty
      (((siteFunctor.{u, w} B S hS f hf).1.sheafPushforwardCocontinuous
          AddCommGrpCat.{max (u + 1) a} (topology.{u, w} B S hS 𝒳)
          (topology.{u, w} B S hS 𝒴)).rightDerived p ≅
        Functor.derivedPresheafDirectImage.{u + 1, u + 1, u, u, a}
            (topology.{u, w} B S hS 𝒳) (siteFunctor.{u, w} B S hS f hf).1 p ⋙
          presheafToSheaf (topology.{u, w} B S hS 𝒴) AddCommGrpCat.{max (u + 1) a}) := by
  have : (siteFunctor.{u, w} B S hS f hf).1.IsCocontinuous
      (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) :=
    siteFunctor_isCocontinuous.{u, w} B S hS f hf
  have : HasSheafify (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
  have : HasSheafify (topology.{u, w} B S hS 𝒴) AddCommGrpCat.{max (u + 1) a} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
  have : EssentiallySmall.{max (u + 1) a} (LisseEtale.{u, w} B S hS 𝒳) :=
    essentiallySmallSelf (LisseEtale.{u, w} B S hS 𝒳)
  have := Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a}
  have := IsGrothendieckAbelian.enoughInjectives
    (C := Sheaf (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a})
  exact ⟨Functor.rightDerivedSheafPushforwardCocontinuousIso.{u + 1, u + 1, u, u, a}
    (siteFunctor.{u, w} B S hS f hf).1 (topology.{u, w} B S hS 𝒳)
    (topology.{u, w} B S hS 𝒴) p⟩

end AlgebraicGeometry.Stack.LisseEtale

end
