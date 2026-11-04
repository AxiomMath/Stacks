module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.DerivedPushforwardFibreCohomology

/-!
# Higher direct images on the flat-fppf site, through the cohomology of the fibres

Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks over a scheme `S` in a big fppf site
`B`, and `f'` the induced morphism of flat-fppf topoi (Stacks 07AT). For an object `y` of
`𝒴_{flat,fppf}`, lying over a scheme `V`, the category `(V ×_{y, 𝒴} 𝒳)'` of the source is the
full subcategory of `V ×_{y, 𝒴} 𝒳` on the objects whose morphism to `𝒳` is flat; as the proof of
Stacks 0GR2 records, its objects are the pairs `(x, φ)` of an object `x` of `𝒳_{flat,fppf}` and
a morphism `φ : f(x) ⟶ y` of `𝒴`, and it is the localization of `𝒳_{flat,fppf}` at the sheaf
`(f')⁻¹ h_y`, with `pr'` the localization morphism. That is the fibre site
`CategoryTheory.Functor.DirectImageFibre.fibre` of the restriction of `f` to the flat-fppf
sites over `y`, with the topology of Stacks 0791 and the restriction `pr'⁻¹` along its
projection.

This file states **Stacks 0GR2** in the flat-fppf case as the source does:

`Rᵖ f'_* ℋ = sheaf associated to y ↦ Hᵖ((V ×_{y, 𝒴} 𝒳)', (pr')⁻¹ ℋ)`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.rightDerived_sheafPushforward_iso_sheafify_fibreCohomology`:
  `Rᵖ f'_*` is the sheafification of the `p`-th right derived presheaf direct image, and the
  value of that presheaf at `y` is the cohomology of the fibre site over `y`, both naturally in
  `ℋ`.

## Implementation notes

The first half is the base's
`AlgebraicGeometry.Stack.FlatFppf.rightDerived_sheafPushforward_iso_sheafify_derivedPresheaf`;
the second is the general
`CategoryTheory.Functor.DirectImageFibre.derivedPresheafDirectImageEvaluationIso`, which holds
for any functor of sites into a category with the same morphism universe. Only the instances of
the source and target sites at the coefficient universe `max (u + 1) a` are specific here.

## References

* [Stacks Project, Tag 0GR2](https://stacks.math.columbia.edu/tag/0GR2)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

open CategoryTheory AlgebraicGeometry.Stack CategoryTheory.Functor.DirectImageFibre

universe u w a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
  (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsFlat B S hS f)

/-- **Stacks 0GR2, the flat-fppf case.** Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic
stacks and `f'` the induced morphism of flat-fppf topoi. For every `p` and every abelian sheaf
`ℋ` on `𝒳_{flat,fppf}`,

`Rᵖ f'_* ℋ = sheaf associated to y ↦ Hᵖ((V ×_{y, 𝒴} 𝒳)', (pr')⁻¹ ℋ)`.

Precisely: `Rᵖ f'_*` is the sheafification of the presheaf-valued functor
`derivedPresheafDirectImage`, and for every object `y` of `𝒴_{flat,fppf}` the value at `y` of
that presheaf is `Hᵖ` of the fibre site `(V ×_{y, 𝒴} 𝒳)'` — the pairs `(x, φ : f(x) ⟶ y)`, i.e.
the localization of `𝒳_{flat,fppf}` at `(f')⁻¹ h_y` — with coefficients in the restriction
`(pr')⁻¹ ℋ`, both naturally in `ℋ`. -/
@[stacks 0GR2 "flat-fppf case: Rᵖf'_*ℋ is the sheaf associated to y ↦ Hᵖ((V ×_y 𝒳)', pr'⁻¹ℋ)"]
public theorem rightDerived_sheafPushforward_iso_sheafify_fibreCohomology (p : ℕ) :
    letI : (siteFunctor.{u, w} B S hS f hf).1.IsCocontinuous
        (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) :=
      siteFunctor_isCocontinuous.{u, w} B S hS f hf
    letI : HasSheafify (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a} :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
    letI : HasSheafify (topology.{u, w} B S hS 𝒴) AddCommGrpCat.{max (u + 1) a} :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
    letI : EssentiallySmall.{max (u + 1) a} (FlatFppf.{u, w} B S hS 𝒳) :=
      essentiallySmallSelf (FlatFppf.{u, w} B S hS 𝒳)
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
            presheafToSheaf (topology.{u, w} B S hS 𝒴) AddCommGrpCat.{max (u + 1) a}) ∧
      ∀ y : FlatFppf.{u, w} B S hS 𝒴,
        letI := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, max (u + 1) a}
          (J := fibreTopology (topology.{u, w} B S hS 𝒳) (siteFunctor.{u, w} B S hS f hf).1 y)
        letI := Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, max (u + 1) a}
          (J := fibreTopology (topology.{u, w} B S hS 𝒳) (siteFunctor.{u, w} B S hS f hf).1 y)
        Nonempty
          (Functor.derivedPresheafDirectImage.{u + 1, u + 1, u, u, a}
                (topology.{u, w} B S hS 𝒳) (siteFunctor.{u, w} B S hS f hf).1 p ⋙
              (evaluation (FlatFppf.{u, w} B S hS 𝒴)ᵒᵖ AddCommGrpCat.{max (u + 1) a}).obj
                (op y) ≅
            fibreRestriction.{u + 1, u + 1, u, a} (topology.{u, w} B S hS 𝒳)
                (siteFunctor.{u, w} B S hS f hf).1 y ⋙
              Sheaf.functorH.{max (u + 1) a, max (u + 1) a, u, u + 1}
                (fibreTopology (topology.{u, w} B S hS 𝒳) (siteFunctor.{u, w} B S hS f hf).1 y)
                p) := by
  refine ⟨rightDerived_sheafPushforward_iso_sheafify_derivedPresheaf.{u, w, a} B S hS f hf p,
    fun y => ?_⟩
  have : HasSheafify (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
  have : EssentiallySmall.{max (u + 1) a} (FlatFppf.{u, w} B S hS 𝒳) :=
    essentiallySmallSelf (FlatFppf.{u, w} B S hS 𝒳)
  have := Sheaf.isGrothendieckAbelian_of_essentiallySmall
    (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a}
  have := IsGrothendieckAbelian.enoughInjectives
    (C := Sheaf (topology.{u, w} B S hS 𝒳) AddCommGrpCat.{max (u + 1) a})
  exact ⟨derivedPresheafDirectImageEvaluationIso.{u + 1, u + 1, u, a}
    (topology.{u, w} B S hS 𝒳) (siteFunctor.{u, w} B S hS f hf).1 y p⟩

end AlgebraicGeometry.Stack.FlatFppf

end
