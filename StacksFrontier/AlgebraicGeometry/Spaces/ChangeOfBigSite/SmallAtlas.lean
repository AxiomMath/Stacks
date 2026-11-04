module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds

/-!
# Algebraic spaces with a small étale atlas descend to the smaller big site

Let `B ⊆ B'` be big fppf sites (`AlgebraicGeometry.IsContained`). An algebraic space `X'` over
`S` on the larger site which receives a surjective étale morphism `U ⟶ X'` from an object `U`
of the smaller site lies in the essential image of the inverse image functor of Stacks 04W1
(`AlgebraicGeometry.changeBigSite`).

By the criterion of Stacks 04W1 (`AlgebraicGeometry.mem_essentialImage_changeBigSite_iff`) it is
enough to find a small object surjecting onto the kernel pair `R = U ×_{X'} U`. The diagonal of
`X'` is representable, so `R` is a scheme, and `R ⟶ U × U` is a monomorphism locally of finite
type (`AlgebraicGeometry.Space.locallyOfFiniteType_and_mono_toScheme_kernelPairToProd`). The
size of `U × U` is below the cutoff of the smaller site, and a monomorphism into a scheme of
size `κ` has source of size at most `max (2 ^ 2 ^ κ) κ`, which is again below the cutoff since
the cutoff is a strong limit; so `R` is itself an object of the smaller site.

## Main results

* `AlgebraicGeometry.Space.mem_essentialImage_changeBigSite_of_etale_surjective`: an algebraic
  space on the larger site with a surjective étale atlas from an object of the smaller site
  descends.

## References

* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **An algebraic space with a small surjective étale atlas descends to the smaller site.**
If `f : U ⟶ X'` is surjective and étale with `U` an object of the smaller site, then the kernel
pair of `f` is a scheme of the smaller site as well, being a subscheme of `U × U`, so `X'` lies
in the essential image of the change of big site by Stacks 04W1. -/
theorem mem_essentialImage_changeBigSite_of_etale_surjective
    (X' : AlgebraicSpaces B' S (largerContains h hS)) (U : BigFppfOver B S hS)
    (f : yoneda.obj ((inclusionOver h S hS).obj U) ⟶ X'.obj)
    (hfs : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS))) f)
    (hfe : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B' S (largerContains h hS))) f) :
    ∃ X : AlgebraicSpaces B S hS, Nonempty ((changeBigSite B B' h S hS).obj X ≅ X') := by
  let hS' : B'.Contains S := largerContains h hS
  let U' : BigFppfOver B' S hS' := (inclusionOver h S hS).obj U
  have hUsize : ((BigFppfOver.toScheme B' S hS').obj U').size < B.cutoff := U.left.property
  -- the kernel pair of the atlas is a subobject of the square of the atlas
  let K := hfe.rep.pullback f
  have hprod : ((BigFppfOver.toScheme B' S hS').obj (U' ⨯ U')).size < B.cutoff :=
    (Scheme.size_congr ((Over.isPullback_of_binaryFan_isLimit _
      (prodIsProd U' U')).map B'.inclusion).isoPullback).trans_lt
      (Scheme.size_pullback_lt _ _ hUsize hUsize)
  have hKsize : ((BigFppfOver.toScheme B' S hS').obj K).size < B.cutoff :=
    (@Scheme.size_le_of_mono _ _ ((BigFppfOver.toScheme B' S hS').map
      (kernelPairToProd B' S hS' hfe.rep))
      (locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B' S hS' f hfe).2).trans_lt
      (Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit hprod)
  let R : BigFppfOver B S hS := Over.mk (Y := B.obj hKsize) (X := B.obj hS) ⟨K.hom.hom⟩
  let eK : yoneda.obj K ≅ pullback f f := (hfe.rep.isPullback' f).isoPullback
  let g : yoneda.obj ((inclusionOver h S hS).obj R) ⟶ pullback f f := eK.hom
  have : IsIso g := eK.isIso_hom
  exact mem_essentialImage_changeBigSite_of_small_presentation B B' h S hS X' U R f g
    (isLocallySurjective_of_surjective_etale B' S hS' f hfs hfe)
    (Presheaf.isLocallySurjective_of_iso _ g)

end AlgebraicGeometry.Space

end
