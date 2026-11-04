module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.CommRing
public import StacksFrontier.CategoryTheory.Images.Sheaf

/-!
# The corestriction to the image of a morphism of sheaves is locally surjective

The image of a morphism of sheaves is the sheafification of the presheaf image, by
`Stacks.SheafImages.hasImages` over `Stacks.ReflectiveImages.hasImages_of_reflective`.  A
morphism of sheaves is therefore *not* surjective on sections onto its image -- that is the whole
difficulty of [Stacks, Tag 05JT] -- but it is locally surjective, and this file proves it: the
explicit factorisation that `Stacks.ReflectiveImages.monoFactorisation` builds has corestriction
`inv (counit) ≫ presheafToSheaf.map (factorThruImage _)`, whose three factors are respectively an
isomorphism, the sheafification of a locally surjective map, and -- after the transport of
`StacksFrontier/AlgebraicGeometry/AlgebraImageSurjective/Transport.lean` -- the comparison with
the chosen image.

## Main results

* `Stacks.AlgebraImageSurjective.sheaf_isLocallySurjective_of_isIso`: an isomorphism of sheaves
  is locally surjective, with `IsIso` an explicit argument so that the statement crosses between
  the `CategoryTheory.Sheaf` and `TopCat.Sheaf` category instances.
* `Stacks.AlgebraImageSurjective.sheaf_isLocallySurjective_factorThruImage`: for any concrete
  category with sheafification, local surjectivity of the presheaf-level corestriction implies
  local surjectivity of the sheaf-level one.
* `Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_commRingCat`: the case of
  sheaves of commutative rings on a small site, where the presheaf-level hypothesis is discharged
  by `Stacks.AlgebraImageSurjective.presheaf_isLocallySurjective_factorThruImage`.
* `Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_topCatSheaf`: the same for
  `TopCat.Sheaf CommRingCat X`, which is the spelling the algebra sheaves of a scheme are written
  at.

## Implementation notes

The passage from a locally surjective morphism of presheaves to its sheafification is **not**
proved here and does not need to be: `CategoryTheory.Presheaf.isLocallySurjective_toSheafify` is
an instance of Mathlib and
`CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff` is the biconditional,
under `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`, which is itself an instance
for a concrete category whose forgetful functor preserves sheafification.  Both synthesize for
`CommRingCat` on the site of opens of a space.

`Stacks.ReflectiveImages.monoFactorisation` lives in a section taking
`CategoryTheory.Functor.PreservesMonomorphisms` of the *inclusion* as a hypothesis, which
`Stacks.ReflectiveImages.hasImages_of_reflective` supplies with a `haveI` from
`Stacks.ReflectiveImages.preservesMonomorphisms_of_isRightAdjoint`.  The same `haveI` is needed
here before the factorisation can be named at all.

The `TopCat.Sheaf` restatement is given separately, as in
`Stacks.SheafImages.hasImagesTopCatSheaf`: `TopCat.Sheaf` is a `def` carrying its own category
instance from `deriving Category`, so the
head symbol of a statement about it is not `CategoryTheory.Sheaf` and the general result is not
found by unification at instance transparency, though the two are definitionally equal and term
elaboration identifies them.

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w w₂ v' u' v u

namespace Stacks.AlgebraImageSurjective

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] {FA : A → A → Type w₂} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]

/-- **An isomorphism of sheaves is locally surjective**, stated with `IsIso` as an explicit
argument rather than an instance.  This is what lets the conclusion be used at the `TopCat.Sheaf`
spelling, whose category instance is not the one the Mathlib instance
`CategoryTheory.Sheaf.isLocallySurjective_of_iso` is stated against: the two are definitionally
equal, so a term-level application bridges them, while instance search does not. -/
theorem sheaf_isLocallySurjective_of_isIso {F G : Sheaf J A} (f : F ⟶ G) (hf : IsIso f) :
    Sheaf.IsLocallySurjective f :=
  have := hf
  Sheaf.isLocallySurjective_of_iso f

/-- **The corestriction to the image of a morphism of sheaves is locally surjective, granted
that the presheaf-level corestriction is.**  The image of a morphism of sheaves is the
sheafification of the presheaf image, so the corestriction is the sheafification of the presheaf
corestriction up to the counit isomorphism and the comparison with the chosen image. -/
theorem sheaf_isLocallySurjective_factorThruImage [HasSheafify J A] [HasImages (Cᵒᵖ ⥤ A)]
    [J.WEqualsLocallyBijective A] {F G : Sheaf J A} (ψ : F ⟶ G)
    (hpre : Presheaf.IsLocallySurjective J (factorThruImage ψ.hom)) :
    Sheaf.IsLocallySurjective (factorThruImage ψ) := by
  have := ReflectiveImages.preservesMonomorphisms_of_isRightAdjoint (sheafificationAdjunction J A)
  have he : (ReflectiveImages.monoFactorisation (sheafificationAdjunction J A) ψ).e
      = inv ((sheafificationAdjunction J A).counit.app F)
        ≫ (presheafToSheaf J A).map (factorThruImage ψ.hom) := rfl
  have h1 : Sheaf.IsLocallySurjective ((presheafToSheaf J A).map (factorThruImage ψ.hom)) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J _).2 hpre
  have h2 : Sheaf.IsLocallySurjective
      (ReflectiveImages.monoFactorisation (sheafificationAdjunction J A) ψ).e := by
    rw [he]
    exact sheaf_isLocallySurjective_of_fac J rfl inferInstance h1
  have h : (ReflectiveImages.monoFactorisation (sheafificationAdjunction J A) ψ).e
      ≫ (IsImage.isoExt (ReflectiveImages.isImage (sheafificationAdjunction J A) ψ)
          (Image.isImage ψ)).hom = factorThruImage ψ := IsImage.e_isoExt_hom _ _
  exact sheaf_isLocallySurjective_of_fac J h h2 inferInstance

end Site

/-- **The corestriction to the image of a morphism of sheaves of commutative rings on a small
site is locally surjective.** -/
theorem isLocallySurjective_factorThruImage_commRingCat {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {F G : Sheaf J CommRingCat.{u}} (ψ : F ⟶ G) :
    Sheaf.IsLocallySurjective (factorThruImage ψ) :=
  sheaf_isLocallySurjective_factorThruImage J ψ
    (presheaf_isLocallySurjective_factorThruImage J ψ.hom)

/-- **The corestriction to the image of a morphism of sheaves of commutative rings on a
topological space is locally surjective.**  Restated for `TopCat.Sheaf`, whose own category
instance hides the site from instance search. -/
theorem isLocallySurjective_factorThruImage_topCatSheaf {X : TopCat.{u}}
    {F G : TopCat.Sheaf CommRingCat.{u} X} (ψ : F ⟶ G) :
    Sheaf.IsLocallySurjective (factorThruImage ψ) :=
  isLocallySurjective_factorThruImage_commRingCat (Opens.grothendieckTopology X) ψ

end Stacks.AlgebraImageSurjective
