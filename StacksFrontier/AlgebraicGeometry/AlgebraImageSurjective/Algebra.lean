module

public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.Generated

/-!
# The corestriction to the image of a morphism of algebra sheaves is locally surjective

This is the statement that
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective` was waiting
for, and with it that theorem applies to an actual image: for a morphism `φ : A ⟶ B` of sheaves
of `𝒪_X`-algebras on a scheme `X`, the corestriction
`CategoryTheory.Limits.factorThruImage φ` of `φ` to its image is locally surjective on underlying
sheaves of commutative rings, so a quasi-coherent image of a finite type quasi-coherent algebra
sheaf is of finite type.

The `CategoryTheory.Under` layer is stripped here.  Images in `CategoryTheory.Under Y` are
computed on underlying objects by `Stacks.UnderImages.isImage`, whose corestriction has
underlying morphism *literally* `CategoryTheory.Limits.factorThruImage φ.right`, so the whole
content of this file is transporting that along the comparison isomorphism with the chosen image
and applying
`Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_topCatSheaf`.

## Main results

* `Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_under`: for a morphism of
  objects under a sheaf of commutative rings on a space, the corestriction to the image is
  locally surjective on underlying sheaves.
* `Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_algebraSheaf`: the same at
  the spelling `Stacks.RelativeSpec.AlgebraSheaf X` of the algebra sheaves of a scheme.  **This
  is the declaration the consumers need.**
* `Stacks.AlgebraImageSurjective.isFiniteType_image`: **a quasi-coherent image of a finite type
  quasi-coherent algebra sheaf is of finite type**, which is
  `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective` applied to
  an image.  Quasi-coherence of the image is a hypothesis; it is not proved here.

## Implementation notes

`CategoryTheory.Under.Hom.right` of the corestriction of `Stacks.UnderImages.monoFactorisation`
is `CategoryTheory.Limits.factorThruImage φ.right` by definition, since that factorisation's
corestriction is `CategoryTheory.Under.homMk (factorThruImage φ.right) rfl`.  The identity at the
level of underlying morphisms is therefore `congrArg CategoryTheory.Under.Hom.right` applied to
the identity in `CategoryTheory.Under Y`, with the left-hand side written out.

That the underlying morphism of an isomorphism under `Y` is an isomorphism is **not** found by
instance search: `CategoryTheory.Under Y` is a definition for a structured-arrow category and
the forgetful functor's action on a morphism is the `right` field only after unfolding, which
instance search does not do.  It is supplied as `inferInstanceAs` against
`(CategoryTheory.Under.forget Y).map`, where the identification is checked at the transparency of
term elaboration -- the same manoeuvre `CategoryTheory.Under.mono_right_of_mono` needs for
monomorphisms.

Local surjectivity of that underlying isomorphism then has to be taken through
`sheaf_isLocallySurjective_of_isIso` rather than through Mathlib's instance: the ambient
category here is `TopCat.Sheaf`, whose `deriving Category` instance is not the instance
`CategoryTheory.Sheaf.isLocallySurjective_of_iso` is stated against, and instance search does
not identify the two even though they are definitionally equal.

**No stacks attribute is attached.**  Neither assertion of [Stacks, Tag 05JT] nor of
[Stacks, Tag 0817] is proved here: these are inputs to them, and `isFiniteType_image` carries a
quasi-coherence hypothesis on the image that the tags do not.

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RelativeSpec

universe u

namespace Stacks.AlgebraImageSurjective

/-- **The corestriction to the image of a morphism under a sheaf of commutative rings is locally
surjective on underlying sheaves.**  Images under `Y` are computed on underlying objects, so this
is `isLocallySurjective_factorThruImage_topCatSheaf` for the underlying morphism, transported
along the comparison isomorphism with the chosen image. -/
theorem isLocallySurjective_factorThruImage_under {X : TopCat.{u}}
    {Y : TopCat.Sheaf CommRingCat.{u} X} {A B : Under Y} (φ : A ⟶ B) :
    Sheaf.IsLocallySurjective (factorThruImage φ).right := by
  let e := IsImage.isoExt (Stacks.UnderImages.isImage φ) (Image.isImage φ)
  have h : (Stacks.UnderImages.monoFactorisation φ).e ≫ e.hom = factorThruImage φ :=
    IsImage.e_isoExt_hom _ _
  have hr : factorThruImage φ.right ≫ e.hom.right = (factorThruImage φ).right :=
    congrArg Under.Hom.right h
  have hiso : IsIso e.hom.right := inferInstanceAs (IsIso ((Under.forget Y).map e.hom))
  exact sheaf_isLocallySurjective_of_fac (_root_.Opens.grothendieckTopology X) hr
    (isLocallySurjective_factorThruImage_topCatSheaf φ.right)
    (sheaf_isLocallySurjective_of_isIso (_root_.Opens.grothendieckTopology X) e.hom.right hiso)

/-- **The corestriction to the image of a morphism of sheaves of `𝒪_X`-algebras on a scheme is
locally surjective.**  This is the hypothesis of
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective` and of
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras`'s
`exists_finiteTypeSubalgebra_section_of_factorisation`, met by an image. -/
theorem isLocallySurjective_factorThruImage_algebraSheaf {X : Scheme.{u}}
    {A B : AlgebraSheaf X} (φ : A ⟶ B) :
    Sheaf.IsLocallySurjective (factorThruImage φ).right :=
  isLocallySurjective_factorThruImage_under φ

/-- **A quasi-coherent image of a finite type quasi-coherent algebra sheaf is of finite type.**
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective` applied to
the image of `φ`, whose corestriction is locally surjective by
`isLocallySurjective_factorThruImage_algebraSheaf`.

Quasi-coherence of the image is a hypothesis, not a conclusion. -/
theorem isFiniteType_image {X : Scheme.{u}} {A B : AlgebraSheaf X} (φ : A ⟶ B)
    (hA : A.IsQuasicoherent) (him : (image φ).IsQuasicoherent) (hAft : A.IsFiniteType) :
    (image φ).IsFiniteType :=
  Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective
    (factorThruImage φ) hA him (isLocallySurjective_factorThruImage_algebraSheaf φ) hAft

end Stacks.AlgebraImageSurjective
