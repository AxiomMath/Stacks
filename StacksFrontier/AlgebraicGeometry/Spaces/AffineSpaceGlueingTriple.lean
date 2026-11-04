module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectBaseChangeAffine

/-!
# A glueing triple out of two site objects with identified restrictions

This module makes a cartesian glueing triple over `U ← U' → X'` out of an object `A` of the big
fppf category over `U`, an object `A'` over `X'`, and an isomorphism over `U'` between their two
base changes.

The point of the construction is which of the two structure arrows of the triple is free. A
cartesian glueing triple has three components and two arrows from the middle component to the
restrictions of the outer two, both required to be invertible. Taking the middle component to be
the base change of `A` *as a site object*, rather than an abstract algebraic space over `U'`,
makes the arrow over `U` the comparison isomorphism
`CategoryTheory.OverShriek.restrictYonedaIso`, so its invertibility is free; and the arrow over
`X'` is then the given identification followed by the same comparison isomorphism for `gX'`, so
its invertibility is free as well. Neither structure arrow needs an argument, and the only
content in the triple is the identification itself.

## Main definitions

* `BeauvilleLaszlo.Space.restrictSchemeSpaceIso`: the restriction of the algebraic space of a
  site object is the algebraic space of that object's base change.
* `BeauvilleLaszlo.Space.glueingDataOfRestrictionIso`: the cartesian glueing triple assembled
  from `A` over `U`, `A'` over `X'`, and an identification of their base changes to `U'`.

## Main results

* `BeauvilleLaszlo.Space.overU_glueingDataOfRestrictionIso`,
  `BeauvilleLaszlo.Space.overU'_glueingDataOfRestrictionIso` and
  `BeauvilleLaszlo.Space.overX'_glueingDataOfRestrictionIso`: the three components of the
  assembled triple are the algebraic spaces of `A`, of the base change of `A`, and of `A'`, on
  the nose.
* `BeauvilleLaszlo.Space.affineComponents_glueingDataOfRestrictionIso`: the assembled triple has
  affine components as soon as `A`, `A'` and the base change of `A` have affine underlying
  schemes.

## Implementation notes

The middle component is `AlgebraicGeometry.schemeSpace ((Over.pullback gU).obj A)` and not
`BeauvilleLaszlo.Space.baseChange B U' U hU' hU gU` applied to `schemeSpace A`. The two are
isomorphic — by exactly the arrow this module installs as the triple's structure arrow over `U`
— but they are not the same object, and the choice matters twice over: the structure arrow over
`U` becomes invertible by construction rather than by an argument, and the middle component stays
visibly representable, which is what makes its affineness a statement about a scheme.

The affineness of the middle component is a hypothesis of
`BeauvilleLaszlo.Space.affineComponents_glueingDataOfRestrictionIso` rather than a consequence of
the other two: it is the base change of `A` along `U' → U`, so it is affine because that morphism
is an affine morphism, which is a property of the square and not of the triple.

## References

* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-! ### The restriction of a representable algebraic space -/

section Restrict

variable {B : BigFppfSite.{u}} {U' U : Scheme.{u}} {hU' : B.Contains U'} {hU : B.Contains U}
  {gU : B.obj hU' ⟶ B.obj hU}

/-- **The restriction of the algebraic space of a site object is the algebraic space of its base
change.** This is `CategoryTheory.OverShriek.restrictYonedaIso`, which identifies the restriction
of a representable presheaf with the presheaf represented by the base change of the representing
object, transported into the category of algebraic spaces over `U'` along the fully faithful
inclusion of that full subcategory of presheaves. -/
noncomputable def restrictSchemeSpaceIso (A : BigFppfOver B U hU) :
    schemeSpace ((Over.pullback gU).obj A) ≅
      (baseChange B U' U hU' hU gU).obj (schemeSpace A) where
  hom := ObjectProperty.homMk (CategoryTheory.OverShriek.restrictYonedaIso gU A).hom
  inv := ObjectProperty.homMk (CategoryTheory.OverShriek.restrictYonedaIso gU A).inv
  hom_inv_id := ObjectProperty.hom_ext _
    (CategoryTheory.OverShriek.restrictYonedaIso gU A).hom_inv_id
  inv_hom_id := ObjectProperty.hom_ext _
    (CategoryTheory.OverShriek.restrictYonedaIso gU A).inv_hom_id

/-- The morphism of presheaves underlying `BeauvilleLaszlo.Space.restrictSchemeSpaceIso` is the
comparison isomorphism of `CategoryTheory.OverShriek.restrictYonedaIso`. -/
theorem restrictSchemeSpaceIso_hom_hom (A : BigFppfOver B U hU) :
    (restrictSchemeSpaceIso (U' := U') (hU' := hU') (gU := gU) A).hom.hom =
      (CategoryTheory.OverShriek.restrictYonedaIso gU A).hom :=
  rfl

end Restrict

/-! ### The triple -/

section Triple

variable (B : BigFppfSite.{u}) (U' U X' : Scheme.{u}) (hU' : B.Contains U')
  (hU : B.Contains U) (hX' : B.Contains X')
  (gU : B.obj hU' ⟶ B.obj hU)
  (gX' : B.obj hU' ⟶ B.obj hX')

/-- **A cartesian glueing triple out of two site objects with identified base changes.** Let `A`
be an object of the big fppf category over `U` and `A'` an object of the big fppf category over
`X'`, and let `chain` identify the base change of `A` to `U'` with the base change of `A'` to
`U'`. Then the algebraic spaces of `A`, of the base change of `A`, and of `A'` are the three
components of a cartesian glueing triple over `U ← U' → X'`.

Both structure arrows are comparison isomorphisms, hence invertible with no argument: over `U`
it is `BeauvilleLaszlo.Space.restrictSchemeSpaceIso` for `gU`, and over `X'` it is `chain`
followed by the same comparison isomorphism for `gX'`. -/
noncomputable def glueingDataOfRestrictionIso
    (A : BigFppfOver B U hU) (A' : BigFppfOver B X' hX')
    (chain : (Over.pullback gU).obj A ≅ (Over.pullback gX').obj A') :
    GlueingData B U' U X' hU' hU hX' gU gX' :=
  ⟨⟨⟨schemeSpace ((Over.pullback gU).obj A), schemeSpace A,
      (restrictSchemeSpaceIso (U' := U') (hU' := hU') (gU := gU) A).hom⟩,
    schemeSpace A',
    ((schemeSpaceFunctor B U' hU').mapIso chain ≪≫
      restrictSchemeSpaceIso (U' := U') (hU' := hU') (gU := gX') A').hom⟩,
    ⟨inferInstanceAs (IsIso
        (restrictSchemeSpaceIso (U' := U') (hU' := hU') (gU := gU) A).hom),
      inferInstanceAs (IsIso ((schemeSpaceFunctor B U' hU').mapIso chain ≪≫
        restrictSchemeSpaceIso (U' := U') (hU' := hU') (gU := gX') A').hom)⟩⟩

/-- The structure arrow over `U` of `BeauvilleLaszlo.Space.glueingDataOfRestrictionIso` is the
comparison isomorphism of the restriction of `A`. -/
theorem glueingDataOfRestrictionIso_obj_left_hom
    (A : BigFppfOver B U hU) (A' : BigFppfOver B X' hX')
    (chain : (Over.pullback gU).obj A ≅ (Over.pullback gX').obj A') :
    (glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A A' chain).obj.left.hom =
      (restrictSchemeSpaceIso (U' := U') (hU' := hU') (gU := gU) A).hom :=
  rfl

/-- The structure arrow over `X'` of `BeauvilleLaszlo.Space.glueingDataOfRestrictionIso` is
`chain` followed by the comparison isomorphism of the restriction of `A'`. -/
theorem glueingDataOfRestrictionIso_obj_hom
    (A : BigFppfOver B U hU) (A' : BigFppfOver B X' hX')
    (chain : (Over.pullback gU).obj A ≅ (Over.pullback gX').obj A') :
    (glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A A' chain).obj.hom =
      schemeSpaceMap chain.hom ≫
        (restrictSchemeSpaceIso (U' := U') (hU' := hU') (gU := gX') A').hom :=
  rfl

/-- The component over `U` of `BeauvilleLaszlo.Space.glueingDataOfRestrictionIso` is the
algebraic space of `A`. -/
@[simp]
theorem overU_glueingDataOfRestrictionIso
    (A : BigFppfOver B U hU) (A' : BigFppfOver B X' hX')
    (chain : (Over.pullback gU).obj A ≅ (Over.pullback gX').obj A') :
    (overU B U' U X' hU' hU hX' gU gX').obj
        (glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A A' chain) =
      schemeSpace A :=
  rfl

/-- The middle component of `BeauvilleLaszlo.Space.glueingDataOfRestrictionIso` is the algebraic
space of the base change of `A` to `U'`. -/
@[simp]
theorem overU'_glueingDataOfRestrictionIso
    (A : BigFppfOver B U hU) (A' : BigFppfOver B X' hX')
    (chain : (Over.pullback gU).obj A ≅ (Over.pullback gX').obj A') :
    (overU' B U' U X' hU' hU hX' gU gX').obj
        (glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A A' chain) =
      schemeSpace ((Over.pullback gU).obj A) :=
  rfl

/-- The component over `X'` of `BeauvilleLaszlo.Space.glueingDataOfRestrictionIso` is the
algebraic space of `A'`. -/
@[simp]
theorem overX'_glueingDataOfRestrictionIso
    (A : BigFppfOver B U hU) (A' : BigFppfOver B X' hX')
    (chain : (Over.pullback gU).obj A ≅ (Over.pullback gX').obj A') :
    (overX' B U' U X' hU' hU hX' gU gX').obj
        (glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A A' chain) =
      schemeSpace A' :=
  rfl

/-- **The assembled triple has affine components.** Each of the three components is the algebraic
space of an object of the big fppf category, so each is an affine algebraic space exactly when
that object's underlying scheme is affine, by
`AlgebraicGeometry.Space.isAffineSpace_yoneda`. -/
theorem affineComponents_glueingDataOfRestrictionIso
    (A : BigFppfOver B U hU) (A' : BigFppfOver B X' hX')
    (chain : (Over.pullback gU).obj A ≅ (Over.pullback gX').obj A')
    (hA : IsAffine ((BigFppfOver.toScheme B U hU).obj A))
    (hA' : IsAffine ((BigFppfOver.toScheme B X' hX').obj A'))
    (hAU' : IsAffine ((BigFppfOver.toScheme B U' hU').obj ((Over.pullback gU).obj A))) :
    affineComponents B U' U X' hU' hU hX' gU gX'
      (glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A A' chain) :=
  ⟨AlgebraicGeometry.Space.isAffineSpace_yoneda B U hU A hA,
    AlgebraicGeometry.Space.isAffineSpace_yoneda B U' hU' _ hAU',
    AlgebraicGeometry.Space.isAffineSpace_yoneda B X' hX' A' hA'⟩

/-- **The assembled triple has affine components, with the middle one discharged.** The same
conclusion as `BeauvilleLaszlo.Space.affineComponents_glueingDataOfRestrictionIso` from
hypotheses about the two given objects alone, the affineness of the middle component being
supplied by `AlgebraicGeometry.BigFppfOver.isAffine_toScheme_obj_pullback` from the one extra
input it needs: that `U' → U` is an affine morphism. -/
theorem affineComponents_glueingDataOfRestrictionIso_of_isAffineHom
    (A : BigFppfOver B U hU) (A' : BigFppfOver B X' hX')
    (chain : (Over.pullback gU).obj A ≅ (Over.pullback gX').obj A')
    (hgU : IsAffineHom (B.inclusion.map gU))
    (hA : IsAffine ((BigFppfOver.toScheme B U hU).obj A))
    (hA' : IsAffine ((BigFppfOver.toScheme B X' hX').obj A')) :
    affineComponents B U' U X' hU' hU hX' gU gX'
      (glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A A' chain) :=
  affineComponents_glueingDataOfRestrictionIso B U' U X' hU' hU hX' gU gX' A A' chain hA hA'
    (BigFppfOver.isAffine_toScheme_obj_pullback B U U' hU hU' gU hgU A hA)

end Triple

end BeauvilleLaszlo.Space

end
