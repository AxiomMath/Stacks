module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomDescentCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.AffineSourceEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Descent.SubobjectEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Closed immersions of algebraic spaces along a surjective étale chart

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` is the one geometric
hypothesis of Stacks 03I2. At `P = AlgebraicGeometry.IsClosedImmersion` it holds outright, as
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion` of
`StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent`, and this file draws
the consequence: Stacks 03I2 itself for closed immersions.

It also records the two facts about the big fppf site that a subobject of an object of the site
needs: the source of a monomorphism into an object of the site is again an object of the site,
and a property of morphisms of schemes which respects isomorphisms transfers between a morphism
of affine schemes and the induced morphism of spectra of global sections.

## Main results

* `AlgebraicGeometry.exists_mono_bigFppfOver`: the source of a monomorphism into an object of the
  big fppf site of `S` is again an object of that site, and the monomorphism is a morphism of the
  site.
* `AlgebraicGeometry.property_specMap_appTop`: a property of morphisms of schemes which respects
  isomorphisms and holds of a morphism of affine schemes holds of the morphism of spectra induced
  by its map of global sections.
* `AlgebraicGeometry.Space.isAlgebraicSpace_and_isClosedImmersion_of_surjectiveEtaleChart` is
  Stacks 03I2 itself for closed immersions, unconditionally.

## Implementation notes

*Why no cardinal hypothesis appears.* The object descended by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion` is the source
of a monomorphism into an object of the site, and
`AlgebraicGeometry.Scheme.size_lt_of_mono_of_isStrongPrelimit` bounds its size by the cutoff for
*any* monomorphism, since the cutoff is closed under powersets. Nothing has to be said about its
cofinality.

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The source of a monomorphism into an object of the big fppf site of `S` is an object of
that site.** The size cutoff of the site is closed under powersets, so
`AlgebraicGeometry.Scheme.size_lt_of_mono_of_isStrongPrelimit` bounds the source of an arbitrary
monomorphism; the structure morphism to `S` is the composite with that of the target.

This is the closed- and locally-closed-subscheme analogue of
`AlgebraicGeometry.exists_restrict_bigFppfOver`, and unlike that statement it returns the given
morphism of schemes on the nose rather than only its image, which is what a subobject which is
not determined by its image needs. -/
theorem exists_mono_bigFppfOver (X : BigFppfOver B S hS) {Z : Scheme.{u}}
    (j : Z ⟶ (BigFppfOver.toScheme B S hS).obj X) (hj : Mono j) :
    ∃ (Y : BigFppfOver B S hS) (g : Y ⟶ X)
      (ε : (BigFppfOver.toScheme B S hS).obj Y ≅ Z),
      ε.hom ≫ j = (BigFppfOver.toScheme B S hS).map g := by
  have _ := hj
  exact ⟨Over.mk (show (⟨Z, Scheme.size_lt_of_mono_of_isStrongPrelimit
      B.cutoff_isStrongPrelimit j X.left.property⟩ : B.Schemes) ⟶ B.obj hS from
      ObjectProperty.homMk j ≫ X.hom), Over.homMk (ObjectProperty.homMk j) rfl,
    Iso.refl _, Category.id_comp _⟩

/-- A property of morphisms of schemes which respects isomorphisms is carried by
`Spec.map g.appTop` whenever it is carried by a morphism `g` of affine schemes: the two differ by
the canonical isomorphisms `AlgebraicGeometry.Scheme.isoSpec`, by
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality`. -/
theorem property_specMap_appTop {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {V W : Scheme.{u}} [IsAffine V] [IsAffine W] (g : V ⟶ W) (hg : P g) :
    P (Spec.map g.appTop) := by
  rw [show Spec.map g.appTop = V.isoSpec.inv ≫ g ≫ W.isoSpec.hom from
    (Iso.eq_inv_comp _).2 (Scheme.isoSpec_hom_naturality g)]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (MorphismProperty.RespectsIso.postcomp _ _ _ hg)

namespace Space

/-- **Stacks 03I2 for closed immersions**, unconditionally. Let `f : X ⟶ Y` be a morphism of
presheaves on the big fppf site of `S` with `X` a sheaf and `Y` an algebraic space over `S`. If
some surjective étale chart `g` of `Y` makes the base change of `f` a closed immersion, then `X`
is an algebraic space over `S` and `f` is a closed immersion.

This is
`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent`
with its descent hypothesis supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion`. -/
theorem isAlgebraicSpace_and_isClosedImmersion_of_surjectiveEtaleChart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : IsAlgebraicSpace B S hS Y)
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ Y}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hV : IsClosedImmersion B S hS (pullback.snd f g)) :
    IsAlgebraicSpace B S hS X ∧ IsClosedImmersion B S hS f :=
  have : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hX hY hs he hV

end Space

end AlgebraicGeometry

end
