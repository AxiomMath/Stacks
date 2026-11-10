module

public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.AlgebraicQuotient

/-!
# A flat surjection of objects of the site is locally surjective on functors of points

Let `g : U' ⟶ U` be a morphism of objects of the big fppf site of `S` which is surjective, flat
and locally of finite presentation as a morphism of schemes.  Then the induced map of presheaves
is locally surjective, both in the represented form `h_{U'} ⟶ h_U` and in the form
`(U' ⟶ -) ⟶ (U ⟶ -)` of restricted functors of points, which is the shape in which
`Stacks.Groupoids.restrictQuotientSheafMap_isIso` — [Stacks, Tag 045Z] — states its hypothesis.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.Space.presheaf_inverseImage_yoneda_map`: a property of morphisms of schemes
  stable under base change passes from a morphism of the site to the map of represented
  presheaves it induces, in the relative sense.
* `AlgebraicGeometry.Space.isLocallySurjective_yoneda_map_of_flat`: `h_{U'} ⟶ h_U` is locally
  surjective.
* `AlgebraicGeometry.Space.isLocallySurjective_whiskerLeft_yoneda_map_of_flat`: the same for the
  restricted functors of points.

## Implementation notes

Local surjectivity of the represented map is [Stacks, Tag 05VM]
(`Space.isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective`),
whose hypothesis is the three properties asserted *together* of one base-change square; it is
assembled here from the three separate relative properties by applying each to the same square,
so that no two choices of represented pullback have to be compared.

The passage to restricted functors of points is `Stacks.Groupoids.pointsIsoYoneda_naturality`:
the restricted functor of points of `F.obj X` is the presheaf represented by `X`, naturally in
`X`, so the two maps differ by isomorphisms on both sides and local surjectivity is invariant.

## References

* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
* [Stacks Project, Tag 045Z](https://stacks.math.columbia.edu/tag/045Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A property of morphisms of schemes which is stable under base change passes from a morphism
of objects of the site to the map of represented presheaves it induces, in the relative sense of
`CategoryTheory.MorphismProperty.presheaf`. -/
theorem presheaf_inverseImage_yoneda_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : P ((BigFppfOver.toScheme B S hS).map f)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS))) (yoneda.map f) := by
  have _ : (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
    refine ⟨?_⟩
    intro A B' B'' T a b a' b' hp hb
    change P ((BigFppfOver.toScheme B S hS).map b) at hb
    change P ((BigFppfOver.toScheme B S hS).map b')
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
      (hp.map (BigFppfOver.toScheme B S hS)) hb
  exact MorphismProperty.relative_map (F := yoneda) hf

/-- **A surjective, flat, locally finitely presented morphism of objects of the site induces a
locally surjective map of represented presheaves.**

This is [Stacks, Tag 05VM] applied to the morphism of represented sheaves; the three properties
are read off a single base-change square. -/
theorem isLocallySurjective_yoneda_map_of_flat {X Y : BigFppfOver B S hS} (g : X ⟶ Y)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map g))
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (yoneda.map g) := by
  have _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  have hs := presheaf_inverseImage_yoneda_map B S hS (@Surjective.{u}) g hsurj
  have hf := presheaf_inverseImage_yoneda_map B S hS (@Flat.{u}) g hflat
  have hl := presheaf_inverseImage_yoneda_map B S hS (@LocallyOfFinitePresentation.{u}) g hlfp
  have hprop : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f) :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map g) := by
    refine ⟨hf.rep, ?_⟩
    intro A A' ξ fst snd sq
    exact ⟨hf.property ξ fst snd sq, hl.property ξ fst snd sq, hs.property ξ fst snd sq⟩
  exact isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
    B S hS (⟨yoneda.map g⟩ : (BigFppfOver.topology B S hS).yoneda.obj X ⟶
      (BigFppfOver.topology B S hS).yoneda.obj Y) hprop

/-- **The local surjectivity hypothesis of [Stacks, Tag 045Z], for a surjective, flat, locally
finitely presented morphism of objects of the site.**

The restricted functor of points of the scheme underlying an object of the site is the presheaf
represented by that object, naturally in the object
(`Stacks.Groupoids.pointsIsoYoneda_naturality`), so this is
`AlgebraicGeometry.Space.isLocallySurjective_yoneda_map_of_flat` conjugated by two
isomorphisms. -/
theorem isLocallySurjective_whiskerLeft_yoneda_map_of_flat {X Y : BigFppfOver B S hS} (g : X ⟶ Y)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map g))
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map g))) := by
  have hA : (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
      (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map g)) =
      (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) X).hom ≫ yoneda.map g ≫
        (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) Y).inv := by
    rw [← Category.assoc, ← pointsIsoYoneda_naturality (Over.post (X := B.obj hS) B.inclusion) g,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hA]
  have := isLocallySurjective_yoneda_map_of_flat B S hS g hsurj hflat hlfp
  infer_instance

end AlgebraicGeometry.Space

end
