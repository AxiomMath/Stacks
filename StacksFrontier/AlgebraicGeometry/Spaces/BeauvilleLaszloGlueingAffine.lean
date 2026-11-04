module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueing

/-!
# Affineness under the Beauville--Laszlo gluing functor (Stacks 0F9Q)

Let `U' → X'`, `U' → U`, `U → X`, `X' → X` be a commutative square of affine schemes of a big
fppf site. The gluing functor of Stacks 0F9N sends an affine algebraic space over `X` to a
cartesian triple whose three components are affine, so it restricts to a functor between the
corresponding full subcategories.

## Main results

* `BeauvilleLaszlo.Space.isAffineSpace_relocalizeRestrict`: the base change of an affine
  algebraic space along a morphism of affine bases is affine.
* `BeauvilleLaszlo.Space.isAffineSpace_components`: **Stacks 0F9Q**, the restriction clause: the
  three components of the gluing triple of an affine algebraic space are affine.
* `BeauvilleLaszlo.Space.affineRestriction`: the resulting functor from affine algebraic spaces
  over `X` to gluing triples with three affine components.

## Implementation notes

Affineness of an algebraic space (`AlgebraicGeometry.Space.IsAffineSpace`) is representability
by an object of the site with affine underlying scheme, and base change of algebraic spaces is
restriction of presheaves along the localization functor. The restriction of a representable
presheaf is represented by the base change of the representing object
(`CategoryTheory.OverShriek.restrictYonedaIso`), whose underlying scheme is a fibre product of
schemes, affine because one of its legs is a morphism of affine schemes.

Glueability for the pair, in the sense of Stacks 0F9P, plays no role in this direction, so the
source is the full subcategory of all affine algebraic spaces over `X`; the subcategory of the
source lemma, cut out by affineness *and* glueability, is contained in it. The equivalence
asserted by Stacks 0F9Q is not proved here, which is why the tag carries a clause: it needs the
Beauville--Laszlo theorem for algebras, that is the inverse construction gluing an `R`-algebra
out of an `R_f`-algebra and an `R'`-algebra agreeing over `R'_f`.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9P](https://stacks.math.columbia.edu/tag/0F9P)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-- The base change of an affine algebraic space along a morphism of affine bases of a big fppf
site is an affine algebraic space. -/
theorem isAffineSpace_relocalizeRestrict (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    [IsAffine S] [IsAffine T] {F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.Space.IsAffineSpace B T hT F) :
    AlgebraicGeometry.Space.IsAffineSpace B S hS
      ((OverShriek.relocalizeRestrict g).obj F) := by
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := hF
  refine ⟨(Over.pullback g).obj T₀, ?_,
    ⟨((OverShriek.relocalizeRestrict g).mapIso e).trans
      (OverShriek.restrictYonedaIso g T₀).symm⟩⟩
  have hpb : IsPullback (B.inclusion.map (pullback.fst T₀.hom g))
      (B.inclusion.map (pullback.snd T₀.hom g))
      (B.inclusion.map T₀.hom) (B.inclusion.map g) :=
    (IsPullback.of_hasPullback T₀.hom g).map B.inclusion
  have : IsAffine (B.inclusion.obj T₀.left) := hT₀
  have : IsAffine (B.inclusion.obj (B.obj hS)) := ‹IsAffine S›
  have : IsAffine (B.inclusion.obj (B.obj hT)) := ‹IsAffine T›
  exact IsAffine.of_isPullback hpb

/-- The base change of an affine algebraic space, as a functor of algebraic spaces, is
affine. -/
theorem isAffineSpace_baseChange (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (g : B.obj hS ⟶ B.obj hT)
    [IsAffine S] [IsAffine T] (Y : AlgebraicSpaces B T hT)
    (hY : AlgebraicGeometry.Space.IsAffineSpace B T hT Y.1) :
    AlgebraicGeometry.Space.IsAffineSpace B S hS ((baseChange B S T hS hT g).obj Y).1 :=
  isAffineSpace_relocalizeRestrict B S T hS hT g hY

/-- The property of an algebraic space over `X` that it is affine. -/
abbrev affineSpaces (B : BigFppfSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) :
    ObjectProperty (AlgebraicSpaces B X hX) :=
  fun Y => AlgebraicGeometry.Space.IsAffineSpace B X hX Y.1

/-- The property of a cartesian gluing triple that its three components are affine. -/
abbrev affineComponents (B : BigFppfSite.{u})
    (U' U X' : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X')
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX') :
    ObjectProperty (GlueingData B U' U X' hU' hU hX' gU gX') :=
  fun Z =>
    AlgebraicGeometry.Space.IsAffineSpace B U hU
        ((overU B U' U X' hU' hU hX' gU gX').obj Z).1 ∧
      AlgebraicGeometry.Space.IsAffineSpace B U' hU'
          ((overU' B U' U X' hU' hU hX' gU gX').obj Z).1 ∧
        AlgebraicGeometry.Space.IsAffineSpace B X' hX'
          ((overX' B U' U X' hU' hU hX' gU gX').obj Z).1

/-- **The gluing functor of Stacks 0F9N takes affine algebraic spaces to triples with affine
components.** All four schemes of the square are assumed affine, as they are in the
Beauville--Laszlo situation, where they are the spectra of `R`, `R_f`, `R'` and `R'_f`. -/
@[stacks 0F9Q "the functor restricts to the affine subcategories"]
theorem isAffineSpace_components
    (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
    [IsAffine U'] [IsAffine U] [IsAffine X'] [IsAffine X]
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX)
    (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (G : GlueingFunctorSpec B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm)
    (Y : AlgebraicSpaces B X hX)
    (hY : AlgebraicGeometry.Space.IsAffineSpace B X hX Y.1) :
    affineComponents B U' U X' hU' hU hX' gU gX' (G.functor.obj Y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (isAffineSpace_baseChange B U X hU hX jU Y hY).of_iso
      (((ObjectProperty.ι _).mapIso (G.overUIso.app Y)).symm)
  · exact (isAffineSpace_baseChange B U' X hU' hX (gU ≫ jU) Y hY).of_iso
      (((ObjectProperty.ι _).mapIso (G.overU'Iso.app Y)).symm)
  · exact (isAffineSpace_baseChange B X' X hX' hX jX' Y hY).of_iso
      (((ObjectProperty.ι _).mapIso (G.overX'Iso.app Y)).symm)

/-- The restriction of the gluing functor of Stacks 0F9N to the full subcategory of affine
algebraic spaces over `X`, landing in the full subcategory of gluing triples with affine
components. -/
noncomputable def affineRestriction
    (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
    [IsAffine U'] [IsAffine U] [IsAffine X'] [IsAffine X]
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX)
    (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (G : GlueingFunctorSpec B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm) :
    (affineSpaces B X hX).FullSubcategory ⥤
      (affineComponents B U' U X' hU' hU hX' gU gX').FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ G.functor)
    (fun Y => isAffineSpace_components B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm G Y.1
      Y.property)

end BeauvilleLaszlo.Space

end
