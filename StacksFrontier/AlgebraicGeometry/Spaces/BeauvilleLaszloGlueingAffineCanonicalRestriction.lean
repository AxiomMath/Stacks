module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSiteSpecDictionary
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.BeauvilleLaszlo
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.RingTheory.BeauvilleLaszlo.AlgebraGlueing
public import StacksFrontier.RingTheory.BeauvilleLaszlo.AlgebraProperties
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueableModuleLinearEquiv
public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueingSubalgebra

/-!
# The Beauville--Laszlo gluing functor on affine glueable spaces (Stacks 0F9Q)

Let `(g : R → R', f)` be a pair of rings and an element, and let `X = Spec R`, `U = Spec R_f`,
`X' = Spec R'`, `U' = Spec R'_{g f}` be the four affine schemes of the associated square of a big
fppf site. This file restricts the gluing functor of Stacks 0F9N to the full subcategory
`BeauvilleLaszlo.Space.affineGlueableSpaces` of affine algebraic spaces over `X` which are
glueable for `(g, f)`, landing in the cartesian triples with three affine components, and
records the pieces from which the equivalence of Stacks 0F9Q is assembled.

## Main definitions

* `BeauvilleLaszlo.Space.canGU`, `canGX'`, `canJU`, `canJX'`: the four canonical morphisms of
  the Beauville--Laszlo square.
* `BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction`: the gluing functor of Stacks 0F9N
  restricted to the affine glueable subcategory.
* `BeauvilleLaszlo.Space.affineGlueingEquivalenceOfParts`: a term of
  `BeauvilleLaszlo.Space.AffineGlueingEquivalenceSpec` from faithfulness, fullness and essential
  surjectivity of that restriction.

## Main results

* `BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction_faithful`: the restriction is
  faithful; this is Stacks 0F9S, which needs glueability alone.
* `BeauvilleLaszlo.Space.isGlueableAlgebraicSpace_schemeSpace`: an affine algebraic space whose
  ring of global sections is glueable is glueable as an algebraic space.

## Implementation notes

This is the version of the restriction for the canonical glueing functor of Stacks 0F9N and
the four canonical morphisms `canGU`, `canGX'`, `canJU`, `canJX'` of the square of an arbitrary
ring map `g : R →+* R'`. The restriction of an arbitrary glueing functor, over the square of an
algebra `R → R'`, is `BeauvilleLaszlo.Space.affineGlueableRestriction` in
`StacksFrontier/AlgebraicGeometry/Spaces/BeauvilleLaszloGlueingAffineRestriction.lean`, and the
equivalence of Stacks 0F9Q in that form is
`BeauvilleLaszlo.Space.beauvilleLaszloAffineEquivalence`.

The subcategory `BeauvilleLaszlo.Space.affineGlueableSpaces` and the statement of Stacks 0F9Q as
data, `BeauvilleLaszlo.Space.AffineGlueingEquivalenceSpec`, are declared in
`StacksFrontier/AlgebraicGeometry/Spaces/BeauvilleLaszloGlueingFullyFaithful.lean`, which is why
this file imports it.

The equivalence is assembled from three independent properties of the restricted functor —
faithful, full and essentially surjective — rather than by exhibiting a quasi-inverse with its
unit and counit. `CategoryTheory.Functor.IsEquivalence` is a class with exactly those three
fields, so no coherence condition has to be verified, and the `functorIso` field of
`BeauvilleLaszlo.Space.AffineGlueingEquivalenceSpec` is then the canonical
`CategoryTheory.ObjectProperty.liftCompιIso`, because the forward functor is literally the lift
of the gluing functor. Faithfulness is Stacks 0F9S; fullness and essential surjectivity are in
`StacksFrontier/AlgebraicGeometry/Spaces/BeauvilleLaszloGlueingAffineCanonicalFull.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/BeauvilleLaszloGlueingAffineCanonicalEssSurj.lean`, where the
Beauville--Laszlo theorem for algebras enters.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9P](https://stacks.math.columbia.edu/tag/0F9P)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9S](https://stacks.math.columbia.edu/tag/0F9S)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-- **The underlying morphism of a canonical cast in a full subcategory** is the canonical cast
of the underlying objects. -/
theorem fullSubcategory_eqToHom_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {Y Z : P.FullSubcategory} (h : Y = Z) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst h
  rfl

section Canonical

/-- The canonical morphism `U' ⟶ U` of the Beauville--Laszlo square. -/
noncomputable abbrev canGU {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (B : BigFppfSite.{u}) (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f)))) : B.obj hU' ⟶ B.obj hU :=
  ⟨Spec.map (CommRingCat.ofHom (Localization.awayMap g f))⟩

/-- The canonical morphism `U' ⟶ X'` of the Beauville--Laszlo square. -/
noncomputable abbrev canGX' {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (B : BigFppfSite.{u}) (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hX' : B.Contains (Spec (.of R'))) : B.obj hU' ⟶ B.obj hX' :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f))))⟩

/-- The canonical morphism `U ⟶ X` of the Beauville--Laszlo square. -/
noncomputable abbrev canJU {R : Type u} [CommRing R] (f : R)
    (B : BigFppfSite.{u}) (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX : B.Contains (Spec (.of R))) : B.obj hU ⟶ B.obj hX :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))⟩

/-- The canonical morphism `X' ⟶ X` of the Beauville--Laszlo square. -/
noncomputable abbrev canJX' {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R')
    (B : BigFppfSite.{u}) (hX' : B.Contains (Spec (.of R')))
    (hX : B.Contains (Spec (.of R))) : B.obj hX' ⟶ B.obj hX :=
  ⟨Spec.map (CommRingCat.ofHom g)⟩

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (B : BigFppfSite.{u})
  (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
  (hU : B.Contains (Spec (.of (Localization.Away f))))
  (hX' : B.Contains (Spec (.of R')))
  (hX : B.Contains (Spec (.of R)))
  (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)

/-- The gluing functor restricted to the affine glueable subcategory. -/
noncomputable def canonicalAffineGlueableRestriction :
    (affineGlueableSpaces g f B hX).FullSubcategory ⥤
      (affineComponents B (Spec (.of (Localization.Away (g f))))
        (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX'
        (canGU g f B hU' hU) (canGX' g f B hU' hX')).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX
      _ _ _ _ hcomm).functor)
    (fun Y => isAffineSpace_components B _ _ _ _ hU' hU hX' hX _ _ _ _ hcomm
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _ hcomm)
      Y.1 Y.property.1)

/-- **Faithfulness**, from Stacks 0F9S. -/
theorem canonicalAffineGlueableRestriction_faithful
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) :
    (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).Faithful := by
  constructor
  intro Y Z a b hab
  apply ObjectProperty.hom_ext
  refine beauvilleLaszloGlueingSpaces_map_injective_of_isGlueable R R' g f hglue B
    hU' hU hX' hX hcomm Y.1 Z.1 Y.property.2 Z.property.2 ?_
  exact congrArg (ObjectProperty.ι _).map hab

/-- Skeleton of the affine equivalence. -/
noncomputable def affineGlueingEquivalenceOfParts
    (hfaithful : (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).Faithful)
    (hfull : (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).Full)
    (hess : (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).EssSurj) :
    AffineGlueingEquivalenceSpec g f B _ _ _ hU' hU hX' hX _ _
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _ hcomm).functor :=
  letI : (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).IsEquivalence :=
    ⟨hfaithful, hfull, hess⟩
  { equivalence := (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).asEquivalence
    functorIso := ObjectProperty.liftCompιIso _ _ _ }

/-- An affine algebraic space whose ring of global sections is glueable is glueable: the
identity is a one-member étale covering by an affine scheme. -/
theorem isGlueableAlgebraicSpace_schemeSpace
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
    (T : BigFppfOver B (Spec (.of R)) hX)
    (hT : IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj T))
    (hT' : AlgebraicGeometry.Space.IsGlueableGlobalSections g f B hX T) :
    AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX (schemeSpace T) := by
  have hS0 : MorphismProperty.ContainsIdentities
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have hS1 : MorphismProperty.RespectsIso (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hE0 : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have hE1 : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hS2 : MorphismProperty.ContainsIdentities
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of R)) hX)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B (Spec (.of R)) hX)
  have hS3 : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of R)) hX)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B (Spec (.of R)) hX)
  have hE2 : MorphismProperty.ContainsIdentities
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of R)) hX)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B (Spec (.of R)) hX)
  have hE3 : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of R)) hX)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B (Spec (.of R)) hX)
  refine (AlgebraicGeometry.Space.exists_etaleCovering_iff_isGlueable g f hglue B hX
    (schemeSpace T)).1 ⟨PUnit.{u + 2}, fun _ => T, fun _ => 𝟙 _, ?_, fun _ => ⟨hT, hT'⟩⟩
  exact AlgebraicGeometry.Space.isEtaleCovering_atlas B (Spec (.of R)) hX
    (isAlgebraicSpace_yoneda B (Spec (.of R)) hX T)
    (MorphismProperty.presheaf_of_isIso _ (𝟙 (yoneda.obj T)))
    (MorphismProperty.presheaf_of_isIso _ (𝟙 (yoneda.obj T)))

end Canonical

end BeauvilleLaszlo.Space

end
