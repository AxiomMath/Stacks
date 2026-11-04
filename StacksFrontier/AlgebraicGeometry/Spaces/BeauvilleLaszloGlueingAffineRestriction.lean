module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingDataIso
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpaceYoneda

/-!
# Restricting the Beauville--Laszlo glueing functor to the affine glueable spaces

Fix a Beauville--Laszlo glueing pair `(g : R → R', f)`, write `X = Spec R`, `U = Spec R_f`,
`X' = Spec R'`, `U' = Spec R'_f`, and let `G` be a glueing functor of Stacks 0F9N for the
resulting square. Stacks 0F9Q asserts that `G` restricts to an *equivalence* between the affine
algebraic spaces over `X` which are glueable for `(g, f)` and the cartesian glueing triples with
affine components. This module carries the elementary half of that assertion — the restricted
functor itself, its identification with `G`, and the dictionary between representable algebraic
spaces and objects of the site which the two substantial halves are phrased in.

## Main definitions

* `BeauvilleLaszlo.Space.pairGU`, `pairGX'`, `pairJU`, `pairJX'` are the four morphisms of the
  Beauville--Laszlo square of `(g, f)`.
* `BeauvilleLaszlo.Space.spaceOfSite` is the algebraic space represented by an object of the
  site, that is `AlgebraicGeometry.schemeSpace`, with `spaceOfSiteHom` and `spaceOfSiteIso` its
  action on morphisms and isomorphisms.
* `BeauvilleLaszlo.Space.affineGlueableRestriction` is the restriction of a glueing functor to
  the affine glueable spaces.

## Main results

* `BeauvilleLaszlo.Space.baseChangeSpaceOfSiteIso` and
  `baseChangeSpaceOfSiteIso_naturality`: base change of a representable algebraic space is
  represented by the base change of the representing object, naturally.
* `BeauvilleLaszlo.Space.isGlueableAlgebraicSpace_spaceOfSite`: an affine algebraic space whose
  global sections are glueable is a glueable algebraic space.
* `BeauvilleLaszlo.Space.affineGlueableRestrictionCompIso` and
  `faithful_comp_glueingFunctor`: the restricted functor composed with the inclusion is the
  glueing functor, and it is faithful as soon as the glueing functor is injective on the
  relevant hom-sets, which is Stacks 0F9S.

## Implementation notes

Everything here is stated for an arbitrary `BeauvilleLaszlo.Space.GlueingFunctorSpec`, not for
the canonical glueing functor of Stacks 0F9N: the structural facts needed are exactly the
natural identifications of the three components with the three base changes, which are the
fields of that structure, and keeping the functor opaque avoids unfolding its construction.

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

section Setup

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (B : BigFppfSite.{u})
  (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
  (hU : B.Contains (Spec (.of (Localization.Away f))))
  (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))

/-- The morphism `U' → U` of the Beauville--Laszlo square. -/
noncomputable def pairGU : B.obj hU' ⟶ B.obj hU :=
  ⟨Spec.map (CommRingCat.ofHom (Localization.awayMap g f))⟩

/-- The morphism `U' → X'` of the Beauville--Laszlo square. -/
noncomputable def pairGX' : B.obj hU' ⟶ B.obj hX' :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f))))⟩

/-- The morphism `U → X` of the Beauville--Laszlo square. -/
noncomputable def pairJU : B.obj hU ⟶ B.obj hX :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))⟩

/-- The morphism `X' → X` of the Beauville--Laszlo square. -/
noncomputable def pairJX' : B.obj hX' ⟶ B.obj hX :=
  ⟨Spec.map (CommRingCat.ofHom g)⟩

end Setup

section Representable

variable (B : BigFppfSite.{u}) (S T : Scheme.{u}) (hS : B.Contains S) (hT : B.Contains T)

/-- A representable algebraic space, as an object of `AlgebraicSpaces`: the algebraic space
`AlgebraicGeometry.schemeSpace W` of `W`, whose algebraicity `hW` is automatic. -/
noncomputable abbrev spaceOfSite (W : BigFppfOver B S hS)
    (_hW : IsAlgebraicSpace B S hS (yoneda.obj W)) : AlgebraicSpaces B S hS :=
  schemeSpace W

/-- An isomorphism of objects of the site induces one of the represented algebraic spaces. -/
noncomputable def spaceOfSiteIso {W W' : BigFppfOver B S hS} (e : W ≅ W')
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W))
    (hW' : IsAlgebraicSpace B S hS (yoneda.obj W')) :
    spaceOfSite B S hS W hW ≅ spaceOfSite B S hS W' hW' :=
  (schemeSpaceFunctor B S hS).mapIso e

/-- The forward morphism of `spaceOfSiteIso e` is `schemeSpaceMap e.hom`. -/
@[simp]
theorem spaceOfSiteIso_hom {W W' : BigFppfOver B S hS} (e : W ≅ W')
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W))
    (hW' : IsAlgebraicSpace B S hS (yoneda.obj W')) :
    (spaceOfSiteIso B S hS e hW hW').hom = schemeSpaceMap e.hom :=
  rfl

/-- The inverse morphism of `spaceOfSiteIso e` is `schemeSpaceMap e.inv`. -/
@[simp]
theorem spaceOfSiteIso_inv {W W' : BigFppfOver B S hS} (e : W ≅ W')
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W))
    (hW' : IsAlgebraicSpace B S hS (yoneda.obj W')) :
    (spaceOfSiteIso B S hS e hW hW').inv = schemeSpaceMap e.inv :=
  rfl

/-- A morphism of objects of the site induces one of the represented algebraic spaces. -/
noncomputable abbrev spaceOfSiteHom {W W' : BigFppfOver B S hS} (k : W ⟶ W')
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W))
    (hW' : IsAlgebraicSpace B S hS (yoneda.obj W')) :
    spaceOfSite B S hS W hW ⟶ spaceOfSite B S hS W' hW' :=
  schemeSpaceMap k

/-- **The base change of a representable algebraic space is represented by the base change of
the representing object.** -/
noncomputable def baseChangeSpaceOfSiteIso (g : B.obj hS ⟶ B.obj hT) (W : BigFppfOver B T hT)
    (hW : IsAlgebraicSpace B T hT (yoneda.obj W))
    (hW' : IsAlgebraicSpace B S hS (yoneda.obj ((Over.pullback g).obj W))) :
    (baseChange B S T hS hT g).obj (spaceOfSite B T hT W hW) ≅
      spaceOfSite B S hS ((Over.pullback g).obj W) hW' :=
  ObjectProperty.isoMk (IsAlgebraicSpace B S hS)
    ((OverShriek.relocalizeRestrict g).mapIso (schemeSpaceIso W) ≪≫
      (OverShriek.restrictYonedaIso g W).symm ≪≫ (schemeSpaceIso _).symm)

/-- Base change of a representable algebraic space is base change of the representing
object. -/
theorem baseChangeSpaceOfSiteIso_naturality (g : B.obj hS ⟶ B.obj hT)
    {W W' : BigFppfOver B T hT} (k : W ⟶ W')
    (hW : IsAlgebraicSpace B T hT (yoneda.obj W))
    (hW₂ : IsAlgebraicSpace B T hT (yoneda.obj W'))
    (hW' : IsAlgebraicSpace B S hS (yoneda.obj ((Over.pullback g).obj W)))
    (hW'₂ : IsAlgebraicSpace B S hS (yoneda.obj ((Over.pullback g).obj W'))) :
    (baseChange B S T hS hT g).map (spaceOfSiteHom B T hT k hW hW₂) ≫
        (baseChangeSpaceOfSiteIso B S T hS hT g W' hW₂ hW'₂).hom =
      (baseChangeSpaceOfSiteIso B S T hS hT g W hW hW').hom ≫
        spaceOfSiteHom B S hS ((Over.pullback g).map k) hW' hW'₂ := by
  have h : (OverShriek.relocalizeRestrict g).map (yoneda.map k) ≫
      (OverShriek.restrictYonedaIso g W').inv =
    (OverShriek.restrictYonedaIso g W).inv ≫ yoneda.map ((Over.pullback g).map k) := by
    rw [Iso.comp_inv_eq, Category.assoc, OverShriek.restrictYonedaIso_naturality,
      Iso.inv_hom_id_assoc]
  have h' : (OverShriek.relocalizeRestrict g).map (schemeSpaceMap k).hom ≫
      (OverShriek.relocalizeRestrict g).map (schemeSpaceIso W').hom ≫
        (OverShriek.restrictYonedaIso g W').inv ≫ (schemeSpaceIso _).inv =
    ((OverShriek.relocalizeRestrict g).map (schemeSpaceIso W).hom ≫
        (OverShriek.restrictYonedaIso g W).inv ≫ (schemeSpaceIso _).inv) ≫
      (schemeSpaceMap ((Over.pullback g).map k)).hom := by
    rw [← Functor.map_comp_assoc, schemeSpaceMap_hom_comp_schemeSpaceIso_hom, Functor.map_comp,
      Category.assoc, reassoc_of% h]
    simp only [Category.assoc, schemeSpaceIso_inv_comp_schemeSpaceMap_hom]
  exact ObjectProperty.hom_ext _ h'

end Representable

section Glueable

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
  (hX : B.Contains (Spec (.of R)))

include hglue in
/-- **An affine algebraic space with glueable global sections is glueable.** It is covered by
itself, so Stacks 0F9P applies to the one-member covering. -/
theorem isGlueableAlgebraicSpace_spaceOfSite (W : BigFppfOver B (Spec (.of R)) hX)
    (hWaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hX).obj W))
    (hWglue : AlgebraicGeometry.Space.IsGlueableGlobalSections g f B hX W)
    (hW : IsAlgebraicSpace B (Spec (.of R)) hX (yoneda.obj W)) :
    AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX
      (spaceOfSite B (Spec (.of R)) hX W hW) := by
  refine (AlgebraicGeometry.Space.exists_etaleCovering_iff_isGlueable g f hglue B hX _).mp ?_
  refine ⟨PUnit.{u + 2}, fun _ ↦ W, fun _ ↦ (schemeSpaceIso W).inv, ?_, fun _ ↦ ⟨hWaff, hWglue⟩⟩
  refine ⟨(schemeSpace W).property, fun _ ↦ hW,
    fun _ ↦ AlgebraicGeometry.Space.isEtale_of_isIso _ _ _ _, ?_⟩
  exact Set.eq_univ_of_univ_subset (Set.subset_iUnion_of_subset PUnit.unit
    (AlgebraicGeometry.Space.pointsMap_surjective_of_isIso _ _ _ _).range_eq.symm.le)

end Glueable

section Square

variable (B : BigFppfSite.{u}) (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
  (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
  (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
  (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)

/-- **The two iterated base changes of a commutative square agree on objects.** Both are the
base change along the common composite `U' → X`, which is how `GlueingFunctorSpec` phrases the
two structure arrows of a glueing triple.

This is recorded as an equality of objects, rather than used through the canonical isomorphism
`BeauvilleLaszlo.Space.squareBaseChangeIso`, because that is the form the two fields
`BeauvilleLaszlo.Space.GlueingFunctorSpec.toU_eq` and `toX'_eq` put the comparison in. It is
proved once, here, where the square and the algebraic space are abstract: the two `rfl` steps
below are the associativity of composition in the site, and asking for them anywhere the square
is a concrete Beauville--Laszlo square instead is asking for them on much larger terms. -/
theorem baseChange_square_obj_eq (hcomm : gU ≫ jU = gX' ≫ jX')
    (Y : AlgebraicSpaces B X hX) :
    (baseChange B U' U hU' hU gU).obj ((baseChange B U X hU hX jU).obj Y) =
      (baseChange B U' X' hU' hX' gX').obj ((baseChange B X' X hX' hX jX').obj Y) := by
  have h₁ : (baseChange B U' X hU' hX (gU ≫ jU)).obj Y =
      (baseChange B U' U hU' hU gU).obj ((baseChange B U X hU hX jU).obj Y) := rfl
  have h₂ : (baseChange B U' X hU' hX (gX' ≫ jX')).obj Y =
      (baseChange B U' X' hU' hX' gX').obj ((baseChange B X' X hX' hX jX').obj Y) := rfl
  rw [← h₁, ← h₂, hcomm]

/-- **The two structure arrows of the glueing triple of an algebraic space agree**, once the two
outer components are identified with the two base changes and the two iterated base changes with
each other. This is the content of the two fields
`BeauvilleLaszlo.Space.GlueingFunctorSpec.toU_eq` and `toX'_eq` taken together: each identifies
its structure arrow with the middle component identification, so the middle one cancels and only
the comparison of the two iterated base changes is left. -/
theorem functor_obj_toU_comp_eq_toX'_comp {hcomm : gU ≫ jU = gX' ≫ jX'}
    (G : GlueingFunctorSpec B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm)
    (Y : AlgebraicSpaces B X hX) :
    (G.functor.obj Y).1.left.hom ≫
        (baseChange B U' U hU' hU gU).map (G.overUIso.hom.app Y) ≫
          eqToHom (baseChange_square_obj_eq B U' U X' X hU' hU hX' hX
            gU gX' jU jX' hcomm Y) =
      (G.functor.obj Y).1.hom ≫
        (baseChange B U' X' hU' hX' gX').map (G.overX'Iso.hom.app Y) := by
  rw [← Category.assoc, G.toU_eq Y, G.toX'_eq Y, Category.assoc, eqToHom_trans]

end Square

section Restriction

variable {R R' : Type u} [CommRing R] [CommRing R'] {g : R →+* R'} {f : R}
  (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f)
  {B : BigFppfSite.{u}}
  {hU' : B.Contains (Spec (.of (Localization.Away (g f))))}
  {hU : B.Contains (Spec (.of (Localization.Away f)))}
  {hX' : B.Contains (Spec (.of R'))} {hX : B.Contains (Spec (.of R))}
  {gU : B.obj hU' ⟶ B.obj hU} {gX' : B.obj hU' ⟶ B.obj hX'}
  {jU : B.obj hU ⟶ B.obj hX} {jX' : B.obj hX' ⟶ B.obj hX}
  {hcomm : gU ≫ jU = gX' ≫ jX'}
  (G : GlueingFunctorSpec B (Spec (.of (Localization.Away (g f))))
    (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R))
    hU' hU hX' hX gU gX' jU jX' hcomm)

/-- The restriction of a glueing functor of Stacks 0F9N to the full subcategory of affine
glueable algebraic spaces over `Spec R`. -/
noncomputable def affineGlueableRestriction :
    (affineGlueableSpaces g f B hX).FullSubcategory ⥤
      (affineComponents B (Spec (.of (Localization.Away (g f))))
        (Spec (.of (Localization.Away f))) (Spec (.of R')) hU' hU hX' gU gX').FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι (affineGlueableSpaces g f B hX) ⋙ G.functor)
    (fun Y => isAffineSpace_components B (Spec (.of (Localization.Away (g f))))
      (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R)) hU' hU hX' hX
      gU gX' jU jX' hcomm G Y.1 Y.property.1)

/-- The forward functor of the equivalence of Stacks 0F9Q is the restriction of the glueing
functor. -/
noncomputable def affineGlueableRestrictionCompIso :
    affineGlueableRestriction G ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι (affineGlueableSpaces g f B hX) ⋙ G.functor :=
  ObjectProperty.liftCompιIso _ _ _

/-- Faithfulness of the glueing functor on the affine glueable spaces, in the form in which
Stacks 0F9S supplies it. -/
theorem faithful_comp_glueingFunctor
    (hinj : ∀ Y Z : AlgebraicSpaces B (Spec (.of R)) hX,
      AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y →
      AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Z →
      Function.Injective (fun φ : Y ⟶ Z ↦ G.functor.map φ)) :
    (ObjectProperty.ι (affineGlueableSpaces g f B hX) ⋙ G.functor).Faithful := by
  constructor
  intro Y Z a b h
  exact ObjectProperty.hom_ext _ (hinj Y.1 Z.1 Y.property.2 Z.property.2 h)

end Restriction

end BeauvilleLaszlo.Space

end

