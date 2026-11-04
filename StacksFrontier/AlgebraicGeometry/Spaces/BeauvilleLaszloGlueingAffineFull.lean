module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpacePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineRestriction
public import StacksFrontier.RingTheory.BeauvilleLaszlo.AlgebraGlueingPair

/-!
# The affine dictionary for the Beauville--Laszlo glueing functor

Fix a Beauville--Laszlo glueing pair `(g : R → R', f)`, write `X = Spec R`, `U = Spec R_f`,
`X' = Spec R'` and `U' = Spec R'_f`, and let `G` be a glueing functor of Stacks 0F9N for the
resulting square. Stacks 0F9Q asserts that `G` restricts to an equivalence between the affine
algebraic spaces over `X` which are glueable for `(g, f)` and the cartesian glueing triples
with affine components.

This module develops the dictionary through which the *fullness* half of that assertion is
proved: it identifies the four morphisms of the Beauville--Laszlo square with structure
morphisms of objects of the site, translates morphisms of representable affine algebraic
spaces and their base changes into algebra maps, reads glueability of an affine glueable
algebraic space off its coordinate ring, and glues a compatible pair of algebra maps.

## Main definitions

* `BeauvilleLaszlo.Space.yonedaSpace` and `BeauvilleLaszlo.Space.specSpace`: the algebraic
  space `AlgebraicGeometry.schemeSpace` represented by an object of the site, resp. by the
  spectrum of an algebra.
* `BeauvilleLaszlo.Space.yonedaSpaceHomEquiv` and
  `BeauvilleLaszlo.Space.specSpaceAlgHomEquiv`: morphisms of representable algebraic spaces are
  morphisms of the representing objects, resp. algebra maps in the other direction.
* `BeauvilleLaszlo.Space.specSpaceBaseChangeIso`: for a pushout square of rings, the base
  change of the space represented by `Spec A` is the space represented by `Spec A₁`, and
  `BeauvilleLaszlo.Space.twoStepBaseChangeIso` is its iterated form.

## Main results

* `BeauvilleLaszlo.Space.pairJU_eq_specSite_hom`,
  `BeauvilleLaszlo.Space.pairJX'_eq_specSite_hom`,
  `BeauvilleLaszlo.Space.pairGU_eq_specSite_hom`,
  `BeauvilleLaszlo.Space.pairGX'_eq_specSite_hom`: the four morphisms of the
  Beauville--Laszlo square are the structure morphisms of the four objects
  `AlgebraicGeometry.Space.specSite` of the site.
* `BeauvilleLaszlo.Space.pairGU_comp_pairJU_eq_specSite_hom` and
  `BeauvilleLaszlo.Space.pairGX'_comp_pairJX'_eq_specSite_hom`: both composites `U' → X` of the
  Beauville--Laszlo square are the structure morphism of `Spec R'_f` over `Spec R`, so that the
  commutativity of the square is a comparison of two casts over one object.
* `BeauvilleLaszlo.Space.specSpaceBaseChangeIso_inv_app_id_left` and
  `BeauvilleLaszlo.Space.twoStepBaseChangeIso_inv_app_id_left`: the tautological point of a
  one-step, resp. two-step, base change projects to `Spec` of the structure map, resp. of the
  composite of the two structure maps.
* `BeauvilleLaszlo.Space.schemeSpace_hom_app_eq`,
  `BeauvilleLaszlo.Space.hom_ext_of_section_comp` and
  `BeauvilleLaszlo.Space.eqToHom_baseChange_app_left`: a morphism out of a representable
  algebraic space is computed from, and determined by, its tautological point, and a cast along
  an equality of base-change morphisms does not move a section.
* `BeauvilleLaszlo.Space.specSpaceAlgHomEquiv_baseChange`: **the base-change dictionary.** The
  algebra map attached to the base change of a morphism of representable affine spaces is
  determined by the original algebra map through the two structure maps of the base change.
* `BeauvilleLaszlo.Space.isGlueableFor_of_isGlueableAlgebraicSpace`: an affine glueable
  algebraic space has glueable coordinate ring.
* `BeauvilleLaszlo.Space.exists_algHom_of_baseChanges_compatible`: a compatible pair of ring
  maps into the two base changes of a glueable algebra, compatible with the structure maps,
  comes from an algebra map.

## Implementation notes

The four morphisms of the Beauville--Laszlo square are the structure morphisms of the objects
`AlgebraicGeometry.Space.specSite` of the site attached to the four rings, which is what lets
the affine presentation theory of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineSpacePresentation` be applied to them; the four
identifications hold definitionally, which is why the development is carried out for an
`Algebra R R'` whose structure map is the given ring map rather than for a bare ring map —
the algebra instances appearing in the base changes are then found by instance synthesis, and
the statement for a bare ring map follows by `RingHom.toAlgebra`.

The base-change dictionary is assembled in two independent halves, which keeps the
associativity bookkeeping of the site separate from the ring-theoretic content:
`BeauvilleLaszlo.Space.specSiteBaseChangeIso_conj_left` records that the conjugated base change
of a morphism of the site commutes with the two structure maps of the base change, and
`BeauvilleLaszlo.Space.specSiteHomEquiv_apply_of_comp` turns any such commutative square into
the transposed square of algebra maps.

Two identifications of one and the same base change are compared through their tautological
points `AlgebraicGeometry.schemeSpacePointEquiv` rather than directly:
`AlgebraicGeometry.schemeSpace_point_ext` reduces such a comparison to an equality of sections,
and a section of a base change of the algebraic space of `W` is read as a morphism of the site
into `W` through `AlgebraicGeometry.schemeSpaceIso`, never by unfolding
`AlgebraicGeometry.schemeSpace`. That reduces the comparison to an equality of morphisms of an
over-category, which `CategoryTheory.Over.OverMorphism.ext` reduces further to the underlying
morphisms of schemes, and `BeauvilleLaszlo.Space.eqToHom_baseChange_app_left` — proved by
substituting the equality of the two base-change morphisms — shows that the casts occurring in
such comparisons act trivially there.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9S](https://stacks.math.columbia.edu/tag/0F9S)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace BeauvilleLaszlo.Space

/-- For a tower of algebras the two structure morphisms of the site compose to the third. -/
private theorem specSite_hom_comp_aux {R₀ R₁ R₂ : Type u} [CommRing R₀] [CommRing R₁]
    [CommRing R₂] [Algebra R₀ R₁] [Algebra R₁ R₂] [Algebra R₀ R₂] [IsScalarTower R₀ R₁ R₂]
    (B : BigFppfSite.{u}) (hX₀ : B.Contains (Spec (.of R₀)))
    (hX₁ : B.Contains (Spec (.of R₁))) (hX₂ : B.Contains (Spec (.of R₂))) :
    (AlgebraicGeometry.Space.specSite B hX₁ hX₂).hom ≫
        (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom =
      (AlgebraicGeometry.Space.specSite B hX₀ hX₂).hom := by
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (algebraMap R₁ R₂)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R₀ R₁)) =
    Spec.map (CommRingCat.ofHom (algebraMap R₀ R₂))
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply R₀ R₁ R₂ r).symm

section Square

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
  (B : BigFppfSite.{u})
  (hU' : B.Contains (Spec (.of (Localization.Away ((algebraMap R R') f)))))
  (hU : B.Contains (Spec (.of (Localization.Away f))))
  (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))

/-- The morphism `U → X` of the Beauville--Laszlo square is the structure morphism of
`Spec R_f` as an object of the big fppf category over `Spec R`. -/
theorem pairJU_eq_specSite_hom :
    pairJU f B hU hX = (AlgebraicGeometry.Space.specSite B hX hU).hom :=
  rfl

/-- The morphism `X' → X` of the Beauville--Laszlo square is the structure morphism of
`Spec R'` as an object of the big fppf category over `Spec R`. -/
theorem pairJX'_eq_specSite_hom :
    pairJX' (algebraMap R R') B hX' hX = (AlgebraicGeometry.Space.specSite B hX hX').hom :=
  rfl

/-- The morphism `U' → U` of the Beauville--Laszlo square is the structure morphism of
`Spec R'_f` as an object of the big fppf category over `Spec R_f`. -/
theorem pairGU_eq_specSite_hom :
    pairGU (algebraMap R R') f B hU' hU = (AlgebraicGeometry.Space.specSite B hU hU').hom :=
  rfl

/-- The morphism `U' → X'` of the Beauville--Laszlo square is the structure morphism of
`Spec R'_f` as an object of the big fppf category over `Spec R'`. -/
theorem pairGX'_eq_specSite_hom :
    pairGX' (algebraMap R R') f B hU' hX' = (AlgebraicGeometry.Space.specSite B hX' hU').hom :=
  rfl

/-- The composite `U' → U → X` of the Beauville--Laszlo square is the structure morphism of
`Spec R'_f` as an object of the big fppf category over `Spec R`. -/
theorem pairGU_comp_pairJU_eq_specSite_hom :
    pairGU (algebraMap R R') f B hU' hU ≫ pairJU f B hU hX =
      (AlgebraicGeometry.Space.specSite B hX hU').hom :=
  specSite_hom_comp_aux B hX hU hU'

/-- The composite `U' → X' → X` of the Beauville--Laszlo square is the structure morphism of
`Spec R'_f` as an object of the big fppf category over `Spec R`. -/
theorem pairGX'_comp_pairJX'_eq_specSite_hom :
    pairGX' (algebraMap R R') f B hU' hX' ≫ pairJX' (algebraMap R R') B hX' hX =
      (AlgebraicGeometry.Space.specSite B hX hU').hom :=
  specSite_hom_comp_aux B hX hX' hU'

end Square

section Transport

/-- Surjectivity of the map a functor induces on a hom-set only depends on the isomorphism
classes of the source and the target. -/
theorem surjective_map_of_iso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {Y Z Y₀ Z₀ : C} (eY : Y ≅ Y₀) (eZ : Z ≅ Z₀)
    (h : Function.Surjective (F.map (X := Y₀) (Y := Z₀))) :
    Function.Surjective (F.map (X := Y) (Y := Z)) := by
  intro β
  obtain ⟨φ, hφ⟩ := h ((F.mapIso eY).inv ≫ β ≫ (F.mapIso eZ).hom)
  refine ⟨eY.hom ≫ φ ≫ eZ.inv, ?_⟩
  rw [F.map_comp, F.map_comp, hφ]
  simp

end Transport

section Dictionary

/-- The algebraic space represented by an object of the big fppf site: the algebraic space
`AlgebraicGeometry.schemeSpace W` of `W`. -/
noncomputable abbrev yonedaSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (W : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  schemeSpace W

/-- The morphism of representable algebraic spaces induced by a morphism of the site:
`AlgebraicGeometry.schemeSpaceMap`. -/
noncomputable abbrev yonedaSpaceHom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W W' : BigFppfOver B S hS} (k : W ⟶ W') :
    yonedaSpace B S hS W ⟶ yonedaSpace B S hS W' :=
  schemeSpaceMap k

/-- Passing from morphisms of the site to morphisms of representable algebraic spaces is
functorial. -/
theorem yonedaSpaceHom_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W W' W'' : BigFppfOver B S hS} (p : W ⟶ W') (q : W' ⟶ W'') :
    yonedaSpaceHom B S hS p ≫ yonedaSpaceHom B S hS q = yonedaSpaceHom B S hS (p ≫ q) :=
  ((schemeSpaceFunctor B S hS).map_comp p q).symm

/-- **A morphism of representable algebraic spaces is a morphism of the representing objects of
the site.** Both the Yoneda embedding and the inclusion of the algebraic spaces into presheaves
are fully faithful. -/
noncomputable def yonedaSpaceHomEquiv (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (W W' : BigFppfOver B S hS) :
    (yonedaSpace B S hS W ⟶ yonedaSpace B S hS W') ≃ (W ⟶ W') where
  toFun φ := (schemeSpaceFunctor B S hS).preimage φ
  invFun k := yonedaSpaceHom B S hS k
  left_inv φ := (schemeSpaceFunctor B S hS).map_preimage φ
  right_inv k := (schemeSpaceFunctor B S hS).preimage_map k

/-- The algebraic space represented by the spectrum of an algebra. -/
noncomputable abbrev specSpace {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A))) :
    AlgebraicSpaces B (Spec (.of R)) hX :=
  yonedaSpace B (Spec (.of R)) hX (AlgebraicGeometry.Space.specSite B hX hA)

/-- **The hom dictionary for representable affine algebraic spaces over an affine base.** A
morphism between the algebraic spaces represented by `Spec A` and by `Spec C` is the same thing
as an `R`-algebra map `C → A`. -/
noncomputable def specSpaceAlgHomEquiv {R A C : Type u} [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra R C] (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (hC : B.Contains (Spec (.of C))) :
    (specSpace B hX hA ⟶ specSpace B hX hC) ≃ (C →ₐ[R] A) :=
  (yonedaSpaceHomEquiv B (Spec (.of R)) hX _ _).trans
    (AlgebraicGeometry.Space.specSiteHomEquiv B hX hA hC)

/-- The algebra map attached to the morphism of representable affine spaces induced by a
morphism of the site is the one the site dictionary attaches to that morphism. -/
theorem specSpaceAlgHomEquiv_yonedaSpaceHom {R A C : Type u} [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra R C] (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (hC : B.Contains (Spec (.of C)))
    (k : AlgebraicGeometry.Space.specSite B hX hA ⟶
      AlgebraicGeometry.Space.specSite B hX hC) :
    specSpaceAlgHomEquiv B hX hA hC (yonedaSpaceHom B (Spec (.of R)) hX k) =
      AlgebraicGeometry.Space.specSiteHomEquiv B hX hA hC k :=
  congrArg (AlgebraicGeometry.Space.specSiteHomEquiv B hX hA hC)
    ((yonedaSpaceHomEquiv B (Spec (.of R)) hX _ _).apply_symm_apply k)

end Dictionary

section Sections

/-- Restriction of a section of the base change of a representable algebraic space is
composition with the underlying morphism of schemes, once the section is read as a morphism of
the site through `AlgebraicGeometry.schemeSpaceIso`. -/
theorem baseChange_map_left (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) (k : B.obj hS ⟶ B.obj hT)
    (W : BigFppfOver B T hT) {V V' : BigFppfOver B S hS} (s : V' ⟶ V)
    (t : ((baseChange B S T hS hT k).obj (schemeSpace W)).obj.obj (Opposite.op V)) :
    ((schemeSpaceIso W).hom.app (Opposite.op ((CategoryTheory.Over.map k).obj V'))
        ((((baseChange B S T hS hT k).obj (schemeSpace W)).obj.map (Opposite.op s)) t)).left =
      s.left ≫ ((schemeSpaceIso W).hom.app
        (Opposite.op ((CategoryTheory.Over.map k).obj V)) t).left :=
  congrArg CategoryTheory.Over.Hom.left
    (NatTrans.naturality_apply (schemeSpaceIso W).hom ((CategoryTheory.Over.map k).map s).op t :)

/-- **The cast along an equality of base-change morphisms is harmless on sections.** The two
base changes of a representable algebraic space along two equal morphisms are identified by a
cast which does not change the underlying morphism of schemes of a section; this is what makes
the commutativity `hcomm` of the Beauville--Laszlo square usable. -/
theorem eqToHom_baseChange_app_left (B : BigFppfSite.{u}) (S T : Scheme.{u})
    (hS : B.Contains S) (hT : B.Contains T) {k₁ k₂ : B.obj hS ⟶ B.obj hT} (hk : k₁ = k₂)
    (W : BigFppfOver B T hT) (V : BigFppfOver B S hS)
    (p : (baseChange B S T hS hT k₁).obj (schemeSpace W) =
      (baseChange B S T hS hT k₂).obj (schemeSpace W))
    (t : ((baseChange B S T hS hT k₁).obj (schemeSpace W)).obj.obj (Opposite.op V)) :
    ((schemeSpaceIso W).hom.app (Opposite.op ((CategoryTheory.Over.map k₂).obj V))
        (((eqToHom p).hom.app (Opposite.op V)) t)).left =
      ((schemeSpaceIso W).hom.app (Opposite.op ((CategoryTheory.Over.map k₁).obj V)) t).left := by
  subst hk
  rfl

/-- **A morphism out of a representable algebraic space is computed from its tautological
point.** Its value at a section `s` over `T` is the restriction of the tautological point
`AlgebraicGeometry.schemeSpacePointEquiv W F α` along the morphism `T ⟶ W` of the site which `s`
is. -/
theorem schemeSpace_hom_app_eq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {W : BigFppfOver B S hS} {F : AlgebraicSpaces B S hS} (α : schemeSpace W ⟶ F)
    {T : BigFppfOver B S hS} (s : (schemeSpace W).obj.obj (Opposite.op T)) :
    α.hom.app (Opposite.op T) s =
      F.obj.map ((schemeSpaceIso W).hom.app (Opposite.op T) s).op
        (schemeSpacePointEquiv W F α) := by
  have h := schemeSpacePointEquiv_schemeSpaceMap_comp
    ((schemeSpaceIso W).hom.app (Opposite.op T) s) α
  rwa [schemeSpacePointEquiv_comp, schemeSpacePointEquiv_schemeSpaceMap,
    Iso.hom_inv_id_app_apply] at h

/-- **Two composites out of a representable algebraic space agree as soon as their tautological
points do.** This is `AlgebraicGeometry.schemeSpace_point_ext` for a pair of composites, with
the hypothesis stated by applying the second factors to the tautological points of the first.

Both the common target `H` and all four factors are abstract, which is what makes the lemma
usable: the identification of the tautological point of a composite with the action of its
second factor on that of its first is then performed once, here, and a comparison of two
presentations of an iterated base change only instantiates it. Performing that identification
at such a comparison instead asks the kernel to reduce the base-change functors of the site and
the Yoneda embedding, which it does not finish. -/
theorem hom_ext_of_section_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : BigFppfOver B S hS) {F G H : AlgebraicSpaces B S hS}
    (a : schemeSpace V ⟶ F) (b : F ⟶ H)
    (c : schemeSpace V ⟶ G) (d : G ⟶ H)
    (h : b.hom.app (Opposite.op V) (schemeSpacePointEquiv V F a) =
      d.hom.app (Opposite.op V) (schemeSpacePointEquiv V G c)) :
    a ≫ b = c ≫ d :=
  schemeSpace_point_ext ((schemeSpacePointEquiv_comp a b).trans
    (h.trans (schemeSpacePointEquiv_comp c d).symm))

end Sections

section BaseChange

variable {R₀ R₁ A A₁ C C₁ : Type u} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  [CommRing A] [Algebra R₀ A] [CommRing A₁] [Algebra R₁ A₁]
  [CommRing C] [Algebra R₀ C] [CommRing C₁] [Algebra R₁ C₁]
  (B : BigFppfSite.{u}) (hX₀ : B.Contains (Spec (.of R₀)))
  (hX₁ : B.Contains (Spec (.of R₁)))

/-- The forward direction of the isomorphism of representable algebraic spaces induced by an
isomorphism of the site. -/
theorem spaceOfSiteIso_hom_eq (S : Scheme.{u}) (hS : B.Contains S)
    {W W' : BigFppfOver B S hS} (e : W ≅ W') :
    (spaceOfSiteIso B S hS e (isAlgebraicSpace_yoneda B S hS W)
        (isAlgebraicSpace_yoneda B S hS W')).hom = yonedaSpaceHom B S hS e.hom :=
  rfl

/-- The backward direction of the isomorphism of representable algebraic spaces induced by an
isomorphism of the site. -/
theorem spaceOfSiteIso_inv_eq (S : Scheme.{u}) (hS : B.Contains S)
    {W W' : BigFppfOver B S hS} (e : W ≅ W') :
    (spaceOfSiteIso B S hS e (isAlgebraicSpace_yoneda B S hS W)
        (isAlgebraicSpace_yoneda B S hS W')).inv = yonedaSpaceHom B S hS e.inv :=
  rfl

/-- Base change of a representable algebraic space along an affine base change, before the
representing object is identified with the spectrum of the base-changed algebra. -/
noncomputable abbrev specSpacePullbackIso (hA : B.Contains (Spec (.of A))) :
    (baseChange B (Spec (.of R₁)) (Spec (.of R₀)) hX₁ hX₀
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj (specSpace B hX₀ hA) ≅
      yonedaSpace B (Spec (.of R₁)) hX₁
        ((CategoryTheory.Over.pullback
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj
          (AlgebraicGeometry.Space.specSite B hX₀ hA)) :=
  baseChangeSpaceOfSiteIso B (Spec (.of R₁)) (Spec (.of R₀)) hX₁ hX₀
    (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom
    (AlgebraicGeometry.Space.specSite B hX₀ hA)
    (isAlgebraicSpace_yoneda B (Spec (.of R₀)) hX₀ _)
    (isAlgebraicSpace_yoneda B (Spec (.of R₁)) hX₁ _)

/-- **Base change of a representable affine algebraic space along an affine base change.** For
a pushout square of rings, the base change of the space represented by `Spec A` is the space
represented by `Spec A₁`. -/
noncomputable def specSpaceBaseChangeIso (u : A →+* A₁)
    (hpush : IsPushout (CommRingCat.ofHom (algebraMap R₀ A))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom u)
      (CommRingCat.ofHom (algebraMap R₁ A₁)))
    (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁))) :
    (baseChange B (Spec (.of R₁)) (Spec (.of R₀)) hX₁ hX₀
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj (specSpace B hX₀ hA) ≅
      specSpace B hX₁ hA₁ :=
  specSpacePullbackIso B hX₀ hX₁ hA ≪≫
    spaceOfSiteIso B (Spec (.of R₁)) hX₁
      (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ u hpush hX₁ hA hA₁)
      (isAlgebraicSpace_yoneda B (Spec (.of R₁)) hX₁ _)
      (isAlgebraicSpace_yoneda B (Spec (.of R₁)) hX₁ _)

/-- The forward direction of the base change isomorphism of representable affine spaces. -/
theorem specSpaceBaseChangeIso_hom (u : A →+* A₁)
    (hpush : IsPushout (CommRingCat.ofHom (algebraMap R₀ A))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom u)
      (CommRingCat.ofHom (algebraMap R₁ A₁)))
    (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁))) :
    (specSpaceBaseChangeIso B hX₀ hX₁ u hpush hA hA₁).hom =
      (specSpacePullbackIso B hX₀ hX₁ hA).hom ≫
        yonedaSpaceHom B (Spec (.of R₁)) hX₁
          (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ u hpush hX₁ hA hA₁).hom :=
  rfl

/-- The backward direction of the base change isomorphism of representable affine spaces. -/
theorem specSpaceBaseChangeIso_inv (u : A →+* A₁)
    (hpush : IsPushout (CommRingCat.ofHom (algebraMap R₀ A))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom u)
      (CommRingCat.ofHom (algebraMap R₁ A₁)))
    (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁))) :
    (specSpaceBaseChangeIso B hX₀ hX₁ u hpush hA hA₁).inv =
      yonedaSpaceHom B (Spec (.of R₁)) hX₁
          (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ u hpush hX₁ hA hA₁).inv ≫
        (specSpacePullbackIso B hX₀ hX₁ hA).inv :=
  rfl

/-- **The projection of the base change to `Spec A`.** The tautological point of the base
change of the space represented by `Spec A`, read as a morphism of the site, has underlying
morphism of schemes `Spec` of the structure map `A → A₁`. -/
theorem specSpaceBaseChangeIso_inv_app_id_left (u : A →+* A₁)
    (hpush : IsPushout (CommRingCat.ofHom (algebraMap R₀ A))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom u)
      (CommRingCat.ofHom (algebraMap R₁ A₁)))
    (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁))) :
    ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX₀ hA)).hom.app
        (Opposite.op ((CategoryTheory.Over.map
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj
          (AlgebraicGeometry.Space.specSite B hX₁ hA₁)))
        (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hX₁ hA₁) _
          (specSpaceBaseChangeIso B hX₀ hX₁ u hpush hA hA₁).inv)).left =
      ObjectProperty.homMk (Spec.map (CommRingCat.ofHom u)) := by
  have key := OverShriek.restrictYonedaIso_hom_app_left
    (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom
    (AlgebraicGeometry.Space.specSite B hX₀ hA)
    (AlgebraicGeometry.Space.specSite B hX₁ hA₁)
    (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ u hpush hX₁ hA hA₁).inv
  rw [AlgebraicGeometry.Space.specSiteBaseChangeIso_inv_left_comp_fst] at key
  refine Eq.trans (congrArg CategoryTheory.Over.Hom.left ?_) key
  refine (congrArg (fun y ↦
      (schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX₀ hA)).hom.app
        (Opposite.op ((CategoryTheory.Over.map
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj
          (AlgebraicGeometry.Space.specSite B hX₁ hA₁)))
        ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX₀ hA)).inv.app
          (Opposite.op ((CategoryTheory.Over.map
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj
            (AlgebraicGeometry.Space.specSite B hX₁ hA₁)))
          ((OverShriek.restrictYonedaIso (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom
            (AlgebraicGeometry.Space.specSite B hX₀ hA)).hom.app
              (Opposite.op (AlgebraicGeometry.Space.specSite B hX₁ hA₁))
            ((schemeSpaceIso ((CategoryTheory.Over.pullback
              (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj
              (AlgebraicGeometry.Space.specSite B hX₀ hA))).hom.app
              (Opposite.op (AlgebraicGeometry.Space.specSite B hX₁ hA₁)) y))))
    (schemeSpacePointEquiv_schemeSpaceMap
      (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ u hpush hX₁ hA hA₁).inv)).trans ?_
  exact (Iso.inv_hom_id_app_apply _ _ _).trans (congrArg
    (fun y ↦ (OverShriek.restrictYonedaIso (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom
      (AlgebraicGeometry.Space.specSite B hX₀ hA)).hom.app
        (Opposite.op (AlgebraicGeometry.Space.specSite B hX₁ hA₁)) y)
    (Iso.inv_hom_id_app_apply _ _ _))

/-- Conjugating the base change of a morphism of representable affine spaces by the base change
isomorphisms gives the morphism of representable affine spaces attached to the base change of
the underlying morphism of the site. -/
theorem specSpaceBaseChangeIso_conj (uA : A →+* A₁) (uC : C →+* C₁)
    (hpA : IsPushout (CommRingCat.ofHom (algebraMap R₀ A))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom uA)
      (CommRingCat.ofHom (algebraMap R₁ A₁)))
    (hpC : IsPushout (CommRingCat.ofHom (algebraMap R₀ C))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom uC)
      (CommRingCat.ofHom (algebraMap R₁ C₁)))
    (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
    (hC : B.Contains (Spec (.of C))) (hC₁ : B.Contains (Spec (.of C₁)))
    (k : AlgebraicGeometry.Space.specSite B hX₀ hA ⟶
      AlgebraicGeometry.Space.specSite B hX₀ hC) :
    (specSpaceBaseChangeIso B hX₀ hX₁ uA hpA hA hA₁).inv ≫
        (baseChange B (Spec (.of R₁)) (Spec (.of R₀)) hX₁ hX₀
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map
          (yonedaSpaceHom B (Spec (.of R₀)) hX₀ k) ≫
        (specSpaceBaseChangeIso B hX₀ hX₁ uC hpC hC hC₁).hom =
      yonedaSpaceHom B (Spec (.of R₁)) hX₁
        ((AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uA hpA hX₁ hA hA₁).inv ≫
          (CategoryTheory.Over.pullback
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k ≫
          (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom) := by
  have hnat : (baseChange B (Spec (.of R₁)) (Spec (.of R₀)) hX₁ hX₀
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map
          (yonedaSpaceHom B (Spec (.of R₀)) hX₀ k) ≫
        (specSpacePullbackIso B hX₀ hX₁ hC).hom =
      (specSpacePullbackIso B hX₀ hX₁ hA).hom ≫
        yonedaSpaceHom B (Spec (.of R₁)) hX₁
          ((CategoryTheory.Over.pullback
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k) :=
    baseChangeSpaceOfSiteIso_naturality B (Spec (.of R₁)) (Spec (.of R₀)) hX₁ hX₀
      (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom k
      (isAlgebraicSpace_yoneda B (Spec (.of R₀)) hX₀ _)
      (isAlgebraicSpace_yoneda B (Spec (.of R₀)) hX₀ _)
      (isAlgebraicSpace_yoneda B (Spec (.of R₁)) hX₁ _)
      (isAlgebraicSpace_yoneda B (Spec (.of R₁)) hX₁ _)
  have hnat' : (baseChange B (Spec (.of R₁)) (Spec (.of R₀)) hX₁ hX₀
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map
          (yonedaSpaceHom B (Spec (.of R₀)) hX₀ k) ≫
        (specSpacePullbackIso B hX₀ hX₁ hC).hom ≫
          yonedaSpaceHom B (Spec (.of R₁)) hX₁
            (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom =
      (specSpacePullbackIso B hX₀ hX₁ hA).hom ≫
        yonedaSpaceHom B (Spec (.of R₁)) hX₁
          ((CategoryTheory.Over.pullback
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k) ≫
          yonedaSpaceHom B (Spec (.of R₁)) hX₁
            (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom := by
    rw [← Category.assoc, hnat, Category.assoc]
  rw [specSpaceBaseChangeIso_inv, specSpaceBaseChangeIso_hom, Category.assoc, hnat',
    Iso.inv_hom_id_assoc]
  exact (congrArg (fun t ↦ yonedaSpaceHom B (Spec (.of R₁)) hX₁
        (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uA hpA hX₁ hA hA₁).inv ≫ t)
      (yonedaSpaceHom_comp B (Spec (.of R₁)) hX₁ _ _)).trans
    (yonedaSpaceHom_comp B (Spec (.of R₁)) hX₁ _ _)

omit [Algebra R₀ R₁] in
/-- **The hom dictionary and a commutative square.** If a morphism of the site over `Spec R₁`
fits in a commutative square with a morphism over `Spec R₀` and the two structure maps of a
base change, then the algebra maps they correspond to fit in the transposed square. -/
theorem specSiteHomEquiv_apply_of_comp (uA : A →+* A₁) (uC : C →+* C₁)
    (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
    (hC : B.Contains (Spec (.of C))) (hC₁ : B.Contains (Spec (.of C₁)))
    (k : AlgebraicGeometry.Space.specSite B hX₀ hA ⟶
      AlgebraicGeometry.Space.specSite B hX₀ hC)
    (m : AlgebraicGeometry.Space.specSite B hX₁ hA₁ ⟶
      AlgebraicGeometry.Space.specSite B hX₁ hC₁)
    (hm : m.left ≫
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom uC)) : B.obj hC₁ ⟶ B.obj hC) =
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom uA)) : B.obj hA₁ ⟶ B.obj hA) ≫
        k.left)
    (c : C) :
    (AlgebraicGeometry.Space.specSiteHomEquiv B hX₁ hA₁ hC₁ m) (uC c) =
      uA ((AlgebraicGeometry.Space.specSiteHomEquiv B hX₀ hA hC k) c) := by
  have hsch : B.inclusion.map m.left ≫ Spec.map (CommRingCat.ofHom uC) =
      Spec.map (CommRingCat.ofHom uA) ≫ B.inclusion.map k.left :=
    (B.inclusion.map_comp _ _).symm.trans
      ((B.inclusion.congr_map hm).trans (B.inclusion.map_comp _ _))
  have hm' : B.inclusion.map m.left =
      Spec.map (CommRingCat.ofHom
        (AlgebraicGeometry.Space.specSiteHomEquiv B hX₁ hA₁ hC₁ m).toRingHom) :=
    AlgebraicGeometry.Space.specSiteHomEquiv_apply_eq B hX₁ hA₁ hC₁ m
  have hk' : B.inclusion.map k.left =
      Spec.map (CommRingCat.ofHom
        (AlgebraicGeometry.Space.specSiteHomEquiv B hX₀ hA hC k).toRingHom) :=
    AlgebraicGeometry.Space.specSiteHomEquiv_apply_eq B hX₀ hA hC k
  have h2 : CommRingCat.ofHom uC ≫ CommRingCat.ofHom
        (AlgebraicGeometry.Space.specSiteHomEquiv B hX₁ hA₁ hC₁ m).toRingHom =
      CommRingCat.ofHom
          (AlgebraicGeometry.Space.specSiteHomEquiv B hX₀ hA hC k).toRingHom ≫
        CommRingCat.ofHom uA := by
    refine Spec.map_injective ?_
    rwa [Spec.map_comp, Spec.map_comp, ← hm', ← hk']
  exact congrArg (fun z : CommRingCat.of C ⟶ CommRingCat.of A₁ ↦ z.hom c) h2

/-- The base change of a morphism of the site, conjugated by the base change isomorphisms,
commutes with the two structure maps of the base change. -/
theorem specSiteBaseChangeIso_conj_left (uA : A →+* A₁) (uC : C →+* C₁)
    (hpA : IsPushout (CommRingCat.ofHom (algebraMap R₀ A))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom uA)
      (CommRingCat.ofHom (algebraMap R₁ A₁)))
    (hpC : IsPushout (CommRingCat.ofHom (algebraMap R₀ C))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom uC)
      (CommRingCat.ofHom (algebraMap R₁ C₁)))
    (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
    (hC : B.Contains (Spec (.of C))) (hC₁ : B.Contains (Spec (.of C₁)))
    (k : AlgebraicGeometry.Space.specSite B hX₀ hA ⟶
      AlgebraicGeometry.Space.specSite B hX₀ hC) :
    ((AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uA hpA hX₁ hA hA₁).inv ≫
          (CategoryTheory.Over.pullback
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k ≫
          (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom).left ≫
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom uC)) : B.obj hC₁ ⟶ B.obj hC) =
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom uA)) : B.obj hA₁ ⟶ B.obj hA) ≫
        k.left := by
  have hfstC :
      (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom.left ≫
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom uC)) : B.obj hC₁ ⟶ B.obj hC) =
      pullback.fst (AlgebraicGeometry.Space.specSite B hX₀ hC).hom
        (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom := by
    rw [← AlgebraicGeometry.Space.specSiteBaseChangeIso_inv_left_comp_fst
      B hX₀ uC hpC hX₁ hC hC₁]
    exact ((CategoryTheory.Over.forget (B.obj hX₁)).mapIso
      (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁)).hom_inv_id_assoc _
  have hpk : ((CategoryTheory.Over.pullback
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k).left ≫
        pullback.fst (AlgebraicGeometry.Space.specSite B hX₀ hC).hom
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom =
      pullback.fst (AlgebraicGeometry.Space.specSite B hX₀ hA).hom
        (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom ≫ k.left :=
    pullback.lift_fst _ _ _
  have e1 : ((AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uA hpA hX₁ hA hA₁).inv ≫
          (CategoryTheory.Over.pullback
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k ≫
          (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom).left ≫
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom uC)) : B.obj hC₁ ⟶ B.obj hC) =
      (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uA hpA hX₁ hA hA₁).inv.left ≫
        ((((CategoryTheory.Over.pullback
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k).left ≫
          (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom.left) ≫
          (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom uC)) :
            B.obj hC₁ ⟶ B.obj hC)) :=
    Category.assoc _ _ _
  have e2 : (((CategoryTheory.Over.pullback
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k).left ≫
          (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom.left) ≫
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom uC)) : B.obj hC₁ ⟶ B.obj hC) =
      ((CategoryTheory.Over.pullback
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k).left ≫
        ((AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom.left ≫
          (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom uC)) :
            B.obj hC₁ ⟶ B.obj hC)) :=
    Category.assoc _ _ _
  have e3 : (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uA hpA hX₁ hA hA₁).inv.left ≫
        (pullback.fst (AlgebraicGeometry.Space.specSite B hX₀ hA).hom
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom ≫ k.left) =
      ((AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uA hpA hX₁ hA hA₁).inv.left ≫
        pullback.fst (AlgebraicGeometry.Space.specSite B hX₀ hA).hom
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom) ≫ k.left :=
    (Category.assoc _ _ _).symm
  rw [e1, e2, hfstC]
  refine (congrArg (fun t ↦
    (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uA hpA hX₁ hA hA₁).inv.left ≫ t)
    hpk).trans ?_
  exact e3.trans (congrArg (fun t ↦ t ≫ k.left)
    (AlgebraicGeometry.Space.specSiteBaseChangeIso_inv_left_comp_fst B hX₀ uA hpA hX₁ hA hA₁))

/-- **The base-change dictionary.** The `R₁`-algebra map attached to the base change of a
morphism of the site is determined by the `R₀`-algebra map attached to that morphism, through
the two structure maps of the base change. -/
theorem specSiteHomEquiv_baseChange_apply (uA : A →+* A₁) (uC : C →+* C₁)
    (hpA : IsPushout (CommRingCat.ofHom (algebraMap R₀ A))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom uA)
      (CommRingCat.ofHom (algebraMap R₁ A₁)))
    (hpC : IsPushout (CommRingCat.ofHom (algebraMap R₀ C))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom uC)
      (CommRingCat.ofHom (algebraMap R₁ C₁)))
    (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
    (hC : B.Contains (Spec (.of C))) (hC₁ : B.Contains (Spec (.of C₁)))
    (k : AlgebraicGeometry.Space.specSite B hX₀ hA ⟶
      AlgebraicGeometry.Space.specSite B hX₀ hC) (c : C) :
    (AlgebraicGeometry.Space.specSiteHomEquiv B hX₁ hA₁ hC₁
        ((AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uA hpA hX₁ hA hA₁).inv ≫
          (CategoryTheory.Over.pullback
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map k ≫
          (AlgebraicGeometry.Space.specSiteBaseChangeIso B hX₀ uC hpC hX₁ hC hC₁).hom))
        (uC c) =
      uA ((AlgebraicGeometry.Space.specSiteHomEquiv B hX₀ hA hC k) c) :=
  specSiteHomEquiv_apply_of_comp B hX₀ hX₁ uA uC hA hA₁ hC hC₁ k _
    (specSiteBaseChangeIso_conj_left B hX₀ hX₁ uA uC hpA hpC hA hA₁ hC hC₁ k) c

/-- **The base-change dictionary, in terms of algebra maps.** Conjugating the base change of a
morphism of representable affine spaces by the base change isomorphisms gives the morphism whose
algebra map is determined by the original one through the two structure maps. -/
theorem specSpaceAlgHomEquiv_baseChange (uA : A →+* A₁) (uC : C →+* C₁)
    (hpA : IsPushout (CommRingCat.ofHom (algebraMap R₀ A))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom uA)
      (CommRingCat.ofHom (algebraMap R₁ A₁)))
    (hpC : IsPushout (CommRingCat.ofHom (algebraMap R₀ C))
      (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom uC)
      (CommRingCat.ofHom (algebraMap R₁ C₁)))
    (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
    (hC : B.Contains (Spec (.of C))) (hC₁ : B.Contains (Spec (.of C₁)))
    (k : AlgebraicGeometry.Space.specSite B hX₀ hA ⟶
      AlgebraicGeometry.Space.specSite B hX₀ hC) (c : C) :
    specSpaceAlgHomEquiv B hX₁ hA₁ hC₁
        ((specSpaceBaseChangeIso B hX₀ hX₁ uA hpA hA hA₁).inv ≫
          (baseChange B (Spec (.of R₁)) (Spec (.of R₀)) hX₁ hX₀
            (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).map
            (yonedaSpaceHom B (Spec (.of R₀)) hX₀ k) ≫
          (specSpaceBaseChangeIso B hX₀ hX₁ uC hpC hC hC₁).hom) (uC c) =
      uA (specSpaceAlgHomEquiv B hX₀ hA hC (yonedaSpaceHom B (Spec (.of R₀)) hX₀ k) c) := by
  rw [specSpaceBaseChangeIso_conj B hX₀ hX₁ uA uC hpA hpC hA hA₁ hC hC₁ k,
    specSpaceAlgHomEquiv_yonedaSpaceHom, specSpaceAlgHomEquiv_yonedaSpaceHom]
  exact specSiteHomEquiv_baseChange_apply B hX₀ hX₁ uA uC hpA hpC hA hA₁ hC hC₁ k c

end BaseChange

section TwoStep

variable {R₀ R₁ R₂ A A₁ A₂ : Type u} [CommRing R₀] [CommRing R₁] [CommRing R₂]
  [CommRing A] [CommRing A₁] [CommRing A₂]
  [Algebra R₀ R₁] [Algebra R₁ R₂] [Algebra R₀ A] [Algebra R₁ A₁] [Algebra R₂ A₂]
  (B : BigFppfSite.{u}) (hX₀ : B.Contains (Spec (.of R₀)))
  (hX₁ : B.Contains (Spec (.of R₁))) (hX₂ : B.Contains (Spec (.of R₂)))
  (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
  (hA₂ : B.Contains (Spec (.of A₂))) (u : A →+* A₁) (u' : A₁ →+* A₂)
  (hpush : IsPushout (CommRingCat.ofHom (algebraMap R₀ A))
    (CommRingCat.ofHom (algebraMap R₀ R₁)) (CommRingCat.ofHom u)
    (CommRingCat.ofHom (algebraMap R₁ A₁)))
  (hpush' : IsPushout (CommRingCat.ofHom (algebraMap R₁ A₁))
    (CommRingCat.ofHom (algebraMap R₁ R₂)) (CommRingCat.ofHom u')
    (CommRingCat.ofHom (algebraMap R₂ A₂)))

/-- **Base change of a representable affine algebraic space in two steps.** -/
noncomputable def twoStepBaseChangeIso :
    (baseChange B (Spec (.of R₂)) (Spec (.of R₁)) hX₂ hX₁
        (AlgebraicGeometry.Space.specSite B hX₁ hX₂).hom).obj
      ((baseChange B (Spec (.of R₁)) (Spec (.of R₀)) hX₁ hX₀
        (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj (specSpace B hX₀ hA)) ≅
      specSpace B hX₂ hA₂ :=
  (baseChange B (Spec (.of R₂)) (Spec (.of R₁)) hX₂ hX₁
        (AlgebraicGeometry.Space.specSite B hX₁ hX₂).hom).mapIso
      (specSpaceBaseChangeIso B hX₀ hX₁ u hpush hA hA₁) ≪≫
    specSpaceBaseChangeIso B hX₁ hX₂ u' hpush' hA₁ hA₂

/-- **The projection of the two-step base change to `Spec A` is `Spec` of the composite of the
two structure maps.** The tautological point of the two-step base change, read as a morphism of
the site, has underlying morphism of schemes `Spec` of `A → A₁ → A₂`. -/
theorem twoStepBaseChangeIso_inv_app_id_left :
    ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX₀ hA)).hom.app
        (Opposite.op ((CategoryTheory.Over.map
          (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj
          ((CategoryTheory.Over.map (AlgebraicGeometry.Space.specSite B hX₁ hX₂).hom).obj
            (AlgebraicGeometry.Space.specSite B hX₂ hA₂))))
        (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hX₂ hA₂) _
          (twoStepBaseChangeIso B hX₀ hX₁ hX₂ hA hA₁ hA₂ u u' hpush hpush').inv)).left =
      ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (u'.comp u))) := by
  have hpt := schemeSpace_hom_app_eq (specSpaceBaseChangeIso B hX₀ hX₁ u hpush hA hA₁).inv
    (T := (CategoryTheory.Over.map (AlgebraicGeometry.Space.specSite B hX₁ hX₂).hom).obj
      (AlgebraicGeometry.Space.specSite B hX₂ hA₂))
    (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hX₂ hA₂) _
      (specSpaceBaseChangeIso B hX₁ hX₂ u' hpush' hA₁ hA₂).inv)
  refine (congrArg (fun z ↦ ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX₀ hA)).hom.app
      (Opposite.op ((CategoryTheory.Over.map
        (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom).obj
        ((CategoryTheory.Over.map (AlgebraicGeometry.Space.specSite B hX₁ hX₂).hom).obj
          (AlgebraicGeometry.Space.specSite B hX₂ hA₂)))) z).left) hpt).trans ?_
  refine (baseChange_map_left B _ _ hX₁ hX₀ _ _ _ _).trans ?_
  refine (congrArg₂ (· ≫ ·)
    (specSpaceBaseChangeIso_inv_app_id_left B hX₁ hX₂ u' hpush' hA₁ hA₂)
    (specSpaceBaseChangeIso_inv_app_id_left B hX₀ hX₁ u hpush hA hA₁)).trans ?_
  apply ObjectProperty.hom_ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- For a tower of algebras the two structure morphisms of the site compose to the third. -/
theorem specSite_hom_comp [Algebra R₀ R₂] [IsScalarTower R₀ R₁ R₂] :
    (AlgebraicGeometry.Space.specSite B hX₁ hX₂).hom ≫
        (AlgebraicGeometry.Space.specSite B hX₀ hX₁).hom =
      (AlgebraicGeometry.Space.specSite B hX₀ hX₂).hom :=
  specSite_hom_comp_aux B hX₀ hX₁ hX₂

end TwoStep

section Glueable

/-- Glueability is invariant under a ring isomorphism compatible with the structure maps. -/
theorem isGlueableFor_of_ringEquiv_comm {R R' A A₂ : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] [CommRing A] [Algebra R A] [CommRing A₂] [Algebra R A₂] (f : R)
    (e : A ≃+* A₂) (he : ∀ r : R, e (algebraMap R A r) = algebraMap R A₂ r)
    (h : BeauvilleLaszlo.IsGlueableFor (S := R') A f) :
    BeauvilleLaszlo.IsGlueableFor (S := R') A₂ f :=
  BeauvilleLaszlo.IsGlueableFor.of_ringEquiv f { e with commutes' := he } h

/-- **An affine glueable algebraic space has glueable coordinate ring.** Testing glueability of
the representable space on the étale covering by itself gives glueability of the global
sections of the representing affine scheme, which `AlgebraicGeometry.Scheme.ΓSpecIso` carries
to the algebra. -/
theorem isGlueableFor_of_isGlueableAlgebraicSpace {R R' A : Type u} [CommRing R]
    [CommRing R'] [CommRing A] [Algebra R A] (g : R →+* R') (f : R) (B : BigFppfSite.{u})
    (hX : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A)))
    (h : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX (specSpace B hX hA)) :
    letI : Algebra R R' := g.toAlgebra
    BeauvilleLaszlo.IsGlueableFor (S := R') A f := by
  let : Algebra R R' := g.toAlgebra
  have hglob := h (AlgebraicGeometry.Space.specSite B hX hA) (schemeSpaceIso _).inv inferInstance
    (AlgebraicGeometry.Space.isEtale_of_isIso B (Spec (.of R)) hX _)
  let : Algebra R Γ(Spec (CommRingCat.of A), ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (B.inclusion.map (AlgebraicGeometry.Space.specSite B hX hA).hom).appTop).hom).toAlgebra
  have hglob' : BeauvilleLaszlo.IsGlueableFor (S := R') Γ(Spec (CommRingCat.of A), ⊤) f :=
    hglob
  have hα : ∀ r : R, algebraMap R Γ(Spec (CommRingCat.of A), ⊤) r =
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop).hom) r := fun _ ↦ rfl
  refine isGlueableFor_of_ringEquiv_comm f
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv (fun r ↦ ?_) hglob'
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop) ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom = CommRingCat.ofHom (algebraMap R A) := by
    rw [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hco : ∀ x : Γ(Spec (CommRingCat.of A), ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv x =
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x := fun _ ↦ rfl
  rw [hα r, hco]
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using
    congrArg (fun z : CommRingCat.of R ⟶ CommRingCat.of A ↦ z.hom r) h2

end Glueable

section RingGlueing

/-- The spectrum of a base change of an algebra whose spectrum the site contains is again an
object of the site: it is the fibre product of two objects of the site. -/
theorem contains_spec_tensorProduct {R A S : Type u} [CommRing R] [CommRing A]
    [CommRing S] [Algebra R A] [Algebra R S] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A))) (hS : B.Contains (Spec (.of S))) :
    B.Contains (Spec (.of (TensorProduct R A S))) := by
  change (Spec (.of (TensorProduct R A S))).size < B.cutoff
  rw [← Scheme.size_congr (pullbackSpecIso R A S)]
  exact Scheme.size_pullback_lt _ _ hA hS

/-- **Glueing a compatible pair of algebra maps.** For a glueable `R`-algebra `A`, a pair of
ring maps from an `R`-algebra `C` into the two base changes of `A` which agree in the base
change to `R'_f` and are compatible with the structure maps comes from an `R`-algebra map
`C → A`. -/
theorem exists_algHom_of_baseChanges_compatible {R R' A C : Type u} [CommRing R]
    [CommRing R'] [Algebra R R'] [CommRing A] [Algebra R A] [CommRing C] [Algebra R C] (f : R)
    (hA : BeauvilleLaszlo.IsGlueableFor (S := R') A f)
    (φ : C →+* TensorProduct R A R')
    (ψ : C →+* TensorProduct R A (Localization.Away f))
    (hcompat : ∀ c, BeauvilleLaszlo.baseChangeToAway (S := R') (M := A) f (φ c) =
      BeauvilleLaszlo.localizedBaseChangeToAway (S := R') (M := A) f (ψ c))
    (hφ : ∀ r : R, φ (algebraMap R C r) = algebraMap R A r ⊗ₜ[R] (1 : R'))
    (hψ : ∀ r : R, ψ (algebraMap R C r) =
      algebraMap R A r ⊗ₜ[R] (1 : Localization.Away f)) :
    ∃ θ : C →ₐ[R] A, (∀ c, (θ c) ⊗ₜ[R] (1 : R') = φ c) ∧
      (∀ c, (θ c) ⊗ₜ[R] (1 : Localization.Away f) = ψ c) := by
  obtain ⟨θ, ⟨h1, h2⟩, -⟩ :=
    BeauvilleLaszlo.existsUnique_ringHom_of_baseChanges_compatible f hA φ ψ hcompat
  refine ⟨{ θ with commutes' := fun r ↦ ?_ }, h1, h2⟩
  apply hA.1
  rw [BeauvilleLaszlo.toTensorBaseChanges_apply, BeauvilleLaszlo.toTensorBaseChanges_apply]
  change ((θ (algebraMap R C r)) ⊗ₜ[R] (1 : R'),
    (θ (algebraMap R C r)) ⊗ₜ[R] (1 : Localization.Away f)) = _
  rw [h1, h2, hφ, hψ]

end RingGlueing

end BeauvilleLaszlo.Space

end

