module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidObjectOfSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SitePullbackContainment
import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealization

/-!
# De-realizing a groupoid in algebraic spaces as a groupoid scheme

`Stacks.Groupoids.GroupoidScheme.realization` turns a groupoid scheme over `S` into a groupoid
in algebraic spaces over a big fppf site, provided the site contains the object scheme, the
arrow scheme and the scheme of composable pairs.  This file goes the other way.

A groupoid in algebraic spaces has no reason to come from a groupoid scheme: its object and
arrow spaces are algebraic spaces, not schemes.  When they *are* representable by schemes of the
site, however, the whole quintuple de-realizes.  The five structure morphisms are obtained from
the corresponding morphisms of presheaves by the full faithfulness of Yoneda, and the groupoid
axioms — which for a groupoid scheme are statements about generalized points over **every**
scheme over `S`, while the groupoid in algebraic spaces only gives equations of presheaves over
the objects of the site — are obtained by reducing each axiom to an equation between morphisms
whose source is one of the four schemes of the presentation, which the site does contain.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation`: **a presentation of a
  groupoid in algebraic spaces by schemes of the site** — a scheme of objects and a scheme of
  arrows which the site contains, together with identifications of the two structure presheaves
  with the presheaves those schemes represent.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.source`, `…target`,
  `…identity`, `…inverse` and `…comp`: the five structure morphisms of schemes a presentation
  de-realizes.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.groupoidObject`: the groupoid
  object of schemes over `S` a presentation de-realizes.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.derealization`: **the groupoid
  scheme a presentation de-realizes.**
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.ofIsRepresentable` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.derealization`: **a groupoid in algebraic spaces
  whose object and arrow spaces are representable is a groupoid scheme**, with no further
  hypothesis.  This is the comparison inverse to
  `Stacks.Groupoids.GroupoidScheme.realization`; that it is one is
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.realizationIso`.
* `AlgebraicGeometry.Space.derealizeSiteHom`: the morphism of schemes over `S` underlying a
  morphism of the presheaves two schemes of the site represent.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.yoneda_source` and its
  companions: each de-realized structure morphism represents the corresponding structure
  morphism of the groupoid in algebraic spaces, read through the two identifications.  Together
  with `…derealization_objects` and its companions they are the precise sense in which the
  de-realization *is* the given groupoid.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.pairMap_comp_fst`,
  `…pairMap_comp_snd` and `…yoneda_comp_pairMap`: the dictionary between generalized composable
  pairs of the de-realization and generalized composable pairs of the groupoid in algebraic
  spaces.  Every axiom is discharged through it.

## Implementation notes

The scheme of composable pairs and the scheme of composable triples of the de-realization are
the chosen fibre products `CategoryTheory.Limits.pullback`, and both are needed: a groupoid
scheme is a groupoid object whose laws are read on generalized points over every scheme over
`S`, and the universal generalized point witnessing the unit and inverse laws lives over the
scheme of composable pairs while the one witnessing associativity lives over the scheme of
composable triples.  Those two are the only test schemes at which anything has to be checked,
which is what `Deformation.GroupoidObject.ofUniversal` makes precise.

That the site contains those two schemes is **not** a hypothesis of the de-realization; it is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.containsPairs` and
`…containsTriples`, both read off
`AlgebraicGeometry.BigFppfSite.contains_pullback_left` — a big fppf site contains the fibre
products of the schemes it contains.  So a presentation is exactly a scheme of objects and a
scheme of arrows which the site contains, together with the two identifications, and nothing
else.  (`Stacks.Groupoids.GroupoidScheme.realization`, going the other way, still asks for the
scheme of composable pairs as a hypothesis `hP`; that hypothesis is likewise redundant, but
removing it would change the signature of every result built on the realization.)

Each axiom is therefore an equation between two morphisms of schemes over `S` whose source and
target the site contains, and
`AlgebraicGeometry.Space.schemeSiteMap_yoneda_injective` reduces it to an equation of
presheaves.  That equation is an instance of the corresponding law of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.toGroupoidObject` at a generalized element indexed
by the presheaf the test scheme represents; those laws are quantified over an arbitrary
presheaf, so no further reduction is needed.

Yoneda carries the chosen fibre product of the de-realized source and target to the presheaf
fibre product of their Yoneda images, which is
`AlgebraicGeometry.Space.yonedaSchemePullbackIso`; the presheaf fibre product of the Yoneda
images is then compared with the presheaf fibre product of the source and target of the groupoid
by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.pairComparison`.  That
comparison is an isomorphism, being induced by isomorphisms of the two cospans, but only the
forward direction is used and it is not built here.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids.GroupoidScheme (schemeSiteMap_id)

namespace AlgebraicGeometry.Space

universe u

/-- **The morphism of schemes over `S` underlying a morphism of the presheaves represented by
two schemes which the site contains.**  Yoneda and the comparison functor from the site to
schemes over `S` are both fully faithful, and the latter returns a scheme of the site unchanged,
so a morphism of represented presheaves comes from a unique morphism of schemes over `S`. -/
noncomputable def derealizeSiteHom (C : BigFppfSite.{u}) {S : Scheme.{u}} (hS : C.Contains S)
    {X Y : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (g : yoneda.obj (schemeSiteObject C hS hX) ⟶ yoneda.obj (schemeSiteObject C hS hY)) :
    X ⟶ Y :=
  (siteToOver C hS).map (yoneda.preimage g)

/-- The presheaf morphism represented by `AlgebraicGeometry.Space.derealizeSiteHom` is the
morphism it was built from. -/
theorem yoneda_schemeSiteMap_derealizeSiteHom (C : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : C.Contains S) {X Y : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (g : yoneda.obj (schemeSiteObject C hS hX) ⟶ yoneda.obj (schemeSiteObject C hS hY)) :
    yoneda.map (schemeSiteMap C hS hX hY (derealizeSiteHom C hS hX hY g)) = g := by
  have h : schemeSiteMap C hS hX hY (derealizeSiteHom C hS hX hY g) = yoneda.preimage g := by
    refine (siteToOver C hS).map_injective ?_
    rw [siteToOver_map_schemeSiteMap]
    rfl
  rw [h, yoneda.map_preimage]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_groupoidSpacesDerealization
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A presentation of a groupoid in algebraic spaces by schemes of the site.**  A scheme of
objects and a scheme of arrows which the site contains, together with identifications of the
object and arrow presheaves of the groupoid with the presheaves those schemes represent. -/
structure SchemePresentation {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B) where
  /-- The scheme of objects. -/
  objects : Over S
  /-- The scheme of arrows. -/
  arrows : Over S
  /-- The site contains the scheme of objects. -/
  containsObjects : C.Contains objects.left
  /-- The site contains the scheme of arrows. -/
  containsArrows : C.Contains arrows.left
  /-- The object space is represented by the scheme of objects. -/
  objectsIso : G.objects.obj ≅ yoneda.obj (Space.schemeSiteObject C hS containsObjects)
  /-- The arrow space is represented by the scheme of arrows. -/
  arrowsIso : G.arrows.obj ≅ yoneda.obj (Space.schemeSiteObject C hS containsArrows)

namespace SchemePresentation

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

/-- The source morphism of schemes a presentation de-realizes. -/
noncomputable def source (P : SchemePresentation G) : P.arrows ⟶ P.objects :=
  Space.derealizeSiteHom C hS P.containsArrows P.containsObjects
    (P.arrowsIso.inv ≫ G.source.hom ≫ P.objectsIso.hom)

/-- The target morphism of schemes a presentation de-realizes. -/
noncomputable def target (P : SchemePresentation G) : P.arrows ⟶ P.objects :=
  Space.derealizeSiteHom C hS P.containsArrows P.containsObjects
    (P.arrowsIso.inv ≫ G.target.hom ≫ P.objectsIso.hom)

/-- The identity morphism of schemes a presentation de-realizes. -/
noncomputable def identity (P : SchemePresentation G) : P.objects ⟶ P.arrows :=
  Space.derealizeSiteHom C hS P.containsObjects P.containsArrows
    (P.objectsIso.inv ≫ (identityHom G).hom ≫ P.arrowsIso.hom)

/-- The inverse morphism of schemes a presentation de-realizes. -/
noncomputable def inverse (P : SchemePresentation G) : P.arrows ⟶ P.arrows :=
  Space.derealizeSiteHom C hS P.containsArrows P.containsArrows
    (P.arrowsIso.inv ≫ (inverseHom G).hom ≫ P.arrowsIso.hom)

/-- The de-realized source represents the source of the groupoid. -/
theorem yoneda_source (P : SchemePresentation G) :
    yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.source) =
      P.arrowsIso.inv ≫ G.source.hom ≫ P.objectsIso.hom :=
  Space.yoneda_schemeSiteMap_derealizeSiteHom C hS P.containsArrows P.containsObjects _

/-- The de-realized target represents the target of the groupoid. -/
theorem yoneda_target (P : SchemePresentation G) :
    yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.target) =
      P.arrowsIso.inv ≫ G.target.hom ≫ P.objectsIso.hom :=
  Space.yoneda_schemeSiteMap_derealizeSiteHom C hS P.containsArrows P.containsObjects _

/-- The de-realized identity represents the unit of the groupoid. -/
theorem yoneda_identity (P : SchemePresentation G) :
    yoneda.map (Space.schemeSiteMap C hS P.containsObjects P.containsArrows P.identity) =
      P.objectsIso.inv ≫ (identityHom G).hom ≫ P.arrowsIso.hom :=
  Space.yoneda_schemeSiteMap_derealizeSiteHom C hS P.containsObjects P.containsArrows _

/-- The de-realized inverse represents the inverse of the groupoid. -/
theorem yoneda_inverse (P : SchemePresentation G) :
    yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsArrows P.inverse) =
      P.arrowsIso.inv ≫ (inverseHom G).hom ≫ P.arrowsIso.hom :=
  Space.yoneda_schemeSiteMap_derealizeSiteHom C hS P.containsArrows P.containsArrows _

/-- **The site contains the scheme of composable pairs of a presentation.**  A big fppf site
contains the fibre products of the schemes it contains, so this is not a further condition on
the presentation. -/
theorem containsPairs (P : SchemePresentation G) :
    C.Contains (pullback P.source P.target).left :=
  C.contains_pullback_left P.source P.target P.containsArrows P.containsArrows

/-- **The site contains the scheme of composable triples of a presentation.** -/
theorem containsTriples (P : SchemePresentation G) :
    C.Contains (pullback (pullback.snd P.source P.target)
      (pullback.fst P.source P.target)).left :=
  C.contains_pullback_left _ _ P.containsPairs P.containsPairs

/-- **The comparison of the presheaf fibre product of the de-realized source and target with the
presheaf fibre product of the source and target of the groupoid.**  On each factor it is the
identification of the arrow presheaf with the presheaf the scheme of arrows represents. -/
noncomputable def pairComparison (P : SchemePresentation G) :
    pullback
        (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
        (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.target)) ⟶
      pullback G.source.hom G.target.hom :=
  pullback.lift
    (pullback.fst
        (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
        (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.target)) ≫
      P.arrowsIso.inv)
    (pullback.snd
        (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
        (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.target)) ≫
      P.arrowsIso.inv)
    (by
      refine (@cancel_mono _ _ _ _ _ P.objectsIso.hom (IsIso.mono_of_iso _) _ _).1 ?_
      have h : pullback.fst
          (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
          (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.target)) ≫
            (P.arrowsIso.inv ≫ G.source.hom ≫ P.objectsIso.hom) =
          pullback.snd
            (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
            (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.target)) ≫
            (P.arrowsIso.inv ≫ G.target.hom ≫ P.objectsIso.hom) := by
        rw [← P.yoneda_source, ← P.yoneda_target]
        exact pullback.condition
      simpa only [Category.assoc] using h)

/-- The first projection of the comparison of fibre products. -/
theorem pairComparison_comp_fst (P : SchemePresentation G) :
    P.pairComparison ≫ pullback.fst G.source.hom G.target.hom =
      pullback.fst
          (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
          (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.target)) ≫
        P.arrowsIso.inv :=
  pullback.lift_fst _ _ _

/-- The second projection of the comparison of fibre products. -/
theorem pairComparison_comp_snd (P : SchemePresentation G) :
    P.pairComparison ≫ pullback.snd G.source.hom G.target.hom =
      pullback.snd
          (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
          (yoneda.map (Space.schemeSiteMap C hS P.containsArrows P.containsObjects P.target)) ≫
        P.arrowsIso.inv :=
  pullback.lift_snd _ _ _

/-- **The composition morphism of schemes a presentation de-realizes**, given that the site
contains its scheme of composable pairs. -/
noncomputable def comp (P : SchemePresentation G)
    :
    pullback P.source P.target ⟶ P.arrows :=
  Space.derealizeSiteHom C hS P.containsPairs P.containsArrows
    ((Space.yonedaSchemePullbackIso C hS P.containsArrows P.containsArrows P.containsObjects
        P.source P.target P.containsPairs).inv ≫
      P.pairComparison ≫ compOnPairs G ≫ P.arrowsIso.hom)

/-- The de-realized composition represents the composition of the groupoid, read through the
identification of the presheaf of the scheme of composable pairs with the presheaf fibre
product. -/
theorem yoneda_comp (P : SchemePresentation G)
    :
    yoneda.map (Space.schemeSiteMap C hS P.containsPairs P.containsArrows (P.comp)) =
      (Space.yonedaSchemePullbackIso C hS P.containsArrows P.containsArrows P.containsObjects
          P.source P.target P.containsPairs).inv ≫
        P.pairComparison ≫ compOnPairs G ≫ P.arrowsIso.hom :=
  Space.yoneda_schemeSiteMap_derealizeSiteHom C hS P.containsPairs P.containsArrows _

/-- **A generalized composable pair of the de-realization, read as a generalized composable pair
of the groupoid in algebraic spaces.** -/
noncomputable def pairMap (P : SchemePresentation G)
    {X : Over S}
    (hX : C.Contains X.left) (k : X ⟶ pullback P.source P.target) :
    yoneda.obj (Space.schemeSiteObject C hS hX) ⟶ pullback G.source.hom G.target.hom :=
  yoneda.map (Space.schemeSiteMap C hS hX P.containsPairs k) ≫
    (Space.yonedaSchemePullbackIso C hS P.containsArrows P.containsArrows P.containsObjects
      P.source P.target P.containsPairs).inv ≫ P.pairComparison

/-- The generalized composable pair of the groupoid determined by a generalized composable pair
of the de-realization, written out. -/
theorem pairMap_eq (P : SchemePresentation G)
    {X : Over S}
    (hX : C.Contains X.left) (k : X ⟶ pullback P.source P.target) :
    P.pairMap hX k = yoneda.map (Space.schemeSiteMap C hS hX P.containsPairs k) ≫
      (Space.yonedaSchemePullbackIso C hS P.containsArrows P.containsArrows P.containsObjects
        P.source P.target P.containsPairs).inv ≫ P.pairComparison := rfl

/-- The first arrow of the generalized composable pair of the groupoid determined by a
generalized composable pair of the de-realization is its first arrow. -/
theorem pairMap_comp_fst (P : SchemePresentation G)
    {X : Over S}
    (hX : C.Contains X.left) (k : X ⟶ pullback P.source P.target) :
    P.pairMap hX k ≫ pullback.fst G.source.hom G.target.hom =
      yoneda.map (Space.schemeSiteMap C hS hX P.containsArrows
        (k ≫ pullback.fst P.source P.target)) ≫ P.arrowsIso.inv := by
  have hι := Space.yonedaSchemePullbackIso_hom_fst C hS P.containsArrows P.containsArrows
    P.containsObjects P.source P.target P.containsPairs
  rw [pairMap_eq, Category.assoc, Category.assoc, pairComparison_comp_fst, ← hι,
    Space.schemeSiteMap_comp C hS hX P.containsPairs P.containsArrows, yoneda.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The second arrow of the generalized composable pair of the groupoid determined by a
generalized composable pair of the de-realization is its second arrow. -/
theorem pairMap_comp_snd (P : SchemePresentation G)
    {X : Over S}
    (hX : C.Contains X.left) (k : X ⟶ pullback P.source P.target) :
    P.pairMap hX k ≫ pullback.snd G.source.hom G.target.hom =
      yoneda.map (Space.schemeSiteMap C hS hX P.containsArrows
        (k ≫ pullback.snd P.source P.target)) ≫ P.arrowsIso.inv := by
  have hι := Space.yonedaSchemePullbackIso_hom_snd C hS P.containsArrows P.containsArrows
    P.containsObjects P.source P.target P.containsPairs
  rw [pairMap_eq, Category.assoc, Category.assoc, pairComparison_comp_snd, ← hι,
    Space.schemeSiteMap_comp C hS hX P.containsPairs P.containsArrows, yoneda.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **Composing a generalized composable pair of the de-realization is composing the generalized
composable pair of the groupoid it determines.** -/
theorem yoneda_comp_pairMap (P : SchemePresentation G)
    {X : Over S}
    (hX : C.Contains X.left) (k : X ⟶ pullback P.source P.target) :
    yoneda.map (Space.schemeSiteMap C hS hX P.containsArrows (k ≫ P.comp)) =
      P.pairMap hX k ≫ compOnPairs G ≫ P.arrowsIso.hom := by
  rw [Space.schemeSiteMap_comp C hS hX P.containsPairs P.containsArrows, yoneda.map_comp,
    P.yoneda_comp, pairMap_eq]
  simp only [Category.assoc]

/-! ### The six equations between structure morphisms -/

/-- The de-realized unit is a section of the de-realized source. -/
theorem identity_comp_source (P : SchemePresentation G) :
    P.identity ≫ P.source = 𝟙 P.objects := by
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsObjects P.containsObjects ?_
  rw [Space.schemeSiteMap_comp C hS P.containsObjects P.containsArrows P.containsObjects,
    yoneda.map_comp, P.yoneda_identity, P.yoneda_source, schemeSiteMap_id, yoneda.map_id]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (identityHom G).hom G.source.hom P.objectsIso.hom,
    identityHom_comp_source G, Category.id_comp, Iso.inv_hom_id]

/-- The de-realized unit is a section of the de-realized target. -/
theorem identity_comp_target (P : SchemePresentation G) :
    P.identity ≫ P.target = 𝟙 P.objects := by
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsObjects P.containsObjects ?_
  rw [Space.schemeSiteMap_comp C hS P.containsObjects P.containsArrows P.containsObjects,
    yoneda.map_comp, P.yoneda_identity, P.yoneda_target, schemeSiteMap_id, yoneda.map_id]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (identityHom G).hom G.target.hom P.objectsIso.hom,
    identityHom_comp_target G, Category.id_comp, Iso.inv_hom_id]

/-- The de-realized inverse exchanges the de-realized source and target. -/
theorem inverse_comp_source (P : SchemePresentation G) : P.inverse ≫ P.source = P.target := by
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsArrows P.containsObjects ?_
  rw [Space.schemeSiteMap_comp C hS P.containsArrows P.containsArrows P.containsObjects,
    yoneda.map_comp, P.yoneda_inverse, P.yoneda_source, P.yoneda_target]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact whisker_eq P.arrowsIso.inv
    ((Category.assoc _ _ _).symm.trans (eq_whisker (inverseHom_comp_source G) P.objectsIso.hom))

/-- The de-realized inverse exchanges the de-realized target and source. -/
theorem inverse_comp_target (P : SchemePresentation G) : P.inverse ≫ P.target = P.source := by
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsArrows P.containsObjects ?_
  rw [Space.schemeSiteMap_comp C hS P.containsArrows P.containsArrows P.containsObjects,
    yoneda.map_comp, P.yoneda_inverse, P.yoneda_target, P.yoneda_source]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact whisker_eq P.arrowsIso.inv
    ((Category.assoc _ _ _).symm.trans (eq_whisker (inverseHom_comp_target G) P.objectsIso.hom))

/-- The universal generalized composable pair of the de-realization: the identity of the scheme
of composable pairs, read as a generalized composable pair of the groupoid. -/
theorem yoneda_comp_eq (P : SchemePresentation G)
    :
    yoneda.map (Space.schemeSiteMap C hS P.containsPairs P.containsArrows (P.comp)) =
      P.pairMap P.containsPairs (𝟙 (pullback P.source P.target)) ≫ compOnPairs G ≫
        P.arrowsIso.hom := by
  have h := P.yoneda_comp_pairMap P.containsPairs (𝟙 (pullback P.source P.target))
  rwa [Category.id_comp] at h

/-- The first arrow of the universal generalized composable pair of the de-realization. -/
theorem pairMap_id_comp_fst (P : SchemePresentation G)
    :
    P.pairMap P.containsPairs (𝟙 (pullback P.source P.target)) ≫
        pullback.fst G.source.hom G.target.hom =
      yoneda.map (Space.schemeSiteMap C hS P.containsPairs P.containsArrows
        (pullback.fst P.source P.target)) ≫ P.arrowsIso.inv := by
  have h := P.pairMap_comp_fst P.containsPairs (𝟙 (pullback P.source P.target))
  rwa [Category.id_comp] at h

/-- The second arrow of the universal generalized composable pair of the de-realization. -/
theorem pairMap_id_comp_snd (P : SchemePresentation G)
    :
    P.pairMap P.containsPairs (𝟙 (pullback P.source P.target)) ≫
        pullback.snd G.source.hom G.target.hom =
      yoneda.map (Space.schemeSiteMap C hS P.containsPairs P.containsArrows
        (pullback.snd P.source P.target)) ≫ P.arrowsIso.inv := by
  have h := P.pairMap_comp_snd P.containsPairs (𝟙 (pullback P.source P.target))
  rwa [Category.id_comp] at h

/-- A composite of a composable pair of the de-realization has the source of the arrow composed
first. -/
theorem comp_comp_source (P : SchemePresentation G)
    :
    P.comp ≫ P.source = pullback.snd P.source P.target ≫ P.source := by
  have key : P.pairMap P.containsPairs (𝟙 (pullback P.source P.target)) ≫
        compOnPairs G ≫ G.source.hom =
      yoneda.map (Space.schemeSiteMap C hS P.containsPairs P.containsArrows
        (pullback.snd P.source P.target)) ≫ P.arrowsIso.inv ≫ G.source.hom := by
    rw [comp_hom_comp_source_hom G,
      ← Category.assoc (P.pairMap P.containsPairs (𝟙 (pullback P.source P.target)))
        (pullback.snd G.source.hom G.target.hom) G.source.hom,
      P.pairMap_id_comp_snd, Category.assoc]
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsPairs P.containsObjects ?_
  rw [Space.schemeSiteMap_comp C hS P.containsPairs P.containsArrows P.containsObjects,
    Space.schemeSiteMap_comp C hS P.containsPairs P.containsArrows P.containsObjects,
    yoneda.map_comp, yoneda.map_comp, P.yoneda_source, P.yoneda_comp_eq]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using eq_whisker key P.objectsIso.hom

/-- A composite of a composable pair of the de-realization has the target of the arrow composed
last. -/
theorem comp_comp_target (P : SchemePresentation G)
    :
    P.comp ≫ P.target = pullback.fst P.source P.target ≫ P.target := by
  have key : P.pairMap P.containsPairs (𝟙 (pullback P.source P.target)) ≫
        compOnPairs G ≫ G.target.hom =
      yoneda.map (Space.schemeSiteMap C hS P.containsPairs P.containsArrows
        (pullback.fst P.source P.target)) ≫ P.arrowsIso.inv ≫ G.target.hom := by
    rw [comp_hom_comp_target_hom G,
      ← Category.assoc (P.pairMap P.containsPairs (𝟙 (pullback P.source P.target)))
        (pullback.fst G.source.hom G.target.hom) G.target.hom,
      P.pairMap_id_comp_fst, Category.assoc]
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsPairs P.containsObjects ?_
  rw [Space.schemeSiteMap_comp C hS P.containsPairs P.containsArrows P.containsObjects,
    Space.schemeSiteMap_comp C hS P.containsPairs P.containsArrows P.containsObjects,
    yoneda.map_comp, yoneda.map_comp, P.yoneda_target, P.yoneda_comp_eq]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using eq_whisker key P.objectsIso.hom

/-- A generalized composable pair of the de-realization whose first arrow is the identity
determines a pair of the groupoid whose first arrow is the identification of the arrows. -/
private theorem pairMap_comp_fst_of_eq_id (P : SchemePresentation G)
    (k : P.arrows ⟶ pullback P.source P.target) (h : k ≫ pullback.fst P.source P.target = 𝟙 _) :
    P.pairMap P.containsArrows k ≫ pullback.fst G.source.hom G.target.hom = P.arrowsIso.inv := by
  rw [P.pairMap_comp_fst P.containsArrows k, h, schemeSiteMap_id, yoneda.map_id,
    Category.id_comp]

/-- A generalized composable pair of the de-realization whose second arrow is the identity
determines a pair of the groupoid whose second arrow is the identification of the arrows. -/
private theorem pairMap_comp_snd_of_eq_id (P : SchemePresentation G)
    (k : P.arrows ⟶ pullback P.source P.target) (h : k ≫ pullback.snd P.source P.target = 𝟙 _) :
    P.pairMap P.containsArrows k ≫ pullback.snd G.source.hom G.target.hom = P.arrowsIso.inv := by
  rw [P.pairMap_comp_snd P.containsArrows k, h, schemeSiteMap_id, yoneda.map_id,
    Category.id_comp]

/-! ### The five laws at the universal composable pair and triple -/

/-- The de-realized unit on the target is a left unit for the de-realized composition. -/
theorem comp_identity_left (P : SchemePresentation G)
    (k : P.arrows ⟶ pullback P.source P.target)
    (h₁ : k ≫ pullback.fst P.source P.target = P.target ≫ P.identity)
    (h₂ : k ≫ pullback.snd P.source P.target = 𝟙 P.arrows) :
    k ≫ P.comp = 𝟙 P.arrows := by
  have key : P.pairMap P.containsArrows k ≫ compOnPairs G = P.arrowsIso.inv := by
    refine (toGroupoidObject G).comp_identity_left P.arrowsIso.inv
      (P.pairMap P.containsArrows k) ?_ ?_
    · change P.pairMap P.containsArrows k ≫ pullback.fst G.source.hom G.target.hom =
        P.arrowsIso.inv ≫ G.target.hom ≫ (identityHom G).hom
      rw [P.pairMap_comp_fst P.containsArrows k, h₁,
        Space.schemeSiteMap_comp C hS P.containsArrows P.containsObjects P.containsArrows,
        yoneda.map_comp, P.yoneda_target, P.yoneda_identity]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    · exact P.pairMap_comp_snd_of_eq_id k h₂
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsArrows P.containsArrows ?_
  rw [P.yoneda_comp_pairMap P.containsArrows k, schemeSiteMap_id, yoneda.map_id,
    ← Category.assoc, key, Iso.inv_hom_id]

/-- The de-realized unit on the source is a right unit for the de-realized composition. -/
theorem comp_identity_right (P : SchemePresentation G)
    (k : P.arrows ⟶ pullback P.source P.target)
    (h₁ : k ≫ pullback.fst P.source P.target = 𝟙 P.arrows)
    (h₂ : k ≫ pullback.snd P.source P.target = P.source ≫ P.identity) :
    k ≫ P.comp = 𝟙 P.arrows := by
  have key : P.pairMap P.containsArrows k ≫ compOnPairs G = P.arrowsIso.inv := by
    refine (toGroupoidObject G).comp_identity_right P.arrowsIso.inv
      (P.pairMap P.containsArrows k) ?_ ?_
    · exact P.pairMap_comp_fst_of_eq_id k h₁
    · change P.pairMap P.containsArrows k ≫ pullback.snd G.source.hom G.target.hom =
        P.arrowsIso.inv ≫ G.source.hom ≫ (identityHom G).hom
      rw [P.pairMap_comp_snd P.containsArrows k, h₂,
        Space.schemeSiteMap_comp C hS P.containsArrows P.containsObjects P.containsArrows,
        yoneda.map_comp, P.yoneda_source, P.yoneda_identity]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsArrows P.containsArrows ?_
  rw [P.yoneda_comp_pairMap P.containsArrows k, schemeSiteMap_id, yoneda.map_id,
    ← Category.assoc, key, Iso.inv_hom_id]

/-- An arrow of the de-realization composed after its inverse is the unit on its source. -/
theorem comp_inverse_left (P : SchemePresentation G)
    (k : P.arrows ⟶ pullback P.source P.target)
    (h₁ : k ≫ pullback.fst P.source P.target = P.inverse)
    (h₂ : k ≫ pullback.snd P.source P.target = 𝟙 P.arrows) :
    k ≫ P.comp = P.source ≫ P.identity := by
  have key : P.pairMap P.containsArrows k ≫ compOnPairs G =
      P.arrowsIso.inv ≫ G.source.hom ≫ (identityHom G).hom := by
    refine (toGroupoidObject G).comp_inverse_left P.arrowsIso.inv
      (P.pairMap P.containsArrows k) ?_ ?_
    · change P.pairMap P.containsArrows k ≫ pullback.fst G.source.hom G.target.hom =
        P.arrowsIso.inv ≫ (inverseHom G).hom
      rw [P.pairMap_comp_fst P.containsArrows k, h₁, P.yoneda_inverse]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · exact P.pairMap_comp_snd_of_eq_id k h₂
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsArrows P.containsArrows ?_
  rw [P.yoneda_comp_pairMap P.containsArrows k,
    Space.schemeSiteMap_comp C hS P.containsArrows P.containsObjects P.containsArrows,
    yoneda.map_comp, P.yoneda_source, P.yoneda_identity, ← Category.assoc, key]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- An arrow of the de-realization composed before its inverse is the unit on its target. -/
theorem comp_inverse_right (P : SchemePresentation G)
    (k : P.arrows ⟶ pullback P.source P.target)
    (h₁ : k ≫ pullback.fst P.source P.target = 𝟙 P.arrows)
    (h₂ : k ≫ pullback.snd P.source P.target = P.inverse) :
    k ≫ P.comp = P.target ≫ P.identity := by
  have key : P.pairMap P.containsArrows k ≫ compOnPairs G =
      P.arrowsIso.inv ≫ G.target.hom ≫ (identityHom G).hom := by
    refine (toGroupoidObject G).comp_inverse_right P.arrowsIso.inv
      (P.pairMap P.containsArrows k) ?_ ?_
    · exact P.pairMap_comp_fst_of_eq_id k h₁
    · change P.pairMap P.containsArrows k ≫ pullback.snd G.source.hom G.target.hom =
        P.arrowsIso.inv ≫ (inverseHom G).hom
      rw [P.pairMap_comp_snd P.containsArrows k, h₂, P.yoneda_inverse]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsArrows P.containsArrows ?_
  rw [P.yoneda_comp_pairMap P.containsArrows k,
    Space.schemeSiteMap_comp C hS P.containsArrows P.containsObjects P.containsArrows,
    yoneda.map_comp, P.yoneda_target, P.yoneda_identity, ← Category.assoc, key]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The de-realized composition is associative, at the universal composable triple. -/
theorem comp_assoc (P : SchemePresentation G)
    (m n : pullback (pullback.snd P.source P.target) (pullback.fst P.source P.target) ⟶
      pullback P.source P.target)
    (hm₁ : m ≫ pullback.fst P.source P.target =
      pullback.fst (pullback.snd P.source P.target) (pullback.fst P.source P.target) ≫ P.comp)
    (hm₂ : m ≫ pullback.snd P.source P.target =
      pullback.snd (pullback.snd P.source P.target) (pullback.fst P.source P.target) ≫
        pullback.snd P.source P.target)
    (hn₁ : n ≫ pullback.fst P.source P.target =
      pullback.fst (pullback.snd P.source P.target) (pullback.fst P.source P.target) ≫
        pullback.fst P.source P.target)
    (hn₂ : n ≫ pullback.snd P.source P.target =
      pullback.snd (pullback.snd P.source P.target) (pullback.fst P.source P.target) ≫
        P.comp) :
    m ≫ P.comp = n ≫ P.comp := by
  have key : P.pairMap P.containsTriples m ≫ compOnPairs G =
      P.pairMap P.containsTriples n ≫ compOnPairs G := by
    refine (toGroupoidObject G).comp_assoc
      (P.pairMap P.containsTriples (pullback.fst (pullback.snd P.source P.target)
        (pullback.fst P.source P.target)))
      (P.pairMap P.containsTriples (pullback.snd (pullback.snd P.source P.target)
        (pullback.fst P.source P.target)))
      (P.pairMap P.containsTriples m) (P.pairMap P.containsTriples n) ?_ ?_ ?_ ?_ ?_
    · change P.pairMap P.containsTriples (pullback.fst (pullback.snd P.source P.target)
            (pullback.fst P.source P.target)) ≫ pullback.snd G.source.hom G.target.hom =
          P.pairMap P.containsTriples (pullback.snd (pullback.snd P.source P.target)
            (pullback.fst P.source P.target)) ≫ pullback.fst G.source.hom G.target.hom
      rw [P.pairMap_comp_snd P.containsTriples _, P.pairMap_comp_fst P.containsTriples _,
        pullback.condition]
    · change P.pairMap P.containsTriples m ≫ pullback.fst G.source.hom G.target.hom =
          P.pairMap P.containsTriples (pullback.fst (pullback.snd P.source P.target)
            (pullback.fst P.source P.target)) ≫ compOnPairs G
      rw [P.pairMap_comp_fst P.containsTriples m, hm₁, P.yoneda_comp_pairMap P.containsTriples _]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · change P.pairMap P.containsTriples m ≫ pullback.snd G.source.hom G.target.hom =
          P.pairMap P.containsTriples (pullback.snd (pullback.snd P.source P.target)
            (pullback.fst P.source P.target)) ≫ pullback.snd G.source.hom G.target.hom
      rw [P.pairMap_comp_snd P.containsTriples m, P.pairMap_comp_snd P.containsTriples _, hm₂]
    · change P.pairMap P.containsTriples n ≫ pullback.fst G.source.hom G.target.hom =
          P.pairMap P.containsTriples (pullback.fst (pullback.snd P.source P.target)
            (pullback.fst P.source P.target)) ≫ pullback.fst G.source.hom G.target.hom
      rw [P.pairMap_comp_fst P.containsTriples n, P.pairMap_comp_fst P.containsTriples _, hn₁]
    · change P.pairMap P.containsTriples n ≫ pullback.snd G.source.hom G.target.hom =
          P.pairMap P.containsTriples (pullback.snd (pullback.snd P.source P.target)
            (pullback.fst P.source P.target)) ≫ compOnPairs G
      rw [P.pairMap_comp_snd P.containsTriples n, hn₂, P.yoneda_comp_pairMap P.containsTriples _]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine Space.schemeSiteMap_yoneda_injective C hS P.containsTriples P.containsArrows ?_
  rw [P.yoneda_comp_pairMap P.containsTriples m, P.yoneda_comp_pairMap P.containsTriples n,
    ← Category.assoc, ← Category.assoc, key]

/-! ### The de-realization -/

/-- **The groupoid object of schemes over `S` a presentation de-realizes.** -/
noncomputable def groupoidObject (P : SchemePresentation G)
    :
    Deformation.GroupoidObject (Over S) :=
  Deformation.GroupoidObject.ofUniversal P.identity P.inverse
    (IsPullback.of_hasPullback P.source P.target) (P.comp)
    (IsPullback.of_hasPullback (pullback.snd P.source P.target)
      (pullback.fst P.source P.target))
    P.identity_comp_source P.identity_comp_target P.inverse_comp_source P.inverse_comp_target
    (P.comp_comp_source) (P.comp_comp_target)
    (fun k h₁ h₂ => P.comp_identity_left k h₁ h₂)
    (fun k h₁ h₂ => P.comp_identity_right k h₁ h₂)
    (fun k h₁ h₂ => P.comp_inverse_left k h₁ h₂)
    (fun k h₁ h₂ => P.comp_inverse_right k h₁ h₂)
    (fun m n hm₁ hm₂ hn₁ hn₂ => P.comp_assoc m n hm₁ hm₂ hn₁ hn₂)

/-- **The groupoid scheme a presentation of a groupoid in algebraic spaces de-realizes.**

Its object and arrow schemes are the two schemes of the presentation, and its source, target,
identity, inverse and composition are the morphisms of schemes which represent those of the
groupoid in algebraic spaces.  This is the comparison inverse to
`Stacks.Groupoids.GroupoidScheme.realization`:
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.realizationIso` identifies the
given groupoid with the realization of this groupoid scheme. -/
noncomputable def derealization (P : SchemePresentation G)
    :
    Stacks.Groupoids.GroupoidScheme S :=
  Stacks.Groupoids.GroupoidScheme.ofGroupoidObject (P.groupoidObject)

/-- The object scheme of the de-realization is the scheme of objects of the presentation. -/
@[simp] theorem derealization_objects (P : SchemePresentation G)
    :
    (P.derealization).objects = P.objects := rfl

/-- The arrow scheme of the de-realization is the scheme of arrows of the presentation. -/
@[simp] theorem derealization_arrows (P : SchemePresentation G)
    :
    (P.derealization).arrows = P.arrows := rfl

/-- The source of the de-realization is the de-realized source. -/
@[simp] theorem derealization_source (P : SchemePresentation G)
    :
    (P.derealization).source = P.source := rfl

/-- The target of the de-realization is the de-realized target. -/
@[simp] theorem derealization_target (P : SchemePresentation G)
    :
    (P.derealization).target = P.target := rfl

/-- The identity of the de-realization is the de-realized unit. -/
@[simp] theorem derealization_identity (P : SchemePresentation G)
    :
    (P.derealization).identity = P.identity := rfl

/-- The inverse of the de-realization is the de-realized inverse. -/
@[simp] theorem derealization_inverse (P : SchemePresentation G)
    :
    (P.derealization).inverse = P.inverse := rfl

/-! ### De-realization from representability alone -/

/-- **A presentation by schemes of the site, from representability of the two structure
spaces.**  The scheme of objects and the scheme of arrows are the chosen representing schemes
`AlgebraicGeometry.Space.representingScheme`, which the site contains, and the two
identifications are the ones that representability supplies.

This is the form in which the de-realization is applied: a groupoid in algebraic spaces whose
object and arrow spaces are representable needs no further data to be a groupoid scheme. -/
noncomputable def ofIsRepresentable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable] :
    SchemePresentation G where
  objects := Space.representingScheme C hS G.objects.obj
  arrows := Space.representingScheme C hS G.arrows.obj
  containsObjects := Space.contains_representingScheme C hS G.objects.obj
  containsArrows := Space.contains_representingScheme C hS G.arrows.obj
  objectsIso := Space.representingSchemeIso C hS G.objects.obj
  arrowsIso := Space.representingSchemeIso C hS G.arrows.obj

/-- The scheme of objects of the presentation representability supplies is the chosen
representing scheme of the object space. -/
@[simp] theorem ofIsRepresentable_objects {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable] :
    (ofIsRepresentable G).objects = Space.representingScheme C hS G.objects.obj := rfl

/-- The scheme of arrows of the presentation representability supplies is the chosen
representing scheme of the arrow space. -/
@[simp] theorem ofIsRepresentable_arrows {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable] :
    (ofIsRepresentable G).arrows = Space.representingScheme C hS G.arrows.obj := rfl

end SchemePresentation

/-- **A groupoid in algebraic spaces whose object and arrow spaces are representable is a
groupoid scheme.**

Its object and arrow schemes are the chosen representing schemes, and its source, target,
identity, inverse and composition are the morphisms of schemes which represent those of the
groupoid in algebraic spaces — the last two being the unit and the inverse that the quintuple
determines, Stacks 06K5.  Nothing beyond representability of the two structure spaces is asked:
the site contains the representing schemes and, by
`AlgebraicGeometry.BigFppfSite.contains_pullback_left`, their fibre products.

This is the comparison inverse to `Stacks.Groupoids.GroupoidScheme.realization`:
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.realizationIso` identifies the given groupoid with
the realization of this groupoid scheme. -/
noncomputable def derealization {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable] :
    Stacks.Groupoids.GroupoidScheme S :=
  (SchemePresentation.ofIsRepresentable G).derealization

/-- The object scheme of the de-realization of a representable groupoid in algebraic spaces is
the chosen representing scheme of its object space. -/
@[simp] theorem derealization_objects {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable] :
    (derealization G).objects = Space.representingScheme C hS G.objects.obj := rfl

/-- The arrow scheme of the de-realization of a representable groupoid in algebraic spaces is
the chosen representing scheme of its arrow space. -/
@[simp] theorem derealization_arrows {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable] :
    (derealization G).arrows = Space.representingScheme C hS G.arrows.obj := rfl

/-- The source of the de-realization of a representable groupoid in algebraic spaces represents
its source. -/
theorem yoneda_derealization_source {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable] :
    yoneda.map (Space.schemeSiteMap C hS
        (Space.contains_representingScheme C hS G.arrows.obj)
        (Space.contains_representingScheme C hS G.objects.obj) (derealization G).source) =
      (Space.representingSchemeIso C hS G.arrows.obj).inv ≫ G.source.hom ≫
        (Space.representingSchemeIso C hS G.objects.obj).hom :=
  (SchemePresentation.ofIsRepresentable G).yoneda_source

/-- The target of the de-realization of a representable groupoid in algebraic spaces represents
its target. -/
theorem yoneda_derealization_target {C : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : C.Contains S} {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable] :
    yoneda.map (Space.schemeSiteMap C hS
        (Space.contains_representingScheme C hS G.arrows.obj)
        (Space.contains_representingScheme C hS G.objects.obj) (derealization G).target) =
      (Space.representingSchemeIso C hS G.arrows.obj).inv ≫ G.target.hom ≫
        (Space.representingSchemeIso C hS G.objects.obj).hom :=
  (SchemePresentation.ofIsRepresentable G).yoneda_target

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
