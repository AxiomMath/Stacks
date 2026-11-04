module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.ImageClosure
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.LocallyClosedImage
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.ReducedClosureGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.ArrowImageOverField
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.OpenImageOverField

/-!
# Morphisms of groupoid schemes on the spectrum of a field

The standing situation for the results on the image on arrows of a morphism of groupoid
schemes over a field: a base scheme `S`, a field `k`, two groupoid schemes
`(U, R₁, s₁, t₁, c₁)` and `(U, R₂, s₂, t₂, c₂)` over `S` whose common scheme of objects `U`
is `Spec k`, and a morphism `a : R₁ ⟶ R₂` for which `(id_U, a)` is a morphism of groupoid
schemes.

## Main definitions

* `AlgebraicGeometry.GroupoidMorphismOverFieldSituation` bundles that data.

## Main results

* `AlgebraicGeometry.GroupoidMorphismOverFieldSituation.objects_left_right_eq` identifies the
  scheme of objects of the second groupoid with `Spec k` as well.
* The remaining results instantiate the library's statements about such a morphism at the data of
  the situation, so that a term of the structure feeds them directly.

## Implementation notes

The two commuting diagrams displayed by the source are the compatibility of `a` with the
source, target and composition maps, which are the fields of
`Stacks.Groupoids.GroupoidScheme.Hom`; the situation therefore records the morphism itself
together with the equation making its component on objects the identity.  The equality of the
schemes of objects is propositional, so that component is compared with the transport along
it rather than with the identity.

## References

* [Stacks Project, Tag 04Q5](https://stacks.math.columbia.edu/tag/04Q5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The standing data of Situation 04Q5: two groupoid schemes over a base scheme sharing a
scheme of objects which is the spectrum of a field, and a morphism between them whose
component on objects is the identity. -/
@[stacks 04Q5]
structure GroupoidMorphismOverFieldSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The field whose spectrum is the common scheme of objects. -/
  k : Type u
  /-- The field structure on `k`. -/
  [field : Field k]
  /-- The first groupoid scheme `(U, R₁, s₁, t₁, c₁)`. -/
  G₁ : GroupoidScheme S
  /-- The second groupoid scheme `(U, R₂, s₂, t₂, c₂)`. -/
  G₂ : GroupoidScheme S
  /-- The two groupoid schemes have the same scheme of objects. -/
  objects_eq : G₁.objects = G₂.objects
  /-- The common scheme of objects is the spectrum of `k`. -/
  objects_left_eq : G₁.objects.left = Spec (.of k)
  /-- The morphism `(id_U, a)` of groupoid schemes. -/
  hom : GroupoidScheme.Hom G₁ G₂
  /-- Its component on objects is the identity of the common scheme of objects. -/
  mapObjects_eq : hom.mapObjects = eqToHom objects_eq

attribute [instance] GroupoidMorphismOverFieldSituation.field

namespace GroupoidMorphismOverFieldSituation

variable (T : GroupoidMorphismOverFieldSituation.{u})

/-- The scheme of objects of the second groupoid scheme is the spectrum of `k` as well. -/
theorem objects_left_right_eq : T.G₂.objects.left = Spec (.of T.k) :=
  (congrArg Over.left T.objects_eq).symm.trans T.objects_left_eq

/-- Tag 04Q6 at the data of the situation: if the image of `a` on arrows is open, it is
closed. -/
theorem isClosed_range_mapArrows_of_isOpen
    (hopen : IsOpen (Set.range T.hom.mapArrows.left.base)) :
    IsClosed (Set.range T.hom.mapArrows.left.base) :=
  _root_.AlgebraicGeometry.isClosed_range_mapArrows_of_isOpen (k := T.k) T.hom T.objects_eq
    T.objects_left_eq T.mapObjects_eq hopen

/-- Tag 04Q9 at the data of the situation: if the image of `a` on arrows is locally closed, it
is closed. -/
theorem isClosed_range_mapArrows_of_isLocallyClosed
    (h : IsLocallyClosed (Set.range T.hom.mapArrows.left.base)) :
    IsClosed (Set.range T.hom.mapArrows.left.base) :=
  _root_.AlgebraicGeometry.isClosed_range_mapArrows_of_isLocallyClosed (k := T.k) T.hom
    T.objects_eq T.objects_left_eq T.mapObjects_eq h

/-- Tag 04Q7 at the data of the situation: the closure of the image of `a` on arrows is stable
under the composition law of the second groupoid scheme. -/
theorem comp_mapsTo_closure_range_mapArrows :
    Set.MapsTo T.G₂.comp.left.base
      ((pullback.fst T.G₂.source T.G₂.target).left.base ⁻¹'
          closure (Set.range T.hom.mapArrows.left.base) ∩
        (pullback.snd T.G₂.source T.G₂.target).left.base ⁻¹'
          closure (Set.range T.hom.mapArrows.left.base))
      (closure (Set.range T.hom.mapArrows.left.base)) :=
  _root_.AlgebraicGeometry.comp_mapsTo_closure_range_mapArrows (k := T.k) T.hom T.objects_eq
    T.objects_left_eq T.mapObjects_eq

/-- Tag 04Q8 at the data of the situation, for `k` perfect: the groupoid structure on the
reduced closure of the image of `a` on arrows. -/
noncomputable def reducedClosureImage [PerfectField T.k] :
    GroupoidScheme.ReducedClosureImage T.hom :=
  GroupoidScheme.reducedClosureImage (k := T.k) T.hom T.objects_eq T.objects_left_eq
    T.mapObjects_eq

/-- Tag 04QA at the data of the situation: for `a` quasi-compact on arrows, the groupoid
structure on the scheme-theoretic image of `a`. -/
theorem exists_groupoidScheme_image [QuasiCompact T.hom.mapArrows.left] :
    ∃ (H : GroupoidScheme T.S) (j : GroupoidScheme.Hom H T.G₂)
      (hHobjects : H.objects = T.G₂.objects)
      (hHarrows : H.arrows = Over.mk (T.hom.mapArrows.left.imageι ≫ T.G₂.arrows.hom)),
        (j.mapObjects = eqToHom hHobjects) ∧
        (j.mapArrows.left =
          eqToHom (congrArg Over.left hHarrows) ≫ T.hom.mapArrows.left.imageι) :=
  _root_.AlgebraicGeometry.exists_groupoidScheme_image (k := T.k) T.hom T.objects_eq
    T.objects_left_eq T.mapObjects_eq

end GroupoidMorphismOverFieldSituation

end AlgebraicGeometry

end
