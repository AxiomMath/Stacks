module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationStabilizerPart
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeEtaleLocalization

/-!
# Splitting a restricted groupoid from a lifting criterion

Stacks 03FM and Stacks 0DTC say that in the strong splitting situation of Stacks 04RL,
respectively the splitting situation of Stacks 0DTB, there is an algebraic space `U'`, an étale
morphism `U' ⟶ U` and a point `u' : Spec κ(u) ⟶ U'` *lying over* `u : Spec κ(u) ⟶ U` such that
the restriction `R|_{U'}` is strongly split, respectively split, over `u'`.
In both cases the Stacks proof produces the localization from the finite part of the groupoid of
Stacks 04RU and then verifies the splitting condition by one and the same mechanism: the open
finite subgroupoid `Z` of the restriction `R|_{U'}` which the finite part supplies is cut out by
an open `Q` of the ambient object space, in the sense that an arrow of `R|_{U'}` lies in `Z`
exactly when its target in the ambient groupoid lies in `Q`, and `Q` contains the chosen point.
Every arrow whose target is the chosen point therefore lies in `Z`.

This file isolates that mechanism and derives both splitting conditions from it. The lifting
criterion is carried as a hypothesis, `AlgebraicGeometry.GroupoidInAlgebraicSpaces`
`.TargetLocusSubgroupoid`, because it is the output of clause (3) of Stacks 04RU — the groupoid
structure on the finite part together with its morphism to the given groupoid — which this
library does not prove; only clauses (1) and (2) are available, as
`AlgebraicGeometry.Space.finitePartUniversalOpen` in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/Groupoid.lean`, line 322.

The criterion must be hypothesised in this bundled form and not as the bare existence of an open
finite subgroupoid of the restriction: a bare open finite subgroupoid is *not* enough to split
anything.  Take `U' = U`, `g = 𝟙`, and for `Z` the image of the unit `e : U ⟶ R`; when `e` is an
open immersion — a finite constant group acting on the spectrum of a field — this is an open
finite subgroupoid of `R|_{U'} = R`, yet it contains no arrow at `u` other than the identity.
What that `Z` fails is exactly the criterion below: with `Q` any open containing the image of
`u'`, an arrow `r ≠ e(u)` with both endpoints `u` has its target in `Q` and does not lie in `Z`.

## Main definitions

* `AlgebraicGeometry.Space.residueFieldSiteObject` and
  `AlgebraicGeometry.Space.yonedaResidueFieldPoint`: the object `Spec κ(u) ⟶ S` of the site
  attached to a point `u` of a scheme over `S`, and `u` itself read as a point of the algebraic
  space represented by that scheme.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.TargetLocusSubgroupoid`: the output of Stacks
  04RU in the form Stacks 03FM and Stacks 0DTC use it — an étale morphism `g : U' ⟶ U`, an open
  finite subgroupoid `Z` of `R|_{U'}`, an open `Q` of `U`, and the lifting criterion identifying
  the arrows of `Z` as those whose ambient target lies in `Q`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.TargetLocusSubgroupoid.PointMem`: the condition
  that a point of the restricted object space has its image in `Q`.

## Main results

* `AlgebraicGeometry.Space.pointsMap_class_eq_yonedaResidueFieldPoint`: a `Spec κ(u)`-valued
  section whose image is the canonical morphism `Spec κ(u) ⟶ U` represents a point over `u`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_mem_arrows_of_target_eq`: the mechanism
  itself, for an arbitrary morphism of groupoids in algebraic spaces — an arrow whose target is
  a point whose image lies in `Q` lifts into `Z`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.TargetLocusSubgroupoid.strongSplitting` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.TargetLocusSubgroupoid.splitting`: the two
  splitting conditions of Stacks 04RK derived from the criterion.
* `Stacks.Groupoids.GroupoidScheme.pointMem_of_lies_over`: a point of `U'` over `u`, at a `u`
  lying in `Q`, satisfies the membership condition under which those two are derived.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_strongSplitting` and
  `Stacks.Groupoids.GroupoidScheme.exists_etale_splitting`: the shapes of Stacks 03FM and
  Stacks 0DTC deduced from the criterion.  **Neither is the tag, and neither is usable**; see
  "Why the criterion has no instances" below.  Stacks 03FM is proved outright, without this
  criterion, as `AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation` in
  `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment`, and that
  is where the `@[stacks 03FM]` attribute sits.

## Why the criterion has no instances

Clause (3) of Stacks 04RU — the groupoid structure on the finite part and its morphism to `R`
— is proved, as `AlgebraicGeometry.Space.nonempty_finitePartGroupoid` at
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/Groupoid.lean:2095`, with the
structure itself at `:2036` and the groupoid structure and canonical morphism at
`More/FinitePart/GroupoidStructure.lean:655` and `:667`.

The real obstruction is that `TargetLocusSubgroupoid` is the **wrong notion**, and is empty for
the finite part.  Its field `mem_arrows_iff` asks that membership of an arrow of `R|_{U'}` in the
subgroupoid be decided by the arrow's *target in* `U` alone, through an open `Q ⊆ U`.  Membership
in the universal finite part `Z_univ` is instead decided by the *section of* `U'` that is the
arrow's source — a point of `U'` names an open of the fibre, and that open is what membership
refers to.  The two cannot agree.  Concretely, take `U = Spec k`, `R = (ℤ/2) × U` and
`s = t = pr`.  Then `U'` carries a point `x₁` whose fibre-open is the unit alone and a point
`x₂` whose fibre-open is everything; of the eight `Spec k`-sections of `R|_{U'}`, three lie in
the image of `Z_univ`.  All eight have the same target in `U = Spec k`, whose only open
subspaces are `∅` and `U`, so `Q = U` admits all eight and `Q = ∅` admits none.  No `Q` cuts out
three.  (Prose only; this counterexample is not formalized.)

What the finite part does supply is a `FinitePartSubgroupoid`, which is what Stacks 04RW
consumes; it is constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationFinitePartConstruction`.

## Implementation notes

The two splitting conditions of Stacks 04RK are conditions on *points* of the arrow space, which
are equivalence classes of field-valued sections, whereas the lifting criterion is a condition on
sections.  The passage from one to the other does not need a representative of the given point to
satisfy the criterion on its own field: it is enough that *some* extension of it does, because an
extension represents the same point.  So the hypothesis that the chosen point lies in `Q` is
taken in the library's own form — the point is in the image of the points of `Q` — and a common
extension of the representative of that image point with the representative of the target of the
given arrow is the field over which the criterion is applied.

The point `u'` of the conclusion is a section of `U'` over the site object `Spec κ(u) ⟶ S`, that
is literally a morphism `Spec κ(u) ⟶ U'`, and the first conjunct pins its composition with
`U' ⟶ U` to the canonical `Spec κ(u) ⟶ U`.  That point is *not* derived here.  Stacks obtains it
from the explicit construction of `U'` as the finite part: the open and closed decomposition
`F_u = Z_u ⨿ Rest` of the fibre of the source over `u` is a `Spec κ(u)`-valued section of the
finite part, hence of `U'`.  This library proves the decomposition, as
`AlgebraicGeometry.Space.StrongSplittingSituation.exists_fiberOpens_stabilizer` and
`AlgebraicGeometry.Space.SplittingSituation.exists_fiberOpens_stabilizer`, but not the
identification of `U'` with the finite part that turns it into a section, since `U'` enters only
through the clause (3) hypothesis and is opaque.  That identification is therefore the extra
hypothesis `hlift` of the two statements: it takes a decomposition of the fibre at `u` to a
section of `U'` over `u`.  It is applied to the decomposition proved here, which is what makes
the standing finiteness and quasi-finiteness hypotheses of Stacks 04RL and Stacks 0DTB enter the
proof.  Modulo that decomposition lemma, `hlift` is of course equivalent to assuming the pinned
point outright; what it records is *which* identification is missing.

Stacks 0DTC is not a corollary of Stacks 03FM.  The hypotheses of Stacks 04RL are stronger than
those of Stacks 0DTB — a strong splitting situation is a splitting situation — and a strong
splitting is in particular a splitting, so the two implications run the same way and cannot be
composed.  The derivation of the splitting condition is therefore carried out again in its own
situation, using
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_target` to see that a point of the
stabilizer over the chosen point is an arrow whose target is that point.

## References

* [Stacks Project, Tag 03FM](https://stacks.math.columbia.edu/tag/03FM)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
* [Stacks Project, Tag 0DTC](https://stacks.math.columbia.edu/tag/0DTC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) {S : Scheme.{u}} (hS : C.Contains S)

/-- The object `Spec κ(x) ⟶ S` of the big fppf site over `S` attached to a point `x` of a scheme
`X` over `S` whose residue field spectrum the site contains. -/
noncomputable abbrev residueFieldSiteObject {X : Over S} (x : X.left)
    (hK : C.Contains (Spec (X.left.residueField x))) : BigFppfOver C S hS :=
  schemeSiteObject C hS (X := Over.mk (X.left.fromSpecResidueField x ≫ X.hom)) hK

/-- A point `x` of a scheme `X` over `S` which the site contains, read as a point of the
algebraic space represented by `X`: the class of the canonical morphism `Spec κ(x) ⟶ X`. -/
noncomputable def yonedaResidueFieldPoint {X : Over S} (hX : C.Contains X.left) (x : X.left)
    (hK : C.Contains (Spec (X.left.residueField x))) :
    points C S hS (yoneda.obj (schemeSiteObject C hS hX)) :=
  FieldValuedPoint.class C S hS _
    { carrier := X.left.residueField x
      contained := hK
      toBase := X.left.fromSpecResidueField x ≫ X.hom
      value := (yonedaSchemePointEquiv C hS hX
        (Opposite.op (residueFieldSiteObject C hS x hK))).symm
        (Over.homMk (X.left.fromSpecResidueField x)) }

/-- A `Spec κ(x)`-valued section of a presheaf over `S` whose image in the algebraic space
represented by `X` is the canonical morphism `Spec κ(x) ⟶ X` represents the point `x`. -/
theorem pointsMap_class_eq_yonedaResidueFieldPoint {X : Over S} (hX : C.Contains X.left)
    (x : X.left) (hK : C.Contains (Spec (X.left.residueField x)))
    {Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : Y ⟶ yoneda.obj (schemeSiteObject C hS hX))
    (v : Y.obj (Opposite.op (residueFieldSiteObject C hS x hK)))
    (hv : (yonedaSchemePointEquiv C hS hX (Opposite.op (residueFieldSiteObject C hS x hK))
      (f.app _ v)).left = X.left.fromSpecResidueField x) :
    pointsMap C S hS Y f
        (FieldValuedPoint.class C S hS Y
          { carrier := X.left.residueField x, contained := hK,
            toBase := X.left.fromSpecResidueField x ≫ X.hom, value := v }) =
      yonedaResidueFieldPoint C hS hX x hK := by
  have h : f.app (Opposite.op (residueFieldSiteObject C hS x hK)) v =
      (yonedaSchemePointEquiv C hS hX
        (Opposite.op (residueFieldSiteObject C hS x hK))).symm
        (Over.homMk (X.left.fromSpecResidueField x)) := by
    rw [Equiv.eq_symm_apply]
    exact Over.OverMorphism.ext hv
  rw [pointsMap_class, yonedaResidueFieldPoint]
  refine congrArg _ ?_
  rw [FieldValuedPoint.map]
  exact congrArg _ h

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- An arrow of `H` whose target is a point whose image in `G` lies in the subfunctor `Q` lifts
into an open subspace `Z` of the arrow space of `H` which is cut out by `Q`.

This is the mechanism by which the finite part of a groupoid splits a restriction of it: the
hypothesis `hZQ` says that a section of the arrow space of `H` lies in `Z` exactly when its
image in `G` has target a section of `Q`, and `hu'` says that the image of the point `u'` in `G`
lies in `Q`. -/
theorem exists_mem_arrows_of_target_eq {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : Hom H G)
    (Z : Subfunctor H.arrows.obj) (Q : Subfunctor G.objects.obj)
    (hZQ : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (a : H.arrows.obj.obj T),
      a ∈ Z.obj T ↔ G.target.hom.app T (φ.toGroupoidHom.mapArrows.app T a) ∈ Q.obj T)
    (u' : Space.points C S hS H.objects.obj)
    (hu' : ∃ q : Space.points C S hS Q.toFunctor,
      Space.pointsMap C S hS Q.toFunctor Q.ι q =
        Space.pointsMap C S hS H.objects.obj φ.toGroupoidHom.mapObjects u')
    (r : Space.points C S hS H.arrows.obj)
    (ht : Space.pointsMap C S hS H.arrows.obj H.target.hom r = u') :
    ∃ z : Space.points C S hS Z.toFunctor,
      Space.pointsMap C S hS Z.toFunctor Z.ι z = r := by
  obtain ⟨q, hq⟩ := hu'
  obtain ⟨q₀, rfl⟩ := Quot.exists_rep q
  obtain ⟨r₀, rfl⟩ := Quot.exists_rep r
  let x₀ : Space.FieldValuedPoint C S hS G.objects.obj :=
    Space.FieldValuedPoint.map C S hS G.arrows.obj G.target.hom
      (Space.FieldValuedPoint.map C S hS H.arrows.obj φ.toGroupoidHom.mapArrows r₀)
  let y₀ : Space.FieldValuedPoint C S hS G.objects.obj :=
    Space.FieldValuedPoint.map C S hS H.objects.obj φ.toGroupoidHom.mapObjects
      (Space.FieldValuedPoint.map C S hS H.arrows.obj H.target.hom r₀)
  have hxy : x₀.class C S hS G.objects.obj = y₀.class C S hS G.objects.obj := by
    refine Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension C S hS _ ?_
    refine ⟨x₀, Space.FieldValuedPoint.dominates_refl C S hS _ x₀, ⟨𝟙 _, ?_⟩⟩
    change G.objects.obj.map (𝟙 _).op y₀.value = x₀.value
    rw [op_id, G.objects.obj.map_id]
    exact (φ.toGroupoidHom.map_target _ r₀.value).symm
  have hclass : x₀.class C S hS G.objects.obj =
      Space.pointsMap C S hS H.objects.obj φ.toGroupoidHom.mapObjects u' := by
    rw [hxy, ← ht]
    rfl
  obtain ⟨w, ⟨f₁, hf₁⟩, ⟨g₁, hg₁⟩⟩ : Space.FieldValuedPoint.HasCommonExtension C S hS
      G.objects.obj (Space.FieldValuedPoint.map C S hS Q.toFunctor Q.ι q₀) x₀ := by
    rw [← Space.FieldValuedPoint.class_eq_class_iff, hclass, ← hq]
    rfl
  have hwmem : w.value ∈ Q.obj (Opposite.op w.siteObject) := by
    rw [← hf₁]
    exact Q.map f₁.op q₀.value.2
  let r₁ : Space.FieldValuedPoint C S hS H.arrows.obj :=
    { w with value := H.arrows.obj.map g₁.op r₀.value }
  have hr₁val : G.target.hom.app (Opposite.op r₁.siteObject)
      (φ.toGroupoidHom.mapArrows.app (Opposite.op r₁.siteObject) r₁.value) = w.value := by
    rw [← hg₁]
    change G.target.hom.app _ (φ.toGroupoidHom.mapArrows.app _
      (H.arrows.obj.map g₁.op r₀.value)) = G.objects.obj.map g₁.op x₀.value
    rw [show φ.toGroupoidHom.mapArrows.app (Opposite.op w.siteObject)
        (H.arrows.obj.map g₁.op r₀.value) =
        G.arrows.obj.map g₁.op (φ.toGroupoidHom.mapArrows.app _ r₀.value) from
      congrArg (fun k => k r₀.value) (φ.toGroupoidHom.mapArrows.naturality g₁.op)]
    exact congrArg (fun k => k (φ.toGroupoidHom.mapArrows.app _ r₀.value))
      (G.target.hom.naturality g₁.op)
  refine ⟨Space.FieldValuedPoint.class C S hS Z.toFunctor
    { r₁ with value := ⟨r₁.value, (hZQ _ r₁.value).mpr (hr₁val ▸ hwmem)⟩ }, ?_⟩
  rw [Space.pointsMap_class]
  exact Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension C S hS _
    ⟨r₁, Space.FieldValuedPoint.dominates_refl C S hS _ r₁, ⟨g₁, rfl⟩⟩

/-- Reading a point of `U'` in the object space of the restriction `R|_{U'}` and then pushing it
forward to `U` is pushing it forward along `g : U' ⟶ U`. -/
theorem pointsMap_mapObjects_pointsMap_eqToHom
    (G : GroupoidInAlgebraicSpaces C S hS B) {U' : AlgebraicSpaces C S hS}
    (g : U' ⟶ G.objects) (z : Space.points C S hS U'.obj) :
    Space.pointsMap C S hS (restrict G g).groupoid.objects.obj
        (restrict G g).hom.toGroupoidHom.mapObjects
        (Space.pointsMap C S hS U'.obj (eqToHom (restrict G g).objects_eq.symm).hom z) =
      Space.pointsMap C S hS U'.obj g.hom z := by
  have key : (eqToHom (restrict G g).objects_eq.symm).hom ≫
      (restrict G g).hom.toGroupoidHom.mapObjects = g.hom := by
    rw [(restrict G g).mapObjects_eq]
    change ((eqToHom (restrict G g).objects_eq.symm) ≫
      (eqToHom (restrict G g).objects_eq ≫ g)).hom = g.hom
    rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rw [← key]
  exact (congrFun (Space.pointsMap_comp C S hS U'.obj
    (eqToHom (restrict G g).objects_eq.symm).hom
    (restrict G g).hom.toGroupoidHom.mapObjects) z).symm

/-- The output of Stacks 04RU in the form Stacks 03FM and Stacks 0DTC use it: an algebraic space
`U'` with an étale morphism `g : U' ⟶ U` to the object space, an open finite subgroupoid `Z` of
the restriction `R|_{U'}`, and an open subspace `Q` of `U` which *cuts `Z` out of the arrows over
`U'`* — a section of the arrow space of `R|_{U'}` lies in `Z` exactly when its target in `R` is a
section of `Q`.

The last condition is the universal lifting property of the finite part, Stacks 04RU clause (3),
in the form its consumers use.  It is a property of `Z` relative to `Q` and not the splitting
condition it is used to derive: it determines the arrows of `Z` completely, in both directions,
whereas a splitting condition only asks for arrows over one point to be present. -/
structure TargetLocusSubgroupoid (G : GroupoidInAlgebraicSpaces C S hS B)
    extends FinitePartSubgroupoid G where
  /-- The open subspace `Q` of the object space which cuts out the subgroupoid. -/
  targetLocus : Subfunctor G.objects.obj
  /-- `Q` is an open subspace. -/
  targetLocus_open : Space.IsOpenSubspace C S hS targetLocus
  /-- An arrow of `R|_{U'}` lies in the subgroupoid exactly when its target in `R` lies in `Q`. -/
  mem_arrows_iff : ∀ (T : (BigFppfOver C S hS)ᵒᵖ)
      (a : (restrict G objectProjection).groupoid.arrows.obj.obj T),
    a ∈ restrictedSubgroupoid.arrows.obj T ↔
      G.target.hom.app T
        ((restrict G objectProjection).hom.toGroupoidHom.mapArrows.app T a) ∈ targetLocus.obj T

namespace TargetLocusSubgroupoid

variable {G : GroupoidInAlgebraicSpaces C S hS B}

/-- The image in the object space of a point of the restricted object space lies in the open `Q`
cutting out the subgroupoid. -/
def PointMem (F : TargetLocusSubgroupoid G)
    (u' : Space.points C S hS (restrict G F.objectProjection).groupoid.objects.obj) : Prop :=
  ∃ q : Space.points C S hS F.targetLocus.toFunctor,
    Space.pointsMap C S hS F.targetLocus.toFunctor F.targetLocus.ι q =
      Space.pointsMap C S hS (restrict G F.objectProjection).groupoid.objects.obj
        (restrict G F.objectProjection).hom.toGroupoidHom.mapObjects u'

/-- Every arrow of `R|_{U'}` whose target is a point lying in `Q` lifts into the subgroupoid. -/
theorem exists_mem_arrows (F : TargetLocusSubgroupoid G)
    {u' : Space.points C S hS (restrict G F.objectProjection).groupoid.objects.obj}
    (hu' : F.PointMem u')
    (r : Space.points C S hS (restrict G F.objectProjection).groupoid.arrows.obj)
    (ht : Space.pointsMap C S hS (restrict G F.objectProjection).groupoid.arrows.obj
      (restrict G F.objectProjection).groupoid.target.hom r = u') :
    ∃ z : Space.points C S hS F.restrictedSubgroupoid.arrows.toFunctor,
      Space.pointsMap C S hS F.restrictedSubgroupoid.arrows.toFunctor
        F.restrictedSubgroupoid.arrows.ι z = r :=
  exists_mem_arrows_of_target_eq (restrict G F.objectProjection).hom
    F.restrictedSubgroupoid.arrows F.targetLocus F.mem_arrows_iff u' hu' r ht

/-- **The strong splitting condition of Stacks 04RK, part (1)**, for the subgroupoid cut out by
`Q`: every arrow of `R|_{U'}` with both endpoints at a point lying in `Q` lifts into it.

Only the condition on the target is used; the condition on the source is not needed. -/
def strongSplitting (F : TargetLocusSubgroupoid G)
    (u' : Space.points C S hS (restrict G F.objectProjection).groupoid.objects.obj)
    (hu' : F.PointMem u') :
    StrongSplitting (restrict G F.objectProjection).groupoid u' :=
  { F.restrictedSubgroupoid with
    contains_arrows := fun _ h => F.exists_mem_arrows hu' _ h.2 }

/-- **The splitting condition of Stacks 04RK, part (2)**, for the subgroupoid cut out by `Q`:
every point of the stabilizer over a point lying in `Q` lifts into it.

The underlying arrow of a point of the stabilizer has target the point it lies over, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow_target`, so this is the previous
derivation applied to that arrow. -/
def splitting (F : TargetLocusSubgroupoid G)
    (u' : Space.points C S hS (restrict G F.objectProjection).groupoid.objects.obj)
    (hu' : F.PointMem u') :
    Splitting (restrict G F.objectProjection).groupoid u' :=
  { F.restrictedSubgroupoid with
    contains_stabilizer := fun g hg => F.exists_mem_arrows hu' _ (by
      rwa [← stabilizerArrow_target (restrict G F.objectProjection).groupoid,
        Space.pointsMap_comp] at hg) }

end TargetLocusSubgroupoid

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-- A `Spec κ(u)`-valued point `v` of `U'` whose composition with `g : U' ⟶ U` is the canonical
morphism `Spec κ(u) ⟶ U`, at a point `u` lying in the open `Q` which cuts out the subgroupoid,
represents a point of the restricted object space whose image in `U` lies in `Q`.

This is the passage from the hypothesis that `Q` contains the chosen point `u`, which is the
form the condition takes in Stacks 03FM and Stacks 0DTC, to the hypothesis
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.TargetLocusSubgroupoid.PointMem` under which the
two splitting conditions are derived. -/
theorem pointMem_of_lies_over {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.objects.left)
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains S)
    (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
    (hP : C.Contains (pullback G.source G.target).left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    (F : TargetLocusSubgroupoid (G.realization C hS hU hR hP))
    (v : F.objects.obj.obj (Opposite.op
      (AlgebraicGeometry.Space.residueFieldSiteObject C hS (X := G.objects) u hK)))
    (hv : (AlgebraicGeometry.Space.yonedaSchemePointEquiv C hS hU
      (Opposite.op (AlgebraicGeometry.Space.residueFieldSiteObject C hS (X := G.objects) u hK))
      (F.objectProjection.hom.app _ v)).left = G.objects.left.fromSpecResidueField u)
    (hQ : ∃ q : AlgebraicGeometry.Space.points C S hS F.targetLocus.toFunctor,
      AlgebraicGeometry.Space.pointsMap C S hS F.targetLocus.toFunctor F.targetLocus.ι q =
        AlgebraicGeometry.Space.yonedaResidueFieldPoint C hS hU u hK) :
    F.PointMem (AlgebraicGeometry.Space.pointsMap C S hS F.objects.obj
      (eqToHom (restrict (G.realization C hS hU hR hP)
        F.objectProjection).objects_eq.symm).hom
      (AlgebraicGeometry.Space.FieldValuedPoint.class C S hS F.objects.obj
        { carrier := G.objects.left.residueField u
          contained := hK
          toBase := G.objects.left.fromSpecResidueField u ≫ G.objects.hom
          value := v })) := by
  obtain ⟨q, hq⟩ := hQ
  refine ⟨q, hq.trans ?_⟩
  rw [pointsMap_mapObjects_pointsMap_eqToHom]
  exact (AlgebraicGeometry.Space.pointsMap_class_eq_yonedaResidueFieldPoint C hS hU u hK
    F.objectProjection.hom v hv).symm

/-- **Stacks Project, Tag 03FM**, conditional on clause (3) of Stacks 04RU and on the
identification `hlift` of `U'` with the finite part.

In the strong splitting situation of Stacks 04RL, given the finite part of the realized groupoid
as an open finite subgroupoid of a restriction along an étale morphism which is cut out by an
open `Q` of the object space containing `u`, there is an algebraic space `U'`, an étale morphism
`U' ⟶ U` and a point `Spec κ(u) ⟶ U'` lying over `u` at which `R|_{U'}` is strongly split.

The point is produced by applying `hlift` to the open and closed decomposition of the fibre of
the source over `u` supplied by
`AlgebraicGeometry.Space.StrongSplittingSituation.exists_fiberOpens_stabilizer`. -/
-- NO `@[stacks 03FM]` ATTRIBUTE IS CARRIED, deliberately, and this theorem is SUPERSEDED.
-- Stacks 03FM asserts the EXISTENCE of an algebraic space `U'`, an étale `U' ⟶ U` and a point
-- over `u`.  All three are hypotheses here: `U'` and the étale map arrive inside
-- `TargetLocusSubgroupoid`, and the point arrives through `hlift`, which modulo the
-- decomposition lemma is equivalent to assuming the pinned point outright.  Only the splitting
-- is derived, so the existential content of the tag is assumed rather than concluded.
-- Worse, `TargetLocusSubgroupoid` has no instances for the finite part — see "Why the criterion
-- has no instances" in the module docstring — so this statement is unusable as well as untagged.
-- Clause (3) of Stacks 04RU is not the obstruction: it is proved, and clause (3)
-- is at `More/FinitePart/Groupoid.lean:2095`.
-- Stacks 03FM is proved OUTRIGHT and unconditionally elsewhere, as
-- `AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation` in
-- `EtaleLocalizationArrowContainment`, which is where the attribute sits.
theorem exists_etale_strongSplitting (D : AlgebraicGeometry.Space.StrongSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    (F : TargetLocusSubgroupoid (D.groupoid.realization C hS hU hR hP))
    (hlift : ∀ W : (D.groupoid.source.left.fiber D.u).Opens,
      (∀ x : D.groupoid.source.left.fiber D.u,
        x ∈ W ↔ D.groupoid.target.left (D.groupoid.source.left.fiberι D.u x) = D.u) →
      IsClosed (W : Set (D.groupoid.source.left.fiber D.u)) →
      AlgebraicGeometry.IsFinite
        (W.ι ≫ D.groupoid.source.left.fiberToSpecResidueField D.u) →
      ∃ v : F.objects.obj.obj (Opposite.op
          (AlgebraicGeometry.Space.residueFieldSiteObject C hS
            (X := D.groupoid.objects) D.u hK)),
        (AlgebraicGeometry.Space.yonedaSchemePointEquiv C hS hU
          (Opposite.op (AlgebraicGeometry.Space.residueFieldSiteObject C hS
            (X := D.groupoid.objects) D.u hK))
          (F.objectProjection.hom.app _ v)).left =
            D.groupoid.objects.left.fromSpecResidueField D.u)
    (hQ : ∃ q : AlgebraicGeometry.Space.points C D.S hS F.targetLocus.toFunctor,
      AlgebraicGeometry.Space.pointsMap C D.S hS F.targetLocus.toFunctor F.targetLocus.ι q =
        AlgebraicGeometry.Space.yonedaResidueFieldPoint C hS hU D.u hK) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      AlgebraicGeometry.Space.IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (AlgebraicGeometry.Space.residueFieldSiteObject C hS
            (X := D.groupoid.objects) D.u hK)),
        (AlgebraicGeometry.Space.yonedaSchemePointEquiv C hS hU
            (Opposite.op (AlgebraicGeometry.Space.residueFieldSiteObject C hS
              (X := D.groupoid.objects) D.u hK))
            (g.hom.app _ v)).left =
              D.groupoid.objects.left.fromSpecResidueField D.u ∧
        IsStronglySplitAt (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid
          (AlgebraicGeometry.Space.pointsMap C D.S hS U'.obj
            (eqToHom (restrict (D.groupoid.realization C hS hU hR hP) g).objects_eq.symm).hom
            (AlgebraicGeometry.Space.FieldValuedPoint.class C D.S hS U'.obj
              { carrier := D.groupoid.objects.left.residueField D.u
                contained := hK
                toBase := D.groupoid.objects.left.fromSpecResidueField D.u ≫
                  D.groupoid.objects.hom
                value := v })) := by
  obtain ⟨W, hW, hWclosed, hWfinite⟩ := D.exists_fiberOpens_stabilizer
  obtain ⟨v, hv⟩ := hlift W hW hWclosed hWfinite
  exact ⟨F.objects, F.objectProjection, F.objectProjection_etale, v, hv,
    ⟨F.strongSplitting _
      (pointMem_of_lies_over D.groupoid D.u C hS hU hR hP hK F v hv hQ)⟩⟩

/-- **Stacks Project, Tag 0DTC**, conditional on clause (3) of Stacks 04RU and on the
identification `hlift` of `U'` with the finite part.

In the splitting situation of Stacks 0DTB, given the finite part of the realized groupoid as an
open finite subgroupoid of a restriction along an étale morphism which is cut out by an open `Q`
of the object space containing `u`, there is an algebraic space `U'`, an étale morphism
`U' ⟶ U` and a point `Spec κ(u) ⟶ U'` lying over `u` at which `R|_{U'}` is split.

The point is produced by applying `hlift` to the open and closed decomposition of the fibre of
the source over `u` supplied by
`AlgebraicGeometry.Space.SplittingSituation.exists_fiberOpens_stabilizer`.

This is not a consequence of Stacks 03FM: the hypotheses of Stacks 04RL are stronger than those
of Stacks 0DTB while a strong splitting is a splitting, so the two implications run the same way,
and the splitting condition has to be derived again. -/
-- NO `@[stacks 0DTC]` ATTRIBUTE IS CARRIED, for the same two reasons as Stacks 03FM above: `U'`,
-- the étale map and the point over `u` are all hypotheses rather than conclusions, so the
-- existential content of the tag is assumed and only the splitting is derived; and
-- `TargetLocusSubgroupoid` has no instances for the finite part, so the statement is unusable.
-- Unlike Stacks 03FM, Stacks 0DTC is NOT proved elsewhere in this library.  What is available is
-- its conclusion under the hypotheses of Stacks 04RL, which are strictly stronger than the
-- Stacks 0DTB the tag asks for:
-- `Stacks.Groupoids.GroupoidScheme.exists_etale_splitting_of_strongSplittingSituation` in
-- `EtaleLocalizationFinitePartConstruction`.  That is not the tag and carries no attribute.
-- The gap is the supporting open of the fibre: the development runs on the open `W` with
-- `x ∈ W ↔ t (s⁻¹ x) = u` supplied by `StrongSplittingSituation.exists_fiberOpens_stabilizer`,
-- whereas in Situation 0DTB the only available open is supported on the stabilizer image, a
-- proper subset of `{r | s r = u ∧ t r = u}` in general.
theorem exists_etale_splitting (D : AlgebraicGeometry.Space.SplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    (F : TargetLocusSubgroupoid (D.groupoid.realization C hS hU hR hP))
    (hlift : ∀ W : (D.groupoid.source.left.fiber D.u).Opens,
      (∀ x : D.groupoid.source.left.fiber D.u,
        x ∈ W ↔ ∃ g : (stabilizer D.groupoid).left,
          (stabilizer D.groupoid).hom g = D.u ∧
            stabilizerArrow D.groupoid g = D.groupoid.source.left.fiberι D.u x) →
      (∀ g : (stabilizer D.groupoid).left, (stabilizer D.groupoid).hom g = D.u →
        ∃ x : D.groupoid.source.left.fiber D.u, x ∈ W ∧
          D.groupoid.source.left.fiberι D.u x = stabilizerArrow D.groupoid g) →
      IsClosed (W : Set (D.groupoid.source.left.fiber D.u)) →
      AlgebraicGeometry.IsFinite
        (W.ι ≫ D.groupoid.source.left.fiberToSpecResidueField D.u) →
      ∃ v : F.objects.obj.obj (Opposite.op
          (AlgebraicGeometry.Space.residueFieldSiteObject C hS
            (X := D.groupoid.objects) D.u hK)),
        (AlgebraicGeometry.Space.yonedaSchemePointEquiv C hS hU
          (Opposite.op (AlgebraicGeometry.Space.residueFieldSiteObject C hS
            (X := D.groupoid.objects) D.u hK))
          (F.objectProjection.hom.app _ v)).left =
            D.groupoid.objects.left.fromSpecResidueField D.u)
    (hQ : ∃ q : AlgebraicGeometry.Space.points C D.S hS F.targetLocus.toFunctor,
      AlgebraicGeometry.Space.pointsMap C D.S hS F.targetLocus.toFunctor F.targetLocus.ι q =
        AlgebraicGeometry.Space.yonedaResidueFieldPoint C hS hU D.u hK) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      AlgebraicGeometry.Space.IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (AlgebraicGeometry.Space.residueFieldSiteObject C hS
            (X := D.groupoid.objects) D.u hK)),
        (AlgebraicGeometry.Space.yonedaSchemePointEquiv C hS hU
            (Opposite.op (AlgebraicGeometry.Space.residueFieldSiteObject C hS
              (X := D.groupoid.objects) D.u hK))
            (g.hom.app _ v)).left =
              D.groupoid.objects.left.fromSpecResidueField D.u ∧
        IsSplitAt (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid
          (AlgebraicGeometry.Space.pointsMap C D.S hS U'.obj
            (eqToHom (restrict (D.groupoid.realization C hS hU hR hP) g).objects_eq.symm).hom
            (AlgebraicGeometry.Space.FieldValuedPoint.class C D.S hS U'.obj
              { carrier := D.groupoid.objects.left.residueField D.u
                contained := hK
                toBase := D.groupoid.objects.left.fromSpecResidueField D.u ≫
                  D.groupoid.objects.hom
                value := v })) := by
  obtain ⟨W, hW, hWstab, hWclosed, hWfinite⟩ := D.exists_fiberOpens_stabilizer
  obtain ⟨v, hv⟩ := hlift W hW hWstab hWclosed hWfinite
  exact ⟨F.objects, F.objectProjection, F.objectProjection_etale, v, hv,
    ⟨F.splitting _ (pointMem_of_lies_over D.groupoid D.u C hS hU hR hP hK F v hv hQ)⟩⟩

end Stacks.Groupoids.GroupoidScheme

end
