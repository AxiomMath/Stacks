module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.PointwiseComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Splittings of a groupoid in algebraic spaces at a point

An *open finite subgroupoid* of a groupoid in algebraic spaces is an open subspace of its
arrow space, with the same object space and the restricted source and target morphisms, which
is closed under composition and whose restricted source and target are finite. Such a
subgroupoid *splits* a groupoid at a point `u` of the object space to the extent that it
contains the arrows over `u`: a *strong splitting* contains every arrow whose source and
target both map to `u`, a *splitting* contains every point of the stabilizer lying over `u`,
and a *quasi-splitting* merely contains the identity arrow at `u`.

Identity arrows are themselves a map on points: the identity arrow at a field-valued point of
the object space is a field-valued point of the arrow space, and this respects the equivalence
relation defining points.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid`: an open subgroupoid of
  the arrow space with finite restricted source and target.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityPoint` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityOnPoints`: the identity arrow at a
  field-valued point, and the induced map on points.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.StrongSplitting`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Splitting` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.QuasiSplitting`, with the three existence
  statements `IsStronglySplitAt`, `IsSplitAt` and `IsQuasiSplitAt`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityPoint_hasCommonExtension`: taking the
  identity arrow respects common extension of field-valued points, so it descends to points.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityOnPoints_class`: the induced map on
  points sends the class of a field-valued point to the class of its identity arrow.

## Implementation notes

The subgroupoid is recorded with the ambient object space and the ambient composition: its
source and target are the restrictions of the ambient ones along the inclusion of the open
subspace, its composition is a morphism out of the presheaf of pairs of its own arrows
composable for those restrictions, and `comp_restricts` says that this composition agrees with
the ambient one. Finiteness is therefore finiteness of a morphism into the *ambient* object
space.

The stabilizer used by `Splitting` is the one of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizer`, read in the slice over the object
space; its points are tested against `u` through its structure morphism and transported to
points of the arrow space along
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrow`.

That the identity arrow descends to points is `Deformation.GroupoidInFunctors.map_identity`:
restricting a section along a morphism of field spectra commutes with taking the identity
arrow, so a common extension of two field-valued points of the object space gives a common
extension of the two identity arrows.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- An open subspace of the arrow space of a groupoid in algebraic spaces which is itself a
groupoid on the ambient object space, with the restricted source and target morphisms finite
and with composition the restriction of the ambient composition.

This is conditions (a) and (b) shared by the three splittings of **Stacks 04RK**. -/
@[stacks 04RK "conditions (a) and (b) on the open subspace"]
structure OpenFiniteSubgroupoid (G : GroupoidInAlgebraicSpaces C S hS B) where
  /-- The open subspace of arrows. -/
  arrows : Subfunctor G.arrows.obj
  /-- It is an open subspace. -/
  arrows_open : Space.IsOpenSubspace C S hS arrows
  /-- The restricted source morphism is finite. -/
  source_finite : Space.IsFinite C S hS (arrows.ι ≫ G.source.hom)
  /-- The restricted target morphism is finite. -/
  target_finite : Space.IsFinite C S hS (arrows.ι ≫ G.target.hom)
  /-- Composition of pairs of arrows of the subgroupoid composable for the restricted source
  and target. -/
  comp : Deformation.composableArrows G.objects.obj arrows.toFunctor
    (arrows.ι ≫ G.source.hom) (arrows.ι ≫ G.target.hom) ⟶ arrows.toFunctor
  /-- Composition in the subgroupoid is the restriction of the ambient composition. -/
  comp_restricts : ∀ T (p : (Deformation.composableArrows G.objects.obj
      arrows.toFunctor (arrows.ι ≫ G.source.hom) (arrows.ι ≫ G.target.hom)).obj T),
    arrows.ι.app T (comp.app T p) =
      G.toGroupoidInFunctors.comp.app T
        ⟨(arrows.ι.app T p.1.1, arrows.ι.app T p.1.2), p.2⟩
  /-- Evaluation at every test scheme is a groupoid. -/
  pointwiseGroupoid : ∀ T, Nonempty (Deformation.PointwiseGroupoid
    ((arrows.ι ≫ G.source.hom).app T) ((arrows.ι ≫ G.target.hom).app T)
    (fun p => comp.app T p))

/-- The field-valued point of the arrow space given by the identity arrow at a field-valued
point of the object space. -/
noncomputable def identityPoint (G : GroupoidInAlgebraicSpaces C S hS B)
    (p : Space.FieldValuedPoint C S hS G.objects.obj) :
    Space.FieldValuedPoint C S hS G.arrows.obj where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase
  value := G.toGroupoidInFunctors.identity (Opposite.op p.siteObject) p.value

/-- Taking the identity arrow at a field-valued point of the object space respects common
extension, so it descends to the points of the two spaces. -/
@[stacks 04RK "part (3): the identity on points is well defined"]
theorem identityPoint_hasCommonExtension (G : GroupoidInAlgebraicSpaces C S hS B)
    {p q : Space.FieldValuedPoint C S hS G.objects.obj}
    (h : Space.FieldValuedPoint.HasCommonExtension C S hS G.objects.obj p q) :
    Space.FieldValuedPoint.HasCommonExtension C S hS G.arrows.obj
      (identityPoint G p) (identityPoint G q) := by
  obtain ⟨r, ⟨f, hf⟩, ⟨g, hg⟩⟩ := h
  refine ⟨identityPoint G r, ?_, ?_⟩
  · refine ⟨f, ?_⟩
    have hn := Deformation.GroupoidInFunctors.map_identity
      G.toGroupoidInFunctors f.op p.value
    have hf' : (G.toGroupoidInFunctors.objects.map f.op) p.value = r.value := hf
    rw [hf'] at hn
    convert hn using 1 <;> rfl
  · refine ⟨g, ?_⟩
    have hn := Deformation.GroupoidInFunctors.map_identity
      G.toGroupoidInFunctors g.op q.value
    have hg' : (G.toGroupoidInFunctors.objects.map g.op) q.value = r.value := hg
    rw [hg'] at hn
    convert hn using 1 <;> rfl

/-- The map on points sending a point of the object space to the identity arrow at it. -/
noncomputable def identityOnPoints (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.points C S hS G.objects.obj → Space.points C S hS G.arrows.obj :=
  Quot.map (identityPoint G) (fun _ _ h => identityPoint_hasCommonExtension G h)

/-- The identity map on points sends the class of a field-valued point to the class of its
identity arrow. -/
@[simp]
theorem identityOnPoints_class (G : GroupoidInAlgebraicSpaces C S hS B)
    (p : Space.FieldValuedPoint C S hS G.objects.obj) :
    identityOnPoints G (p.class C S hS G.objects.obj) =
      (identityPoint G p).class C S hS G.arrows.obj := rfl

/-- A strong splitting of a groupoid in algebraic spaces at a point `u` of its object space: an
open finite subgroupoid containing every point of the arrow space whose source and target are
both `u`. -/
@[stacks 04RK "part (1): a strong splitting"]
structure StrongSplitting (G : GroupoidInAlgebraicSpaces C S hS B)
    (u : Space.points C S hS G.objects.obj) extends OpenFiniteSubgroupoid G where
  /-- Every arrow with both endpoints at `u` lies in the subgroupoid. -/
  contains_arrows : ∀ r : Space.points C S hS G.arrows.obj,
    (Space.pointsMap C S hS G.arrows.obj G.source.hom r = u ∧
      Space.pointsMap C S hS G.arrows.obj G.target.hom r = u) →
      ∃ p : Space.points C S hS arrows.toFunctor,
        Space.pointsMap C S hS arrows.toFunctor arrows.ι p = r

/-- A splitting of a groupoid in algebraic spaces at a point `u` of its object space: an open
finite subgroupoid containing every point of the stabilizer which lies over `u`. -/
@[stacks 04RK "part (2): a splitting"]
structure Splitting (G : GroupoidInAlgebraicSpaces C S hS B)
    (u : Space.points C S hS G.objects.obj) extends OpenFiniteSubgroupoid G where
  /-- Every point of the stabilizer over `u` lies in the subgroupoid. -/
  contains_stabilizer : ∀ g : Space.points C S hS (stabilizer G).left,
    Space.pointsMap C S hS (stabilizer G).left (stabilizer G).hom g = u →
      ∃ p : Space.points C S hS arrows.toFunctor,
        Space.pointsMap C S hS arrows.toFunctor arrows.ι p =
          Space.pointsMap C S hS (stabilizer G).left (stabilizerArrow G) g

/-- A quasi-splitting of a groupoid in algebraic spaces at a point `u` of its object space: an
open finite subgroupoid containing the identity arrow at `u`. -/
@[stacks 04RK "part (3): a quasi-splitting"]
structure QuasiSplitting (G : GroupoidInAlgebraicSpaces C S hS B)
    (u : Space.points C S hS G.objects.obj) extends OpenFiniteSubgroupoid G where
  /-- The identity arrow at `u` lies in the subgroupoid. -/
  contains_identity : ∃ q : Space.points C S hS arrows.toFunctor,
    Space.pointsMap C S hS arrows.toFunctor arrows.ι q = identityOnPoints G u

/-- A groupoid in algebraic spaces is *strongly split* at a point of its object space when a
strong splitting there exists. -/
@[stacks 04RK "part (1): strongly split over a point"]
abbrev IsStronglySplitAt (G : GroupoidInAlgebraicSpaces C S hS B)
    (u : Space.points C S hS G.objects.obj) : Prop := Nonempty (StrongSplitting G u)

/-- A groupoid in algebraic spaces is *split* at a point of its object space when a splitting
there exists. -/
@[stacks 04RK "part (2): split over a point"]
abbrev IsSplitAt (G : GroupoidInAlgebraicSpaces C S hS B)
    (u : Space.points C S hS G.objects.obj) : Prop := Nonempty (Splitting G u)

/-- A groupoid in algebraic spaces is *quasi-split* at a point of its object space when a
quasi-splitting there exists. -/
@[stacks 04RK "part (3): quasi-split over a point"]
abbrev IsQuasiSplitAt (G : GroupoidInAlgebraicSpaces C S hS B)
    (u : Space.points C S hS G.objects.obj) : Prop := Nonempty (QuasiSplitting G u)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
