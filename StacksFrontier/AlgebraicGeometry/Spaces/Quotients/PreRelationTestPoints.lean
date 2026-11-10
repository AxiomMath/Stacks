module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoarseQuotient

/-!
# Points of a pre-relation of algebraic spaces, in the slice of presheaves

Let `B` be an algebraic space over a scheme `S` of a big fppf site. The pre-relation
vocabulary of Stacks 043C is used in two slices: the slice of the algebraic spaces over `B`,
which is where the fibre products and coproducts of algebraic spaces live, and the slice of
presheaves over the underlying presheaf of `B`, which is where the induced relation on the
points of a test scheme, the quotient sheaf and the orbits of a field-valued point live. The
functor carrying the first to the second is `AlgebraicGeometry.Space.overForgetSpace` and the
induced pre-relation is `AlgebraicGeometry.Space.presheafPreRelation`, both defined in
`StacksFrontier/AlgebraicGeometry/Spaces/Quotients/CoarseQuotient.lean`.

This file supplies what a consumer in the smaller slice needs in order to use that reading:
the two maps of the induced pre-relation, as natural transformations; that invariance is the
same condition on either side; and the identification of a test point of an algebraic space
over `B` with a morphism of algebraic spaces over `B` out of the representable algebraic
space of the test scheme, under which an arrow of the pre-relation out of that representable
is exactly a related pair of test points.

## Main definitions

* `AlgebraicGeometry.Space.representableOver` is a test scheme over `B`, read as an algebraic
  space over `B`.
* `AlgebraicGeometry.Space.testPointOver` and `AlgebraicGeometry.Space.overTestPoint` are the
  two directions of the identification of test points with morphisms out of the
  representable.

## Main results

* `AlgebraicGeometry.Space.over_w_hom`: a morphism of algebraic spaces over `B` is a morphism
  over the underlying presheaf of `B`.
* `AlgebraicGeometry.Space.presheafPreRelation_target_left` and
  `AlgebraicGeometry.Space.presheafPreRelation_source_left`: the two maps of the induced
  pre-relation are the two maps of the original.
* `AlgebraicGeometry.Space.isInvariant_presheafPreRelation_iff`: invariance is unchanged by
  this reading.
* `AlgebraicGeometry.Space.rel_presheafPreRelation`: an arrow out of the representable
  relates the test points its target and its source cut out, and
  `AlgebraicGeometry.Space.rel_presheafPreRelation_iff`: every related pair arises this way.

## Implementation notes

That the presheaf represented by a test scheme is an algebraic space is Stacks 025Z, in the
form of the functor `AlgebraicGeometry.schemeSpaceFunctor`.

Algebraic spaces over `B` are a full subcategory of the presheaves over `B.obj`, so a test
point of an algebraic space over `B` and a morphism out of the representable carry literally
the same data; `AlgebraicGeometry.Space.overTestPoint` and
`AlgebraicGeometry.Space.testPointOver` are mutually inverse by `rfl`, and only one of the two
round trips is recorded, the other being the uniqueness of the morphism out of the
representable with a given underlying natural transformation.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 048E](https://stacks.math.columbia.edu/tag/048E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : AlgebraicSpaces site S hS}

/-- The underlying natural transformation of a morphism of algebraic spaces over `B` is a
morphism over the underlying presheaf of `B`. -/
theorem over_w_hom {U V : Over B} (f : U ⟶ V) : f.left.hom ≫ V.hom.hom = U.hom.hom := by
  simpa only [ObjectProperty.FullSubcategory.comp_hom] using
    congrArg (fun g : U.left ⟶ B => g.hom) (Over.w f)

/-- The target map of the pre-relation of presheaves is the target map of the original. -/
theorem presheafPreRelation_target_left {R U : Over B} (j : PreRelation R U) :
    (presheafPreRelation j).target.left = j.target.left.hom := by
  rw [presheafPreRelation_target]; rfl

/-- The source map of the pre-relation of presheaves is the source map of the original. -/
theorem presheafPreRelation_source_left {R U : Over B} (j : PreRelation R U) :
    (presheafPreRelation j).source.left = j.source.left.hom := by
  rw [presheafPreRelation_source]; rfl

/-- **Stacks 048E.** Invariance of a morphism of algebraic spaces under a pre-relation is
unchanged by reading the pre-relation in the slice of presheaves. -/
theorem isInvariant_presheafPreRelation_iff {R U X : Over B} (j : PreRelation R U)
    (φ : U ⟶ X) :
    IsInvariant (presheafPreRelation j) (φ.left.hom) ↔ IsInvariant j φ.left := by
  change (presheafPreRelation j).target.left ≫ φ.left.hom =
      (presheafPreRelation j).source.left ≫ φ.left.hom ↔ _
  rw [presheafPreRelation_target_left, presheafPreRelation_source_left]
  refine ⟨ObjectProperty.hom_ext _, fun h => ?_⟩
  have h' := congrArg (fun g : R.left ⟶ X.left => g.hom) h
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h'
  exact h'

/-! ### Test points as morphisms out of a representable -/

/-- **Stacks 025Z.** A test scheme over `B`, read as an algebraic space over `B`: the presheaf
it represents is an algebraic space. -/
noncomputable def representableOver (T : BigFppfOver site S hS) (b : yoneda.obj T ⟶ B.obj) :
    Over B :=
  Over.mk (ObjectProperty.homMk (X := (schemeSpaceFunctor site S hS).obj T) b)

/-- The structure morphism of the representable algebraic space of a test scheme over `B` is
the given point of `B`. -/
@[simp]
theorem representableOver_hom_hom (T : BigFppfOver site S hS) (b : yoneda.obj T ⟶ B.obj) :
    (representableOver (B := B) T b).hom.hom = b := rfl

/-- A test point of an algebraic space over `B`, read as a morphism of algebraic spaces over
`B` out of the representable algebraic space of the test scheme. -/
noncomputable def testPointOver {T : BigFppfOver site S hS} {b : yoneda.obj T ⟶ B.obj}
    {X : Over B} (x : TestPoint T b ((overForgetSpace B).obj X)) :
    representableOver (B := B) T b ⟶ X :=
  Over.homMk (ObjectProperty.homMk x.1) (ObjectProperty.hom_ext _ x.2)

/-- The underlying natural transformation of the morphism attached to a test point is the test
point. -/
@[simp]
theorem testPointOver_left_hom {T : BigFppfOver site S hS} {b : yoneda.obj T ⟶ B.obj}
    {X : Over B} (x : TestPoint T b ((overForgetSpace B).obj X)) :
    (testPointOver (B := B) x).left.hom = x.1 := rfl

/-- A morphism of algebraic spaces over `B` out of the representable algebraic space of a test
scheme, read as a test point. -/
noncomputable def overTestPoint {T : BigFppfOver site S hS} {b : yoneda.obj T ⟶ B.obj}
    {X : Over B} (f : representableOver (B := B) T b ⟶ X) :
    TestPoint T b ((overForgetSpace B).obj X) :=
  ⟨f.left.hom, over_w_hom f⟩

/-- The test point attached to a morphism out of the representable is its underlying natural
transformation. -/
@[simp]
theorem overTestPoint_coe {T : BigFppfOver site S hS} {b : yoneda.obj T ⟶ B.obj} {X : Over B}
    (f : representableOver (B := B) T b ⟶ X) : (overTestPoint f).1 = f.left.hom := rfl

/-- Reading a test point as a morphism out of the representable and back gives the test point
again. -/
@[simp]
theorem overTestPoint_testPointOver {T : BigFppfOver site S hS} {b : yoneda.obj T ⟶ B.obj}
    {X : Over B} (x : TestPoint T b ((overForgetSpace B).obj X)) :
    overTestPoint (testPointOver (B := B) x) = x := rfl

variable {R U : Over B}

/-- An arrow of a pre-relation out of the representable algebraic space of a test scheme
relates the two test points its target and its source cut out. -/
theorem rel_presheafPreRelation (j : PreRelation R U) {T : BigFppfOver site S hS}
    {b : yoneda.obj T ⟶ B.obj} (r : representableOver (B := B) T b ⟶ R) :
    (presheafPreRelation j).Rel b (overTestPoint (r ≫ j.target))
      (overTestPoint (r ≫ j.source)) := by
  refine ⟨overTestPoint r, ?_, ?_⟩
  · rw [presheafPreRelation_target_left]; rfl
  · rw [presheafPreRelation_source_left]; rfl

/-- Two test points of `U` are related by a pre-relation exactly when they are the target and
the source of an arrow out of the representable algebraic space of the test scheme. -/
theorem rel_presheafPreRelation_iff (j : PreRelation R U) {T : BigFppfOver site S hS}
    {b : yoneda.obj T ⟶ B.obj} (x y : TestPoint T b ((overForgetSpace B).obj U)) :
    (presheafPreRelation j).Rel b x y ↔
      ∃ r : representableOver (B := B) T b ⟶ R,
        overTestPoint (r ≫ j.target) = x ∧ overTestPoint (r ≫ j.source) = y := by
  constructor
  · rintro ⟨r, ht, hs⟩
    rw [presheafPreRelation_target_left] at ht
    rw [presheafPreRelation_source_left] at hs
    exact ⟨testPointOver r, Subtype.ext ht, Subtype.ext hs⟩
  · rintro ⟨r, rfl, rfl⟩
    exact rel_presheafPreRelation j r

end AlgebraicGeometry.Space

end
