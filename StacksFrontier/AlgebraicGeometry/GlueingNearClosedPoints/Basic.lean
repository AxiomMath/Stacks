module

public import Mathlib.CategoryTheory.Comma.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RestrictionComparison.Basic

/-!
# Gluing data near finitely many closed points, and the canonical restriction functor

Let `S` be a scheme and let `s : I → S` be a finite family of closed points.  Write
`U = S \ {s i | i}` for the open complement, `S_i = Spec 𝒪_{S, s i}` for the local scheme at
`s i`, and `U_i` for the preimage of `U` in `S_i`.  A *gluing datum* is a scheme of finite
presentation over `U`, a family of schemes of finite presentation over the `S_i`, and an
isomorphism between their two restrictions to the `U_i`.

This file builds the category of such gluing data and the canonical functor from schemes of
finite presentation over `S` into it.  The comparison isomorphism used to build that functor is
not chosen: it is the base-change associativity isomorphism
`AlgebraicGeometry.canonicalRestrictionComparison`, pinned by the equation saying that it
commutes with the projections down to the scheme being restricted.  This is why the functor is
*the* canonical restriction functor rather than one of many.

The assertion of [Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) that this functor
is an equivalence is not proved here.

## Main definitions

* `AlgebraicGeometry.isFinitePresentationOver`: being of finite presentation, read as a property
  of the objects of an over-category of schemes.
* `AlgebraicGeometry.nestedFullSubcategoryEquivalence`: cutting a full subcategory down by a
  second property gives the full subcategory on the conjunction of the two.
* `AlgebraicGeometry.IsoComma`: the iso-comma model of the categorical fibre product of two
  functors, namely the full subcategory of the comma category on the objects whose comparison
  morphism is invertible.
* `AlgebraicGeometry.glueingData`: the category of gluing data, as the iso-comma category of the
  two restriction functors into the product of the categories over the punctured local schemes.
* `AlgebraicGeometry.openComponent` and `AlgebraicGeometry.localComponent`: the two projections
  out of the category of gluing data.
* `AlgebraicGeometry.canonicalRestrictionFunctor`: the canonical functor from schemes of finite
  presentation over `S` to gluing data.

## Implementation notes

An object of `IsoComma F G` carries the isomorphism as part of its data — the full-subcategory
predicate is `IsIso X.hom` on a comma object — and a morphism of `IsoComma F G` is literally a
morphism of the comma category, so it satisfies the compatibility square automatically.  This is
what makes `ObjectProperty.lift` the whole construction of the canonical functor: the object and
morphism assignments land in the comma category, and the side condition is that the comparison
component is invertible, which it is because it is a component of a natural *isomorphism*.

The functoriality of the assignment is the naturality of that isomorphism, so `map` is given by
`NatTrans.naturality` rather than by a separate proof.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe v u

namespace AlgebraicGeometry

/-! ### Generalities on over-categories and full subcategories -/

/-- The property of being of finite presentation, as a property of objects of `Over T`. -/
def isFinitePresentationOver (T : Scheme.{u}) : ObjectProperty (Over T) :=
  fun X ↦ FinitePresentation X.hom

/-- Cutting a full subcategory down by a further property is the full subcategory on the
conjunction of the two properties. -/
def nestedFullSubcategoryEquivalence {C : Type u} [Category.{v} C]
    (A B : ObjectProperty C) :
    (B.inverseImage A.ι).FullSubcategory ≌ (A ⊓ B).FullSubcategory where
  functor :=
    { obj := fun X ↦ ⟨X.obj.obj, ⟨X.obj.property, X.property⟩⟩
      map := fun f ↦ ObjectProperty.homMk f.hom.hom }
  inverse :=
    { obj := fun X ↦ ⟨⟨X.obj, X.property.1⟩, X.property.2⟩
      map := fun f ↦ ObjectProperty.homMk (ObjectProperty.homMk f.hom) }
  unitIso := NatIso.ofComponents fun X ↦
    ObjectProperty.isoMk (B.inverseImage A.ι) (Iso.refl _)
  counitIso := NatIso.ofComponents fun X ↦
    ObjectProperty.isoMk (A ⊓ B) (Iso.refl _)
  functor_unitIso_comp := by intro X; cat_disch

/-! ### Gluing data -/

/-- The iso-comma model for the categorical fibre product of `F : A ⥤ C` and `G : B ⥤ C`: the
full subcategory of the comma category on the objects whose comparison morphism is an
isomorphism. -/
abbrev IsoComma {A B C : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    (F : A ⥤ C) (G : B ⥤ C) :=
  (show ObjectProperty (Comma F G) from fun X ↦ IsIso X.hom).FullSubcategory

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- Gluing data for the complement of a finite family of closed points: a scheme of finite
presentation over the open complement, a family of schemes of finite presentation over the local
schemes, and an isomorphism of their restrictions to the punctured local schemes. -/
abbrev glueingData :=
  IsoComma (restrictOpenToPuncturedLocals s hs) (restrictLocalsToPuncturedLocals s hs)

/-- The projection of a gluing datum to its component over the open complement. -/
noncomputable def openComponent :
    glueingData s hs ⥤ FinitePresentationOver (complementOfClosedPoints s hs).toScheme :=
  (show ObjectProperty (Comma (restrictOpenToPuncturedLocals s hs)
      (restrictLocalsToPuncturedLocals s hs)) from fun X ↦ IsIso X.hom).ι ⋙
    Comma.fst _ _

/-- The projection of a gluing datum to its family of components over the local schemes. -/
noncomputable def localComponent :
    glueingData s hs ⥤ ((i : I) → FinitePresentationOver (Spec (S.presheaf.stalk (s i)))) :=
  (show ObjectProperty (Comma (restrictOpenToPuncturedLocals s hs)
      (restrictLocalsToPuncturedLocals s hs)) from fun X ↦ IsIso X.hom).ι ⋙
    Comma.snd _ _

/-- **Stacks Project, Tag 0E8Q**, the canonical functor.  The functor taking a scheme of finite
presentation over `S` to the gluing datum given by its restriction to the complement of the
closed points, its restrictions to the local schemes at them, and the base-change associativity
isomorphism between the two restrictions to each punctured local scheme.

The comparison is `AlgebraicGeometry.canonicalRestrictionComparison`, which is pinned by its
compatibility equation, so this is the canonical functor and not merely a functor into the
category of gluing data. -/
@[stacks 0E8Q "canonical functor"]
noncomputable def canonicalRestrictionFunctor :
    FinitePresentationOver S ⥤ glueingData s hs :=
  (show ObjectProperty (Comma (restrictOpenToPuncturedLocals s hs)
      (restrictLocalsToPuncturedLocals s hs)) from fun X ↦ IsIso X.hom).lift
    { obj := fun X ↦ ⟨(restrictToComplementOfClosedPoints s hs).obj X,
        (restrictToLocalSchemes s).obj X,
        (canonicalRestrictionComparison s hs).1.hom.app X⟩
      map := fun f ↦ ⟨(restrictToComplementOfClosedPoints s hs).map f,
        (restrictToLocalSchemes s).map f,
        (canonicalRestrictionComparison s hs).1.hom.naturality f⟩
      map_id := by intro X; ext <;> simp
      map_comp := by intro X Y Z f g; ext <;> simp } (fun X ↦ inferInstance)

/-- The open-complement component of the canonical restriction functor is restriction to the
open complement. -/
theorem openComponent_comp_canonicalRestrictionFunctor :
    canonicalRestrictionFunctor s hs ⋙ openComponent s hs =
      restrictToComplementOfClosedPoints s hs :=
  rfl

/-- The local component of the canonical restriction functor is simultaneous restriction to the
local schemes. -/
theorem localComponent_comp_canonicalRestrictionFunctor :
    canonicalRestrictionFunctor s hs ⋙ localComponent s hs = restrictToLocalSchemes s :=
  rfl

end AlgebraicGeometry

end
