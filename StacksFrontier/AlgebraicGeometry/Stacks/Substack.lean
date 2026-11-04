module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Open, closed and locally closed substacks (Stacks 04YM)

Let `𝒳` be an algebraic stack over `S`. Following Stacks 04YM, an *open substack* of `𝒳` is a
strictly full subcategory `𝒳' ⊆ 𝒳` which is itself an algebraic stack and whose inclusion
`𝒳' → 𝒳` is an open immersion; a *closed substack* is the same with a closed immersion, and a
*locally closed substack* with an immersion.

## Main definitions

* `AlgebraicGeometry.Stack.fullSubcategoryBased`: the category over the big fppf site of `S`
  carried by the full subcategory of `𝒳` selected by a property of its objects.
* `AlgebraicGeometry.Stack.fullSubcategoryInclusion`: the canonical inclusion of that full
  subcategory, as a 1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.OpenSubstack`: **Stacks 04YM**, part (1).
* `AlgebraicGeometry.Stack.IsClosedSubstack`: **Stacks 04YM**, part (2).
* `AlgebraicGeometry.Stack.IsLocallyClosedSubstack`: **Stacks 04YM**, part (3).

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.ext`: an open substack is determined by its objects.
* `AlgebraicGeometry.Stack.fullSubcategoryInclusion_obj` and
  `AlgebraicGeometry.Stack.fullSubcategoryInclusion_map`: the inclusion acts as the ordinary
  full-subcategory inclusion, and is full and faithful.

## Implementation notes

A subcategory of `𝒳` is given by a `CategoryTheory.ObjectProperty` on the objects of `𝒳`, and
*strict* fullness is `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`: the full
subcategory on a property closed under isomorphism is exactly a strictly full subcategory, so no
separate replete-subcategory notion is needed. The full subcategory is made a category over the
big fppf site of `S` by restricting the structure functor of `𝒳` along the inclusion, and the
algebraic-stack condition on that restriction supplies its fibred-in-groupoids structure, which
is what lets the inclusion be read as a 1-morphism of algebraic stacks.

Part (1) is a structure rather than a predicate on object properties, because its last field
mentions the proof recorded in its third field — the inclusion is a 1-morphism only once the
subcategory is known to be an algebraic stack. Parts (2) and (3) are predicates, with that proof
bound by an existential; no choice is recorded, since the open-immersion condition does not
depend on which proof of algebraicity is used.

The immersion conditions are the Stacks 04YL predicates of
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack`, which are written out in the
Stacks 04XB form; see that module for why they are not phrased through
`AlgebraicGeometry.Stack.HasRelativeProperty`.

## References

* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The restriction of the structure functor of an algebraic stack to the full subcategory
selected by a property of its objects. -/
abbrev fullSubcategoryBased (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj) :
    BasedCategory.{u, u + 1} (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (P.ι ⋙ 𝒳.val.val.p)

/-- The canonical inclusion of the full subcategory selected by a property of the objects of an
algebraic stack, as a 1-morphism of categories over the big fppf site of `S`. -/
@[implicit_reducible]
def fullSubcategoryBasedInclusion (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj) :
    fullSubcategoryBased 𝒳 P ⥤ᵇ 𝒳.val.val where
  toFunctor := P.ι
  w := rfl

/-- The full subcategory selected by a property of the objects of an algebraic stack, as an
algebraic stack, given a proof that it is one. -/
abbrev fullSubcategoryAlgebraicStack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    AlgebraicStacks.{u, w} B S hS :=
  ⟨CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 P) hP.choose, hP⟩

/-- The canonical inclusion of the full subcategory selected by a property of the objects of an
algebraic stack, as a 1-morphism of algebraic stacks. -/
@[implicit_reducible]
def fullSubcategoryInclusion (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    fullSubcategoryAlgebraicStack 𝒳 P hP ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 P))

/-- **Stacks 04YM**, part (1). An *open substack* of an algebraic stack `𝒳` over `S` is a
strictly full subcategory of `𝒳` which is an algebraic stack and whose canonical inclusion into
`𝒳` is an open immersion. -/
@[stacks 04YM "open_substack"]
structure OpenSubstack (𝒳 : AlgebraicStacks.{u, w} B S hS) where
  /-- The property of objects of `𝒳` selecting the full subcategory. -/
  property : ObjectProperty 𝒳.val.val.obj
  /-- Strict fullness: membership is invariant under isomorphism. -/
  strictlyFull : property.IsClosedUnderIsomorphisms
  /-- The full subcategory is an algebraic stack. -/
  isAlgebraic : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 property)
  /-- Its canonical inclusion into `𝒳` is an open immersion. -/
  isOpenImmersion : AlgebraicStacks.IsOpenImmersion B S hS
    (fullSubcategoryInclusion 𝒳 property isAlgebraic)

/-- Two open substacks with the same objects are equal. -/
@[ext, stacks 04YM "open_substack"]
theorem OpenSubstack.ext {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V : OpenSubstack 𝒳}
    (h : U.property = V.property) : U = V := by
  cases U with
  | mk up us ua ui =>
    cases V with
    | mk vp vs va vi =>
      simp_all

/-- The canonical inclusion of an algebraic full subcategory is full. -/
instance full_fullSubcategoryInclusion (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    (fullSubcategoryInclusion 𝒳 P hP).hom.hom.toFunctor.Full :=
  ObjectProperty.full_ι P

/-- The canonical inclusion of an algebraic full subcategory is faithful. -/
instance faithful_fullSubcategoryInclusion (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) :
    (fullSubcategoryInclusion 𝒳 P hP).hom.hom.toFunctor.Faithful :=
  ObjectProperty.faithful_ι P

/-- On objects, the canonical inclusion forgets the membership proof. -/
@[simp, stacks 04YM "open_substack"]
theorem fullSubcategoryInclusion_obj (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (X : P.FullSubcategory) :
    (fullSubcategoryInclusion 𝒳 P hP).hom.hom.toFunctor.obj X = X.obj :=
  rfl

/-- On morphisms, the canonical inclusion forgets the membership proof. -/
@[simp, stacks 04YM "open_substack"]
theorem fullSubcategoryInclusion_map (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    (fullSubcategoryInclusion 𝒳 P hP).hom.hom.toFunctor.map f = f.hom :=
  rfl

/-- **Stacks 04YM**, part (2). A property of the objects of an algebraic stack `𝒳` over `S`
selects a *closed substack* when it is closed under isomorphism, its full subcategory is an
algebraic stack, and the canonical inclusion of that full subcategory into `𝒳` is a closed
immersion. -/
@[stacks 04YM "closed_substack"]
abbrev IsClosedSubstack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj) : Prop :=
  P.IsClosedUnderIsomorphisms ∧
    ∃ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
      AlgebraicStacks.IsClosedImmersion B S hS (fullSubcategoryInclusion 𝒳 P hP)

/-- **Stacks 04YM**, part (3). A property of the objects of an algebraic stack `𝒳` over `S`
selects a *locally closed substack* when it is closed under isomorphism, its full subcategory is
an algebraic stack, and the canonical inclusion of that full subcategory into `𝒳` is an
immersion. -/
@[stacks 04YM "locally_closed_substack"]
abbrev IsLocallyClosedSubstack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj) : Prop :=
  P.IsClosedUnderIsomorphisms ∧
    ∃ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
      AlgebraicStacks.IsImmersion B S hS (fullSubcategoryInclusion 𝒳 P hP)

end AlgebraicGeometry.Stack

end
