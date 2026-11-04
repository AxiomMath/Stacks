module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# Schemes as algebraic spaces, and algebraic spaces over varying bases (Stacks 04U8)

Let `S` be a scheme contained in a big fppf site `B`. A scheme `U` over `S` is an algebraic
space over `S`, namely its presheaf of points; this is the inclusion by Yoneda, and it is
functorial in `U`.

Stacks 04U8 describes the morphisms of the category whose objects are pairs consisting of a
scheme over `S` and an algebraic space over it — the comma category of the inclusion of
algebraic spaces over Yoneda — as a map of base schemes together with a map over the source
scheme into the base change. This file carries the inclusion of schemes and the reading of a
comma object's structure map as a morphism of algebraic spaces, which is what that
description is phrased with; the hom-set equation itself is **not** proved here, see the
implementation notes.

## Main definitions

* `AlgebraicGeometry.schemeSpace`: a scheme over `S`, regarded as an algebraic space over
  `S`.
* `AlgebraicGeometry.schemeSpaceMap`: the morphism of algebraic spaces induced by a morphism
  of schemes over `S`.
* `AlgebraicGeometry.schemeSpaceFunctor`: the two together, as the Yoneda embedding of the
  schemes over `S` corestricted to the algebraic spaces over `S`.
* `AlgebraicGeometry.commaHomAsSpaceMap`: the structure map of an object of the comma
  category, read as a morphism of algebraic spaces into the including scheme.

## Implementation notes

All algebraic spaces are presheaves on the one fixed big fppf site of `S`, so the inclusion
of a scheme is `CategoryTheory.yoneda` and algebraicity of the result is Stacks 025Z. A
morphism of algebraic spaces is a morphism of presheaves
(`CategoryTheory.ObjectProperty.homMk` into the full subcategory), so both the induced map
and the structure map of a comma object are produced by that constructor, and
`commaHomAsSpaceMap` is the identity on the underlying map of presheaves.

The hom-set equation of Stacks 04U8 is not in this file: it is stated with the fibre product
in the category of algebraic spaces over `S` and with the fact that that square is a
pullback, which is Stacks 02X2, a result this library does not yet have.

`schemeSpace` and `schemeSpaceMap` take the site, the base scheme and the containment
implicitly, since the scheme over `S` determines all three; `schemeSpaceFunctor` has nothing
to infer them from and so takes them explicitly.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 04U8](https://stacks.math.columbia.edu/tag/04U8)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A scheme over `S`, regarded as an algebraic space over `S`: its presheaf of points. -/
def schemeSpace (U : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩

/-- The morphism of algebraic spaces over `S` induced by a morphism of schemes over `S`. -/
def schemeSpaceMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    schemeSpace U ⟶ schemeSpace V :=
  ObjectProperty.homMk (yoneda.map g)

/-- The presheaf underlying the algebraic space of a scheme is the representable presheaf. -/
theorem schemeSpace_obj (U : BigFppfOver B S hS) : (schemeSpace U).obj = yoneda.obj U := rfl

/-- The morphism underlying `schemeSpaceMap` is the Yoneda image of the morphism. -/
theorem schemeSpaceMap_hom {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    (schemeSpaceMap g).hom = yoneda.map g := rfl

/-- The structure map of an object of the comma category of algebraic spaces over Yoneda,
read as a morphism of algebraic spaces into the algebraic space of its base scheme. -/
def commaHomAsSpaceMap
    (X : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    X.left ⟶ schemeSpace X.right :=
  ObjectProperty.homMk (show X.left.obj ⟶ (schemeSpace X.right).obj from by
    change (ObjectProperty.ι _).obj X.left ⟶ yoneda.obj X.right
    exact X.hom)

section Functor

variable (B) (S) (hS)

/-- Reading a scheme over `S` as an algebraic space over `S` is functorial: the Yoneda
embedding of the schemes over `S` of a big fppf site, corestricted to the algebraic spaces
over `S`.

This and `AlgebraicGeometry.schemeSpace` are the vocabulary of Stacks 04U8 rather than part
of its content, which is the hom-set equation `AlgebraicGeometry.spaceHomEquivPullbackHom`,
so neither carries that tag; see the implementation notes. -/
def schemeSpaceFunctor : BigFppfOver B S hS ⥤ AlgebraicSpaces B S hS where
  obj U := schemeSpace U
  map g := schemeSpaceMap g
  map_id := by
    intro T
    apply ObjectProperty.hom_ext
    rfl
  map_comp := by
    intro T U V g k
    apply ObjectProperty.hom_ext
    rfl

/-- On objects, the corestricted Yoneda embedding is the representable presheaf. -/
@[simp]
theorem schemeSpaceFunctor_obj_val (U : BigFppfOver B S hS) :
    ((schemeSpaceFunctor B S hS).obj U).1 = yoneda.obj U := rfl

/-- On morphisms, the corestricted Yoneda embedding is the Yoneda image of the morphism. -/
@[simp]
theorem schemeSpaceFunctor_map_hom {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    ((schemeSpaceFunctor B S hS).map g).hom = yoneda.map g := rfl

end Functor

end AlgebraicGeometry

end
