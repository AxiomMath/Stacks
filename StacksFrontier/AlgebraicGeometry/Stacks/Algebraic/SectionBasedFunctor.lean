module

public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Basic

/-!
# A compatible family of sections as a 1-morphism into a category of elements

Let `A` be a category over a base `C` and let `F : Cᵒᵖ ⥤ Type u` be a set-valued presheaf. A
family of sections `s x : F (p x)`, one for each object `x` of `A`, which is compatible in the
sense that a morphism of `A` restricts the section at its target to the section at its source,
is the same thing as a 1-morphism from `A` to the category of elements of `F` over `C`.

## Main definitions

* `AlgebraicGeometry.Stack.sectionBasedFunctor`: the 1-morphism attached to a compatible family
  of sections.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Stack

/-- The 1-morphism into the category of elements of `F` given by a family of sections `s x` of
`F`, indexed by the objects of a category `A` over the site, which is compatible in the sense `hs`
that a morphism of `A` restricts the section at its target to the section at its source. -/
public def sectionBasedFunctor {C : Type*} [Category C]
    (A : BasedCategory C) (F : Cᵒᵖ ⥤ Type u)
    (s : ∀ x : A.obj, F.obj (Opposite.op (A.p.obj x)))
    (hs : ∀ {x y : A.obj} (g : x ⟶ y), s x = F.map (A.p.map g).op (s y)) :
    A ⥤ᵇ presheafOfCategories (F ⋙ typeToCat) where
  toFunctor := {
    obj x := ⟨A.p.obj x, Discrete.mk (s x)⟩
    map g := ⟨A.p.map g, Discrete.eqToHom (hs g)⟩
    map_id x := presheaf_hom_ext F (A.p.map_id x)
    map_comp g h := presheaf_hom_ext F (A.p.map_comp g h) }
  w := rfl

end AlgebraicGeometry.Stack

end
