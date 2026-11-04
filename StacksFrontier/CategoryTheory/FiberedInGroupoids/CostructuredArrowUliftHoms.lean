module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# Raising the morphism universe of a category of costructured arrows

Let `G : 𝒜 ⥤ ℰ` be a functor and let `d` be an object of `ℰ`. Raising the morphism universe of the
source, that is replacing `𝒜` by `CategoryTheory.ULiftHom 𝒜` and `G` by `ULiftHom.down ⋙ G`, does
not change the objects of the category of costructured arrows to `d` and wraps its morphisms in
`ULift`:

`CostructuredArrow G d` is equivalent to `CostructuredArrow (ULiftHom.down ⋙ G) d`

and the equivalence lies, in both directions, *strictly* over any category `C` over which `𝒜`
lies: both comparison functors are the identity on the underlying objects, and on morphisms they
only add or remove the `ULift` wrapper.

The two categories of costructured arrows are *not* `CategoryTheory.ULiftHom` of one another: a
morphism of `CostructuredArrow (ULiftHom.down ⋙ G) d` is a `ULift`ed morphism of `𝒜` together with
a commuting triangle, while a morphism of `ULiftHom (CostructuredArrow G d)` is a `ULift`ed pair of
the two. So the comparison is not the morphism-universe lift `CategoryTheory.Functor.uliftHomMap`
of a functor, and it is built here directly; what it shares with
`CategoryTheory.Functor.isEquivalenceOver_uliftHomMap` is that nothing happens, every component
being a `ULift` wrapper added or removed.

## Main definitions

* `StacksRepresentableCFG.costructuredArrowUliftHomsFunctor` and
  `StacksRepresentableCFG.costructuredArrowUnliftHomsFunctor`: the two comparison functors.
* `StacksRepresentableCFG.costructuredArrowUliftHomsHom` and
  `StacksRepresentableCFG.costructuredArrowUliftHomsInv`: the same, as 1-morphisms over `C`.
* `StacksRepresentableCFG.costructuredArrowUliftHoms`: the equivalence over `C`.

## Implementation notes

The object and morphism assignments of the two comparison functors are given as named definitions
rather than inline in the functor. The triangle a morphism of costructured arrows has to satisfy is
stated at the raised universe and holds at the original one by definitional unfolding, so inline it
is an `autoParam` whose implicit endpoints only get solved after the functor laws are elaborated,
and those laws are then stuck on metavariables.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
-/

@[expose] public section

open CategoryTheory

namespace StacksRepresentableCFG

universe w v₀ u₀ v₁ u₁ v₂ u₂

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {ℰ : Type u₂} [Category.{v₂} ℰ] (G : 𝒜 ⥤ ℰ) (d : ℰ)

/-! ### The comparison in the direction of the raised universe -/

/-- A costructured arrow `G x ⟶ d` read at the raised morphism universe: the arrow is unchanged,
only the category its source lives in is. -/
def costructuredArrowUliftHomsObj (c : CostructuredArrow G d) :
    CostructuredArrow ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ G) d :=
  CostructuredArrow.mk (Y := (ULiftHom.up : 𝒜 ⥤ ULiftHom.{w} 𝒜).obj c.left) c.hom

/-- A morphism of costructured arrows read at the raised morphism universe: its underlying
morphism of `𝒜` is wrapped in `ULift`, and the triangle it has to satisfy is the original one. -/
def costructuredArrowUliftHomsMap {c c' : CostructuredArrow G d} (m : c ⟶ c') :
    (costructuredArrowUliftHomsObj G d c :
        CostructuredArrow ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ G) d) ⟶
      costructuredArrowUliftHomsObj G d c' :=
  CostructuredArrow.homMk ((ULiftHom.up : 𝒜 ⥤ ULiftHom.{w} 𝒜).map m.left)
    (by exact CostructuredArrow.w m)

/-- **The costructured arrows to `d` read at the raised morphism universe.** -/
def costructuredArrowUliftHomsFunctor :
    CostructuredArrow G d ⥤
      CostructuredArrow ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ G) d where
  obj := costructuredArrowUliftHomsObj G d
  map := costructuredArrowUliftHomsMap G d
  map_id _ := CostructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := CostructuredArrow.hom_ext _ _ rfl

/-! ### The comparison back -/

/-- A costructured arrow at the raised morphism universe, read back. -/
def costructuredArrowUnliftHomsObj
    (c : CostructuredArrow ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ G) d) :
    CostructuredArrow G d :=
  CostructuredArrow.mk (Y := (ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜).obj c.left) c.hom

/-- A morphism of costructured arrows at the raised morphism universe, read back: the `ULift`
wrapper is removed and the triangle is the original one. -/
def costructuredArrowUnliftHomsMap
    {c c' : CostructuredArrow ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ G) d} (m : c ⟶ c') :
    costructuredArrowUnliftHomsObj G d c ⟶ costructuredArrowUnliftHomsObj G d c' :=
  CostructuredArrow.homMk ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜).map m.left)
    (by exact CostructuredArrow.w m)

/-- **The costructured arrows at the raised morphism universe read back.** -/
def costructuredArrowUnliftHomsFunctor :
    CostructuredArrow ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ G) d ⥤ CostructuredArrow G d where
  obj := costructuredArrowUnliftHomsObj G d
  map := costructuredArrowUnliftHomsMap G d
  map_id _ := CostructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := CostructuredArrow.hom_ext _ _ rfl

/-! ### The equivalence over a base -/

variable {C : Type u₀} [Category.{v₀} C] (p : 𝒜 ⥤ C)

/-- **The forward comparison 1-morphism over `C`.** -/
def costructuredArrowUliftHomsHom :
    MorphismOver (CostructuredArrow.proj G d ⋙ p)
      (CostructuredArrow.proj ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ G) d ⋙
        (ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ p) where
  functor := costructuredArrowUliftHomsFunctor G d
  w := rfl

/-- **The backward comparison 1-morphism over `C`.** -/
def costructuredArrowUliftHomsInv :
    MorphismOver
      (CostructuredArrow.proj ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ G) d ⋙
        (ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ p)
      (CostructuredArrow.proj G d ⋙ p) where
  functor := costructuredArrowUnliftHomsFunctor G d
  w := rfl

/-- **Raising the morphism universe of the source gives an equivalent category of costructured
arrows over `C`.** Both 1-morphisms are strictly over `C`, and the unit and counit are the
identity: the two round trips of adding and removing the `ULift` wrapper are the identity on the
nose.

This is the morphism-universe half of the third link of the identification the smoothness clause
of **Stacks 0DQ0** needs: the polarized families over a fixed finitely presented, flat and proper
family of algebraic spaces are the same whether the category of polarized families is read with
its own morphisms or with them `ULift`ed into the universe the 2-fibre product `PolarizedCurves`
lives in. -/
def costructuredArrowUliftHoms :
    StacksRepresentableCFG.EquivalenceOver (CostructuredArrow.proj G d ⋙ p)
      (CostructuredArrow.proj ((ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ G) d ⋙
        (ULiftHom.down : ULiftHom.{w} 𝒜 ⥤ 𝒜) ⋙ p) where
  hom := costructuredArrowUliftHomsHom G d p
  inv := costructuredArrowUliftHomsInv G d p
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  unit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl
  counit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl

end StacksRepresentableCFG

end
