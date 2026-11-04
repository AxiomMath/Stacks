module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Properties preserved by base change

A property of objects or of morphisms over a varying base is *stable under base change* when it
passes across every pullback square. For schemes over a base `S` the relevant category is
`CategoryTheory.Over S`, and base change along `g : S' ⟶ S` is the pullback functor; but nothing
in the definitions is special to schemes, so they are given for an arbitrary category.

Both definitions are stated in terms of arbitrary pullback squares (`CategoryTheory.IsPullback`)
rather than of a chosen pullback, so they do not presuppose that the category has pullbacks and
specialize to any particular construction of them. For a morphism property this means two
squares, one for the source and one for the target, together with the commutativity that makes
them a square over the base change.

A property that depends only on the underlying morphism, forgetting the map to the base, is the
inverse image along `CategoryTheory.Over.forget`; the instances below transport Mathlib's
base-independent `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` and
`.IsStableUnderBaseChangeAgainst` to that case, and Mathlib's class is also adopted as the
base-independent specialization of part (2).

## Main definitions

* `CategoryTheory.IsStableUnderBaseChange`: stability for a family of object properties on over
  categories.
* `CategoryTheory.MorphismPropertyOverBase`: a property of morphisms over a varying base.
* `CategoryTheory.MorphismPropertyOverBase.IsStableUnderBaseChange`: stability for such a family.
* `CategoryTheory.MorphismPropertyOverBase.IsStableUnderBaseChangeAgainst`: stability restricted
  to base morphisms with a prescribed property, which models preservation under flat, smooth or
  other specified base changes.

## Main results

* `CategoryTheory.IsStableUnderBaseChange.of_isPullback` applies the object-property definition
  to an arbitrary pullback square.
* `CategoryTheory.MorphismPropertyOverBase.IsStableUnderBaseChange.pullbackMap` and
  `.IsStableUnderBaseChangeAgainst.pullbackMap` apply the morphism-property definitions to
  Mathlib's pullback functor, which is their principal interface.

## References

* [Stacks Project, Tag 01JZ](https://stacks.math.columbia.edu/tag/01JZ)
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- A family of properties of objects over a base is stable under base change if
the property passes across every pullback square. -/
@[stacks 01JZ "part (1): properties of objects over a base"]
public class IsStableUnderBaseChange
    (P : (S : C) → ObjectProperty (Over S)) : Prop where
  of_isPullback {S S' : C} {X : Over S} {X' : Over S'}
    {i : X'.left ⟶ X.left} {g : S' ⟶ S}
    (sq : IsPullback i X'.hom X.hom g) (hX : P S X) : P S' X'

/-- A property of morphisms over a varying base. -/
public abbrev MorphismPropertyOverBase :=
  (S : C) → CategoryTheory.MorphismProperty (Over S)

namespace MorphismPropertyOverBase

variable (P : MorphismPropertyOverBase (C := C))

/-- A family of properties of morphisms over a base is stable under arbitrary
base change if it passes across every pair of pullback squares defining the
base change of a morphism. -/
@[stacks 01JZ "part (2): properties of morphisms over a base",
  sga "3 VIB 2.0" "stable under base change",
  ega "I 3.5.1" "more general",
  ega "I 5.5.12",
  sga "3 IV 4.7" "more general",
  sga "3 VIB 10.1"]
public class IsStableUnderBaseChange : Prop where
  of_isPullback {S S' : C} {X Y : Over S} {X' Y' : Over S'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {i : X'.left ⟶ X.left}
    {j : Y'.left ⟶ Y.left} {g : S' ⟶ S}
    (comm : f'.left ≫ j = i ≫ f.left)
    (src : IsPullback i X'.hom X.hom g)
    (tgt : IsPullback j Y'.hom Y.hom g)
    (hf : P S f) : P S' f'

/-- Stability under base change restricted to a specified property of the
morphism between bases. -/
@[ega "I 3.5.1" "more general", ega "I 5.5.12"]
public class IsStableUnderBaseChangeAgainst (Q : CategoryTheory.MorphismProperty C) : Prop where
  of_isPullback {S S' : C} {X Y : Over S} {X' Y' : Over S'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {i : X'.left ⟶ X.left}
    {j : Y'.left ⟶ Y.left} {g : S' ⟶ S}
    (hg : Q g) (comm : f'.left ≫ j = i ≫ f.left)
    (src : IsPullback i X'.hom X.hom g)
    (tgt : IsPullback j Y'.hom Y.hom g)
    (hf : P S f) : P S' f'

/-- Stability under arbitrary base change is stability against every property of the base
morphism. -/
public instance [IsStableUnderBaseChange P] (Q : CategoryTheory.MorphismProperty C) :
    IsStableUnderBaseChangeAgainst P Q where
  of_isPullback _ comm src tgt hf :=
    IsStableUnderBaseChange.of_isPullback comm src tgt hf

namespace IsStableUnderBaseChange

/-- A morphism property stable under arbitrary base change is preserved by the
map of every pullback functor. -/
public theorem pullbackMap [IsStableUnderBaseChange P] {S S' : C} (g : S' ⟶ S)
    [HasPullbacksAlong g] {X Y : Over S} (f : X ⟶ Y) (hf : P S f) :
    P S' ((Over.pullback g).map f) :=
  of_isPullback (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _) hf

end IsStableUnderBaseChange

namespace IsStableUnderBaseChangeAgainst

/-- A morphism property stable under base changes in `Q` is preserved by the
map of a pullback functor whose defining morphism satisfies `Q`. -/
public theorem pullbackMap (Q : CategoryTheory.MorphismProperty C)
    [IsStableUnderBaseChangeAgainst P Q] {S S' : C} (g : S' ⟶ S)
    (hg : Q g) [HasPullbacksAlong g] {X Y : Over S} (f : X ⟶ Y) (hf : P S f) :
    P S' ((Over.pullback g).map f) :=
  of_isPullback hg (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _) hf

end IsStableUnderBaseChangeAgainst

/-- A base-independent morphism property stable under base change in `C`
gives a stable family on the over categories by forgetting the maps to the
base. -/
public instance inverseImage_forget_isStableUnderBaseChange
    (Q : CategoryTheory.MorphismProperty C)
    [Q.IsStableUnderBaseChange] :
    IsStableUnderBaseChange
      (fun S => Q.inverseImage (Over.forget S)) where
  of_isPullback {S} {S'} {X} {Y} {X'} {Y'} {f} {f'} {i} {j} {g}
      comm src tgt hf :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q)
      ((show IsPullback _ (f'.left ≫ Y'.hom) (f.left ≫ Y.hom) _ from
        by simpa only [Over.w] using src).of_bot comm.symm tgt) hf

/-- A base-independent morphism property stable under base changes in `R`
gives a family on the over categories stable under base changes in `R`. -/
public instance inverseImage_forget_isStableUnderBaseChangeAgainst
    (Q R : CategoryTheory.MorphismProperty C)
    [Q.IsStableUnderBaseChangeAgainst R] [R.IsStableUnderBaseChange] :
    IsStableUnderBaseChangeAgainst
      (fun S => Q.inverseImage (Over.forget S)) R where
  of_isPullback {S} {S'} {X} {Y} {X'} {Y'} {f} {f'} {i} {j} {g}
      hg comm src tgt hf :=
    (MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong
      (P := Q) (P' := R) j
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback tgt.flip hg)).of_isPullback
      ((show IsPullback _ (f'.left ≫ Y'.hom) (f.left ≫ Y.hom) _ from
        by simpa only [Over.w] using src).of_bot comm.symm tgt) hf

end MorphismPropertyOverBase

add_to_stacks 01JZ "part (2), base-independent properties"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "3 IV 3.4.1" "(a)" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "3 IV 4.6.3" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "3 IV 4.7" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "3 VIB 10.1" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "3 VIB 2.0" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "3 XXIV 7.1.9" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "4 IV 8.5.4" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "4 IV 9.1.7" "ST1" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "4 VII 5.4" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_sga "4 Vbis 3.3" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_ega "I 3.5.1" CategoryTheory.MorphismProperty.IsStableUnderBaseChange
add_to_ega "I 5.5.12" CategoryTheory.MorphismProperty.IsStableUnderBaseChange

end CategoryTheory
