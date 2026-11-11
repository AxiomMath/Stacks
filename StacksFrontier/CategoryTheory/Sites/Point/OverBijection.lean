module

public import Mathlib.CategoryTheory.Sites.Point.Over

/-! # Points of a localized site above a given point: the subfunctors `v_x`

Let `(C, J)` be a site, let `p` be a point of `C` with fibre functor `u = p.fiber`, and let `U` be
an object of `C`.  Stacks 04H2 attaches to every `x ∈ u(U)` a point `q_x` of the localized site
`C/U` lying above `p`, whose fibre functor is
```
  v_x : (φ : V ⟶ U) ↦ {y ∈ u(V) | u(φ)(y) = x} ;
```
this is Mathlib's `CategoryTheory.GrothendieckTopology.Point.over`, built from the subfunctor
`FunctorToTypes.fromOverSubfunctor u x` of `Over.forget U ⋙ u`.

This file records the correspondence `x ↦ v_x` on the level of subfunctors of
`Over.forget U ⋙ u`: the subfunctors of the form `v_x` are characterised by the two conditions
`FunctorToTypes.IsFromOver` (the shape of the fibre functor of a point over `p` in Stacks' proof
of 04H3), and `x ↦ v_x` is a bijection onto them.  Stacks 04H3 itself, the one-to-one
correspondence between `u(U)` and the points of `C/U` lying over `p`, is
`CategoryTheory.GrothendieckTopology.Point.OverPoint.fiberEquivOverPoint` in
`StacksFrontier/CategoryTheory/Sites/Point/OverPoint.lean`.

## Main results

* `CategoryTheory.FunctorToTypes.fromOverSubfunctor_obj`: the sections of `v_x`.
* `CategoryTheory.FunctorToTypes.IsFromOver`: the two conditions on a subfunctor of
  `Over.forget X ⋙ F` satisfied by the subfunctors `v_x`.
* `CategoryTheory.FunctorToTypes.fromOverSubfunctorEquiv`: `x ↦ v_x` is a bijection onto the
  subfunctors satisfying `IsFromOver`.
* `CategoryTheory.GrothendieckTopology.Point.over_fiber_eq_toFunctor`: the fibre functor of the
  point `q_x = Φ.over x` of `C/U` is the functor underlying the subfunctor `v_x`.
-/

@[expose] public section

namespace CategoryTheory.FunctorToTypes

universe w v u
variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) (X : C)

/-- The conditions on a subfunctor `S` of `Over.forget X ⋙ F` which, in Stacks' proof of 04H3,
the fibre functor of a point of `C/X` lying over the point of `C` with fibre functor `F`
satisfies:

1. `S.obj (X/X)` is a singleton, `X/X` being the final object of `C/X`; and
2. for every `W = (φ : V ⟶ X)` the square
```
  S.obj W  ---> F.obj V
     |             | F.map φ
  S.obj (X/X) ---> F.obj X
```
is cartesian, i.e. `S.obj W` is the preimage of `S.obj (X/X)` under `F.map φ`. -/
def IsFromOver (S : Subfunctor (Over.forget X ⋙ F)) : Prop :=
  (∃ x : F.obj X, S.obj (Over.mk (𝟙 X)) = {x}) ∧
    ∀ W : Over X, S.obj W = F.map W.hom ⁻¹' S.obj (Over.mk (𝟙 X))

/-- The sections of `v_x = FunctorToTypes.fromOverSubfunctor F x` over an object `W = (φ : V ⟶ X)`
of `C/X` are the elements of `F.obj V` lying over `x`. -/
lemma fromOverSubfunctor_obj (x : F.obj X) (W : Over X) :
    (fromOverSubfunctor F x).obj W = F.map W.hom ⁻¹' ({x} : Set (F.obj X)) :=
  Set.ext fun y => (mem_fromOverSubfunctor_iff F x y).trans (by simp)

/-- The sections of `v_x` over the final object `X/X` of `C/X` form the singleton `{x}`: this is
the "`v(U/U)` is a singleton, with image `x` in `u(U)`" step of Stacks 04H3. -/
lemma fromOverSubfunctor_obj_id (x : F.obj X) :
    (fromOverSubfunctor F x).obj (Over.mk (𝟙 X)) = {x} := by
  rw [fromOverSubfunctor_obj]
  ext y
  simp

/-- The subfunctor `v_x = FunctorToTypes.fromOverSubfunctor F x` satisfies the two conditions of
`IsFromOver`. -/
lemma isFromOver_fromOverSubfunctor (x : F.obj X) : IsFromOver F X (fromOverSubfunctor F x) :=
  ⟨⟨x, fromOverSubfunctor_obj_id F X x⟩, fun W => by
    rw [fromOverSubfunctor_obj_id F X x, fromOverSubfunctor_obj]⟩

/-- Distinct elements `x` of `u(U)` give distinct subfunctors `v_x`, because `x` is recovered
from `v_x` as the unique section over the final object `U/U`. -/
lemma fromOverSubfunctor_injective :
    Function.Injective (fun x : F.obj X => fromOverSubfunctor F x) := fun x x' h => by
  have h' : ({x} : Set (F.obj X)) = {x'} := by
    rw [← fromOverSubfunctor_obj_id F X x, ← fromOverSubfunctor_obj_id F X x']
    exact congrArg (fun S : Subfunctor (Over.forget X ⋙ F) => S.obj (Over.mk (𝟙 X))) h
  exact Set.singleton_eq_singleton_iff.1 h'

/-- A subfunctor of `Over.forget U ⋙ u` whose sections over the final object `U/U` form a
singleton `{x}` and whose squares over `U/U` are cartesian is `v_x`.  This is the subfunctor
form of the last paragraph of Stacks' proof of 04H3: "the top horizontal map gives a bijection
`v(V/U) → {y ∈ u(V) | y ↦ x}`". -/
lemma exists_eq_fromOverSubfunctor {S : Subfunctor (Over.forget X ⋙ F)} (hS : IsFromOver F X S) :
    ∃ x : F.obj X, S = fromOverSubfunctor F x := by
  obtain ⟨⟨x, hx⟩, hcart⟩ := hS
  refine ⟨x, Subfunctor.ext (funext fun W => ?_)⟩
  rw [hcart W, hx, fromOverSubfunctor_obj]

/-- The construction of Stacks 04H2 on subfunctors: `x ↦ v_x` is a one to one correspondence
```
  u(U) ≃ {S : Subfunctor (Over.forget U ⋙ u) // IsFromOver u U S} ,   x ↦ v_x ,
```
between the elements of `u(U)` and the subfunctors `S` of `Over.forget U ⋙ u` satisfying the two
conditions of `IsFromOver`.  The correspondence with the points of `C/U` lying over `p`
(Stacks 04H3) is `GrothendieckTopology.Point.OverPoint.fiberEquivOverPoint`. -/
noncomputable def fromOverSubfunctorEquiv :
    F.obj X ≃ { S : Subfunctor (Over.forget X ⋙ F) // IsFromOver F X S } :=
  Equiv.ofBijective (fun x => ⟨fromOverSubfunctor F x, isFromOver_fromOverSubfunctor F X x⟩)
    ⟨fun _ _ h => fromOverSubfunctor_injective F X (Subtype.ext_iff.1 h), fun S => by
      obtain ⟨x, hx⟩ := exists_eq_fromOverSubfunctor F X S.2
      exact ⟨x, Subtype.ext hx.symm⟩⟩

end CategoryTheory.FunctorToTypes

namespace CategoryTheory.GrothendieckTopology.Point

universe w v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  (Φ : Point.{w} J) {X : C} (x : Φ.fiber.obj X)

/-- The fibre functor of the point `q_x = Φ.over x` of the localized site `C/X` (Stacks 04H2) is
the functor underlying the subfunctor `v_x` of `Over.forget X ⋙ Φ.fiber`.

That `q_x` lies over `Φ` is `Point.sheafFiberOverIso`, the second half of Stacks 04H2. -/
lemma over_fiber_eq_toFunctor :
    (Φ.over x).fiber = (FunctorToTypes.fromOverSubfunctor Φ.fiber x).toFunctor :=
  rfl

end CategoryTheory.GrothendieckTopology.Point
