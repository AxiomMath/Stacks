module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import StacksCore.Tactic.StacksAttribute

/-!
# Actions of group schemes, and free actions

An action of a group scheme on a scheme over the same base is an action of an internal monoid
object in the cartesian monoidal category of schemes over that base, so it satisfies the
associativity and unit diagrams.  Such an action is *free* when the induced action on points
over every base scheme is free, which happens exactly when the morphism
`(g, x) ↦ (g • x, x)` is a monomorphism.

## Main definitions

* `AlgebraicGeometry.IsFreeAction` says that a group object acts freely on an object.

## Main results

* `CategoryTheory.ModObj.mul_smul_self` and `CategoryTheory.ModObj.one_smul_self` are the
  associativity and identity equations for an action.
* `AlgebraicGeometry.isFreeAction_iff_mono_leftSMul` characterizes free actions by the
  monomorphism property of the action–projection morphism.

## Implementation notes

Everything is stated in an arbitrary cartesian monoidal category.  Taking the category to be
schemes over a scheme `S` gives the statements of the source: the tensor product is the fibre
product over `S`, morphisms `T ⟶ G` and `T ⟶ X` are the `T`-points, `ModObj.leftSMul G X` is
the morphism `(g, x) ↦ (g • x, x)` from `G ×_S X` to `X ×_S X`, and Mathlib's `IsCancelSMul`
is the predicate that a group action is free.  `IsFreeAction` is an abbreviation so that
clients can use the existing `IsCancelSMul` API directly.

## References

* [Stacks Project, Tag 03LD](https://stacks.math.columbia.edu/tag/03LD)
* [Stacks Project, Tag 07S1](https://stacks.math.columbia.edu/tag/07S1)
* [Stacks Project, Tag 07S2](https://stacks.math.columbia.edu/tag/07S2)
-/

@[expose] public section

open CategoryTheory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

add_to_stacks 03LD "associativity" CategoryTheory.ModObj.mul_smul_self
add_to_stacks 03LD "identity" CategoryTheory.ModObj.one_smul_self

namespace AlgebraicGeometry

universe u v

/-- A group object acts freely on `X` if its action on `T`-points is free for every object `T`. -/
@[stacks 07S1]
abbrev IsFreeAction {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G X : C) [GrpObj G] [ModObj G X] : Prop :=
  ∀ T : C, IsCancelSMul (T ⟶ G) (T ⟶ X)

/-- A group action is free if and only if `(g, x) ↦ (g • x, x)` is a monomorphism. -/
@[stacks 07S2,
  sga "3 IV 3.2.1" "(i), special case",
  sga "3 V 10.2.1" "more general",
  sga "4 IV 9.8.2" "Remark after d)"]
lemma isFreeAction_iff_mono_leftSMul {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] (G X : C) [GrpObj G] [ModObj G X] :
    IsFreeAction G X ↔ Mono (ModObj.leftSMul G X) := by
  constructor
  · intro h
    refine ⟨fun {T} f g e => ?_⟩
    have hs : f ≫ snd _ _ = g ≫ snd _ _ := by simpa using e =≫ snd X X
    have hfst : f ≫ γ[G, X] = g ≫ γ[G, X] := by simpa using e =≫ fst X X
    refine CartesianMonoidalCategory.hom_ext_iff.2 ⟨?_, hs⟩
    have hfst' : (f ≫ fst G X) • (f ≫ snd G X) = (g ≫ fst G X) • (g ≫ snd G X) := by
      simpa only [Hom.smul_def, lift_comp_fst_snd] using hfst
    exact (h T).right_cancel _ _ _ (by simpa [hs] using hfst')
  · intro hm T
    constructor
    intro m n x e
    have hl : lift m x = lift n x :=
      hm.right_cancellation _ _ (by rw [ModObj.lift_leftSMul, ModObj.lift_leftSMul, e])
    simpa using hl =≫ fst G X

end AlgebraicGeometry

end
