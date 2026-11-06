module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.Logic.Small.Basic
public import StacksFrontier.AlgebraicGeometry.Size.SmallerUniverse
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Subfunctors of a presheaf on an essentially small category form a small type

A subfunctor of `F : C ⥤ Type w` is a family of subsets of the `F.obj U`, so `Subfunctor F`
lives in `Type (max u w)` for `C : Type u`. When `C` is essentially small at `w` this is
larger than it needs to be: a subfunctor is determined by its values on a small skeleton,
because the condition defining a subfunctor forces `G.obj U` to be the preimage of `G.obj V`
along any isomorphism `U ≅ V`. So `Subfunctor F` is `w`-small.

The point of this for the big fppf site of a scheme `S` is that a presheaf `X` on
`AlgebraicGeometry.BigFppfOver B S hS` has `Subfunctor X : Type (u + 1)`, while every
limit-of-algebraic-spaces statement in this library — Situation 084R,
`AlgebraicGeometry.Space.LimitSituation`, in particular — indexes its inverse systems by a
`Type u`. A family of closed subspaces of `X` indexed by subfunctors of `X` therefore cannot
be fed to those statements directly. With the smallness proved here it can, after
transporting the index along `equivShrink`.

## Main definitions

No new definitions are introduced.

## Main results

* `CategoryTheory.Subfunctor.obj_eq_preimage_of_iso`: a subfunctor takes, at an object, the
  preimage of its value at any isomorphic object.
* `CategoryTheory.Subfunctor.small`: subfunctors of a presheaf of `w`-types on a category
  essentially small at `w` form a `w`-small type.

That the big fppf site over `S` is itself essentially small, which is what makes the smallness
above applicable to it, is `AlgebraicGeometry.BigFppfOver.essentiallySmall`.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w}

/-- **A subfunctor is determined along isomorphisms.** The value of a subfunctor at `U` is the
preimage, under the bijection `F.map φ.hom`, of its value at `V`, for any isomorphism
`φ : U ≅ V`.

One inclusion is the defining condition of a subfunctor at `φ.hom`; the other is that condition
at `φ.inv`, together with `F.map φ.inv ∘ F.map φ.hom = id`. -/
theorem obj_eq_preimage_of_iso (G : Subfunctor F) {U V : C} (φ : U ≅ V) :
    G.obj U = F.map φ.hom ⁻¹' G.obj V := by
  ext x
  refine ⟨fun hx => G.map φ.hom hx, fun hx => ?_⟩
  have h := G.map φ.inv hx
  rw [Set.mem_preimage] at h
  have hid : F.map φ.inv (F.map φ.hom x) = x := by
    rw [← Functor.map_comp_apply, φ.hom_inv_id, Functor.map_id_apply]
  rwa [hid] at h

/-- **Subfunctors of a presheaf of `w`-types on a category essentially small at `w` form a
`w`-small type.**

Restriction to the objects of the form `(equivSmallModel C).inverse.obj s`, for `s` in the
small model, is injective on subfunctors: every object of `C` is isomorphic to one of those,
and by `CategoryTheory.Subfunctor.obj_eq_preimage_of_iso` a subfunctor's value at an object is
determined by its value at any isomorphic object. The target of that restriction is a function
type from `SmallModel C : Type w` into sets of `w`-types, so it is a `Type w` outright. -/
theorem small [EssentiallySmall.{w} C] (F : C ⥤ Type w) : Small.{w} (Subfunctor F) := by
  classical
  let e := equivSmallModel.{w} C
  have hinj : Function.Injective
      (fun G : Subfunctor F => fun s : SmallModel.{w} C => G.obj (e.inverse.obj s)) := by
    intro G H hGH
    refine Subfunctor.ext (funext fun U => ?_)
    have φ : U ≅ e.inverse.obj (e.functor.obj U) := e.unitIso.app U
    have hUU : G.obj (e.inverse.obj (e.functor.obj U)) =
        H.obj (e.inverse.obj (e.functor.obj U)) := congrFun hGH (e.functor.obj U)
    rw [obj_eq_preimage_of_iso G φ, obj_eq_preimage_of_iso H φ, hUU]
  exact small_of_injective hinj

end CategoryTheory.Subfunctor

end
