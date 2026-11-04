module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Morphisms over the slice at an open are morphisms on the open subscheme

For a scheme `T` and a Zariski open `W` of `T`, the restriction `M.over W` of an
`AlgebraicGeometry.Scheme.Modules` to the slice of the small Zariski site at `W` is a sheaf of
modules on the *slice site* `Over W`, over the sliced structure sheaf.  Statements proved on a
scheme — the first display of [Stacks, Tag 01YB] above all — are stated with that object, while
the objects a *geometric* construction produces live on the open subscheme `W.toScheme`.

This file identifies the two Hom-sets.  Mathlib has both halves:
`AlgebraicGeometry.Scheme.Modules.overEquiv` is an equivalence of the sheaves of modules on the
slice site with the `AlgebraicGeometry.Scheme.Modules` of the open subscheme, and
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` identifies the composite of restriction to
the slice with that equivalence as the geometric restriction functor along `W.ι`.  What is not
there is the consequence: that morphisms `M|_W ⟶ N|_W` of the sliced modules are exactly
morphisms of the geometric restrictions.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.overHomEquivRestrict`: **morphisms of the restrictions to the
  slice at an open are morphisms of the geometric restrictions to the open subscheme.**

## Main results

* `AlgebraicGeometry.Scheme.Modules.overHomEquivRestrict_map`: on a morphism coming from a
  morphism of modules on the ambient scheme the bijection is the action of
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.

## Implementation notes

The bijection is `CategoryTheory.Equivalence.fullyFaithfulFunctor` of
`AlgebraicGeometry.Scheme.Modules.overEquiv` followed by
`CategoryTheory.Iso.homCongr` on the two components of
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`.  Both steps are formal; the content is
entirely Mathlib's.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `CategoryTheory.SheafOfModules` whose
`CategoryTheory.Category` instance is a structure copy, so the two spellings reach `Category` by
different routes; the statements below are therefore spelled on the `Scheme.Modules` side
throughout, which is the side both [Stacks, Tag 01YB] and the geometric restriction functor use.

No declaration here carries a `stacks` tag: this is plumbing between two spellings of one
restriction, not an assertion of any tag.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

/-- **A conjugated morphism is the one a naturality square names.**  If `a ≫ β.hom = α.hom ≫ d`
then `α.inv ≫ a ≫ β.hom = d`.

This is isolated so that the rewrites are performed on a goal with three morphisms in it: on the
concrete goal of `AlgebraicGeometry.Scheme.Modules.overHomEquivRestrict_map` every rewrite whose
pattern is headed by a composition spends the whole heartbeat budget inside `isDefEq`. -/
theorem inv_comp_comp_hom {C : Type*} [Category C] {A B A' B' : C} (α : A ≅ A') (β : B ≅ B')
    (a : A ⟶ B) (d : A' ⟶ B') (h : a ≫ β.hom = α.hom ≫ d) :
    α.inv ≫ a ≫ β.hom = d := by
  rw [h, α.inv_hom_id_assoc]

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {T : Scheme.{u}} (W : T.Opens)

/-- **Morphisms of the restrictions of two modules to the slice of the small Zariski site at an
open are morphisms of their geometric restrictions to the open subscheme.**

The left-hand side is the Hom-set in which the first display of [Stacks, Tag 01YB] states its
bijection; the right-hand side is the Hom-set of modules on the scheme `W.toScheme`, which is
where a construction performed on an open subscheme lands. -/
noncomputable def overHomEquivRestrict (M N : T.Modules) :
    (M.over W ⟶ N.over W) ≃
      ((restrictFunctor W.ι).obj M ⟶ (restrictFunctor W.ι).obj N) :=
  (overEquiv W).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr ((overFunctorEquiv W).app M) ((overFunctorEquiv W).app N))

/-- **On a morphism restricted from the ambient scheme the bijection is the geometric restriction
functor.**  This pins `AlgebraicGeometry.Scheme.Modules.overHomEquivRestrict` down: without it
the bijection would be an unidentified transport. -/
theorem overHomEquivRestrict_map {M N : T.Modules} (f : M ⟶ N) :
    overHomEquivRestrict W M N (f.over W) = (restrictFunctor W.ι).map f := by
  refine Eq.trans (Iso.homCongr_apply ((overFunctorEquiv W).app M) ((overFunctorEquiv W).app N)
    ((overEquiv W).functor.map (f.over W))) ?_
  exact Stacks.CategoryTheory.inv_comp_comp_hom ((overFunctorEquiv W).app M)
    ((overFunctorEquiv W).app N) ((overEquiv W).functor.map (f.over W))
    ((restrictFunctor W.ι).map f) ((overFunctorEquiv W).hom.naturality f)

end AlgebraicGeometry.Scheme.Modules

end
