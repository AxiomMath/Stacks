module

public import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # The stalk functor at a point is left exact

## Main results

* `preservesFiniteLimits_sheafFiber`: for a point `Φ` of a site the stalk functor `Sh(C) ⥤ Set`
  preserves finite
  limits (Stacks 0F4E). The cofilteredness of the category of neighbourhoods, which is the
  hypothesis of the Stacks lemma, is part of the data of `GrothendieckTopology.Point`.

Tags covered: 0F4E.
-/

@[expose] public section

open CategoryTheory

universe u

/-- **Stacks 0F4E.** Let `Φ` be a point of the site `(C, J)`, i.e. a functor `u : C ⥤ Type`
together with cofilteredness of its category of neighbourhoods. Then the stalk functor
`Sh(C) ⥤ Set` at `Φ` is left exact, i.e. it preserves finite limits. -/
@[stacks 0F4E]
theorem preservesFiniteLimits_sheafFiber
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (Φ : J.Point) :
    Limits.PreservesFiniteLimits (Φ.sheafFiber (A := Type u)) :=
  inferInstance
