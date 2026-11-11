module

public import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # The stalk functor of a functor with cofiltered neighbourhoods is left exact

## Main results

* `preservesFiniteLimits_sheafToPresheaf_comp_stalk`: for a site `(C, J)` and any functor
  `u : C ⥤ Type u` whose category of neighbourhoods `u.Elements` is cofiltered, the stalk functor
  `Sh(C) ⥤ Set`, `𝓕 ↦ colim_{(U, x) ∈ u.Elementsᵒᵖ} 𝓕(U)`, preserves finite limits (Stacks 0F4E).
  No covering condition on `u` is assumed: `u` need not be a point of the site.
* `preservesFiniteLimits_sheafFiber`: the special case of a point `Φ : J.Point`, whose stalk
  functor is `Φ.sheafFiber`.

Tags covered: 0F4E.
-/

@[expose] public section

open CategoryTheory

universe u

/-- **Stacks 0F4E.** Let `(C, J)` be a site and `u : C ⥤ Type u` a functor whose category of
neighbourhoods `u.Elements` (pairs `(U, x)` with `x ∈ u(U)`) is cofiltered. Then the stalk functor
`Sh(C) ⥤ Set`, sending a sheaf `𝓕` to `colim_{(U, x) ∈ u.Elementsᵒᵖ} 𝓕(U)` (Stacks 04EH), is left
exact, i.e. it preserves finite limits. Exactly the Stacks hypotheses: `u` is an arbitrary functor
with cofiltered category of neighbourhoods, and no covering condition on `u` is required. -/
@[stacks 0F4E "The stalk functor is written as `sheafToPresheaf` followed by the colimit over the
opposite of the category of neighbourhoods `u.Elements`; `u` is any functor with
`IsCofiltered u.Elements`."]
theorem preservesFiniteLimits_sheafToPresheaf_comp_stalk
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (u : C ⥤ Type u) [IsCofiltered u.Elements] :
    Limits.PreservesFiniteLimits (sheafToPresheaf J (Type u) ⋙
      (Functor.whiskeringLeft _ _ (Type u)).obj (CategoryOfElements.π u).op ⋙ Limits.colim) :=
  inferInstance

/-- For a point `Φ` of the site `(C, J)`, the stalk functor `Φ.sheafFiber : Sh(C) ⥤ Set` preserves
finite limits. This is the special case of Stacks 0F4E
(`preservesFiniteLimits_sheafToPresheaf_comp_stalk`) for functors that are points: a
`GrothendieckTopology.Point` bundles, besides cofilteredness of the category of neighbourhoods,
the covering condition of a point, which the Stacks lemma does not need. -/
theorem preservesFiniteLimits_sheafFiber
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (Φ : J.Point) :
    Limits.PreservesFiniteLimits (Φ.sheafFiber (A := Type u)) :=
  inferInstance
