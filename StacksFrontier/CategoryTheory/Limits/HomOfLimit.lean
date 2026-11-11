module

public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Limits.Opposites
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms into a limit and out of a colimit

Let `M : I ⥤ C` be a diagram. Stacks Remark 002H says:

1. if `c` is a limit cone of `M`, then for every object `W` the cone of sets
   `Hom(W, c.pt) → Hom(W, M i)` is a limit cone, i.e. `Hom(W, lim M) = lim_i Hom(W, M i)`;
2. if `c` is a colimit cocone of `M`, then for every object `W` the cone of sets
   `Hom(c.pt, W) → Hom(M i, W)`, indexed by `Iᵒᵖ`, is a limit cone, i.e.
   `Hom(colim M, W) = lim_{i ∈ Iᵒᵖ} Hom(M i, W)`;

and, by the Yoneda lemma, these formulas determine the limit and the colimit. Mathlib states
both parts through preservation of limits by `coyoneda.obj` and `yoneda.obj` (the
registrations in `StacksCore/CategoryTheory/Limits.lean`); part 2 there is about diagrams valued in
`Cᵒᵖ`. This file states both parts directly for a diagram `M : I ⥤ C`, in every universe of the
shape, and registers Mathlib's converses.

## Main results

* `CategoryTheory.Limits.IsLimit.mapConeCoyoneda`: part 1.
* `CategoryTheory.Limits.IsColimit.mapConeOpYoneda`: part 2.
-/

@[expose] public section

universe w t v u

namespace CategoryTheory.Limits

open Opposite

variable {I : Type w} [Category.{t} I] {C : Type u} [Category.{v} C] {M : I ⥤ C}

/-- If `c` is a limit cone of `M : I ⥤ C`, then for every `W : C` the image of `c` under
`Hom(W, -)` is a limit cone in sets: `Hom(W, lim M) = lim_i Hom(W, M i)`. -/
@[stacks 002H "part 1, for any diagram `M : I ⥤ C` and any limit cone of `M`"]
noncomputable def IsLimit.mapConeCoyoneda {c : Cone M} (hc : IsLimit c) (W : C) :
    IsLimit ((coyoneda.obj (Opposite.op W)).mapCone c) :=
  isLimitOfPreserves _ hc

/-- If `c` is a colimit cocone of `M : I ⥤ C`, then for every `W : C` the image of the opposite
cone `c.op` (over `M.op : Iᵒᵖ ⥤ Cᵒᵖ`) under `Hom(-, W)` is a limit cone in sets:
`Hom(colim M, W) = lim_{i ∈ Iᵒᵖ} Hom(M i, W)`. -/
@[stacks 002H "part 2, for any diagram `M : I ⥤ C` and any colimit cocone; limit over `Iᵒᵖ`"]
noncomputable def IsColimit.mapConeOpYoneda {c : Cocone M} (hc : IsColimit c) (W : C) :
    IsLimit ((yoneda.obj W).mapCone c.op) :=
  isLimitOfPreserves _ hc.op

add_to_stacks 002H "part 1 determines the limit" Cone.isLimitCoyonedaEquiv
add_to_stacks 002H "part 2 determines the colimit" Cocone.isColimitYonedaEquiv

end CategoryTheory.Limits
