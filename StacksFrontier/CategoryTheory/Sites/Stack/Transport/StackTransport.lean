module

public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.EffectiveDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.MorPresheaf

/-!
# The stack condition transports along an equivalence over the base

A category over `𝒞` which is equivalent over `𝒞` to a stack is a stack.

## Main results

* `CategoryTheory.BasedCategory.Equivalence.isStack`: if `𝒳` is a stack and `𝒴` is equivalent to
  `𝒳` over `𝒞`, then `𝒴` is a stack.

## References

* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

namespace BasedCategory.Equivalence

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
  (e : BasedCategory.Equivalence 𝒳 𝒴)

include e

/-- Let `(𝒞, J)` be a site and let `𝒳`, `𝒴` be categories over `𝒞`, possibly in different
universes, which are equivalent as categories over `𝒞`. If `𝒳` is a stack over `𝒞`, then so is
`𝒴`. -/
theorem isStack (J : GrothendieckTopology 𝒞) (h : 𝒳.p.IsStack J) : 𝒴.p.IsStack J :=
  have : 𝒳.p.IsFibered := h.isFibered
  have : 𝒴.p.IsFibered := e.isFibered h.isFibered
  { isFibered := e.isFibered h.isFibered
    isMorSheaf := e.isMorSheaf J h.isMorSheaf
    hasEffectiveDescent := e.hasEffectiveDescent J h.hasEffectiveDescent }

end BasedCategory.Equivalence

end CategoryTheory
