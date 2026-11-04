module

public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.SetoidTransport

/-!
# The stack property transports along an equivalence over the base

Let `(𝒞, J)` be a site and let `𝒳`, `𝒴` be categories over `𝒞` which are equivalent as categories
over `𝒞`, that is `BasedCategory.Equivalence 𝒳 𝒴`. Then `𝒳` is a stack over `𝒞` if and only if `𝒴`
is, and `𝒳` is a stack in setoids over `𝒞` if and only if `𝒴` is. The two categories over `𝒞` may
live in different object and morphism universes.

## Main results

* `CategoryTheory.BasedCategory.isStack_iff_of_equivalence`: `𝒳` is a stack if and only if `𝒴` is.
* `CategoryTheory.BasedCategory.isStackInSetoids_iff_of_equivalence`: `𝒳` is a stack in setoids if
  and only if `𝒴` is.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : BasedCategory.{v₂, u₂} 𝒞}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒞}

/-- Let `(𝒞, J)` be a site and let `𝒳`, `𝒴` be categories over `𝒞`. If `𝒳` and `𝒴` are equivalent
as categories over `𝒞`, then `𝒳` is a stack over `𝒞` if and only if `𝒴` is. -/
@[stacks 042W]
theorem BasedCategory.isStack_iff_of_equivalence
    (e : BasedCategory.Equivalence 𝒳 𝒴) (J : GrothendieckTopology 𝒞) :
    𝒳.p.IsStack J ↔ 𝒴.p.IsStack J :=
  ⟨e.isStack J, e.symm.isStack J⟩

/-- Let `(𝒞, J)` be a site and let `𝒳`, `𝒴` be categories over `𝒞`. If `𝒳` and `𝒴` are equivalent
as categories over `𝒞`, then `𝒳` is a stack in setoids over `𝒞` if and only if `𝒴` is. -/
@[stacks 0431]
theorem BasedCategory.isStackInSetoids_iff_of_equivalence
    (e : BasedCategory.Equivalence 𝒳 𝒴) (J : GrothendieckTopology 𝒞) :
    𝒳.p.IsStackInSetoids J ↔ 𝒴.p.IsStackInSetoids J :=
  ⟨e.isStackInSetoids J, e.symm.isStackInSetoids J⟩

end CategoryTheory
