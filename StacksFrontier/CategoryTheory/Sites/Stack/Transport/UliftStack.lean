module

public import StacksFrontier.CategoryTheory.FiberedCategory.UliftBasedCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport

/-!
# The universe lift of a stack is a stack

Let `(𝒞, J)` be a site and let `𝒳` be a category over `𝒞`. Its universe lift
`CategoryTheory.BasedCategory.ulift` is equivalent to it in the 2-category of categories over `𝒞`,
so `𝒳.ulift` is a stack over `(𝒞, J)` exactly when `𝒳` is.

## Main definitions

* `CategoryTheory.BasedCategory.uliftEquivalence`: the universe lift as an equivalence in the
  2-category of categories over `𝒞`.

## Main results

* `CategoryTheory.BasedCategory.isStack_ulift`: the universe lift of a stack is a stack.
* `CategoryTheory.BasedCategory.isStack_ulift_iff`: `𝒳` is a stack if and only if its universe
  lift is.
* `CategoryTheory.BasedCategory.isStackInSetoids_ulift_iff`: `𝒳` is a stack in setoids if and
  only if its universe lift is.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
-/

@[expose] public section

namespace CategoryTheory

namespace BasedCategory

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- The universe lift of a category `𝒳` over `𝒞`, as an equivalence from `𝒳` to its lift in
the 2-category of categories over `𝒞`. -/
noncomputable def uliftEquivalence (𝒳 : BasedCategory.{v₂, u₂} 𝒞) :
    BasedCategory.Equivalence 𝒳 (𝒳.ulift : BasedCategory.{max v₂ v₃, max u₂ u₃} 𝒞) :=
  (StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
    (𝒳 := (𝒳.ulift : BasedCategory.{max v₂ v₃, max u₂ u₃} 𝒞)) (𝒴 := 𝒳)
    (𝒳.uliftEquivalenceOver)).symm

/-- The universe lift of a stack over the site `(𝒞, J)` is a stack over `(𝒞, J)`. -/
theorem isStack_ulift (𝒳 : BasedCategory.{v₂, u₂} 𝒞) (J : GrothendieckTopology 𝒞)
    (h : 𝒳.p.IsStack J) :
    (𝒳.ulift : BasedCategory.{max v₂ v₃, max u₂ u₃} 𝒞).p.IsStack J :=
  𝒳.uliftEquivalence.isStack J h

/-- A category over `𝒞` is a stack over `(𝒞, J)` if and only if its universe lift is. -/
theorem isStack_ulift_iff (𝒳 : BasedCategory.{v₂, u₂} 𝒞) (J : GrothendieckTopology 𝒞) :
    𝒳.p.IsStack J ↔ (𝒳.ulift : BasedCategory.{max v₂ v₃, max u₂ u₃} 𝒞).p.IsStack J :=
  isStack_iff_of_equivalence 𝒳.uliftEquivalence J

/-- A category over `𝒞` is a stack in setoids over `(𝒞, J)` if and only if its universe lift
is. -/
theorem isStackInSetoids_ulift_iff (𝒳 : BasedCategory.{v₂, u₂} 𝒞) (J : GrothendieckTopology 𝒞) :
    𝒳.p.IsStackInSetoids J ↔
      (𝒳.ulift : BasedCategory.{max v₂ v₃, max u₂ u₃} 𝒞).p.IsStackInSetoids J :=
  isStackInSetoids_iff_of_equivalence 𝒳.uliftEquivalence J

end BasedCategory

end CategoryTheory

end
