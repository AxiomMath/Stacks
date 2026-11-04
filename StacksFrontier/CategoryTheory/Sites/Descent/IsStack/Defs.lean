module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.OfFiber
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 026F for a functor

`CategoryTheory.Functor.IsStack` is the presentation of a stack for a functor `p : 𝒳 ⥤ 𝒮`, which is
what Stacks 04TU quantifies over: `p` is a fibred category, the presheaves `Mor(x, y)` of
Stacks 02ZB are sheaves, and descent along a covering sieve is effective.

Mathlib's `CategoryTheory.Pseudofunctor.IsStack` states the same conditions for a pseudofunctor
`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, where condition (1) is built into the presentation. Mathlib has
no cleaving construction turning a fibred category into a pseudofunctor — only the Grothendieck
construction `CategoryTheory.Pseudofunctor.CoGrothendieck` in the other direction — so
conditions (2) and (3) are built here directly from the chosen pullbacks that condition (1)
provides.

## Main definitions

* `CategoryTheory.Functor.IsStack`, Stacks 026F for a functor.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- The three conditions of Stacks 026F for a functor `p : 𝒳 ⥤ 𝒮`: `p` is a fibred category, the
presheaves `Mor(x, y)` of Stacks 02ZB are sheaves, and descent along a covering sieve is
effective.

Condition (2) refers to the chosen pullbacks that condition (1) provides, which is why its field
reintroduces `isFibered` as an instance. -/
@[stacks_fixed 026F "for a functor, the three conditions being the three fields"]
structure IsStack (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮) : Prop where
  /-- Stacks 026F (1). -/
  isFibered : p.IsFibered
  /-- Stacks 026F (2). -/
  isMorSheaf : haveI : p.IsFibered := isFibered
    ∀ (U : 𝒮) (x y : p.Fiber U), IsMorSheaf p J U x y
  /-- Stacks 026F (3). -/
  hasEffectiveDescent : haveI : p.IsFibered := isFibered
    HasEffectiveDescent p J

end Functor

end CategoryTheory
