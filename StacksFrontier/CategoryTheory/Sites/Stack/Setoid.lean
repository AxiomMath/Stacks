module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Defs
import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.CategoryTheory.FiberedInGroupoids
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.Algebra.Group.End

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks in setoids

A *stack in setoids* over a site `(𝒞, J)` is a stack over `𝒞` all of whose fibre categories are
setoids, that is groupoids with at most one morphism between any two objects; a *stack in sets*,
also called a *stack in discrete categories*, is a stack over `𝒞` all of whose fibre categories
are discrete. The *2-category of stacks in setoids* is the full sub-2-category of the 2-category
of categories over `𝒞` spanned by the stacks in setoids: its 1-morphisms are the functors `G`
with `p' ∘ G = p` and its 2-morphisms the morphisms of functors `t` with `p'(t_x) = 𝟙 (p x)`.

## Main definitions

* `CategoryTheory.Functor.IsStackInSetoids`, `CategoryTheory.Functor.IsStackInSets`
* `CategoryTheory.StackInSetoids` and its `Bicategory` instance

## Implementation notes

"Stack over the site `(𝒞, J)`" is `CategoryTheory.Functor.IsStack`, the rendering of Stacks 026F
as a condition on the structure functor `p : 𝒮 ⥤ 𝒞` of a category over `𝒞`. Mathlib's
`CategoryTheory.Pseudofunctor.IsStack` carries the same tag 026F but states the condition for a
pseudofunctor `LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat`; the pinned Mathlib has no bridge between the two
presentations, and the 1-morphisms and 2-morphisms of the 2-category below, like the inertia,
are given in the fibred presentation, so that is the presentation used here.

There is a second rendering of a stack in the library,
`CategoryTheory.Functor.IsStackInGroupoids`, which spells the descent conditions out for
covering families with genuine fibre-product overlaps rather than through `Functor.IsStack`.
The two are not related by a lemma, so "all of whose fibre categories are groupoids" is written
out below rather than referred to that definition.

The 2-category is `CategoryTheory.Bicategory.InducedBicategory`, Mathlib's full sub-bicategory
construction, applied to the bicategory `BasedCategory 𝒞` of categories over `𝒞`, whose
1-morphisms are the `BasedFunctor`s and whose 2-morphisms are the `BasedNatTrans`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **Stacks 042Z**.
A *stack in setoids* over the site `(𝒞, J)`: a stack over `𝒞` all of whose fibre categories are
setoids, that is groupoids in which there is at most one morphism between any two objects. -/
@[stacks_fixed 042Z "(1)"]
structure Functor.IsStackInSetoids (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) : Prop where
  /-- `p` is a stack over the site `(𝒞, J)`. -/
  isStack : p.IsStack J
  /-- Every fibre category of `p` is a groupoid. -/
  fiber_isGroupoid (U : 𝒞) : IsGroupoid (p.Fiber U)
  /-- Every fibre category of `p` is thin: it has at most one morphism between any two
  objects. -/
  fiber_isThin (U : 𝒞) : Quiver.IsThin (p.Fiber U)

/-- **Stacks 042Z**.
A *stack in sets*, also called a *stack in discrete categories*, over the site `(𝒞, J)`: a stack
over `𝒞` all of whose fibre categories are discrete. -/
@[stacks_fixed 042Z "(2)"]
structure Functor.IsStackInSets (p : 𝒮 ⥤ 𝒞) (J : GrothendieckTopology 𝒞) : Prop where
  /-- `p` is a stack over the site `(𝒞, J)`. -/
  isStack : p.IsStack J
  /-- Every fibre category of `p` is discrete. -/
  fiber_isDiscrete (U : 𝒞) : IsDiscrete (p.Fiber U)

namespace Functor

variable {p : 𝒮 ⥤ 𝒞} {J : GrothendieckTopology 𝒞}

/-- A stack in setoids is a category fibred in groupoids: it is a fibred category with groupoid
fibres. Together with thinness of the fibres this is the canonical spelling of "fibred in
setoids". -/
lemma IsStackInSetoids.isFiberedInGroupoids (h : p.IsStackInSetoids J) :
    p.IsFiberedInGroupoids :=
  IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid.mpr
    ⟨h.isStack.isFibered, h.fiber_isGroupoid⟩

/-- A stack in sets is a stack in setoids: a discrete category is a thin groupoid. -/
lemma IsStackInSets.isStackInSetoids (h : p.IsStackInSets J) : p.IsStackInSetoids J where
  isStack := h.isStack
  fiber_isGroupoid U := have := h.fiber_isDiscrete U; {}
  fiber_isThin U := have := h.fiber_isDiscrete U; fun _ _ ↦ inferInstance

end Functor

/-- **Stacks 0433**.
An object of the 2-category of stacks in setoids over the site `(𝒞, J)`: a category over `𝒞`
whose structure functor is a stack in setoids. -/
@[stacks_fixed 0433]
structure StackInSetoids (𝒞 : Type u₁) [Category.{v₁} 𝒞] (J : GrothendieckTopology 𝒞) where
  /-- The underlying category over `𝒞`. -/
  toBasedCategory : BasedCategory.{v₂, u₂} 𝒞
  /-- Its structure functor is a stack in setoids. -/
  isStackInSetoids : toBasedCategory.p.IsStackInSetoids J

variable {J : GrothendieckTopology 𝒞}

/-- **Stacks 0433**.
The 2-category of stacks in setoids over the site `(𝒞, J)`: the full sub-2-category of the
2-category `BasedCategory 𝒞` of categories over `𝒞` spanned by the stacks in setoids. A
1-morphism `𝒳 ⟶ 𝒴` is a functor `G` over `𝒞`, that is with `p' ∘ G = p`, and a 2-morphism
`F ⟶ G` is a morphism of functors `t` with `p'(t_x) = 𝟙 (p x)` for every object `x`. -/
@[stacks 0433]
instance StackInSetoids.bicategory : Bicategory (StackInSetoids.{v₁, v₂, u₁, u₂} 𝒞 J) :=
  Bicategory.InducedBicategory.bicategory (C := BasedCategory.{v₂, u₂} 𝒞)
    (F := fun 𝒳 : StackInSetoids.{v₁, v₂, u₁, u₂} 𝒞 J ↦ 𝒳.toBasedCategory)

end CategoryTheory
