module

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
public import Mathlib.Algebra.Group.End

public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoCategory
import StacksCore.Tactic.StacksAttribute

/-!
# The 2-category of stacks in groupoids over a site

Let `(𝒞, J)` be a site. The *2-category of stacks in groupoids over `𝒞`* has as objects the
stacks in groupoids `p : 𝒮 ⥤ 𝒞`, as 1-morphisms the functors `G : 𝒮 ⥤ 𝒮'` with `p' ∘ G = p`,
and as 2-morphisms the morphisms of functors `t` with `p'(t_x) = 𝟙 (p x)` for every object `x`.

## Main definitions

* `CategoryTheory.StackInGroupoids`, an object of the 2-category: a category over `𝒞` whose
  structure functor is a stack in groupoids.
* `CategoryTheory.StackInGroupoids.bicategory`, the 2-category itself.
* `CategoryTheory.StackInGroupoids.homEquivBasedFunctor` and
  `CategoryTheory.StackInGroupoids.twoHomEquivBasedNatTrans`, identifying its 1-morphisms and
  2-morphisms with the ones the source prescribes.

## Main results

* `CategoryTheory.Functor.IsFibredOneMorphism.of_isFiberedInGroupoids`, the parenthetical of
  Stacks 02ZK (2): a functor over `𝒞` into a category fibred in groupoids over `𝒞` automatically
  preserves strongly cartesian morphisms.
* `CategoryTheory.StackInGroupoids.isFibredOneMorphism`, the same statement read off a
  1-morphism of the 2-category below, which is what makes it a sub-2-category of the 2-category
  of stacks (Stacks 02ZG).
* `CategoryTheory.StackInGroupoids.ofBasedStack`, the implication (3) ⟹ (1) of Stacks 02ZJ read on
  the 2-categories: an object of the 2-category of stacks over `𝒞` whose structure functor is
  fibred in groupoids is an object of the 2-category below.

## Implementation notes

Unlike the 2-category of all stacks (Stacks 02ZG,
`CategoryTheory.BasedStack`), whose 1-morphisms carry the extra condition of preserving strongly
cartesian morphisms, item (2) of Stacks 02ZK imposes no condition on a 1-morphism beyond being a
functor over `𝒞`: in a category fibred in groupoids every morphism is strongly cartesian, so the
condition holds automatically. The 2-category is therefore the *full* sub-2-category of the
2-category `BasedCategory 𝒞` of categories over `𝒞` spanned by the stacks in groupoids, and is
built with Mathlib's `CategoryTheory.Bicategory.InducedBicategory`, exactly as
`CategoryTheory.StackInSetoids` is for Stacks 0433.

The parenthetical is not left as a remark: `IsFibredOneMorphism.of_isFiberedInGroupoids` proves
it, so the claim that this is a sub-2-category of the 02ZG one is checkable rather than asserted.
Only the *target* need be fibred in groupoids, which is why that is the sole hypothesis.

"Stack in groupoids" is `CategoryTheory.Functor.IsStackInGroupoids`, the rendering of Stacks 02ZI
that spells the descent conditions out for covering families with genuine fibre-product overlaps.
The library's other rendering of a stack, `CategoryTheory.Functor.IsStack` (Stacks 026F), is
related to it in one direction, by `CategoryTheory.Functor.IsStack.isStackInGroupoids`: a stack in
the sense of 026F whose structure functor is fibred in groupoids satisfies the conditions of 02ZI,
with no hypothesis on the base. That gives the inclusion
`CategoryTheory.StackInGroupoids.ofBasedStack` of the fibred-in-groupoids part of
`CategoryTheory.BasedStack` into this 2-category.

An inclusion of this 2-category *into* `CategoryTheory.BasedStack` still cannot be written down,
and not for want of a lemma: the conditions of 02ZI take the fibre products `Uᵢ ×_U Uⱼ` of a
covering family as arguments, so over a base where those fibre products do not exist — which the
Stacks project's notion of a site permits, and which is why `IsStackInGroupoids` assumes no
`Limits.HasPullbacks` — they say nothing about a covering sieve, and the conditions of 026F do not
follow. What *is* proved about the 1-morphisms is that they satisfy the defining condition of a
1-morphism of `BasedStack`, which is the content of item (2).
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

namespace Functor.IsFibredOneMorphism

variable {𝒴 : Type*} [Category 𝒴]

/-- **Stacks 02ZK (2)**, the parenthetical.
A functor `G : 𝒳 ⥤ 𝒴` over `𝒞`, that is with `G ⋙ q = p`, whose *target* `q : 𝒴 ⥤ 𝒞` is fibred
in groupoids is automatically a 1-morphism of fibred categories over `𝒞`: since every morphism of
a category fibred in groupoids is strongly cartesian over its image, `G.map φ` is strongly
cartesian as soon as it lies over `f`, which it does because `G` is over `𝒞`.

Fibredness of the source is not needed, and not assumed. -/
@[sga "4 XVIII 1.4.6" "more general"]
lemma of_isFiberedInGroupoids {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {G : 𝒳 ⥤ 𝒴}
    (hq : q.IsFiberedInGroupoids) (hG : G ⋙ q = p) : Functor.IsFibredOneMorphism p q G where
  comp_eq := hG
  map_isStronglyCartesian := by
    intro _ _ f _ _ φ hφ
    have : p.IsHomLift f φ := hφ.toIsHomLift
    have : q.IsHomLift f (G.map φ) := Functor.isHomLift_map_of_comp_eq hG f φ
    exact hq.isStronglyCartesian_homLift f (G.map φ)

end Functor.IsFibredOneMorphism

/-- **Stacks 02ZK (1)**.
An object of the 2-category of stacks in groupoids over the site `(𝒞, J)`: a category over `𝒞`
whose structure functor is a stack in groupoids. -/
@[stacks_fixed 02ZK "(1)"]
structure StackInGroupoids (𝒞 : Type u₁) [Category.{v₁} 𝒞] (J : GrothendieckTopology 𝒞) where
  /-- The underlying category over `𝒞`. -/
  toBasedCategory : BasedCategory.{v₂, u₂} 𝒞
  /-- Its structure functor is a stack in groupoids over `(𝒞, J)`. -/
  isStackInGroupoids : Functor.IsStackInGroupoids.{w} toBasedCategory.p J

variable {J : GrothendieckTopology 𝒞}

/-- **Stacks 02ZK**.
The 2-category of stacks in groupoids over the site `(𝒞, J)`: the sub-2-category of the
2-category of stacks over `𝒞` (Stacks 02ZG) whose objects are the stacks in groupoids. Since
every morphism of a category fibred in groupoids is strongly cartesian, no condition is imposed
on a 1-morphism beyond being a functor over `𝒞` — see
`CategoryTheory.StackInGroupoids.isFibredOneMorphism` — so this is the full sub-2-category of the
2-category `BasedCategory 𝒞` of categories over `𝒞` spanned by the stacks in groupoids. -/
@[stacks 02ZK]
instance StackInGroupoids.bicategory :
    Bicategory (StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒞 J) :=
  Bicategory.InducedBicategory.bicategory (C := BasedCategory.{v₂, u₂} 𝒞)
    (F := fun 𝒳 : StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒞 J ↦ 𝒳.toBasedCategory)

namespace StackInGroupoids

variable (𝒳 𝒴 : StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒞 J)

/-- **Stacks 02ZK (2)**.
The 1-morphisms of the 2-category of stacks in groupoids are the functors over `𝒞`: a
1-morphism `𝒳 ⟶ 𝒴` is the same thing as a `BasedFunctor`, that is a functor `G` with
`p' ∘ G = p`. -/
@[stacks 02ZK "(2)"]
def homEquivBasedFunctor : (𝒳 ⟶ 𝒴) ≃ (𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory) where
  toFun f := f.hom
  invFun G := Bicategory.InducedBicategory.mkHom G
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stacks 02ZK (3)**.
The 2-morphisms of the 2-category of stacks in groupoids are the morphisms of functors whose
components lie over identities: a 2-morphism `F ⟶ G` is the same thing as a `BasedNatTrans`,
that is a morphism of functors `t` with `p'(t_x) = 𝟙 (p x)` for every object `x`. -/
@[stacks 02ZK "(3)"]
def twoHomEquivBasedNatTrans {𝒳 𝒴 : StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒞 J} (F G : 𝒳 ⟶ 𝒴) :
    (F ⟶ G) ≃ BasedNatTrans F.hom G.hom where
  toFun η := η.hom
  invFun t := Bicategory.InducedBicategory.Hom₂.mk t
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every 1-morphism of the 2-category of stacks in groupoids preserves strongly cartesian
morphisms, so it is a 1-morphism of the 2-category of stacks over `𝒞` (Stacks 02ZG, item (2) of
Stacks 4.33.9). This is what makes the 2-category above a sub-2-category of the 2-category of
stacks, as Stacks 02ZK describes it. -/
lemma isFibredOneMorphism (f : 𝒳 ⟶ 𝒴) :
    Functor.IsFibredOneMorphism 𝒳.toBasedCategory.p 𝒴.toBasedCategory.p f.hom.toFunctor :=
  Functor.IsFibredOneMorphism.of_isFiberedInGroupoids
    𝒴.isStackInGroupoids.isFiberedInGroupoids f.hom.w

/-- **The implication (3) ⟹ (1) of Stacks 02ZJ**, read on the 2-categories: an object of the
2-category of stacks over the site `(𝒞, J)` (Stacks 02ZG, `CategoryTheory.BasedStack`) whose
structure functor is fibred in groupoids is an object of the 2-category of stacks in groupoids
(Stacks 02ZK), by `CategoryTheory.Functor.IsStack.isStackInGroupoids`.

The inclusion in the opposite direction is not available; see the implementation notes above. -/
def ofBasedStack (𝒳 : BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J)
    (h : 𝒳.toBasedCategory.p.IsFiberedInGroupoids) :
    StackInGroupoids.{w, v₁, v₂, u₁, u₂} 𝒞 J where
  toBasedCategory := 𝒳.toBasedCategory
  isStackInGroupoids := 𝒳.isStack.isStackInGroupoids h

end StackInGroupoids

end CategoryTheory
