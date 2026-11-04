module

public import StacksFrontier.CategoryTheory.FiberedInSetoids.Defs
public import StacksFrontier.CategoryTheory.RelativeInertia

/-!
# Fibredness in setoids detected by the inertia category

Stacks 042J: a category fibred in groupoids `p : 𝒮 ⥤ 𝒞` is fibred in setoids if and only if
the canonical 1-morphism `I_𝒮 ⥤ 𝒮` of Stacks 042H is an equivalence. Objects of the inertia
category `I_𝒮 = CategoryTheory.AbsoluteInertia p` are pairs `(x, α)` with `α` an automorphism
of `x` lying over `𝟙 (p x)`, and its projection `π : (x, α) ↦ x` is always faithful and
essentially surjective; it is full exactly when every such `α` is the identity, which is the
fibred-in-setoids condition.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **Stacks 042J.** A category fibred in groupoids `p : 𝒮 ⥤ 𝒞` is fibred in setoids if and
only if the forgetful 1-morphism `π : I_𝒮 ⥤ 𝒮` of the absolute inertia is an equivalence.
Since `π` is always faithful and essentially surjective, the content is that `π` is full
exactly when the fibres of `p` are thin. -/
@[stacks 042J]
theorem isFiberedInSetoids_iff_π_isEquivalence (p : 𝒮 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) :
    p.IsFiberedInSetoids ↔ (RelativeInertia.π p : AbsoluteInertia p ⥤ 𝒮).IsEquivalence where
  mp h := have := RelativeInertia.π_full_of_fiber_isThin p h.fiber_isThin; .mk
  mpr h :=
    { isFiberedInGroupoids := hp
      fiber_isThin := RelativeInertia.fiber_isThin_of_π_full p hp.fiber_isGroupoid h.full }
