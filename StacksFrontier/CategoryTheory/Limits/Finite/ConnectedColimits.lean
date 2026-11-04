module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import StacksFrontier.CategoryTheory.Limits.Finite.Connected

/-!
# Connected finite colimits (Stacks 04AV)

A category `C` has colimits of every finite *connected* shape if and only if it has
coequalizers and pushouts. This is the exact dual of Stacks 04AT, and the Stacks
proof is "dual to the previous lemma"; the formalization follows suit rather than
re-running the construction.

Concretely, the substantive direction applies
`hasLimitsOfShape_isConnected_iff_hasEqualizers_and_hasPullbacks` to `Cᵒᵖ` — where
`HasCoequalizers C` gives `HasEqualizers Cᵒᵖ` and `HasPushouts C` gives
`HasPullbacks Cᵒᵖ` — at the shape `Jᵒᵖ`, which is again finite (`FinCategory Jᵒᵖ`)
and connected (`CategoryTheory.isConnected_op`), and then transports back along
`hasColimitsOfShape_of_hasLimitsOfShape_op`.

Connectedness is essential in the same way as in 04AT: coequalizers and pushouts
never produce an initial object, so the statement is false with the empty shape
admitted. Mathlib's `IsConnected` includes nonemptiness, which is the reading Stacks
intends.

The easy direction specialises at `WalkingParallelPair` (coequalizers) and
`WalkingSpan` (pushouts), both finite and connected.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v u

/-- The substantive direction of Stacks 04AV, in its per-shape form: coequalizers and
pushouts give colimits of every finite connected shape. Obtained from its dual
`hasLimitsOfShape_of_isConnected` (Stacks 04AT) by passing to `Cᵒᵖ` and `Jᵒᵖ`. -/
theorem hasColimitsOfShape_of_isConnected
    (C : Type u) [Category.{v} C] [HasCoequalizers C] [HasPushouts C]
    (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J] :
    HasColimitsOfShape J C := by
  have : HasLimitsOfShape Jᵒᵖ Cᵒᵖ :=
    (hasLimitsOfShape_isConnected_iff_hasEqualizers_and_hasPullbacks Cᵒᵖ).2
      ⟨inferInstance, inferInstance⟩ Jᵒᵖ
  exact hasColimitsOfShape_of_hasLimitsOfShape_op

/-- **Stacks 04AV.** A category `C` admits colimits over every finite connected shape
if and only if it has coequalizers and pushouts. -/
@[stacks 04AV]
theorem hasColimitsOfShape_isConnected_iff_hasCoequalizers_and_hasPushouts
    (C : Type u) [Category.{v} C] :
    (∀ (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J], HasColimitsOfShape J C) ↔
      (HasCoequalizers C ∧ HasPushouts C) := by
  constructor
  · -- `WalkingParallelPair` and `WalkingSpan` are both finite and connected.
    intro h
    exact ⟨h WalkingParallelPair, h WalkingSpan⟩
  · rintro ⟨_, _⟩ J _ _ _
    exact hasColimitsOfShape_of_isConnected C J

end CategoryTheory.Limits
