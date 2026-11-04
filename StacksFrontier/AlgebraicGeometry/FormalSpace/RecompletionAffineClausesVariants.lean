module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClauses
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionMcQuillan

/-!
# Variants of the results of `StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClauses`

The declarations below extend `StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClauses`
and are kept in a module of their own so that that module stays unchanged. A primed name `X'` is a
variant of the declaration `X` there.

## Main declarations

* `hasSomeSurjectivePresentation_completionAlong'`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Clause (2) of Stacks 0GVV.** Let `S` be a scheme, let `X` be a McQuillan affine formal
algebraic space over `S`, let `i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be
closed. Then the completion `X_{/T}` of `X` along `T` is again McQuillan, that is satisfies
condition (4) of Stacks 0AIC: it is an affine formal algebraic space some presentation of which
by affine thickenings has all its section-ring projections surjective.

Nothing is assumed beyond the tag's own hypotheses. This is
`AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheafULift` in the
source's spelling `X_{/T}` for a closed subset `T` of the points of a reduction; the source's
step — write `X = Spf(A)` and observe that `X_{/T} ⟶ X ⟶ Spec(A)` satisfies condition (2) of
Stacks 0AIC — is
`AlgebraicGeometry.FormalSpace.hasAffineClosedImmersionCriterion_completionSheafULift`, and the
geometric content it rests on is
`AlgebraicGeometry.FormalSpace.completionClosedSubscheme_of_isAffineFormalAlgebraicSpace`: a
closed immersion of an object of the site into `X_{/T}` is a closed immersion into `X`. -/
@[stacks 0GVV "clause (2): if `X` is McQuillan so is `X_{/T}`, with McQuillan read as \
`HasSomeSurjectivePresentation` (condition (4) of Stacks 0AIC, registered for Stacks 0AID at \
StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/Types.lean). Carried hypotheses: `hX` is the \
tag's own McQuillan hypothesis on `X`, `hi` supplies the reduction as data because Stacks \
0AIN is unavailable in this library (the convention of the library's Stacks 0GVT and 0GB8), and \
`hT` is the tag's own closedness of `T` in `|X_red|`. Nothing else: the source's step producing \
condition (2) of Stacks 0AIC for the completion is proved — \
`hasAffineClosedImmersionCriterion_completionSheafULift`, resting on \
`completionClosedSubscheme_of_isAffineFormalAlgebraicSpace`; and the set-theoretic condition of \
Stacks 0AIS on the completion is proved — \
`satisfiesSetTheoreticCondition_completionSheafULift`. The step from condition (2) to the \
conclusion is Stacks 0AIC, (2) ⇒ (5) ⇒ (4)."]
theorem hasSomeSurjectivePresentation_completionAlong' {X Xred : FppfSheaf B S hS}
    (hX : HasSomeSurjectivePresentation B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T) :
    HasSomeSurjectivePresentation B S hS (completionAlong i T) :=
  hasSomeSurjectivePresentation_completionSheafULift B S hS X hX _
    (hi.isClosed_image_pointsMapULift (T := T) hT)

end AlgebraicGeometry.FormalSpace

end
