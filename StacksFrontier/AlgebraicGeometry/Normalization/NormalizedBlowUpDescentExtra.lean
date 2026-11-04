module

public import StacksFrontier.AlgebraicGeometry.Normalization.NormalizedBlowUpDescent
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing

/-!
# Descending a sequence of normalized blowups from the completion, unconditionally

`AlgebraicGeometry.exists_normalizedBlowUpSeqDescent_of_adicCompletion` carries the Nagata
property of the completion `A^` as a hypothesis. Here it is discharged: `A^` is Noetherian, local
and complete for its own maximal ideal, so [Stacks, Tag 032W] applies to it.

## Main results

* `AlgebraicGeometry.exists_normalizedBlowUpSeqDescent_of_adicCompletion_unconditional`: the
  descent statement with no Nagata hypothesis, Tag 0BGA.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0BGA.** Let `A` be a Noetherian local domain whose completion `A^` is
normal. Every finite sequence of normalized blowups `Yₙ → ⋯ → Y₁ → Spec A^` is the base change
to `A^` of a finite sequence of normalized blowups `Xₙ → ⋯ → X₁ → Spec A`, stage by stage, and
the latter sequence is proper over `Spec A`.

That `A^` is a Nagata ring is not a hypothesis here: `A^` is Noetherian, local, and complete for
its own maximal ideal, so [Stacks, Tag 032W] applies to it. -/
@[stacks 0BGA]
public theorem exists_normalizedBlowUpSeqDescent_of_adicCompletion_unconditional
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hnormal : IsNormalRing (AdicCompletion (maximalIdeal A) A))
    {Y : Scheme.{u}} {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))}
    (hseq : NormalizedBlowUpSeq (Spec (.of (AdicCompletion (maximalIdeal A) A))) Y g) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (p : Y ⟶ X),
      NormalizedBlowUpSeqDescent A X f Y g p ∧ IsProper f :=
  exists_normalizedBlowUpSeqDescent_of_adicCompletion A hnormal
    IsNagataRing.of_isPrecomplete_maximalIdeal hseq


end AlgebraicGeometry

end
