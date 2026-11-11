module

public import StacksFrontier.AlgebraicGeometry.Normalization.NormalizedBlowUpDescent
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing

/-!
# Descending a sequence of normalized blowups from the completion, unconditionally

`AlgebraicGeometry.exists_normalizedBlowUpTowerDescent_of_adicCompletion` and
`AlgebraicGeometry.exists_normalizedBlowUpSeqDescent_of_adicCompletion` carry the Nagata
property of the completion `A^` as a hypothesis. Here it is discharged: `A^` is Noetherian, local
and complete for its own maximal ideal, so [Stacks, Tag 032W] applies to it.

## Main results

* `AlgebraicGeometry.exists_normalizedBlowUpTowerDescent_of_adicCompletion_unconditional`: every
  given sequence of normalized blowups of `Spec A^` descends to `Spec A` stage by stage, with no
  Nagata hypothesis, Tag 0BGA.
* `AlgebraicGeometry.exists_normalizedBlowUpSeqDescent_of_adicCompletion_unconditional`: the
  same for a sequence known only through its top stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Let `A` be a Noetherian local domain whose completion `A^` is normal. For every
`Y ⟶ Spec A^` reached by *some* finite sequence of normalized blowups, there is a sequence of
normalized blowups over `Spec A`, proper over `Spec A`, descending *a* sequence of normalized
blowups with top stage `Y ⟶ Spec A^`, stage by stage.

The hypothesis only records the top stage; the descent of a sequence given in advance, stage by
stage, which is Tag 0BGA, is
`exists_normalizedBlowUpTowerDescent_of_adicCompletion_unconditional`. -/
public theorem exists_normalizedBlowUpSeqDescent_of_adicCompletion_unconditional
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hnormal : IsNormalRing (AdicCompletion (maximalIdeal A) A))
    {Y : Scheme.{u}} {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))}
    (hseq : NormalizedBlowUpSeq (Spec (.of (AdicCompletion (maximalIdeal A) A))) Y g) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (p : Y ⟶ X),
      NormalizedBlowUpSeqDescent A X f Y g p ∧ IsProper f :=
  exists_normalizedBlowUpSeqDescent_of_adicCompletion A hnormal
    IsNagataRing.of_isPrecomplete_maximalIdeal hseq

/-- **Stacks Project, Tag 0BGA.** Let `A` be a Noetherian local domain whose completion `A^` is
normal. Given any sequence of normalized blowups `T : Yₙ → ⋯ → Y₁ → Spec A^` (its stages and the
closed points blown up, as data), there is a sequence of normalized blowups
`Xₙ → ⋯ → X₁ → Spec A`, proper over `Spec A`, whose base change to `A^` recovers `T` stage by
stage: at every step the normalized blowup of `Yᵢ` at the closed point `yᵢ` recorded in `T` is the
base change, along the comparison `Yᵢ ⟶ Xᵢ`, of the normalized blowup of `Xᵢ` at the image of
`yᵢ`, a cartesian square.

That `A^` is a Nagata ring is not a hypothesis here: `A^` is Noetherian, local, and complete for
its own maximal ideal, so [Stacks, Tag 032W] applies to it. -/
@[stacks 0BGA]
public theorem exists_normalizedBlowUpTowerDescent_of_adicCompletion_unconditional
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hnormal : IsNormalRing (AdicCompletion (maximalIdeal A) A))
    {Y : Scheme.{u}} {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))}
    (T : NormalizedBlowUpTower (Spec (.of (AdicCompletion (maximalIdeal A) A))) Y g) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (p : Y ⟶ X),
      NormalizedBlowUpTowerDescent A T X f p ∧ IsProper f :=
  exists_normalizedBlowUpTowerDescent_of_adicCompletion A hnormal
    IsNagataRing.of_isPrecomplete_maximalIdeal T


end AlgebraicGeometry

end
