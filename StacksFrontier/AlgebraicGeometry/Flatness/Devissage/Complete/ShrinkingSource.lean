module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.ShrinkingFinalTarget

/-!
# Prescribing the source of a standard shrinking

A complete dévissage of `F/X/S` at `x` can be shrunk so that its source open lies inside any
prescribed open neighbourhood of `x`.

## Main results

* `AlgebraicGeometry.exists_shrinkingPlan_source`: a shrinking plan whose source open lies inside
  a prescribed open neighbourhood of `x` exists.
* `AlgebraicGeometry.NonemptyCompleteDevissageAt.exists_standardShrinking_source`: a standard
  shrinking whose source open lies inside a prescribed open neighbourhood of `x` exists.

## Implementation notes

The plan of a shrinking, `AlgebraicGeometry.ShrinkingPlan`, is the bookkeeping of
`StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.ShrinkingFinalTarget`: a choice of
four principal opens at every stage, each stage's smooth open being the next stage's source
open. Only the first pass has to be redone here, because the condition asked of the plan is a
condition on the *first* stage rather than on the last one; the second pass, which turns a plan
into an actual chain of stages, is `AlgebraicGeometry.realizes_shrinkingPlan` verbatim, and the
open of the last stage that it needs is simply the smooth open the plan already chose there.

The induction walks up the chain in the order the source does. At the first stage,
`AlgebraicGeometry.exists_shrinkingOpens_source` produces, from the prescribed neighbourhood of
`x`, a neighbourhood `V` of the distinguished point of the first smooth scheme that is small
enough for *any* principal open inside it to be the smooth open of a shrinking with source
inside the prescribed one. The rest of the chain is then shrunk, by the inductive hypothesis
applied with `V` as its prescribed neighbourhood, and only afterwards is the first stage shrunk
— to exactly the source open the rest of the chain has settled on. This is the order of the
source's proof of Stacks 05HM (3), with the two applications of Stacks 05HA (3) and (2) to the
first stage fused into one, so that the base is shrunk once rather than twice.

## References

* [Stacks Project, Tag 05HM](https://stacks.math.columbia.edu/tag/05HM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks 05HM (3), first pass.** A prescribed open neighbourhood of `x` contains the source
open of a shrinking plan of a pointed dévissage chain at `x`. -/
lemma exists_shrinkingPlan_source {S X : Scheme.{u}} {s : S} {f : X ⟶ S} {F : X.Modules}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} {x : X}
    {chain : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x chain) (hfx : f x = s) (U : X.Opens)
    (hx : x ∈ U) :
    ∃ (S' : S.Opens) (X' : X.Opens) (W : (finalTargetScheme P).Opens),
      X' ≤ U ∧ Nonempty (ShrinkingPlan P S' X' W) := by
  induction P with
  | @last X f F hl hq ht x D hzero p =>
    subst s
    cases D with
    | mk D rank α η hη hα =>
      cases p with
      | mk A hA y hyA =>
        cases hA
        cases hyA
        obtain ⟨V, d, hVd, hyV, hall⟩ := exists_shrinkingOpens_source f F x A U hx
        obtain ⟨S', X', B, hB, hXU⟩ := hall V d hVd hyV le_rfl
        exact ⟨S', X', B.Y', hXU, ⟨⟨B, (inf_eq_left.mpr B.smooth_over_base).symm⟩⟩⟩
  | @more X f F hl hq ht x D hqC htC hlY tail p pt ih =>
    subst s
    cases D with
    | mk D rank α η hη hα =>
      cases p with
      | mk A hA y hyA =>
        cases hA
        cases hyA
        obtain ⟨V, d, hVd, hyV, hall⟩ := exists_shrinkingOpens_source f F x A U hx
        obtain ⟨S₂, X₂, W, hX₂V, ⟨At⟩⟩ := ih A.g_y V hyV
        obtain ⟨b, c, hb, hc, hs₂, hy₂, hXS⟩ := At.exists_sections
        obtain ⟨S₃, X₃, B, hB, hXU⟩ := hall X₂ c hc hy₂ hX₂V
        have hsub : S₃ ≤ S₂ := by
          intro t ht
          obtain ⟨q, hq', hqt⟩ := B.smooth_surjOn t ht
          have hqX : q ∈ X₂ := (show q ∈ X₂ ⊓ _ from hB ▸ hq').1
          have hqS : A.toOneStepDevissage.g q ∈ S₂ := hXS hqX
          rwa [hqt] at hqS
        have Bt := ShrinkingPlan.restrict pt At A.g_y S₃ B.base_section B.base_standard hsub
          B.mem_base
        rw [← hB] at Bt
        exact ⟨S₃, X₃, W, hXU, ⟨⟨B, Bt⟩⟩⟩

namespace NonemptyCompleteDevissageAt

/-- **Stacks 05HM, source shrinking.** A complete dévissage of `F/X/S` at `x` admits a standard
shrinking whose source open lies inside any prescribed open neighbourhood of `x`. -/
@[stacks 05HM "source_shrinking"]
theorem exists_standardShrinking_source {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : NonemptyCompleteDevissageAt f F x) (U : X.Opens) (hx : x ∈ U) :
    ∃ E : NonemptyCompleteDevissageAt.StandardShrinking f F x D, E.X' ≤ U := by
  obtain ⟨S', X', W, hXU, ⟨A⟩⟩ := exists_shrinkingPlan_source D.pointed rfl U hx
  obtain ⟨b, c, hb, hc, hs, hx', hXS⟩ := A.exists_sections
  have hlf := locallyOfFiniteType_resLE f S' X' hXS
  have hqc : (F.restrict X'.ι).IsQuasicoherent := inferInstance
  have hft : (F.restrict X'.ι).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict X'.ι F
  have hpt : f.resLE S' X' hXS ⟨x, hx'⟩ = (⟨f x, hs⟩ : S'.toScheme) :=
    Subtype.ext (Scheme.Hom.coe_resLE_apply f hXS ⟨x, hx'⟩)
  obtain ⟨chain', P', h, -⟩ :
      ∃ chain' : DevissageChain (f.resLE S' X' hXS ⟨x, hx'⟩) X'.toScheme (f.resLE S' X' hXS)
        (F.restrict X'.ι) hlf hqc hft,
      ∃ P' : PointedDevissageChain (f.resLE S' X' hXS ⟨x, hx'⟩) X'.toScheme
        (f.resLE S' X' hXS) (F.restrict X'.ι) hlf hqc hft ⟨x, hx'⟩ chain',
        ∃ h : PointedChainIsStandardRestriction S'.ι X'.ι D.pointed P',
          FinalTargetIsBaseRestriction S'.ι S' D.pointed P' h W := by
    rw [hpt]
    exact realizes_shrinkingPlan D.pointed A rfl hs hx' hXS (F.restrict X'.ι) (Iso.refl _)
  exact ⟨{ S' := S'
           X' := X'
           base_section := b
           source_section := c
           base_standard := hb
           source_standard := hc
           mem_base := hs
           mem_source := hx'
           source_over_base := hXS
           restricted_morphism := f.resLE S' X' hXS
           restricted_morphism_eq := rfl
           locally_finite_type := hlf
           quasi_coherent := hqc
           finite_type := hft
           restricted_devissage := ⟨⟨chain'⟩, P'⟩
           restricted_stages := h }, hXU⟩

end NonemptyCompleteDevissageAt

end AlgebraicGeometry

end
