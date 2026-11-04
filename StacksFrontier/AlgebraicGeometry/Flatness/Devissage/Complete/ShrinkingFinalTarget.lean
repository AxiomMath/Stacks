module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.StageRestriction

/-!
# Prescribing the final target of a standard shrinking

A complete dévissage of `F/X/S` at `x` ends in a smooth scheme `Y_n` carrying a distinguished
point `y_n`. Given a principal open neighbourhood `W` of `y_n`, there is a standard shrinking of
the whole dévissage whose last smooth open is exactly `W` cut down to the new base.

## Main definitions

* `AlgebraicGeometry.finalTargetScheme` and `AlgebraicGeometry.finalTargetPoint`: the smooth
  scheme of the last stage of a pointed dévissage chain, and its distinguished point.
* `AlgebraicGeometry.FinalTargetIsBaseRestriction`: the assertion that the last smooth open of a
  standard restriction of a chain is a prescribed open cut down to the new base.
* `AlgebraicGeometry.ShrinkingPlan`: a choice of four principal opens at every stage of a chain,
  each stage's smooth open being the next stage's source open, and the last one being the
  prescribed open cut down to the base.

## Main results

* `AlgebraicGeometry.exists_shrinkingPlan`: a plan with a prescribed principal open at the last
  stage exists.
* `AlgebraicGeometry.exists_standardShrinking_finalTarget`: a standard shrinking with a
  prescribed final smooth open exists.

## Implementation notes

The construction is in two passes, and the reason is that the base shrinks as one walks *up* the
chain. The first pass, `AlgebraicGeometry.exists_shrinkingPlan`, descends to the last stage,
chooses the four opens there from the prescribed `W`, and then works back towards the first
stage: each earlier stage has to be shrunk so that its smooth open lies inside the source open
already chosen for the next one, and that shrinks the base again, so every plan already built
below has to be cut down to the new base. Cutting a plan down is cheap because a plan records
only opens and the global functions cutting them out.

The second pass, `AlgebraicGeometry.realizes_shrinkingPlan`, turns a plan into an actual chain of
stages over the base the plan ended with, by applying
`AlgebraicGeometry.exists_stageIsStandardRestriction_of_shrinkingOpens` at every stage and
feeding the comparison of the cokernels into the next one. The module of the restricted chain is
therefore not the restriction of the original module but any module isomorphic to it, which is
what the statement quantifies over.

## References

* [Stacks Project, Tag 05HM](https://stacks.math.columbia.edu/tag/05HM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The last stage of a chain -/

/-- The smooth scheme of the last stage of a pointed dévissage chain. -/
def finalTargetScheme {S X : Scheme.{u}} {s : S} {f : X ⟶ S} {F : X.Modules}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} {x : X}
    {chain : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x chain) : Scheme.{u} :=
  match P with
  | .last _ stage _ _ => stage.oneStep.Y
  | .more _ _ _ _ _ _ _ tail => finalTargetScheme tail

/-- The distinguished point of the smooth scheme of the last stage of a pointed dévissage
chain. -/
def finalTargetPoint {S X : Scheme.{u}} {s : S} {f : X ⟶ S} {F : X.Modules}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} {x : X}
    {chain : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x chain) : finalTargetScheme P :=
  match P with
  | .last _ _ _ pointed => pointed.y
  | .more _ _ _ _ _ _ _ tail => finalTargetPoint tail

/-- The last smooth open of a stagewise standard restriction of a chain is the prescribed open
`W` cut down to the inverse image of the new base: at the last stage the range of the open
immersion of smooth schemes is `W ⊓ g_n ⁻¹ᵁ V`, and at an earlier stage the assertion is the one
for the rest of the chain. -/
inductive FinalTargetIsBaseRestriction {S S' : Scheme.{u}} {s : S} {s' : S'} (jS : S' ⟶ S)
    (V : S.Opens) :
    {X : Scheme.{u}} → {f : X ⟶ S} → {F : X.Modules} → {hl : LocallyOfFiniteType f} →
      {hq : F.IsQuasicoherent} → {ht : F.IsFiniteType} →
      {X' : Scheme.{u}} → {f' : X' ⟶ S'} → {F' : X'.Modules} →
      {hl' : LocallyOfFiniteType f'} → {hq' : F'.IsQuasicoherent} → {ht' : F'.IsFiniteType} →
      {jX : X' ⟶ X} → {x : X} → {x' : X'} →
      {chain : DevissageChain s X f F hl hq ht} →
      {chain' : DevissageChain s' X' f' F' hl' hq' ht'} →
      (P : PointedDevissageChain s X f F hl hq ht x chain) →
      (P' : PointedDevissageChain s' X' f' F' hl' hq' ht' x' chain') →
      PointedChainIsStandardRestriction jS jX P P' → (W : (finalTargetScheme P).Opens) →
      Prop where
  /-- At the last stage the range of the open immersion of smooth schemes is `W ⊓ g ⁻¹ᵁ V`. -/
  | last {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {X' : Scheme.{u}} {f' : X' ⟶ S'}
      {F' : X'.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
      [ht : F.IsFiniteType] [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent]
      [ht' : F'.IsFiniteType] {jX : X' ⟶ X} {x : X} {x' : X'}
      {D : @DevissageStage X S f F s hl hq ht}
      {D' : @DevissageStage X' S' f' F' s' hl' hq' ht'}
      {hz : IsZero D.coker} {hz' : IsZero D'.coker}
      {P : @PointedDevissageStage X S f F s x hl hq ht D}
      {P' : @PointedDevissageStage X' S' f' F' s' x' hl' hq' ht' D'}
      (hstage : StageIsStandardRestriction jS jX D D')
      (hpoint : PointedStageIsStandardRestriction jS jX P P' hstage) (W : D.oneStep.Y.Opens)
      (hW : letI := hstage.openImmersion_jY
        hstage.jY.opensRange = W ⊓ (D.oneStep.g ⁻¹ᵁ V)) :
      FinalTargetIsBaseRestriction jS V (.last x D hz P) (.last x' D' hz' P')
        (.last hstage hpoint) W
  /-- At an earlier stage the assertion is the one for the rest of the chain. -/
  | more {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {X' : Scheme.{u}} {f' : X' ⟶ S'}
      {F' : X'.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
      [ht : F.IsFiniteType] [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent]
      [ht' : F'.IsFiniteType] {jX : X' ⟶ X} {x : X} {x' : X'}
      {D : @DevissageStage X S f F s hl hq ht}
      {D' : @DevissageStage X' S' f' F' s' hl' hq' ht'}
      {hqC : D.coker.IsQuasicoherent} {htC : D.coker.IsFiniteType}
      {hlY : LocallyOfFiniteType D.oneStep.g} {hqC' : D'.coker.IsQuasicoherent}
      {htC' : D'.coker.IsFiniteType} {hlY' : LocallyOfFiniteType D'.oneStep.g}
      {tail : DevissageChain s D.oneStep.Y D.oneStep.g D.coker hlY hqC htC}
      {tail' : DevissageChain s' D'.oneStep.Y D'.oneStep.g D'.coker hlY' hqC' htC'}
      {P : @PointedDevissageStage X S f F s x hl hq ht D}
      {P' : @PointedDevissageStage X' S' f' F' s' x' hl' hq' ht' D'}
      {Pt : PointedDevissageChain s D.oneStep.Y D.oneStep.g D.coker hlY hqC htC P.y tail}
      {Pt' : PointedDevissageChain s' D'.oneStep.Y D'.oneStep.g D'.coker hlY' hqC' htC'
        P'.y tail'}
      (hstage : StageIsStandardRestriction jS jX D D')
      (hpoint : PointedStageIsStandardRestriction jS jX P P' hstage)
      (htail : PointedChainIsStandardRestriction jS hstage.jY Pt Pt')
      (W : (finalTargetScheme Pt).Opens)
      (hW : FinalTargetIsBaseRestriction jS V Pt Pt' htail W) :
      FinalTargetIsBaseRestriction jS V (.more x D hqC htC hlY tail P Pt)
        (.more x' D' hqC' htC' hlY' tail' P' Pt') (.more hstage hpoint htail) W

/-! ### Plans -/

/-- A choice of four principal opens at every stage of a pointed dévissage chain: all the stages
are shrunk over the same base `S'`, the smooth open of each stage is the source open of the
next, and the smooth open of the last stage is the prescribed open `W` cut down to the inverse
image of `S'`. -/
def ShrinkingPlan {S X : Scheme.{u}} {s : S} {f : X ⟶ S} {F : X.Modules}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} {x : X}
    {chain : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x chain) (S' : S.Opens) (X' : X.Opens)
    (W : (finalTargetScheme P).Opens) : Type u :=
  match P with
  | .last x D _ p =>
      { A : D.oneStep.ShrinkingOpens x p.y S' X' // A.Y' = W ⊓ D.oneStep.g ⁻¹ᵁ S' }
  | .more x D _ _ _ _ p tail =>
      (A : D.oneStep.ShrinkingOpens x p.y S' X') × ShrinkingPlan tail S' A.Y' W

/-- The distinguished point of a pointed stage lies over the image of the source point. -/
lemma pointedStage_map_y {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : DevissageStage f F (f x)) (P : PointedDevissageStage f F (f x) x D) :
    D.oneStep.g P.y = f x := by
  cases D with
  | mk D r α η hη hα =>
    cases P with
    | mk A hA y hy =>
      cases hA
      cases hy
      exact A.g_y

/-- A principal open neighbourhood of the distinguished point of a pointed stage is the smooth
open of a choice of four opens, cut down to the base. -/
private lemma exists_shrinkingOpens_of_pointedStage {X S : Scheme.{u}} {f : X ⟶ S}
    {F : X.Modules} {x : X} [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : DevissageStage f F (f x)) (P : PointedDevissageStage f F (f x) x D)
    (W : D.oneStep.Y.Opens) (a : Γ(D.oneStep.Y, ⊤)) (hW : W = D.oneStep.Y.basicOpen a)
    (hy : P.y ∈ W) :
    ∃ (S' : S.Opens) (X' : X.Opens) (B : D.oneStep.ShrinkingOpens x P.y S' X'),
      B.Y' = W ⊓ D.oneStep.g ⁻¹ᵁ S' := by
  cases D with
  | mk D r α η hη hα =>
    cases P with
    | mk A hA y hy' =>
      cases hA
      cases hy'
      exact exists_shrinkingOpens_smooth f F x A W a hW hy

/-- The base and source opens of the first stage of a plan are principal and contain the two
points, and the source open lies over the base open. -/
lemma ShrinkingPlan.exists_sections {S X : Scheme.{u}} {s : S} {f : X ⟶ S} {F : X.Modules}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} {x : X}
    {chain : DevissageChain s X f F hl hq ht}
    {P : PointedDevissageChain s X f F hl hq ht x chain} {S' : S.Opens} {X' : X.Opens}
    {W : (finalTargetScheme P).Opens} (A : ShrinkingPlan P S' X' W) :
    ∃ a : Γ(S, ⊤), ∃ b : Γ(X, ⊤), S' = S.basicOpen a ∧ X' = X.basicOpen b ∧ f x ∈ S' ∧
      x ∈ X' ∧ X' ≤ f ⁻¹ᵁ S' := by
  cases P with
  | last x D hz p =>
    exact ⟨A.val.base_section, A.val.source_section, A.val.base_standard, A.val.source_standard,
      A.val.mem_base, A.val.mem_source, A.val.source_over_base⟩
  | more x D hqC htC hlY tail p pt =>
    exact ⟨A.1.base_section, A.1.source_section, A.1.base_standard, A.1.source_standard,
      A.1.mem_base, A.1.mem_source, A.1.source_over_base⟩

/-- Cutting a plan down to a smaller principal open of the base. -/
def ShrinkingPlan.restrict {S X : Scheme.{u}} {s : S} {f : X ⟶ S} {F : X.Modules}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} {x : X}
    {chain : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x chain) {S' : S.Opens} {X' : X.Opens}
    {W : (finalTargetScheme P).Opens} (A : ShrinkingPlan P S' X' W) (hfx : f x = s)
    (S'' : S.Opens) (a : Γ(S, ⊤)) (hS'' : S'' = S.basicOpen a) (hsub : S'' ≤ S')
    (hs'' : s ∈ S'') : ShrinkingPlan P S'' (X' ⊓ f ⁻¹ᵁ S'') W := by
  induction P generalizing S' with
  | @last X f F hl hq ht x D hzero p =>
    subst s
    obtain ⟨A, hA⟩ := A
    refine ⟨A.restrict S'' a hS'' hsub hs'' (pointedStage_map_y D p), ?_⟩
    change A.Y' ⊓ D.oneStep.g ⁻¹ᵁ S'' = W ⊓ D.oneStep.g ⁻¹ᵁ S''
    rw [hA]
    exact (inf_assoc _ _ _).trans
      (congrArg (W ⊓ ·) (inf_eq_right.mpr fun _ h => hsub h))
  | @more X f F hl hq ht x D hqC htC hlY tail p pt ih =>
    subst s
    obtain ⟨A, At⟩ := A
    exact ⟨A.restrict S'' a hS'' hsub hs'' (pointedStage_map_y D p),
      ih At (pointedStage_map_y D p) hsub⟩

/-- **Stacks 05HM (2), first pass.** A prescribed principal open neighbourhood of the
distinguished point of the last smooth scheme occurs as the last smooth open of a plan. -/
lemma exists_shrinkingPlan {S X : Scheme.{u}} {s : S} {f : X ⟶ S} {F : X.Modules}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} {x : X}
    {chain : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x chain) (hfx : f x = s)
    (W : (finalTargetScheme P).Opens) (a : Γ(finalTargetScheme P, ⊤))
    (hW : W = (finalTargetScheme P).basicOpen a) (hy : finalTargetPoint P ∈ W) :
    ∃ S' : S.Opens, ∃ X' : X.Opens, Nonempty (ShrinkingPlan P S' X' W) := by
  induction P with
  | @last X f F hl hq ht x D hzero p =>
    subst s
    obtain ⟨S', X', B, hB⟩ := exists_shrinkingOpens_of_pointedStage D p W a hW hy
    exact ⟨S', X', ⟨⟨B, hB⟩⟩⟩
  | @more X f F hl hq ht x D hqC htC hlY tail p pt ih =>
    subst s
    obtain ⟨S₀, X₀, ⟨At⟩⟩ := ih (pointedStage_map_y D p) W a hW hy
    obtain ⟨b, c, hb, hc, hs, hx, hXS⟩ := At.exists_sections
    obtain ⟨S', X', B, hB⟩ := exists_shrinkingOpens_of_pointedStage D p X₀ c hc hx
    have hsub : S' ≤ S₀ := by
      intro t ht
      obtain ⟨q, hq', hqt⟩ := B.smooth_surjOn t ht
      have hqX : q ∈ X₀ := (show q ∈ X₀ ⊓ _ from hB ▸ hq').1
      have hqS : D.oneStep.g q ∈ S₀ := hXS hqX
      rwa [hqt] at hqS
    have Bt := ShrinkingPlan.restrict pt At (pointedStage_map_y D p) S' B.base_section
      B.base_standard hsub B.mem_base
    rw [← hB] at Bt
    exact ⟨S', X', ⟨⟨B, Bt⟩⟩⟩

/-- **Stacks 05HM (2), second pass.** A plan is realised by an actual stagewise standard
restriction of the chain, whose last smooth open is the prescribed one. -/
lemma realizes_shrinkingPlan {S X : Scheme.{u}} {s : S} {f : X ⟶ S} {F : X.Modules}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} {x : X}
    {chain : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x chain) {S' : S.Opens} {X' : X.Opens}
    {W : (finalTargetScheme P).Opens} (A : ShrinkingPlan P S' X' W) (hfx : f x = s)
    (hs : s ∈ S') (hx : x ∈ X') (hXS : X' ≤ f ⁻¹ᵁ S') (M : X'.toScheme.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (eM : M ≅ F.restrict X'.ι) :
    letI := locallyOfFiniteType_resLE f S' X' hXS
    ∃ chain' : DevissageChain (⟨s, hs⟩ : S'.toScheme) X'.toScheme (f.resLE S' X' hXS) M
        inferInstance inferInstance inferInstance,
      ∃ P' : PointedDevissageChain (⟨s, hs⟩ : S'.toScheme) X'.toScheme (f.resLE S' X' hXS) M
          inferInstance inferInstance inferInstance ⟨x, hx⟩ chain',
        ∃ h : PointedChainIsStandardRestriction S'.ι X'.ι P P',
          FinalTargetIsBaseRestriction S'.ι S' P P' h W := by
  induction P generalizing S' with
  | @last X f F hl hq ht x D hzero p =>
    subst s
    have := locallyOfFiniteType_resLE f S' X' hXS
    obtain ⟨A, hA⟩ := A
    obtain ⟨D', p', R, hp, hcart, hY, hjY, hg, hy⟩ :=
      exists_stageIsStandardRestriction_of_shrinkingOpens D p A M eM
    have hz' := isZero_coker_of_stageIsStandardRestriction R hcart hzero
    refine ⟨.last D' hz', .last _ D' hz' p', .last R hp,
      FinalTargetIsBaseRestriction.last R hp W ?_⟩
    have := R.openImmersion_jY
    exact (opensRange_eq_of_heq_ι A.Y' R.jY hY hjY).trans hA
  | @more X f F hl hq ht x D hqC htC hlY tail p pt ih =>
    subst s
    have := locallyOfFiniteType_resLE f S' X' hXS
    obtain ⟨A, At⟩ := A
    obtain ⟨D', p', R, hp, hcart, hY, hjY, hg, hy⟩ :=
      exists_stageIsStandardRestriction_of_shrinkingOpens D p A M eM
    rcases D' with ⟨⟨Z, Y, i, π, g, G, hqG, htG, over, affX, affS, affZ, affY, closed, fp,
      emod, finite, smooth, irred, dim⟩, r, α, η, hη, hα⟩
    dsimp only at hY
    subst hY
    have hg' := eq_of_heq hg
    dsimp only at hg'
    subst hg'
    have hjY' := eq_of_heq hjY
    have hy' := eq_of_heq hy
    let D'' : DevissageStage (f.resLE S' X' hXS) M (⟨f x, hs⟩ : S'.toScheme) :=
      ⟨⟨Z, A.Y'.toScheme, i, π, D.oneStep.g.resLE S' A.Y' A.smooth_over_base, G, hqG, htG,
        over, affX, affS, affZ, affY, closed, fp, emod, finite, smooth, irred, dim⟩,
        r, α, η, hη, hα⟩
    have eC : D''.coker ≅ D.coker.restrict A.Y'.ι := by
      refine (cokernelIsoOfStageIsStandardRestriction R hcart).symm ≪≫ ?_
      rw [hjY']
      exact ((Scheme.Modules.restrictFunctorIsoPullback A.Y'.ι).app D.coker).symm
    have hqC' : D''.coker.IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_of_iso eC.symm
        (inferInstanceAs ((D.coker.restrict A.Y'.ι).IsQuasicoherent))
    have htC' : D''.coker.IsFiniteType :=
      have := htC
      SheafOfModules.isFiniteType_of_iso eC.symm
        (Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict A.Y'.ι D.coker)
    have hlY' : LocallyOfFiniteType D''.oneStep.g :=
      locallyOfFiniteType_resLE D.oneStep.g S' A.Y' A.smooth_over_base
    obtain ⟨tail', pt', hrest, hfin⟩ := ih At (pointedStage_map_y D p) hs A.mem_smooth
      A.smooth_over_base D''.coker eC
    have htrans : ∃ pt'' : PointedDevissageChain (⟨f x, hs⟩ : S'.toScheme) D''.oneStep.Y
        D''.oneStep.g D''.coker hlY' hqC' htC' p'.y tail',
        ∃ h : PointedChainIsStandardRestriction S'.ι R.jY pt pt'',
          FinalTargetIsBaseRestriction S'.ι S' pt pt'' h W := by
      let Q (j : D''.oneStep.Y ⟶ D.oneStep.Y) (q : D''.oneStep.Y) : Prop :=
        ∃ pt'' : PointedDevissageChain (⟨f x, hs⟩ : S'.toScheme) D''.oneStep.Y D''.oneStep.g
          D''.coker hlY' hqC' htC' q tail',
          ∃ h : PointedChainIsStandardRestriction S'.ι j pt pt'',
            FinalTargetIsBaseRestriction S'.ι S' pt pt'' h W
      have hQ : Q A.Y'.ι ⟨p.y, A.mem_smooth⟩ := ⟨pt', hrest, hfin⟩
      exact Eq.mpr (congrArg₂ Q hjY' hy') hQ
    obtain ⟨pt'', hrest'', hfin''⟩ := htrans
    exact ⟨.more D'' hqC' htC' hlY' tail',
      .more _ D'' hqC' htC' hlY' tail' p' pt'', .more R hp hrest'',
      .more R hp hrest'' W hfin''⟩

/-- **Stacks 05HM, final target shrinking.** Let `W` be a principal open neighbourhood of the
distinguished point of the smooth scheme of the last stage of a complete dévissage of `F/X/S` at
`x`. Then there is a standard shrinking of the dévissage whose last smooth open is `W` cut down
to the inverse image of the new base. -/
@[stacks 05HM "final_target_shrinking"]
theorem exists_standardShrinking_finalTarget {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : NonemptyCompleteDevissageAt f F x) (W : (finalTargetScheme D.pointed).Opens)
    (a : Γ(finalTargetScheme D.pointed, ⊤))
    (hW : W = (finalTargetScheme D.pointed).basicOpen a)
    (hy : finalTargetPoint D.pointed ∈ W) :
    ∃ E : NonemptyCompleteDevissageAt.StandardShrinking f F x D,
      letI := E.locally_finite_type
      letI := E.quasi_coherent
      letI := E.finite_type
      FinalTargetIsBaseRestriction E.S'.ι E.S' D.pointed E.restricted_devissage.pointed
        E.restricted_stages W := by
  obtain ⟨S', X', ⟨A⟩⟩ := exists_shrinkingPlan D.pointed rfl W a hW hy
  obtain ⟨b, c, hb, hc, hs, hx, hXS⟩ := A.exists_sections
  have hlf := locallyOfFiniteType_resLE f S' X' hXS
  have hqc : (F.restrict X'.ι).IsQuasicoherent := inferInstance
  have hft : (F.restrict X'.ι).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict X'.ι F
  have hpt : f.resLE S' X' hXS ⟨x, hx⟩ = (⟨f x, hs⟩ : S'.toScheme) :=
    Subtype.ext (Scheme.Hom.coe_resLE_apply f hXS ⟨x, hx⟩)
  obtain ⟨chain', P', h, hfin⟩ :
      ∃ chain' : DevissageChain (f.resLE S' X' hXS ⟨x, hx⟩) X'.toScheme (f.resLE S' X' hXS)
        (F.restrict X'.ι) hlf hqc hft,
      ∃ P' : PointedDevissageChain (f.resLE S' X' hXS ⟨x, hx⟩) X'.toScheme
        (f.resLE S' X' hXS) (F.restrict X'.ι) hlf hqc hft ⟨x, hx⟩ chain',
        ∃ h : PointedChainIsStandardRestriction S'.ι X'.ι D.pointed P',
          FinalTargetIsBaseRestriction S'.ι S' D.pointed P' h W := by
    rw [hpt]
    exact realizes_shrinkingPlan D.pointed A rfl hs hx hXS (F.restrict X'.ι) (Iso.refl _)
  exact ⟨{ S' := S'
           X' := X'
           base_section := b
           source_section := c
           base_standard := hb
           source_standard := hc
           mem_base := hs
           mem_source := hx
           source_over_base := hXS
           restricted_morphism := f.resLE S' X' hXS
           restricted_morphism_eq := rfl
           locally_finite_type := hlf
           quasi_coherent := hqc
           finite_type := hft
           restricted_devissage := ⟨⟨chain'⟩, P'⟩
           restricted_stages := h }, hfin⟩

end AlgebraicGeometry

end
