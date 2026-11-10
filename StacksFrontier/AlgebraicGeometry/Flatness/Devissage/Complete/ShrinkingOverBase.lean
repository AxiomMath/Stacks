module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.BaseChangeAt
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.StandardShrinking

/-!
# Shrinking a complete dévissage over a standard open of the base

Restricting a complete dévissage at a point to a standard open neighbourhood of the image of
that point in the base gives a standard shrinking. At every stage the restricted closed
subscheme and smooth scheme are the corresponding base changes.

## Main results

* `AlgebraicGeometry.NonemptyCompleteDevissageAt.exists_standardShrinking_base`: the
  base-induced standard shrinking, together with its stagewise base-change property.

## Implementation notes

The open source is the inverse image of the chosen base open, so the restriction square is
cartesian and the stagewise base change of Stacks 05HK applies verbatim. A base change along
an open immersion whose range is a standard open *is* a standard restriction: the two
conditions on the free-module maps are the same equation, because the comparison morphism of
a standard restriction is the base-change morphism of its commuting square, and the open
subschemes cut out at each stage are the inverse images of the chosen basic open, hence
basic opens themselves.

## References

* [Stacks Project, Tag 05HM](https://stacks.math.columbia.edu/tag/05HM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The range of the first projection of a cartesian square whose right-hand morphism is an
open immersion is the inverse image of its range. -/
lemma opensRange_eq_preimage_of_isPullback {A B C D : Scheme.{u}} {p : A ⟶ B} {q' : A ⟶ C}
    {q : B ⟶ D} {j : C ⟶ D} (hsq : IsPullback p q' q j) [IsOpenImmersion j]
    [IsOpenImmersion p] : p.opensRange = q ⁻¹ᵁ j.opensRange := by
  apply TopologicalSpace.Opens.ext
  change Set.range (p : A → B) = (q : B → D) ⁻¹' Set.range (j : C → D)
  calc
    Set.range (p : A → B) = Set.range (hsq.isoPullback.hom ≫ Limits.pullback.fst q j) := by
      rw [hsq.isoPullback_hom_fst]
    _ = Set.range (Limits.pullback.fst q j) := by
      change Set.range ((Limits.pullback.fst q j) ∘ hsq.isoPullback.hom) = _
      rw [Set.range_comp, Set.range_eq_univ.mpr hsq.isoPullback.hom.surjective, Set.image_univ]
    _ = (q : B → D) ⁻¹' Set.range (j : C → D) := Scheme.Pullback.range_fst q j

/-- The base of a complete dévissage is affine: every stage of the chain says so. -/
lemma isAffine_of_devissageChain {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
    {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType}
    (C : DevissageChain s X f F hl hq ht) : IsAffine S := by
  cases C with
  | last stage _ => exact stage.oneStep.affine_S
  | more stage _ _ _ _ => exact stage.oneStep.affine_S

section Stage

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {F : X.Modules} {F' : X'.Modules}
  {s : S} {s' : S'}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
  [LocallyOfFiniteType f'] [F'.IsQuasicoherent] [F'.IsFiniteType]

/-- A stage obtained by base change along an open immersion whose range is a standard open is
a standard restriction: the opens cut out at each stage are the inverse images of the chosen
basic open, and the two conditions on the free-module maps are the same equation. -/
def stageIsStandardRestriction_of_baseChange {jS : S' ⟶ S} [IsOpenImmersion jS] (a : Γ(S, ⊤))
    (hopen : jS.opensRange = S.basicOpen a) {jX : X' ⟶ X} [IsOpenImmersion jX]
    {D : DevissageStage f F s} {D' : DevissageStage f' F' s'}
    (hbc : StageIsBaseChange jS jX D D') : StageIsStandardRestriction jS jX D D' := by
  have hOpenY : IsOpenImmersion hbc.pY :=
    MorphismProperty.of_isPullback hbc.y_square.flip inferInstance
  have hOpenZ : IsOpenImmersion hbc.pZ :=
    MorphismProperty.of_isPullback hbc.x_square.flip inferInstance
  have hrangeY : hbc.pY.opensRange = D.oneStep.Y.basicOpen (D.oneStep.g.appTop a) := by
    rw [opensRange_eq_preimage_of_isPullback hbc.y_square, hopen]
    exact Scheme.preimage_basicOpen_top D.oneStep.g a
  have hrangeZ : hbc.pZ.opensRange =
      D.oneStep.Z.basicOpen ((D.oneStep.π ≫ D.oneStep.g).appTop a) := by
    rw [opensRange_eq_preimage_of_isPullback hbc.z_square,
      opensRange_eq_preimage_of_isPullback hbc.y_square, ← Scheme.Hom.comp_preimage, hopen]
    exact Scheme.preimage_basicOpen_top (D.oneStep.π ≫ D.oneStep.g) a
  exact
    { jZ := hbc.pZ
      jY := hbc.pY
      openImmersion_jZ := hOpenZ
      openImmersion_jY := hOpenY
      closed_section := (D.oneStep.π ≫ D.oneStep.g).appTop a
      smooth_section := D.oneStep.g.appTop a
      closed_standard := hrangeZ
      smooth_standard := hrangeY
      closed_comm := hbc.x_square.w
      finite_comm := hbc.z_square.w
      smooth_comm := hbc.y_square.w
      G_eq := hbc.G_eq
      rank_eq := hbc.rank_eq
      alpha_restrict := hbc.alpha_baseChange }

/-- The distinguished points of a stagewise base change along an open immersion with standard
range are those of the corresponding standard restriction. -/
private def pointedStageIsStandardRestriction_of_baseChange {jS : S' ⟶ S} [IsOpenImmersion jS]
    (a : Γ(S, ⊤)) (hopen : jS.opensRange = S.basicOpen a) {jX : X' ⟶ X} [IsOpenImmersion jX]
    {D : DevissageStage f F s} {D' : DevissageStage f' F' s'} {x : X} {x' : X'}
    {P : PointedDevissageStage f F s x D} {P' : PointedDevissageStage f' F' s' x' D'}
    (hbc : StageIsBaseChange jS jX D D') (hpoint : PointedStageIsBaseChange jS jX P P' hbc) :
    PointedStageIsStandardRestriction jS jX P P'
      (stageIsStandardRestriction_of_baseChange a hopen hbc) :=
  { x_eq := hpoint.x_eq
    y_eq := hpoint.y_eq
    z := hpoint.z
    z' := hpoint.z'
    z_eq := hpoint.z_eq
    z_is_pointed := hpoint.z_is_pointed
    z'_is_pointed := hpoint.z'_is_pointed }

end Stage

section Chain

variable {S S' : Scheme.{u}} {s : S} {s' : S'}

/-- A stagewise base change along an open immersion with standard range is a stagewise
standard restriction. -/
theorem pointedChainIsStandardRestriction_of_baseChange {jS : S' ⟶ S} [IsOpenImmersion jS]
    (a : Γ(S, ⊤)) (hopen : jS.opensRange = S.basicOpen a) {X : Scheme.{u}} {f : X ⟶ S}
    {F : X.Modules} {x : X} {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent}
    {ht : F.IsFiniteType} {chain : DevissageChain s X f F hl hq ht}
    (P : PointedDevissageChain s X f F hl hq ht x chain) :
    ∀ {X' : Scheme.{u}} {f' : X' ⟶ S'} {F' : X'.Modules} {x' : X'}
      {hl' : LocallyOfFiniteType f'} {hq' : F'.IsQuasicoherent} {ht' : F'.IsFiniteType}
      {chain' : DevissageChain s' X' f' F' hl' hq' ht'}
      (P' : PointedDevissageChain s' X' f' F' hl' hq' ht' x' chain') (jX : X' ⟶ X)
      [IsOpenImmersion jX], PointedChainIsBaseChange jS jX P P' →
        PointedChainIsStandardRestriction jS jX P P' := by
  induction P with
  | last x D hz Pstage =>
    intro X' f' F' x' hl' hq' ht' chain' P' jX hjX hbc
    cases hbc with
    | last hbcStage hpoint =>
      exact .last (stageIsStandardRestriction_of_baseChange a hopen hbcStage)
        (pointedStageIsStandardRestriction_of_baseChange a hopen hbcStage hpoint)
  | more x D hqC htC hlY tail Pstage Pt ih =>
    intro X' f' F' x' hl' hq' ht' chain' P' jX hjX hbc
    cases hbc with
    | more hbcStage hpoint htail =>
      have hjY : IsOpenImmersion hbcStage.pY :=
        (stageIsStandardRestriction_of_baseChange a hopen hbcStage).openImmersion_jY
      exact .more (stageIsStandardRestriction_of_baseChange a hopen hbcStage)
        (pointedStageIsStandardRestriction_of_baseChange a hopen hbcStage hpoint)
        (ih _ hbcStage.pY htail)

end Chain

namespace NonemptyCompleteDevissageAt

/-- **Stacks 05HM, base shrinking.** Restricting a complete dévissage at `x` over a standard
open neighbourhood of `f x` gives a standard shrinking whose base and source are that open
and its inverse image, and all of whose stages are the corresponding base changes. -/
@[stacks 05HM "base_shrinking"]
theorem exists_standardShrinking_base {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : NonemptyCompleteDevissageAt f F x)
    (V : S.Opens) (a : Γ(S, ⊤)) (hV : V = S.basicOpen a) (hs : f x ∈ V) :
    ∃ E : NonemptyCompleteDevissageAt.StandardShrinking f F x D,
      E.S' = V ∧ E.X' = f ⁻¹ᵁ V ∧
        (letI := E.locally_finite_type
         letI := E.quasi_coherent
         letI := E.finite_type
         PointedChainIsBaseChange E.S'.ι E.X'.ι D.pointed E.restricted_devissage.pointed) := by
  have hS : IsAffine S := isAffine_of_devissageChain D.toNonemptyCompleteDevissage.chain
  have hVaff : IsAffine V.toScheme := by
    rw [hV]
    infer_instance
  have hU : f ⁻¹ᵁ V = X.basicOpen (f.appTop a) := by
    rw [hV]
    exact Scheme.preimage_basicOpen_top f a
  have hxU : x ∈ f ⁻¹ᵁ V := hs
  have hX : IsPullback (f ⁻¹ᵁ V).ι (f.resLE V (f ⁻¹ᵁ V) le_rfl) f V.ι := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using (isPullback_morphismRestrict f V).flip
  have hlf' : LocallyOfFiniteType (f.resLE V (f ⁻¹ᵁ V) le_rfl) := by
    delta Scheme.Hom.resLE
    infer_instance
  have hqc : (F.restrict (f ⁻¹ᵁ V).ι).IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent
  have hft : (F.restrict (f ⁻¹ᵁ V).ι).IsFiniteType :=
    SheafOfModules.isFiniteType_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).symm
      (SheafOfModules.pullback_isFiniteType (f ⁻¹ᵁ V).ι.toLRSHom.toShHom F)
  have hbase : V.ι (f.resLE V (f ⁻¹ᵁ V) le_rfl ⟨x, hxU⟩) = f x :=
    Scheme.Hom.coe_resLE_apply f le_rfl ⟨x, hxU⟩
  obtain ⟨D', hbc⟩ := exists_completeDevissage_baseChange
    (f' := f.resLE V (f ⁻¹ᵁ V) le_rfl) (F' := F.restrict (f ⁻¹ᵁ V).ι) hbase
    D.toNonemptyCompleteDevissage (f ⁻¹ᵁ V).ι hX
    ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).symm
  obtain ⟨DAt', hDAt'eq, hDAt'⟩ := exists_completeDevissageAt_baseChange
    (f' := f.resLE V (f ⁻¹ᵁ V) le_rfl) (F' := F.restrict (f ⁻¹ᵁ V).ι) hbase inferInstance
    D (f ⁻¹ᵁ V).ι hX ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).symm
    rfl D' hbc
  exact ⟨{ S' := V
           X' := f ⁻¹ᵁ V
           base_section := a
           source_section := f.appTop a
           base_standard := hV
           source_standard := hU
           mem_base := hs
           mem_source := hxU
           source_over_base := le_rfl
           restricted_morphism := f.resLE V (f ⁻¹ᵁ V) le_rfl
           restricted_morphism_eq := rfl
           locally_finite_type := hlf'
           quasi_coherent := hqc
           finite_type := hft
           restricted_devissage := DAt'
           restricted_stages := pointedChainIsStandardRestriction_of_baseChange a
             (by rw [Scheme.Opens.opensRange_ι, hV]) D.pointed DAt'.pointed (f ⁻¹ᵁ V).ι
             hDAt' },
    rfl, rfl, hDAt'⟩

end NonemptyCompleteDevissageAt

end AlgebraicGeometry

end
