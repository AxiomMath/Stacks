module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Capture
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings

/-!
# Closed immersions into a quasi-compact quasi-separated space as limits

Let `S` be a scheme and let `f : X ⟶ Y` be a closed immersion of algebraic spaces over `S` with
`Y` quasi-compact and quasi-separated. Then `X` is a directed limit `X = lim X_i` whose transition
morphisms are closed immersions and whose morphisms `X_i ⟶ Y` are closed immersions of finite
presentation.

## Main results

* `AlgebraicGeometry.Space.hasClosedSubspaceApproximation_of_isQuasiCompactSpace`: a closed
  subspace of a quasi-compact quasi-separated algebraic space is the directed inverse limit of
  closed subspaces of finite presentation, in the interface
  `AlgebraicGeometry.Space.HasClosedSubspaceApproximation`.
* `AlgebraicGeometry.Space.exists_isLimit_closedSubspaces_of_isClosedImmersion`: the same for a
  closed immersion `f : X ⟶ Y`.

## References

* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- Let `Y` be a quasi-compact and quasi-separated algebraic space over `S` and let `X ⊆ Y` be a
closed subspace. Then there are a directed index with a chosen element and an antitone family of
closed subspaces of `Y` containing `X`, each of finite presentation over `Y`, whose inclusions
exhibit `X` as their inverse limit. -/
theorem hasClosedSubspaceApproximation_of_isQuasiCompactSpace (Y : AlgebraicSpaces B S hS)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (X : ClosedSubspaces B S hS Y.1) :
    HasClosedSubspaceApproximation B S hS Y X := by
  classical
  obtain ⟨V, φ, hVaff, hφs, hφe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.1 Y.2).1 hYqc
  have he := (isEtale_iff_presheaf_of_yoneda B S hS φ).1 hφe
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  set U : SmallEtale B S hS Y.1 := chartOfSurjectiveEtale B S hS Y he
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hVaff
  set K := etaleChartKer B S hS Y X U with hK
  let G := {J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData // J.IsFiniteType ∧ J ≤ K}
  have hT : ∀ g : G, ∃ T : ClosedSubspaces B S hS Y.1, IsFinitePresentation B S hS T.1.ι ∧
      X.1 ≤ T.1 ∧ g.1 ≤ chartKer B S hS Y T φ := fun g ↦
    exists_isFinitePresentation_le_chartKer B S hS hZ Y hYqc hYqs X φ he g.1 g.2.1 g.2.2
  choose T hTfp hXT hgT using hT
  let g₀ : G := ⟨⊥, Stacks.FiniteTypeIdealSheaf.isFiniteType_bot, bot_le⟩
  let stage : Finset G → Subfunctor Y.1 := fun F ↦
    (insert g₀ F).inf' (Finset.insert_nonempty _ _) fun g ↦ (T g).1
  have hstage : ∀ F, IsClosedSubspace B S hS (stage F) ∧
      IsFinitePresentation B S hS (stage F).ι := fun F ↦
    Finset.inf'_induction (Finset.insert_nonempty _ _) (fun g ↦ (T g).1)
      (p := fun Z ↦ IsClosedSubspace B S hS Z ∧ IsFinitePresentation B S hS Z.ι)
      (fun Z₁ h₁ Z₂ h₂ ↦
        have := inf_isClosedSubspace B S hS Y.1 Y.2 ⟨Z₁, h₁.1⟩ ⟨Z₂, h₂.1⟩
        ⟨this, isFinitePresentation_inf B S hS Y.2 Z₁ Z₂ h₁.1 h₂.1 this h₁.2 h₂.2⟩)
      fun g _ ↦ ⟨(T g).2, hTfp g⟩
  let Z : Finset G → ClosedSubspaces B S hS Y.1 := fun F ↦ ⟨stage F, (hstage F).1⟩
  have hanti : ∀ ⦃F F' : Finset G⦄, F ≤ F' → (Z F').1 ≤ (Z F).1 := fun F F' h ↦
    Finset.inf'_mono _ (Finset.insert_subset_insert g₀ h) (Finset.insert_nonempty _ _)
  have hle : ∀ F, X.1 ≤ (Z F).1 := fun F ↦
    Finset.le_inf' (Finset.insert_nonempty _ _) _ fun g _ ↦ hXT g
  have hsup : etaleChartKer B S hS Y X U ≤ ⨆ F, etaleChartKer B S hS Y (Z F) U := by
    rw [← hK, ← Stacks.FiniteTypeIdealSheaf.iSup_isFiniteType_eq K]
    refine iSup_le fun g ↦ le_iSup_of_le {g} ?_
    refine (le_chartKer_iff B S hS Y (Z {g}) φ g.1).2 ?_
    refine le_trans (fun W x hx ↦ ?_) ((le_chartKer_iff B S hS Y (T g) φ g.1).1 (hgT g))
    exact Finset.inf'_le (fun g ↦ (T g).1)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self g)) _ hx
  exact ⟨{ index := Finset G
           point := ∅
           stage := Z
           stage_antitone := hanti
           le_stage := hle
           stage_isFinitePresentation := fun F ↦ (hstage F).2
           isLimit := isLimitClosedSubspaceCone B S hS ∅ (fun F ↦ (Z F).1) hanti X.1 hle
             (iInf_le_of_etaleChartKer_le_iSup_of_chart B S hS Y Z X U hφs hsup) }⟩

/-- Let `S` be a scheme and let `f : X ⟶ Y` be a closed immersion of algebraic spaces over `S`,
with `Y` quasi-compact and quasi-separated. Then `X` is a directed limit `X = lim X_i`: there are a
nonempty directed index set and an inverse system of closed subspaces `X_i ⊆ Y` whose transition
morphisms are closed immersions and whose inclusions `X_i ⟶ Y` are closed immersions of finite
presentation, together with a limiting cone with vertex `X` whose legs `X ⟶ X_i` compose with the
inclusions to `f`. -/
@[stacks 0A0U]
theorem exists_isLimit_closedSubspaces_of_isClosedImmersion (Y : AlgebraicSpaces B S hS)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y.1)
    (hf : IsClosedImmersion B S hS f) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (Z : I → ClosedSubspaces B S hS Y.1) (hZ : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1)
      (hle : ∀ i, Subfunctor.range f ≤ (Z i).1),
      (∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B S hS
        ((closedSubspaceDiagram B S hS (fun i => (Z i).1) hZ).map g)) ∧
      (∀ i, IsClosedImmersion B S hS (Z i).1.ι ∧ IsFinitePresentation B S hS (Z i).1.ι) ∧
      (∀ i, ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ (Subfunctor.range f) hle).extend
        (Subfunctor.toRange f)).π.app (op i) ≫ (Z i).1.ι = f) ∧
      Nonempty (IsLimit ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ (Subfunctor.range f)
        hle).extend (Subfunctor.toRange f))) := by
  have : Mono f := mono_of_isClosedImmersion B S hS f hf
  let C : ClosedSubspaces B S hS Y.1 :=
    ⟨Subfunctor.range f, isClosedSubspace_range_of_isClosedImmersion B S hS f hX hf⟩
  obtain ⟨A⟩ := hasClosedSubspaceApproximation_of_isQuasiCompactSpace B S hS hZ Y hYqc hYqs C
  let := A.indexPreorder
  have := A.indexDirected
  refine ⟨A.index, A.indexPreorder, A.indexDirected, ⟨A.point⟩, A.stage, A.stage_antitone,
    A.le_stage, fun i j g ↦ isClosedImmersion_closedSubspaceDiagram_map B S hS A.stage
      A.stage_antitone g, fun i ↦ ⟨(A.stage i).2.2, A.stage_isFinitePresentation i⟩,
    fun i ↦ ?_, ⟨IsLimit.ofIsoLimit A.isLimit
      (Cone.extendIso (closedSubspaceCone B S hS (fun i ↦ (A.stage i).1) A.stage_antitone C.1
        A.le_stage) (asIso (Subfunctor.toRange f)).symm)⟩⟩
  show (Subfunctor.toRange f ≫ Subfunctor.homOfLe (A.le_stage i)) ≫ (A.stage i).1.ι = f
  rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]

end AlgebraicGeometry.Space

end
