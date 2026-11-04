module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCover.SectionFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen

/-!
# The induction on the number of local sections in the proof of Stacks 0CQ7

The fourth paragraph of the proof of [Stacks, Tag 0CQ7] removes the condition that the open `V`
lies in every `Wᵢ`: with `Yᵢ` the reduced closed subspace on the complement of `Wᵢ`, the
statement for `(𝒳 → Y, V ∩ W₁ ∩ … ∩ Wₙ)` and for the base changes `(𝒳_{Yᵢ} → Yᵢ, V ∩ Yᵢ)`,
which carry only `n - 1` local sections, gives the statement for `(𝒳 → Y, V)`, because
`V = (V ∩ W₁ ∩ … ∩ Wₙ) ∪ ⋃ᵢ (V ∩ Yᵢ)` on points. Here the base change of `𝒳` is never formed:
the local sections are read over the proper map `Yᵢ ⟶ Y₀ ⟶ Y`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.SectionFamily.reindex`: a subfamily of local sections
  still covering `q₀⁻¹(W)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasSectionCoverOver_of_sectionFamily_of_step`: the
  induction, from the case where `V₀` lies in every open of the family and the union of section
  covers.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

attribute [local instance] AlgebraicGeometry.Space.pointTopology

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- In a quasi-separated space, an open compact set meets finitely many open compact sets in an
open compact set. -/
theorem isCompact_inter_biInter_of_quasiSeparatedSpace {X : Type*} [TopologicalSpace X]
    [QuasiSeparatedSpace X] {ι : Type*} (s : Finset ι) {t : Set X} (ht : _root_.IsOpen t)
    (htc : _root_.IsCompact t) (v : ι → Set X) (hv : ∀ i, _root_.IsOpen (v i))
    (hvc : ∀ i, _root_.IsCompact (v i)) :
    _root_.IsOpen (t ∩ ⋂ i ∈ s, v i) ∧ _root_.IsCompact (t ∩ ⋂ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨ht, htc⟩
  | insert a s _ ih =>
    rw [Finset.set_biInter_insert, Set.inter_comm (v a), ← Set.inter_assoc]
    exact ⟨ih.1.inter (hv a),
      QuasiSeparatedSpace.inter_isCompact _ _ ih.1 ih.2 (hv a) (hvc a)⟩

/-- The points of a quasi-compact algebraic space map onto a compact set. -/
theorem isCompact_range_pointsMap_of_isQuasiCompactSpace {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hFqc : Space.IsQuasiCompactSpace B S hS F) (g : F ⟶ G) :
    IsCompact (Set.range (Space.pointsMap B S hS F g)) := by
  have := (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS F hF).1 hFqc
  exact isCompact_range (Space.continuous_pointsMap B S hS g)

namespace SectionFamily

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
  {W : Subfunctor Y} {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY₀ : IsAlgebraicSpace B S hS Y₀}
  {q₀ : Y₀ ⟶ Y} {ι : Type}

/-- A subfamily of a family of local sections, indexed by `e : κ → ι`, whose opens still cover
`q₀⁻¹(W)` on points. -/
def reindex (F : SectionFamily hY f W hY₀ q₀ ι) {κ : Type} (e : κ → ι)
    (hcov : Set.range (Space.pointsMap B S hS (W.preimage q₀).toFunctor (W.preimage q₀).ι) ⊆
      ⋃ k, Set.range (Space.pointsMap B S hS (F.U (e k)).toFunctor (F.U (e k)).ι)) :
    SectionFamily hY f W hY₀ q₀ κ where
  U k := F.U (e k)
  isOpen k := F.isOpen (e k)
  isQC k := F.isQC (e k)
  le k := F.le (e k)
  cover := hcov
  x k := F.x (e k)
  hx k := F.hx (e k)

end SectionFamily

/-- **The induction of the proof of Stacks 0CQ7 on the number of local sections.** Let `V ⊆ W`
and suppose that the conclusion is known (`hstep`) for every family of local sections over a
quasi-compact quasi-separated base and every quasi-compact open `V₀` of it lying over `V` and in
every open of the family, and that section covers glue along unions (`hunion`). Then it holds
without the condition that `V₀` lies in every open of the family. -/
theorem hasSectionCoverOver_of_sectionFamily_of_step {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} {W : Subfunctor Y}
    (hW : Space.IsOpenSubspace B S hS W) (V : Subfunctor Y)
    (hunion : ∀ {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₀ : IsAlgebraicSpace B S hS Y₀)
      (q₀ : Y₀ ⟶ Y) (V₁ V₂ V' : Subfunctor Y₀),
      HasSectionCoverOver hY f W hW hY₀ q₀ V₁ → HasSectionCoverOver hY f W hW hY₀ q₀ V₂ →
      Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι) ⊆
        Set.range (Space.pointsMap B S hS V₁.toFunctor V₁.ι) ∪
          Set.range (Space.pointsMap B S hS V₂.toFunctor V₂.ι) →
      HasSectionCoverOver hY f W hW hY₀ q₀ V')
    (hstep : ∀ {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₀ : IsAlgebraicSpace B S hS Y₀)
      (q₀ : Y₀ ⟶ Y) {n : ℕ} (F : SectionFamily hY f W hY₀ q₀ (Fin n)),
      Space.IsQuasiCompactSpace B S hS Y₀ →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      ∀ (V₀ : Subfunctor Y₀), Space.IsOpenSubspace B S hS V₀ →
        Space.IsQuasiCompactSpace B S hS V₀.toFunctor → (∀ i, V₀ ≤ F.U i) →
        V₀ ≤ V.preimage q₀ → HasSectionCoverOver hY f W hW hY₀ q₀ V₀) :
    ∀ (n : ℕ) {Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₀ : IsAlgebraicSpace B S hS Y₀)
      (q₀ : Y₀ ⟶ Y) (_F : SectionFamily hY f W hY₀ q₀ (Fin n)),
      Space.IsQuasiCompactSpace B S hS Y₀ →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y₀ →
      ∀ (V₀ : Subfunctor Y₀), Space.IsOpenSubspace B S hS V₀ →
        Space.IsQuasiCompactSpace B S hS V₀.toFunctor → V₀ ≤ V.preimage q₀ →
        HasSectionCoverOver hY f W hW hY₀ q₀ V₀ := by
  intro n
  induction n with
  | zero =>
    intro Y₀ hY₀ q₀ F hqc hqs V₀ hV₀ hV₀qc hV₀V
    exact hstep hY₀ q₀ F hqc hqs V₀ hV₀ hV₀qc (fun i => i.elim0) hV₀V
  | succ n ih =>
    intro Y₀ hY₀ q₀ F hqc hqs V₀ hV₀ hV₀qc hV₀V
    classical
    have := Space.quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS Y₀ hY₀ hqs
    -- the piece `V₀ ∩ U₁ ∩ … ∩ Uₙ`
    set Pset := Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) ∩
      ⋂ i ∈ (Finset.univ : Finset (Fin (n + 1))),
        Set.range (Space.pointsMap B S hS (F.U i).toFunctor (F.U i).ι) with hPset
    have hPoc := isCompact_inter_biInter_of_quasiSeparatedSpace Finset.univ
      (Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY₀ V₀ hV₀)
      (isCompact_range_pointsMap_of_isQuasiCompactSpace hV₀.1 hV₀qc V₀.ι)
      (fun i => Set.range (Space.pointsMap B S hS (F.U i).toFunctor (F.U i).ι))
      (fun i => Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY₀ _ (F.isOpen i))
      (fun i => isCompact_range_pointsMap_of_isQuasiCompactSpace (F.isOpen i).1 (F.isQC i) _)
    set P₀ := Space.openSubspaceOfPoints B S hS Y₀ Pset
    have hP₀ : Space.IsOpenSubspace B S hS P₀ :=
      Space.isOpenSubspace_openSubspaceOfPoints B S hS hY₀ Pset hPoc.1
    have hP₀r : Set.range (Space.pointsMap B S hS P₀.toFunctor P₀.ι) = Pset :=
      Space.range_pointsMap_ι_openSubspaceOfPoints B S hS Pset
    have hP₀qc : Space.IsQuasiCompactSpace B S hS P₀.toFunctor :=
      Space.isQuasiCompactSpace_of_isCompact_range B S hS hY₀ hP₀ (hP₀r ▸ hPoc.2)
    have hP₀V₀ : P₀ ≤ V₀ := Space.le_of_range_pointsMap_ι_subset B S hS hV₀
      (hP₀r.symm ▸ Set.inter_subset_left)
    have hP₀U : ∀ i, P₀ ≤ F.U i := fun i => Space.le_of_range_pointsMap_ι_subset B S hS
      (F.isOpen i) (by
        rw [hP₀r]
        exact Set.inter_subset_right.trans (Set.biInter_subset_of_mem (Finset.mem_univ i)))
    have hcP₀ := hstep hY₀ q₀ F hqc hqs P₀ hP₀ hP₀qc hP₀U (hP₀V₀.trans hV₀V)
    -- the pieces over the complements of the `U i`
    have hpiece : ∀ i : Fin (n + 1), ∃ R : Subfunctor Y₀,
        HasSectionCoverOver hY f W hW hY₀ q₀ R ∧
        Set.range (Space.pointsMap B S hS V₀.toFunctor V₀.ι) \
            Set.range (Space.pointsMap B S hS (F.U i).toFunctor (F.U i).ι) ⊆
          Set.range (Space.pointsMap B S hS R.toFunctor R.ι) := by
      intro i
      have hT : _root_.IsClosed (Set.range (Space.pointsMap B S hS (F.U i).toFunctor (F.U i).ι))ᶜ :=
        (Space.isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY₀ _ (F.isOpen i)).isClosed_compl
      set Yi := Space.reducedClosedSubspace B S hS Y₀ hY₀ _ hT
      have hYi := Space.isClosedSubspace_reducedClosedSubspace B S hS Y₀ hY₀ _ hT
      have hYir := Space.range_pointsMap_ι_reducedClosedSubspace B S hS Y₀ hY₀ _ hT
      have hcp : Space.IsProper B S hS Yi.ι :=
        Space.isProper_of_isClosedImmersion B S hS hYi.1 hY₀ Yi.ι hYi.2
      have hcqc : Space.IsQuasiCompact B S hS Yi.ι := hcp.2.1.2
      set Fi := (F.restrict hYi.1 Yi.ι hcqc).reindex (Fin.succAbove i) (by
        intro y hy
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 ((F.restrict hYi.1 Yi.ι hcqc).cover hy)
        have hj' : Space.pointsMap B S hS _ Yi.ι y ∈
            Set.range (Space.pointsMap B S hS (F.U j).toFunctor (F.U j).ι) := by
          have := hj
          change y ∈ Set.range (Space.pointsMap B S hS ((F.U j).preimage Yi.ι).toFunctor
            ((F.U j).preimage Yi.ι).ι) at this
          rwa [Space.range_pointsMap_preimage_ι] at this
        have hji : j ≠ i := by
          rintro rfl
          exact hYir.le ⟨y, rfl⟩ hj'
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        exact Set.mem_iUnion.2 ⟨k, hj⟩)
      have hYiqc : Space.IsQuasiCompactSpace B S hS Yi.toFunctor :=
        Space.isQuasiCompactSpace_of_isClosedImmersion B S hS hqc Yi.ι hYi.2
      have hYiqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Yi.toFunctor :=
        Space.isAbsolutelyQuasiSeparated_subfunctor B S hS B.contains_terminal hqs Yi hYi.1
      set Vi := V₀.preimage Yi.ι
      have hVi : Space.IsOpenSubspace B S hS Vi :=
        Space.isOpenSubspace_preimage B S hS Yi.ι V₀ hY₀ hYi.1 hV₀
      have hViqc : Space.IsQuasiCompactSpace B S hS Vi.toFunctor :=
        Space.isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hY₀ hYi.1 Yi.ι hcqc hV₀
          hV₀qc
      have hcVi := ih hYi.1 (Yi.ι ≫ q₀) Fi hYiqc hYiqs Vi hVi hViqc
        (fun T y hy => hV₀V T hy)
      refine ⟨Subfunctor.range (Vi.ι ≫ Yi.ι), ?_, ?_⟩
      · refine HasSectionCoverOver.trans hY₀ hYi.1 Yi.ι hcp hcVi ?_
        rw [Space.range_pointsMap_ι_range]
        rintro _ ⟨v, rfl⟩
        exact ⟨_, ⟨v, rfl⟩, (Space.pointsMap_comp_apply B S hS _ _ v).symm⟩
      · rintro v ⟨hv₀, hvi⟩
        obtain ⟨y, rfl⟩ : v ∈ Set.range (Space.pointsMap B S hS Yi.toFunctor Yi.ι) :=
          hYir.ge hvi
        have hyV : y ∈ Set.range (Space.pointsMap B S hS Vi.toFunctor Vi.ι) := by
          rw [Space.range_pointsMap_preimage_ι]
          exact hv₀
        obtain ⟨z, rfl⟩ := hyV
        rw [Space.range_pointsMap_ι_range]
        exact ⟨z, Space.pointsMap_comp_apply B S hS _ _ z⟩
    choose R hR hRcov using hpiece
    -- glue the pieces one at a time
    have hglue : ∀ (m : ℕ) (hm : m ≤ n + 1) (V' : Subfunctor Y₀),
        Set.range (Space.pointsMap B S hS V'.toFunctor V'.ι) ⊆
          Set.range (Space.pointsMap B S hS P₀.toFunctor P₀.ι) ∪
            ⋃ (k : Fin (n + 1)) (_ : k.val < m),
              Set.range (Space.pointsMap B S hS (R k).toFunctor (R k).ι) →
        HasSectionCoverOver hY f W hW hY₀ q₀ V' := by
      intro m
      induction m with
      | zero =>
        intro _ V' hV'
        refine hcP₀.mono (hV'.trans ?_)
        simp
      | succ m ihm =>
        intro hm V' hV'
        set Q := Space.openSubspaceOfPoints B S hS Y₀
          (Set.range (Space.pointsMap B S hS P₀.toFunctor P₀.ι) ∪
            ⋃ (k : Fin (n + 1)) (_ : k.val < m),
              Set.range (Space.pointsMap B S hS (R k).toFunctor (R k).ι))
        have hQr := Space.range_pointsMap_ι_openSubspaceOfPoints B S hS
          (Set.range (Space.pointsMap B S hS P₀.toFunctor P₀.ι) ∪
            ⋃ (k : Fin (n + 1)) (_ : k.val < m),
              Set.range (Space.pointsMap B S hS (R k).toFunctor (R k).ι))
        refine hunion hY₀ q₀ Q (R ⟨m, hm⟩) V' (ihm (Nat.le_of_succ_le hm) Q hQr.le) (hR _)
          (hV'.trans ?_)
        rw [hQr]
        rintro v (hv | hv)
        · exact Or.inl (Or.inl hv)
        · obtain ⟨k, hk, hvk⟩ := Set.mem_iUnion₂.1 hv
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
          · exact Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨k, hk, hvk⟩))
          · have : k = ⟨m, hm⟩ := Fin.ext hk
            subst this
            exact Or.inr hvk
    refine hglue (n + 1) le_rfl V₀ ?_
    intro v hv
    by_cases hall : ∀ i, v ∈ Set.range (Space.pointsMap B S hS (F.U i).toFunctor (F.U i).ι)
    · left
      rw [hP₀r]
      exact ⟨hv, Set.mem_iInter₂.2 fun i _ => hall i⟩
    · simp only [not_forall] at hall
      obtain ⟨i, hi⟩ := hall
      exact Or.inr (Set.mem_iUnion₂.2 ⟨i, i.2, hRcov i ⟨hv, hi⟩⟩)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
