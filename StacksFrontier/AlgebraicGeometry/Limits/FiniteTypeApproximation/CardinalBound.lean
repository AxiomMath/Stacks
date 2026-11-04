module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepFullCardinality

/-!
# Noetherian approximation with a bounded index set

Noetherian approximation of a quasi-compact quasi-separated scheme `S` relative to a quasi-compact
open (Stacks 07RN), and absolute Noetherian approximation (Stacks 01ZA), can be achieved by an
inverse system whose index set is no larger than the given index set and the scheme: the index
built at each step of the induction over an affine cover consists of pairs of an old index and a
finitely generated subalgebra of a ring of size at most `size S`
(`Stacks.GluedStep.mk_idx_le`).

Such a bound is what is needed to apply the descent results for inverse systems of algebraic
spaces, which ask the index set to be smaller than the cofinality of the size cutoff of the big
fppf site, to a system produced by Noetherian approximation.

## Main results

* `AlgebraicGeometry.exists_finiteTypeApproximation_card_le`: Stacks 07RN with a cofinal
  reindexing and `#J ≤ max #I (size S)`.
* `AlgebraicGeometry.Scheme.exists_isLimit_affine_locallyOfFiniteType_card_le`: Stacks 01ZA with
  `#I ≤ size S`.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.FiniteTypeApproximation

attribute [local instance] indexPreorder indexNonempty indexDirected

/-- The induction of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.exists_of_isOneAffineOpenStep` over a finite
affine cover of the complement of the open, keeping track of the size of the index: each step is
`AlgebraicGeometry.exists_finiteTypeApproximation_of_sup_affine_card` on an open of `S`, whose size
is at most that of `S`. -/
private theorem exists_card_aux (S : Scheme.{u}) (hS : CompactSpace S)
    (hQS : QuasiSeparatedSpace S) (n : ℕ) :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : Iᵒᵈ ⥤ Scheme.{u}),
      (∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)) →
      (∀ i, LocallyOfFiniteType (terminal.from (D.obj i))) →
      (∀ i, QuasiCompact (terminal.from (D.obj i))) →
      ∀ (U : S.Opens), CompactSpace (U : Scheme.{u}) →
      ∀ (A : Fin n → S.Opens), (∀ l, IsAffineOpen (A l)) → U ⊔ ⨆ l, A l = ⊤ →
      ∀ (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D),
        IsLimit (Cone.mk (U : Scheme.{u}) p) →
        ∃ Q : FiniteTypeApproximation D S U p, IsCofinal Q ∧
          Cardinal.mk Q.indexType ≤ max (Cardinal.mk I) S.size := by
  have := hS
  have := hQS
  induction n with
  | zero =>
    intro I _ _ _ D hAff hFT hQC U hU A hA hcov p hp
    have hU' : U = ⊤ := by simpa using hcov
    exact ⟨ofEqTop D S hU' p hp, isCofinal_ofEqTop D S hU' p hp, le_max_left _ _⟩
  | succ n ih =>
    intro I _ _ _ D hAff hFT hQC U hU A hA hcov p hp
    have := hU
    have hUc : IsCompact ((U : S.Opens) : Set S) := isCompact_iff_compactSpace.mpr hU
    set V : S.Opens := U ⊔ A 0 with hVdef
    have hUV : U ≤ V := le_sup_left
    have hAV : A 0 ≤ V := le_sup_right
    have hVc : CompactSpace (V : Scheme.{u}) := by
      rw [hVdef]
      exact compactSpace_sup U (A 0) hUc (hA 0).isCompact
    have hVqs : QuasiSeparatedSpace (V : Scheme.{u}) :=
      QuasiSeparatedSpace.of_isOpenEmbedding V.ι.isOpenEmbedding
    have hU1c : CompactSpace ((V.ι ⁻¹ᵁ U : (V : Scheme.{u}).Opens) : Scheme.{u}) :=
      Scheme.Opens.compactSpace_preimage_ι V hUV hUc
    have hA1 : IsAffineOpen (V.ι ⁻¹ᵁ A 0 : (V : Scheme.{u}).Opens) :=
      Scheme.Opens.isAffineOpen_preimage_ι V hAV (hA 0)
    have hcovV : (V.ι ⁻¹ᵁ U : (V : Scheme.{u}).Opens) ⊔ V.ι ⁻¹ᵁ A 0 = ⊤ := by
      have h : (V.ι ⁻¹ᵁ U : (V : Scheme.{u}).Opens) ⊔ V.ι ⁻¹ᵁ A 0 = V.ι ⁻¹ᵁ V := rfl
      rw [h]
      exact Scheme.Opens.preimage_ι_self V
    set σ := Scheme.Opens.isoPreimage V hUV with hσ
    set p₁ := ((Cone.mk (U : Scheme.{u}) p).extend σ.inv).π with hp₁def
    have hp₁ : IsLimit (Cone.mk
        ((V.ι ⁻¹ᵁ U : (V : Scheme.{u}).Opens) : Scheme.{u}) p₁) := by
      refine IsLimit.ofIsoLimit hp (Cone.ext σ ?_)
      intro j
      simp [hp₁def]
    obtain ⟨Q₁, hQ₁, hc₁⟩ := AlgebraicGeometry.exists_finiteTypeApproximation_of_sup_affine_card
      D _ _ hA1 hcovV p₁ hp₁
    have hcov' : V ⊔ ⨆ l : Fin n, A l.succ = ⊤ := by
      rw [← hcov, iSup_fin_succ_split, hVdef, sup_assoc]
    obtain ⟨Q₂, hQ₂, hc₂⟩ := ih Q₁.ambient (fun f ↦ Q₁.transition_affine f)
      Q₁.locallyOfFiniteType Q₁.quasiCompact V hVc (fun l ↦ A l.succ) (fun l ↦ hA l.succ) hcov'
      Q₁.ambientCone Q₁.ambientCone_isLimit
    refine ⟨Q₁.comp Q₂ (𝟙 _) (fun j ↦ Category.id_comp _) hUV σ ?_ hQ₂ ?_, ?_, ?_⟩
    · rw [hσ, Category.comp_id]
      exact Scheme.Opens.isoPreimage_hom_ι V hUV
    · intro i
      simp [hp₁def]
    · intro i
      obtain ⟨j₁, hj₁⟩ := hQ₁ i
      obtain ⟨j, hj⟩ := hQ₂ j₁
      exact ⟨j, hj₁.trans (Q₁.index.monotone hj)⟩
    · have hVS : (V : Scheme.{u}).size ≤ S.size := S.size_coe_opens_le V
      show Cardinal.mk Q₂.indexType ≤ _
      exact hc₂.trans (max_le (hc₁.trans (max_le_max le_rfl hVS)) (le_max_right _ _))

end Scheme.FiniteTypeApproximation

attribute [local instance] Scheme.FiniteTypeApproximation.indexPreorder
  Scheme.FiniteTypeApproximation.indexNonempty Scheme.FiniteTypeApproximation.indexDirected

/-- **Stacks 07RN with a bounded index set.**  Let `S` be a quasi-compact and quasi-separated
scheme and let `U` be a quasi-compact open subscheme which is the inverse limit of a directed
system `D`, indexed by `I`, of schemes of finite type over the integers with affine transition
morphisms. Then that system extends to such a system approximating `S`, compatibly with `D` on
`U`, whose reindexing to `I` is cofinal and whose index set has cardinality at most that of `I`
and the size of `S`. -/
theorem exists_finiteTypeApproximation_card_le {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵈ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵈ} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
    [∀ i, QuasiCompact (terminal.from (D.obj i))]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens)
    [CompactSpace (U : Scheme.{u})]
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    ∃ Q : Scheme.FiniteTypeApproximation D S U p, Q.IsCofinal ∧
      Cardinal.mk Q.indexType ≤ max (Cardinal.mk I) S.size := by
  obtain ⟨n, A, hA⟩ := Scheme.exists_finite_affineOpens_sup_eq_top S U
  exact Scheme.FiniteTypeApproximation.exists_card_aux S ‹_› ‹_› n D (fun f ↦ inferInstance)
    (fun i ↦ inferInstance) (fun i ↦ inferInstance) U ‹_›
    (fun l ↦ ((A l : S.affineOpens) : S.Opens)) (fun l ↦ (A l).2) hA p hp

/-- **Stacks 01ZA with a bounded index set.**  A quasi-compact and quasi-separated scheme `S` is
the inverse limit of an inverse system of schemes over a directed set of cardinality at most the
size of `S`, whose transition morphisms are affine and whose every stage is of finite type over
the integers. -/
theorem Scheme.exists_isLimit_affine_locallyOfFiniteType_card_le (S : Scheme.{u})
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : Iᵒᵈ ⥤ Scheme.{u}) (c : (Functor.const Iᵒᵈ).obj S ⟶ F),
      (∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (F.map f)) ∧
      (∀ i, LocallyOfFiniteType (terminal.from (F.obj i))) ∧
      (∀ i, QuasiCompact (terminal.from (F.obj i))) ∧
      Nonempty (IsLimit (Cone.mk S c)) ∧ Cardinal.mk I ≤ S.size := by
  have : IsEmpty ((⊥ : S.Opens) : Scheme.{u}) := inferInstanceAs (IsEmpty (∅ : Set S))
  have : ∀ {i j : PUnit.{u + 1}ᵒᵈ} (f : i ⟶ j), IsAffineHom ((botDiagram S).map f) :=
    fun _ ↦ inferInstanceAs (IsAffineHom (𝟙 _))
  have : ∀ i, LocallyOfFiniteType (terminal.from ((botDiagram S).obj i)) :=
    fun _ ↦ locallyOfFiniteType_terminal_from_of_isEmpty ((⊥ : S.Opens) : Scheme.{u})
  have : ∀ i, QuasiCompact (terminal.from ((botDiagram S).obj i)) :=
    fun _ ↦ quasiCompact_terminal_from_of_isEmpty ((⊥ : S.Opens) : Scheme.{u})
  have : CompactSpace ((⊥ : S.Opens) : Scheme.{u}) := inferInstance
  obtain ⟨Q, -, hQ⟩ := exists_finiteTypeApproximation_card_le (botDiagram S) S ⊥ (𝟙 _)
    (isLimitConstConePUnit ((⊥ : S.Opens) : Scheme.{u}))
  refine ⟨Q.indexType, Q.indexPreorder, Q.indexNonempty, Q.indexDirected, Q.ambient,
    Q.ambientCone, Q.transition_affine, Q.locallyOfFiniteType, Q.quasiCompact,
    ⟨Q.ambientCone_isLimit⟩, hQ.trans (max_le ?_ le_rfl)⟩
  rw [Cardinal.mk_punit]
  exact Cardinal.one_le_aleph0.trans S.aleph0_le_size

end AlgebraicGeometry

end
