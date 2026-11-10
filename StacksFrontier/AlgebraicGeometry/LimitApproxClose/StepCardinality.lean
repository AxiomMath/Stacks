module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Step
public import StacksFrontier.AlgebraicGeometry.Size.GlobalSections

/-!
# The size of the index of the one-affine-open step

The one-affine-open step of Tag 07RN (`Stacks.GluedStep.exists_approximation`) extends a
directed system of finite-type schemes approximating a quasi-compact open `V` of `S` to one
approximating `S`. This file records that the index of the extended system is no larger than the
old index and the scheme: its cardinality is at most `max #I S.size`. The bound is what keeps the
approximating systems of
`StacksFrontier/AlgebraicGeometry/Limits/FiniteTypeApproximation/CardinalBound.lean` inside a
bounded universe of indices.

## Main results

* `Stacks.GluedStep.mk_idx_le`: the index of pairs is bounded by the old index and the scheme.
* `Stacks.GluedStep.exists_approximation_card`: the step from a charting family, with the bound.

The same bound for the one-affine-open step of Tag 07RN itself is
`AlgebraicGeometry.exists_finiteTypeApproximation_of_sup_affine_card`, in
`StacksFrontier/AlgebraicGeometry/LimitApproxClose/StepFullCardinality.lean`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.GluedStep

open Stacks.StageSubalgebra

variable {K : Type u} [Preorder K] {Dv : Kᵒᵈ ⥤ Scheme.{u}} {S : Scheme.{u}} {V Y : S.Opens}
  (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
  (W : ∀ a, (Dv.obj a).Opens)
  (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
  (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y)

variable {n : ℕ} (g : Fin n → Γ((Y : Scheme.{u}), ⊤))
  (f : ∀ k : K, Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k), ⊤))
  (hf : ∀ (k : K) (l : Fin n), (tau pv W hW hT).app (op (OrderDual.toDual k)) (f k l) =
    str (V := V) (Y := Y) (g l))

/-- **The index of the extended system is no larger than the old index and the scheme.**  A pair
of the index is a stage together with a finitely generated subalgebra of the fibre-product ring at
that stage, and that ring is a subring of `Γ(Y) × Γ(W_k)`, where `Γ(Y)` is bounded by the size of
`S` and `Γ(W_k)` is countable, `W_k` being a quasi-compact scheme of finite type over the integers.
-/
lemma mk_idx_le [∀ a, LocallyOfFiniteType (terminal.from (Dv.obj a))] [IsAffine (Y : Scheme.{u})]
    (hWc : ∀ a : Kᵒᵈ, IsCompact ((W a : (Dv.obj a).Opens) : Set (Dv.obj a))) :
    Cardinal.mk (idx pv W hW hT g f hf) ≤ max (Cardinal.mk K) S.size := by
  have hS0 : Cardinal.aleph0 ≤ S.size := S.aleph0_le_size
  have hrng : ∀ k, Cardinal.mk ((rng pv W hW hT).obj k) ≤ S.size := by
    intro k
    have h1 : Cardinal.mk Γ((Y : Scheme.{u}), ⊤) ≤ S.size :=
      (Scheme.mk_globalSections_le_size (Y : Scheme.{u})).trans (S.size_coe_opens_le Y)
    have h2 : Cardinal.mk Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k), ⊤) ≤
        Cardinal.aleph0 := by
      have : CompactSpace ((W (OrderDual.toDual k) : (Dv.obj (OrderDual.toDual k)).Opens) :
          Scheme.{u}) := isCompact_iff_compactSpace.mp (hWc _)
      have : LocallyOfFiniteType (terminal.from
          ((W (OrderDual.toDual k) : (Dv.obj (OrderDual.toDual k)).Opens) : Scheme.{u})) := by
        rw [terminal.hom_ext (terminal.from _)
          ((W (OrderDual.toDual k)).ι ≫ terminal.from (Dv.obj (OrderDual.toDual k)))]
        infer_instance
      exact Scheme.mk_globalSections_le_aleph0 _
    calc Cardinal.mk ((rng pv W hW hT).obj k)
        ≤ Cardinal.mk (Γ((Y : Scheme.{u}), ⊤) ×
            Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k), ⊤)) := Cardinal.mk_subtype_le _
      _ = Cardinal.mk Γ((Y : Scheme.{u}), ⊤) *
            Cardinal.mk Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k), ⊤) := by
          rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
      _ ≤ S.size * S.size := mul_le_mul' h1 (h2.trans hS0)
      _ = S.size := Cardinal.mul_eq_self hS0
  have hsub : ∀ k, Cardinal.mk {A : Subalgebra ℤ ((rng pv W hW hT).obj k) //
      pred pv W hW hT g f hf k A} ≤ S.size := by
    intro k
    refine (Cardinal.mk_le_of_injective (f := fun A => (⟨A.1, A.2.fg⟩ :
      {A : Subalgebra ℤ ((rng pv W hW hT).obj k) // A.FG})) ?_).trans ?_
    · intro A B h
      exact Subtype.ext (Subtype.mk.inj h)
    · exact (Subalgebra.mk_fg_le ℤ _).trans (max_le hS0 (hrng k))
  change Cardinal.mk (Σ k : K, {A : Subalgebra ℤ ((rng pv W hW hT).obj k) //
    pred pv W hW hT g f hf k A}) ≤ _
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_sum _ (fun _ => S.size) hsub).trans ?_
  rw [Cardinal.sum_const, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.mul_le_max_of_aleph0_le_right hS0

end Stacks.GluedStep

namespace Stacks.GluedStep

open Stacks.StageSubalgebra

/-- `Stacks.GluedStep.approximation_of_data`, recording also that the index of the approximation is
the index `Stacks.GluedStep.idx` of pairs. -/
theorem approximation_of_data_card {K : Type u} [Preorder K] [Nonempty K] [IsDirected K (· ≤ ·)]
    {Dv : Kᵒᵈ ⥤ Scheme.{u}} [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)]
    [∀ a, LocallyOfFiniteType (terminal.from (Dv.obj a))]
    [∀ a, QuasiCompact (terminal.from (Dv.obj a))] [∀ a, CompactSpace (Dv.obj a)]
    {S : Scheme.{u}} {V Y : S.Opens}
    (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
    (W : ∀ a, (Dv.obj a).Opens)
    (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
    (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y)
    {n : ℕ} (g : Fin n → Γ((Y : Scheme.{u}), ⊤))
    (f : ∀ k : K, Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k), ⊤))
    (hf : ∀ (k : K) (l : Fin n), (tau pv W hW hT).app (op (OrderDual.toDual k)) (f k l) =
      str (V := V) (Y := Y) (g l))
    [Nonempty (idx pv W hW hT g f hf)] [IsDirected (idx pv W hW hT g f hf) (· ≤ ·)]
    [∀ j, IsOpenImmersion ((legSpec pv W hW hT g f hf).app j)]
    [∀ j : (idx pv W hW hT g f hf)ᵒᵈ, LocallyOfFiniteType (terminal.from
      ((specDiagram (rng pv W hW hT) (pred pv W hW hT g f hf)).obj j))]
    [∀ j : (idx pv W hW hT g f hf)ᵒᵈ,
      CompactSpace ((overlapDiagram Dv (pred pv W hW hT g f hf)).obj j)]
    (hS : V ⊔ Y = ⊤)
    (halpha : ∀ ⦃j k : (idx pv W hW hT g f hf)ᵒᵈ⦄ (u : j ⟶ k),
      (overlapDiagram Dv (pred pv W hW hT g f hf)).map u ⁻¹ᵁ
          ((legOpen pv W hW hT g f hf).app k).opensRange =
        ((legOpen pv W hW hT g f hf).app j).opensRange)
    (hbeta : ∀ ⦃j k : (idx pv W hW hT g f hf)ᵒᵈ⦄ (u : j ⟶ k),
      (specDiagram (rng pv W hW hT) (pred pv W hW hT g f hf)).map u ⁻¹ᵁ
          ((legSpec pv W hW hT g f hf).app k).opensRange =
        ((legSpec pv W hW hT g f hf).app j).opensRange)
    (hXr : ∀ j, (coneX pv W hW hT g f hf).π.app j ⁻¹ᵁ
      ((legOpen pv W hW hT g f hf).app j).opensRange = V.ι ⁻¹ᵁ Y)
    (hYr : ∀ j, (coneY pv W hW hT g f hf).π.app j ⁻¹ᵁ
      ((legSpec pv W hW hT g f hf).app j).opensRange = Y.ι ⁻¹ᵁ V)
    (hXW : ∀ j, S.homOfLE (inf_le_left : V ⊓ Y ≤ V) ≫ (coneX pv W hW hT g f hf).π.app j =
      (coneWp pv W hW hT g f hf).π.app j ≫ (legOpen pv W hW hT g f hf).app j)
    (hYW : ∀ j, S.homOfLE (inf_le_right : V ⊓ Y ≤ Y) ≫ (coneY pv W hW hT g f hf).π.app j =
      (coneWp pv W hW hT g f hf).π.app j ≫ (legSpec pv W hW hT g f hf).app j)
    (hX : IsLimit (coneX pv W hW hT g f hf)) (hYlim : IsLimit (coneY pv W hW hT g f hf))
    (hWlim : IsLimit (coneWp pv W hW hT g f hf))
    (hprojcof : ∀ k : K, ∃ j : idx pv W hW hT g f hf,
      k ≤ (proj (F := rng pv W hW hT) (P := pred pv W hW hT g f hf)) j) :
    ∃ A : Scheme.FiniteTypeApproximation Dv S V pv,
      (∀ k : K, ∃ j : A.indexType, k ≤ A.index j) ∧
        Cardinal.mk A.indexType = Cardinal.mk (idx pv W hW hT g f hf) := by
  refine ⟨{ indexType := idx pv W hW hT g f hf
            index := proj (F := rng pv W hW hT) (P := pred pv W hW hT g f hf)
            ambient := gluePairFunctor (legOpen pv W hW hT g f hf) (legSpec pv W hW hT g f hf)
            openPart := overlapDiagram Dv (pred pv W hW hT g f hf)
            inclusion := gluePairFunctorInl _ _
            comparison := Iso.refl _
            ambientCone := gluePairFunctorCone _ _ V Y (coneX pv W hW hT g f hf).π
              (coneY pv W hW hT g f hf).π (coneWp pv W hW hT g f hf).π hXW hYW hS
            openCone := (coneX pv W hW hT g f hf).π
            transition_affine := fun u ↦ isAffineHom_gluePairFunctor_map _ _ halpha hbeta u
            locallyOfFiniteType := fun j ↦
              locallyOfFiniteType_terminal_from_gluePairFunctor_obj _ _ j
            quasiCompact := fun j ↦ quasiCompact_terminal_from_gluePairFunctor_obj _ _ j
            inclusion_isOpenImmersion := fun j ↦
              isOpenImmersion_gluePairFunctorInl_app _ _ j
            transition_isPullback := fun u ↦ isPullback_gluePairFunctorInl_app _ _ hbeta u
            ambientCone_isLimit := isLimitGluePairFunctorCone _ _ V Y _ _ _ hXW hYW hS
              halpha hbeta hXr hYr hX hYlim hWlim
            openCone_isLimit := hX
            inclusion_compatibility := fun j ↦
              ι_gluePairFunctorCone_app_left _ _ V Y _ _ _ hXW hYW hS j
            comparison_compatibility := fun j ↦ Category.comp_id _ }, hprojcof, rfl⟩

/-- `Stacks.GluedStep.exists_approximation`, with the size of the new index bounded by those of the
old index and of the scheme. -/
theorem exists_approximation_card {K : Type u} [Preorder K] [Nonempty K] [IsDirected K (· ≤ ·)]
    {Dv : Kᵒᵈ ⥤ Scheme.{u}} [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)]
    [∀ a, LocallyOfFiniteType (terminal.from (Dv.obj a))]
    [∀ a, QuasiCompact (terminal.from (Dv.obj a))]
    {S : Scheme.{u}} {V Y : S.Opens} [IsAffine (Y : Scheme.{u})]
    (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
    (W : ∀ a, (Dv.obj a).Opens)
    (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
    (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y)
    (hWc : ∀ a : Kᵒᵈ, IsCompact ((W a : (Dv.obj a).Opens) : Set (Dv.obj a)))
    (hS : V ⊔ Y = ⊤)
    (hpv : IsLimit (Cone.mk (V : Scheme.{u}) pv))
    (hwlim : IsLimit (cw pv W hW hT))
    (hcolim : IsColimit (Scheme.Γ.mapCocone (cw pv W hW hT).op))
    {n : ℕ} (g : Fin n → Γ((Y : Scheme.{u}), ⊤))
    (hin : ∀ l, (Y : Scheme.{u}).basicOpen (g l) ≤
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange)
    (hgcov : (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange ≤
      ⨆ l, (Y : Scheme.{u}).basicOpen (g l))
    (f : ∀ k : K, Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k), ⊤))
    (hf : ∀ (k : K) (l : Fin n), (tau pv W hW hT).app (op (OrderDual.toDual k)) (f k l) =
      str (V := V) (Y := Y) (g l))
    (hfmap : ∀ {k k' : K} (u : k ⟶ k') (l : Fin n), (secK (Dv := Dv) W hW).map u (f k l) = f k' l)
    (haff : ∀ (k : K) (l : Fin n),
      IsAffineOpen (((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k)).basicOpen (f k l)))
    (hcov : ∀ k : K,
      ⨆ l, ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k)).basicOpen (f k l) = ⊤) :
    ∃ A : Scheme.FiniteTypeApproximation Dv S V pv,
      (∀ k : K, ∃ j : A.indexType, k ≤ A.index j) ∧
        Cardinal.mk A.indexType ≤ max (Cardinal.mk K) S.size := by
  classical
  have hmc : ∀ a : Kᵒᵈ, CompactSpace ((mdl (Dv := Dv) W hW).obj a) :=
    compactSpace_compatibleOpensDiagram_obj W hW hWc
  have hzc : CompactSpace ((V ⊓ Y : S.Opens) : Scheme.{u}) :=
    Scheme.compactSpace_of_isLimit _ _ hwlim
  have hmft : ∀ a : Kᵒᵈ, LocallyOfFiniteType (terminal.from ((mdl (Dv := Dv) W hW).obj a)) :=
    fun a ↦ locallyOfFiniteType_terminal_from_opens (W a)
  have hqa : ∀ k : K, ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k)).IsQuasiAffine :=
    fun k ↦ Scheme.isQuasiAffine_of_iSup_basicOpen_eq_top _ (f k) (haff k) (hcov k)
  have hvc : ∀ a : Kᵒᵈ, CompactSpace (Dv.obj a) :=
    fun a ↦ (compactSpace_iff_quasiCompact (Dv.obj a)).mpr inferInstance
  have hoi : ∀ k : K, IsOpenImmersion (chart pv W hW hT k) := fun k ↦
    isOpenImmersion_toSpecΓ_comp_SpecMap_snd_of_basicOpen_le
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)) (tau pv W hW hT) (OrderDual.toDual k) g hin
      (f k) (hf k) (haff k) (hcov k)
  have hrange : ∀ k : K, (chart pv W hW hT k).opensRange =
      (⨆ l, PrimeSpectrum.basicOpen (fam pv W hW hT g f hf k l) :
        (Spec (CommRingCat.of ((rng pv W hW hT).obj k))).Opens) := fun k ↦
    opensRange_toSpecΓ_comp_SpecMap_snd (tau pv W hW hT) (str (V := V) (Y := Y))
      (OrderDual.toDual k) g (f k) (hf k)
      (fun l ↦ bijective_awayMap_appTop_of_basicOpen_le_opensRange
        (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)) (g l) (hin l)) (haff k) (hcov k)
  have hrU : ∀ (k : K) (l : Fin n),
      (PrimeSpectrum.basicOpen (fam pv W hW hT g f hf k l) :
          (Spec (CommRingCat.of ((rng pv W hW hT).obj k))).Opens) ≤
        (chart pv W hW hT k).opensRange := fun k l ↦ (le_iSup _ l).trans (hrange k).ge
  have hcovr : ∀ k : K, (chart pv W hW hT k).opensRange ≤
      ⨆ l, (PrimeSpectrum.basicOpen (fam pv W hW hT g f hf k l) :
        (Spec (CommRingCat.of ((rng pv W hW hT).obj k))).Opens) := fun k ↦ (hrange k).le
  have hft : ∀ (k : K) (l : Fin n),
      Algebra.FiniteType ℤ (Localization.Away (fam pv W hW hT g f hf k l)) :=
    finiteType_localization_away_charting (Dw := mdl (Dv := Dv) W hW)
      (fun k ↦ ((rng pv W hW hT).obj k)) (chart pv W hW hT) hoi (fam pv W hW hT g f hf) hrU
  have hne : Nonempty (idx pv W hW hT g f hf) :=
    nonempty_isChartedSubalgebra (rng pv W hW hT) (fam pv W hW hT g f hf) hft
  have hdir : IsDirected (idx pv W hW hT g f hf) (· ≤ ·) :=
    isDirected_isChartedSubalgebra (rng pv W hW hT) (fam pv W hW hT g f hf) hft
  have hprojcof : ∀ k : K, ∃ j : idx pv W hW hT g f hf,
      k ≤ (proj (F := rng pv W hW hT) (P := pred pv W hW hT g f hf)) j := fun k ↦
    exists_le_proj_isChartedSubalgebra (rng pv W hW hT) (fam pv W hW hT g f hf) hft k
  -- the ring-level colimit
  have hfpcol : IsColimit (FibreProduct.cocone (sec (Dv := Dv) W hW) (tau pv W hW hT)
      (str (V := V) (Y := Y))) := FibreProduct.isColimitCocone _ _ _ hcolim
  have hsurj : ∀ x : Γ((Y : Scheme.{u}), ⊤), ∃ (k : K) (y : (rng pv W hW hT).obj k),
      (rngCocone pv W hW hT).app k y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := FibreProduct.exists_app_eq hfpcol x
    exact ⟨OrderDual.ofDual i.unop, y, hy⟩
  have hsep : ∀ (k : K) (y z : (rng pv W hW hT).obj k),
      (rngCocone pv W hW hT).app k y = (rngCocone pv W hW hT).app k z →
        ∃ (k' : K) (v : k ⟶ k'), (rng pv W hW hT).map v y = (rng pv W hW hT).map v z := by
    intro k y z h
    obtain ⟨i, v, hv⟩ := FibreProduct.exists_map_eq hfpcol y z h
    refine ⟨OrderDual.ofDual i.unop, homOfLE (leOfHom v.unop), ?_⟩
    have hvv : (preorderToOpDual K).map (homOfLE (leOfHom v.unop)) = v :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    change (FibreProduct.diagram (sec (Dv := Dv) W hW) (tau pv W hW hT)
      (str (V := V) (Y := Y))).map ((preorderToOpDual K).map
        (homOfLE (leOfHom v.unop))) y = _
    rw [hvv]
    exact hv
  have hringcol : IsColimit (ringCocone (P := pred pv W hW hT g f hf)
      (rngCocone pv W hW hT)) :=
    (nonempty_isColimit_ringCocone (rngCocone pv W hW hT) (fun _ _ h ↦ h.fg)
      (fun k C hC ↦ exists_isChartedSubalgebra_ge (fam pv W hW hT g f hf k) (hft k) C hC)
      hsurj hsep).some
  have hYspec : IsLimit (Cone.mk (Spec Γ((Y : Scheme.{u}), ⊤))
      (specDiagramCone (rngCocone pv W hW hT) (pred pv W hW hT g f hf))) :=
    isLimitSpecDiagramCone _ _ hringcol
  have hYlim : IsLimit (coneY pv W hW hT g f hf) :=
    isLimitConeExtend hYspec (asIso ((Y : Scheme.{u}).toSpecΓ))
  -- the two legs
  have hbetaoi : ∀ j, IsOpenImmersion ((legSpec pv W hW hT g f hf).app j) := fun j ↦
    isOpenImmersion_specLeg_app (fam pv W hW hT g f hf) (chart pv W hW hT)
      (fun h ↦ chart_naturality pv W hW hT h) hrU hcovr j
  have hb : ∀ {k k' : K} (h : k ≤ k') (l : Fin n),
      (rng pv W hW hT).map (homOfLE h) (fam pv W hW hT g f hf k l) =
        fam pv W hW hT g f hf k' l := fun h l ↦
    FibreProduct.diagramMap_famMk (secK (Dv := Dv) W hW) (tauK pv W hW hT)
      (str (V := V) (Y := Y)) g f hf hfmap (homOfLE h) l
  have halpha := preimage_opensRange_openInclusionLeg (F := rng pv W hW hT) W hW
    (pred pv W hW hT g f hf)
  have hbeta := preimage_opensRange_specLeg (fam pv W hW hT g f hf) (chart pv W hW hT)
    (fun h ↦ chart_naturality pv W hW hT h) hrU hcovr hb
  -- the four cone compatibilities
  have hXr : ∀ j, (coneX pv W hW hT g f hf).π.app j ⁻¹ᵁ
      ((legOpen pv W hW hT g f hf).app j).opensRange = V.ι ⁻¹ᵁ Y := by
    intro j
    have hor : ((legOpen pv W hW hT g f hf).app j).opensRange =
        W (OrderDual.toDual (stage (OrderDual.ofDual j))) := Scheme.Opens.opensRange_ι _
    rw [hor]
    exact hT _
  have hgrange : (⨆ l, (Y : Scheme.{u}).basicOpen (g l)) =
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange := le_antisymm (iSup_le hin) hgcov
  have hYr : ∀ j, (coneY pv W hW hT g f hf).π.app j ⁻¹ᵁ
      ((legSpec pv W hW hT g f hf).app j).opensRange = Y.ι ⁻¹ᵁ V := by
    intro j
    have hel : ∀ l : Fin n, (ringCocone (P := pred pv W hW hT g f hf)
        (rngCocone pv W hW hT)).ι.app (OrderDual.ofDual j)
          ⟨fam pv W hW hT g f hf (stage (OrderDual.ofDual j)) l,
            (isChartedSubalgebra_sub (fam pv W hW hT g f hf) (OrderDual.ofDual j)).mem l⟩ =
        g l := fun l ↦ rfl
    have hsup : (⨆ l, PrimeSpectrum.basicOpen
          ((ringCocone (P := pred pv W hW hT g f hf) (rngCocone pv W hW hT)).ι.app
            (OrderDual.ofDual j)
            ⟨fam pv W hW hT g f hf (stage (OrderDual.ofDual j)) l,
              (isChartedSubalgebra_sub (fam pv W hW hT g f hf) (OrderDual.ofDual j)).mem l⟩) :
          (Spec Γ((Y : Scheme.{u}), ⊤)).Opens) =
        ⨆ l, PrimeSpectrum.basicOpen (g l) :=
      iSup_congr fun l ↦ congrArg PrimeSpectrum.basicOpen (hel l)
    have hstep : Spec.map ((ringCocone (P := pred pv W hW hT g f hf)
          (rngCocone pv W hW hT)).ι.app (OrderDual.ofDual j)) ⁻¹ᵁ
        ((legSpec pv W hW hT g f hf).app j).opensRange =
      ⨆ l, PrimeSpectrum.basicOpen (g l) := by
      rw [opensRange_specLeg_app (fam pv W hW hT g f hf) (chart pv W hW hT)
        (fun h ↦ chart_naturality pv W hW hT h) hrU hcovr j]
      exact (SpecMap_preimage_iSup_basicOpen _ _).trans hsup
    refine Eq.trans (congrArg (fun U ↦ (Y : Scheme.{u}).toSpecΓ ⁻¹ᵁ U) hstep) ?_
    refine Eq.trans (Scheme.Hom.preimage_iSup _ _) ?_
    simp only [Scheme.toSpecΓ_preimage_basicOpen]
    rw [hgrange, Scheme.opensRange_homOfLE_inf_right]
  have hXW : ∀ j, S.homOfLE (inf_le_left : V ⊓ Y ≤ V) ≫ (coneX pv W hW hT g f hf).π.app j =
      (coneWp pv W hW hT g f hf).π.app j ≫ (legOpen pv W hW hT g f hf).app j := fun j ↦
    (overlapCone_app_comp_ι V Y pv W hW hT _).symm
  have hYW : ∀ j, S.homOfLE (inf_le_right : V ⊓ Y ≤ Y) ≫ (coneY pv W hW hT g f hf).π.app j =
      (coneWp pv W hW hT g f hf).π.app j ≫ (legSpec pv W hW hT g f hf).app j := by
    intro j
    rw [coneExtend_app, specDiagramCone_app, specLeg_app, ringCocone_ι_app]
    refine Eq.trans (congrArg (fun m ↦ S.homOfLE (inf_le_right : V ⊓ Y ≤ Y) ≫
      (Y : Scheme.{u}).toSpecΓ ≫ m) (Spec.map_comp _ _)) ?_
    refine Eq.trans (keyY pv W hW hT (OrderDual.toDual (stage (OrderDual.ofDual j)))
      (Spec.map (CommRingCat.ofHom ((sub (OrderDual.ofDual j)).val :
        sub (OrderDual.ofDual j) →+* (rng pv W hW hT).obj (stage (OrderDual.ofDual j)))))) ?_
    exact congrArg (fun m ↦ (coneWp pv W hW hT g f hf).π.app j ≫ m)
      (Category.assoc _ _ _).symm
  have hX : IsLimit (coneX pv W hW hT g f hf) :=
    isLimitWhiskerOfCofinal (proj (F := rng pv W hW hT) (P := pred pv W hW hT g f hf))
      hprojcof hpv
  have hWlim : IsLimit (coneWp pv W hW hT g f hf) :=
    isLimitWhiskerOfCofinal (proj (F := rng pv W hW hT) (P := pred pv W hW hT g f hf))
      hprojcof hwlim
  have hxc : ∀ j : (idx pv W hW hT g f hf)ᵒᵈ,
      CompactSpace ((overlapDiagram Dv (pred pv W hW hT g f hf)).obj j) := fun _ ↦ hvc _
  have hspft : ∀ j : (idx pv W hW hT g f hf)ᵒᵈ, LocallyOfFiniteType (terminal.from
      ((specDiagram (rng pv W hW hT) (pred pv W hW hT g f hf)).obj j)) := by
    intro j
    have : Algebra.FiniteType ℤ (sub (OrderDual.ofDual j)) :=
      (Subalgebra.fg_iff_finiteType _).mp
        (isChartedSubalgebra_sub (fam pv W hW hT g f hf) (OrderDual.ofDual j)).fg
    exact locallyOfFiniteType_terminal_from_spec_of_finiteType _
  obtain ⟨A, hA, hcard⟩ := approximation_of_data_card pv W hW hT g f hf hS halpha hbeta hXr hYr
    hXW hYW hX hYlim hWlim hprojcof
  exact ⟨A, hA, hcard ▸ mk_idx_le pv W hW hT g f hf hWc⟩

end Stacks.GluedStep

end
