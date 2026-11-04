module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepCardinality
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepFull

/-!
# The size of the index of the one-affine-open step of Tag 07RN

`AlgebraicGeometry.exists_finiteTypeApproximation_of_sup_affine` extends a directed system of
finite-type schemes approximating a quasi-compact open `V` of a quasi-separated scheme `S` to one
approximating `S`, as soon as `V` together with one affine open covers `S`. This file records that
the index of the extended system has cardinality at most `max #I S.size`, from the bound
`Stacks.GluedStep.exists_approximation_card` of
`StacksFrontier/AlgebraicGeometry/LimitApproxClose/StepCardinality.lean`.

## Main results

* `AlgebraicGeometry.exists_approximation_of_lateStage_card`
* `AlgebraicGeometry.exists_finiteTypeApproximation_of_sup_affine_card`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks Stacks.GluedStep Stacks.StageSubalgebra

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.FiniteTypeApproximation.indexPreorder
  Scheme.FiniteTypeApproximation.indexNonempty Scheme.FiniteTypeApproximation.indexDirected

/-- `AlgebraicGeometry.exists_approximation_of_lateStage`, with the size of the new index bounded
by those of the old index and of the scheme. -/
theorem exists_approximation_of_lateStage_card {K : Type u} [Preorder K] [Nonempty K]
    [IsDirected K (· ≤ ·)]
    {Dv : Kᵒᵈ ⥤ Scheme.{u}} [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)]
    [∀ a, LocallyOfFiniteType (terminal.from (Dv.obj a))]
    [∀ a, QuasiCompact (terminal.from (Dv.obj a))]
    {S : Scheme.{u}} {V Y : S.Opens} [IsAffine (Y : Scheme.{u})]
    (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
    (W : ∀ a, (Dv.obj a).Opens)
    (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
    (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y)
    (hWc : ∀ a : Kᵒᵈ, IsCompact ((W a : (Dv.obj a).Opens) : Set (Dv.obj a)))
    (hqs : ∀ a : Kᵒᵈ, QuasiSeparatedSpace (Dv.obj a))
    (hS : V ⊔ Y = ⊤)
    (hpv : IsLimit (Cone.mk (V : Scheme.{u}) pv))
    (hovl : IsLimit (cw pv W hW hT))
    {n : ℕ} (g : Fin n → Γ((Y : Scheme.{u}), ⊤))
    (hin : ∀ l, (Y : Scheme.{u}).basicOpen (g l) ≤
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange)
    (hgcov : (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange ≤
      ⨆ l, (Y : Scheme.{u}).basicOpen (g l))
    (k₁ : K) (f₁ : Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁), ⊤))
    (hf₁ : ∀ l, (tau pv W hW hT).app (op (OrderDual.toDual k₁)) (f₁ l) =
      str (V := V) (Y := Y) (g l))
    (haff₁ : ∀ l, IsAffineOpen
      (((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁)).basicOpen (f₁ l)))
    (hcov₁ : ⨆ l, ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k₁)).basicOpen (f₁ l) = ⊤) :
    ∃ A : Scheme.FiniteTypeApproximation Dv S V pv,
      (∀ k : K, ∃ j : A.indexType, k ≤ A.index j) ∧
        Cardinal.mk A.indexType ≤ max (Cardinal.mk K) S.size := by
  classical
  have hne₂ : Nonempty ↥(Set.Ici k₁) := Stacks.Order.nonempty_Ici k₁
  have hdir₂ : IsDirected ↥(Set.Ici k₁) (· ≤ ·) := Stacks.Order.isDirected_Ici k₁
  have hpv₂ : IsLimit (Cone.mk (V : Scheme.{u}) (laterPv pv k₁)) :=
    isLimitWhiskerOfCofinal (laterStages k₁) (exists_le_laterStages k₁) hpv
  obtain ⟨A, hA, hcard⟩ := Stacks.GluedStep.exists_approximation_card (laterPv pv k₁)
    (laterW W k₁) (laterW_compatible W hW k₁) (laterT pv W hT k₁) (fun a ↦ hWc _) hS
    hpv₂ (isLimit_laterCw pv W hW hT k₁ hovl)
    (isColimit_Γ_mapCocone_laterCw pv W hW hT k₁ hovl hWc hqs)
    g hin hgcov (laterFam W hW k₁ f₁)
    (tau_laterFam pv W hW hT k₁ g f₁ hf₁) (fun u l ↦ map_laterFam W hW k₁ f₁ u l)
    (isAffineOpen_basicOpen_laterFam W hW k₁ f₁ haff₁)
    (iSup_basicOpen_laterFam_eq_top W hW k₁ f₁ hcov₁)
  exact ⟨A.ofWhisker (laterStages k₁),
    exists_le_comp A.index (laterStages k₁) hA (exists_le_laterStages k₁),
    hcard.trans (max_le_max (Cardinal.mk_subtype_le _) le_rfl)⟩

/-- `AlgebraicGeometry.exists_finiteTypeApproximation_of_sup_affine`, with the size of the new
index bounded by those of the old index and of the scheme. -/
theorem exists_finiteTypeApproximation_of_sup_affine_card {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵈ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵈ} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
    [∀ i, QuasiCompact (terminal.from (D.obj i))]
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (V Y : S.Opens) [CompactSpace (V : Scheme.{u})]
    (hY : IsAffineOpen Y) (hS : V ⊔ Y = ⊤)
    (p : (Functor.const Iᵒᵈ).obj (V : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (V : Scheme.{u}) p)) :
    ∃ A : Scheme.FiniteTypeApproximation D S V p, (∀ i : I, ∃ j : A.indexType, i ≤ A.index j) ∧
      Cardinal.mk A.indexType ≤ max (Cardinal.mk I) S.size := by
  classical
  have hYaff : IsAffine (Y : Scheme.{u}) := hY
  -- step (i): the overlap descends to a compatible family of quasi-compact opens
  obtain ⟨i₀, V₀, hV₀c, hV₀⟩ := exists_stage_preimage_eq_inf D V p hp Y hY.isCompact
  have hne₁ : Nonempty ↥(Set.Ici i₀) := Stacks.Order.nonempty_Ici i₀
  have hdir₁ : IsDirected ↥(Set.Ici i₀) (· ≤ ·) := Stacks.Order.isDirected_Ici i₀
  have hqs₁ : ∀ a : (↥(Set.Ici i₀))ᵒᵈ, QuasiSeparatedSpace ((laterDiagram D i₀).obj a) :=
    fun _ ↦ quasiSeparatedSpace_of_locallyOfFiniteType_terminal _
  have hT₁ : ∀ a, (laterPv p i₀).app a ⁻¹ᵁ laterPreimage D V₀ a = V.ι ⁻¹ᵁ Y :=
    laterPreimage_preimage_eq D V p V₀ hV₀
  have hpv₁ : IsLimit (Cone.mk (V : Scheme.{u}) (laterPv p i₀)) :=
    isLimitWhiskerOfCofinal (laterStages i₀) (exists_le_laterStages i₀) hp
  have hovl₁ : IsLimit (cw (laterPv p i₀) (laterPreimage D V₀)
      (laterPreimage_compatible D V₀) hT₁ (Y := Y)) :=
    isLimitOverlapCone V Y (laterPv p i₀) (laterPreimage D V₀)
      (laterPreimage_compatible D V₀) hT₁ (isLimitLaterCompatibleOpensCone D V p hp V₀ hV₀)
  have hmc₁ : ∀ a, CompactSpace ((mdl (Dv := laterDiagram D i₀) (laterPreimage D V₀)
      (laterPreimage_compatible D V₀)).obj a) :=
    compactSpace_compatibleOpensDiagram_obj _ (laterPreimage_compatible D V₀)
      (isCompact_laterPreimage D V₀ hV₀c)
  have hmqs₁ : ∀ a, QuasiSeparatedSpace ((mdl (Dv := laterDiagram D i₀) (laterPreimage D V₀)
      (laterPreimage_compatible D V₀)).obj a) :=
    quasiSeparatedSpace_compatibleOpensDiagram_obj _ (laterPreimage_compatible D V₀) hqs₁
  have hzc : CompactSpace ((V ⊓ Y : S.Opens) : Scheme.{u}) :=
    Scheme.compactSpace_of_isLimit _ _ hovl₁
  -- the finite family of sections of the affine open whose standard opens cover the overlap
  obtain ⟨n, g, hin, hgcov⟩ :=
    exists_fin_basicOpen_le_opensRange (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y))
  -- step (ii): the charting family at one stage
  obtain ⟨j₁, f₁, hf₁, haff₁, hcov₁⟩ :=
    exists_stage_affine_basicOpen_cover_of_opensRange _ _ hovl₁
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)) g hin hgcov
  obtain ⟨A, hA, hcard⟩ := exists_approximation_of_lateStage_card (laterPv p i₀)
    (laterPreimage D V₀)
    (laterPreimage_compatible D V₀) hT₁ (isCompact_laterPreimage D V₀ hV₀c) hqs₁ hS hpv₁ hovl₁
    g hin hgcov (OrderDual.ofDual j₁) f₁ hf₁ haff₁ hcov₁
  exact ⟨A.ofWhisker (laterStages i₀),
    exists_le_comp A.index (laterStages i₀) hA (exists_le_laterStages i₀),
    hcard.trans (max_le_max (Cardinal.mk_subtype_le _) le_rfl)⟩

end AlgebraicGeometry

end
