module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaThreefold
public import StacksFrontier.AlgebraicGeometry.Blowup.LocalDescent

/-!
# The involution of Hironaka's threefold

Let `k` be a field, `Y = ℙ³_k`, and let `V ⟶ Y` be Hironaka's threefold
(`Stacks.Examples.HironakaThreefold.hironakaThreefold`): over `Y - {Q}` the blow-up of the conic
`C` followed by the blow-up of the strict transform of `D`, over `Y - {P}` the same with `C` and
`D` exchanged, glued over `Y - {P, Q}`. Let `σ : Y ⟶ Y` be an involution which exchanges the
ideal sheaves of `C` and `D` and the two opens `Y - {P}` and `Y - {Q}` (for instance the
involution `[x : y : z : w] ↦ [y : x : w : z]`). Then `σ` lifts to an involution `τ` of `V`
over `σ`.

Over `Y - {Q}`, `σ` restricts to an isomorphism `Y - {Q} ≅ Y - {P}` pulling the pair `(D, C)`
back to the pair `(C, D)`, so it identifies the tower over `Y - {Q}` with the tower over
`Y - {P}`. The lift `τ` is this identification on the chart over `Y - {Q}` and its inverse on
the chart over `Y - {P}`; the two agree on the overlap because over `Y - {P, Q}` the threefold is
the single blow-up of `Y - {P, Q}` in `𝒥_C · 𝒥_D`, and two morphisms into a blow-up over the same
morphism to the base agree as soon as the centre pulls back to an effective Cartier divisor.

## Main definitions

* `Stacks.Examples.HironakaInvolution.chartIso`: the identification of the tower over `Y - {Q}`
  with the tower over `Y - {P}`, over `σ`.
* `Stacks.Examples.HironakaInvolution.threefoldInvolution`: the lift `τ : V ⟶ V` of `σ`.

## Main results

* `Stacks.Examples.HironakaInvolution.hom_ext_of_range_subset_opensAwayPQ`: two morphisms into
  `V` over the same morphism to `Y - {P, Q}`, one of them flat, are equal.
* `Stacks.Examples.HironakaInvolution.threefoldInvolution_hironakaMorphism`: `τ` lies over `σ`.
* `Stacks.Examples.HironakaInvolution.threefoldInvolution_comp_self`: `τ ≫ τ = 𝟙`, so `τ` is an
  isomorphism (`Stacks.Examples.HironakaInvolution.isIso_threefoldInvolution`).

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [Stacks Project, Tag 08KF](https://stacks.math.columbia.edu/tag/08KF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.TwoStepTower Stacks.Examples.HironakaConicIdealSheaf
open Stacks.Examples.HironakaThreefold

universe u

namespace Stacks.Examples.HironakaInvolution

/-! ### General facts -/

section General

/-- **Maps into a scheme isomorphic to a blow-up.** Let `p : X ⟶ Y` be isomorphic over `Y` to
`Bl_K B ⟶ B ⟶ Y` with `B ⟶ Y` a monomorphism. Two morphisms `g h : Z ⟶ X` with
`g ≫ p = h ≫ p` and `g` flat are equal: the centre `K` pulls back along `g` to a flat pullback of
the exceptional divisor, hence to an effective Cartier divisor. -/
theorem hom_ext_of_overIso_blowUp {X B Y Z : Scheme.{u}} (K : B.IdealSheafData) (j : B ⟶ Y)
    [Mono j] {p : X ⟶ Y} (e : Over.mk p ≅ Over.mk (blowUpToBase K ≫ j)) {g h : Z ⟶ X}
    [hg : Flat g] (hgh : g ≫ p = h ≫ p) : g = h := by
  have hw : e.hom.left ≫ blowUpToBase K ≫ j = p := by simpa using Over.w e.hom
  have hIso : IsIso e.hom.left := by
    change IsIso ((Over.forget _).map e.hom)
    infer_instance
  have hb : h ≫ e.hom.left ≫ blowUpToBase K = g ≫ e.hom.left ≫ blowUpToBase K := by
    rw [← cancel_mono j]
    simp only [Category.assoc, hw, hgh]
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor
      (K.comap (g ≫ e.hom.left ≫ blowUpToBase K)) := by
    have hP := Stacks.Divisors.isPullbackDefined_of_flat (g ≫ e.hom.left)
      (K.comap (blowUpToBase K)) (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal K)
    rw [← Category.assoc, Scheme.IdealSheafData.comap_comp]
    exact hP
  have hgh' := blowUp_hom_ext K _ hE (g ≫ e.hom.left) (h ≫ e.hom.left)
    (Category.assoc _ _ _) (by rw [Category.assoc, hb])
  exact (cancel_mono e.hom.left).mp hgh'

variable {Y Y' : Scheme.{u}} (σ : Y ⟶ Y') [IsIso σ] {U : Y.Opens} {U' : Y'.Opens}

/-- An isomorphism `σ : Y ⟶ Y'` restricts to an isomorphism `U ≅ U'` of opens with
`σ ⁻¹ᵁ U' = U`. -/
def opensIsoOfPreimageEq (h : σ ⁻¹ᵁ U' = U) : U.toScheme ≅ U'.toScheme :=
  (Y.isoOfEq h).symm ≪≫ asIso (σ ∣_ U')

/-- The restriction of `σ` to `U ≅ U'` lies over `σ`. -/
@[reassoc]
theorem opensIsoOfPreimageEq_hom_ι (h : σ ⁻¹ᵁ U' = U) :
    (opensIsoOfPreimageEq σ h).hom ≫ U'.ι = U.ι ≫ σ := by
  rw [opensIsoOfPreimageEq, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, Scheme.isoOfEq_inv_ι]

/-- The restriction to `U'` of an ideal sheaf, pulled back along `U ≅ U'`, is the restriction to
`U` of its pullback along `σ`. -/
theorem comap_comap_opensIsoOfPreimageEq (h : σ ⁻¹ᵁ U' = U) (I : Y'.IdealSheafData) :
    (I.comap U'.ι).comap (opensIsoOfPreimageEq σ h).hom = (I.comap σ).comap U.ι := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    opensIsoOfPreimageEq_hom_ι]

end General

/-! ### Uniqueness over `Y - {P, Q}` -/

variable (k : Type u) [Field k]

/-- The part of the chart over `Y - {Q}` lying over `Y - {P}`, an open of the chart. -/
abbrev overlapOpens : (chartAwayQ k).Opens :=
  towerAwayQ k ⁻¹ᵁ ((opensAwayQ k).ι ⁻¹ᵁ opensAwayP k)

/-- The part of the chart over `Y - {Q}` lying over `Y - {P}`, mapped into the chart over
`Y - {P}` by the gluing isomorphism. -/
def overlapToChartP : (overlapOpens k).toScheme ⟶ chartAwayP k :=
  (gluingDatum k).overlapι₂

/-- The gluing isomorphism lies over `Y`. -/
theorem overlapToChartP_towerAwayP :
    overlapToChartP k ≫ towerAwayP k ≫ (opensAwayP k).ι =
      (overlapOpens k).ι ≫ towerAwayQ k ≫ (opensAwayQ k).ι := by
  have h := (gluingDatum k).comm
  rw [← Category.assoc] at h
  exact h

/-- **Over `Y - {P, Q}` the threefold is the blow-up in `𝒥_C · 𝒥_D`**: the part of the tower over
`Y - {Q}` lying over `Y - {P}` is isomorphic over `Y` to the blow-up of `Y - {P, Q}` in the
product of the restricted conic ideals. -/
def overlapBlowUpIso :
    Over.mk ((overlapOpens k).ι ≫ towerAwayQ k ≫ (opensAwayQ k).ι) ≅
      Over.mk (blowUpToBase ((idealSheafC k).comap (opensAwayPQ k).ι *
        (idealSheafD k).comap (opensAwayPQ k).ι) ≫ (opensAwayPQ k).ι) :=
  restrictTowerIso (opensAwayQ k) _ (opensAwayPQ k) (overlapAwayQIso k) (overlapAwayQIso_hom_ι k)
      (idealSheafC k) (idealSheafD k) ≪≫
    overCompIso (strictTowerMulIso (disjoint_supportSet_comap_opensAwayPQ k)) (opensAwayPQ k).ι

/-- A morphism into `V` whose composite with `f` lands in `Y - {P, Q}` factors through the part
of the chart over `Y - {Q}` lying over `Y - {P}`. -/
theorem range_subset_range_overlapOpens_ι {Z : Scheme.{u}} (c : Z ⟶ hironakaThreefold k)
    (hc : Set.range (c ≫ hironakaMorphism k) ⊆ (opensAwayPQ k : Set (projectiveThreeSpace k))) :
    Set.range c ⊆ Set.range ((overlapOpens k).ι ≫ ιAwayQ k) := by
  rintro _ ⟨z, rfl⟩
  have hz : (c ≫ hironakaMorphism k) z ∈ opensAwayPQ k := hc ⟨z, rfl⟩
  rw [← opensAwayQ_inf_opensAwayP, TopologicalSpace.Opens.mem_inf] at hz
  obtain ⟨hzQ, hzP⟩ := hz
  have hQ : c z ∈ hironakaMorphism k ⁻¹ᵁ opensAwayQ k := by
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply]
    exact hzQ
  have h₁ : (ιAwayQ k).opensRange = hironakaMorphism k ⁻¹ᵁ opensAwayQ k :=
    (gluingDatum k).opensRange_ι₁
  obtain ⟨x, hx⟩ : c z ∈ Set.range (ιAwayQ k) := by
    have h₂ : c z ∈ (ιAwayQ k).opensRange := by
      rw [h₁]
      exact hQ
    exact h₂
  have h₄ : (towerAwayQ k ≫ (opensAwayQ k).ι) x = hironakaMorphism k (c z) := by
    rw [← hx, ← Scheme.Hom.comp_apply, ιAwayQ_hironakaMorphism]
  have hx' : x ∈ overlapOpens k := by
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, h₄,
      ← Scheme.Hom.comp_apply]
    exact hzP
  obtain ⟨y, hy⟩ : x ∈ Set.range (overlapOpens k).ι := by
    rw [Scheme.Opens.range_ι]
    exact hx'
  refine ⟨y, ?_⟩
  rw [Scheme.Hom.comp_apply, hy]
  exact hx

/-- **Uniqueness over `Y - {P, Q}`.** Two morphisms `a b : Z ⟶ V` with `a ≫ f = b ≫ f` landing
over `Y - {P, Q}`, with `a` flat, are equal: there `V` is the blow-up in `𝒥_C · 𝒥_D`, whose
centre pulls back along the flat `a` to an effective Cartier divisor. -/
theorem hom_ext_of_range_subset_opensAwayPQ {Z : Scheme.{u}} {a b : Z ⟶ hironakaThreefold k}
    [Flat a] (hab : a ≫ hironakaMorphism k = b ≫ hironakaMorphism k)
    (ha : Set.range (a ≫ hironakaMorphism k) ⊆ (opensAwayPQ k : Set (projectiveThreeSpace k))) :
    a = b := by
  have hb : Set.range (b ≫ hironakaMorphism k) ⊆ (opensAwayPQ k : Set (projectiveThreeSpace k)) :=
    by rw [← hab]; exact ha
  have hra := range_subset_range_overlapOpens_ι k a ha
  have hrb := range_subset_range_overlapOpens_ι k b hb
  have hfa : Flat (IsOpenImmersion.lift ((overlapOpens k).ι ≫ ιAwayQ k) a hra) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
      (IsOpenImmersion.isPullback_lift_id a ((overlapOpens k).ι ≫ ιAwayQ k) hra).flip ‹_›
  obtain ⟨a', ha', hfa'⟩ : ∃ a', a' ≫ ((overlapOpens k).ι ≫ ιAwayQ k) = a ∧ Flat a' :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hra, hfa⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' ≫ ((overlapOpens k).ι ≫ ιAwayQ k) = b :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrb⟩
  subst ha' hb'
  simp only [Category.assoc] at hab
  rw [ιAwayQ_hironakaMorphism] at hab
  rw [hom_ext_of_overIso_blowUp _ (opensAwayPQ k).ι (overlapBlowUpIso k) (hg := hfa') hab]

/-! ### The lift of an involution of `ℙ³` -/

variable (σ : projectiveThreeSpace k ⟶ projectiveThreeSpace k) [IsIso σ]
  (hσσ : σ ≫ σ = 𝟙 _) (hC : (idealSheafC k).comap σ = idealSheafD k)
  (hD : (idealSheafD k).comap σ = idealSheafC k)
  (hQ : σ ⁻¹ᵁ opensAwayQ k = opensAwayP k) (hP : σ ⁻¹ᵁ opensAwayP k = opensAwayQ k)

/-- The restriction of `σ` to an isomorphism `Y - {Q} ≅ Y - {P}`. -/
abbrev opensAwayQIso : (opensAwayQ k).toScheme ≅ (opensAwayP k).toScheme :=
  opensIsoOfPreimageEq σ hP

/-- **The identification of the two towers along `σ`**, over `Y - {P}`: the tower over `Y - {Q}`
followed by `σ : Y - {Q} ≅ Y - {P}` is the tower over `Y - {P}`. -/
def chartOverIso :
    Over.mk (towerAwayQ k ≫ (opensAwayQIso k σ hP).hom) ≅ Over.mk (towerAwayP k) :=
  have hI : (idealSheafC k).comap (opensAwayQ k).ι =
      ((idealSheafD k).comap (opensAwayP k).ι).comap (opensAwayQIso k σ hP).hom := by
    rw [comap_comap_opensIsoOfPreimageEq, hD]
  have hJ : (idealSheafD k).comap (opensAwayQ k).ι =
      ((idealSheafC k).comap (opensAwayP k).ι).comap (opensAwayQIso k σ hP).hom := by
    rw [comap_comap_opensIsoOfPreimageEq, hC]
  overCompIso (towerEqIso hI hJ) (opensAwayQIso k σ hP).hom ≪≫
    towerIsoOfIso (opensAwayQIso k σ hP) ((idealSheafD k).comap (opensAwayP k).ι)
      ((idealSheafC k).comap (opensAwayP k).ι)

/-- **The identification of the two charts along `σ`.** -/
def chartIso : chartAwayQ k ≅ chartAwayP k :=
  (Over.forget _).mapIso (chartOverIso k σ hC hD hP)

/-- The identification of the two charts lies over `σ`. -/
@[reassoc]
theorem chartIso_hom_towerAwayP :
    (chartIso k σ hC hD hP).hom ≫ towerAwayP k ≫ (opensAwayP k).ι =
      towerAwayQ k ≫ (opensAwayQ k).ι ≫ σ := by
  have hw : (chartIso k σ hC hD hP).hom ≫ towerAwayP k =
      towerAwayQ k ≫ (opensAwayQIso k σ hP).hom :=
    Over.w (chartOverIso k σ hC hD hP).hom
  rw [← Category.assoc, hw, Category.assoc, opensIsoOfPreimageEq_hom_ι]

include hσσ in
/-- The inverse identification of the two charts lies over `σ`, as `σ` is an involution. -/
@[reassoc]
theorem chartIso_inv_towerAwayQ :
    (chartIso k σ hC hD hP).inv ≫ towerAwayQ k ≫ (opensAwayQ k).ι =
      towerAwayP k ≫ (opensAwayP k).ι ≫ σ := by
  have h : (chartIso k σ hC hD hP).inv ≫ towerAwayQ k ≫ (opensAwayQ k).ι ≫ σ =
      towerAwayP k ≫ (opensAwayP k).ι := by
    rw [← chartIso_hom_towerAwayP k σ hC hD hP, Iso.inv_hom_id_assoc]
  calc _ = ((chartIso k σ hC hD hP).inv ≫ towerAwayQ k ≫ (opensAwayQ k).ι ≫ σ) ≫ σ := by
        simp only [Category.assoc, hσσ, Category.comp_id]
    _ = _ := by rw [h, Category.assoc]

omit [IsIso σ] in
include hQ hP in
/-- `σ` maps `Y - {P, Q}` into itself. -/
theorem range_comp_subset_opensAwayPQ {Z : Scheme.{u}} (g : Z ⟶ projectiveThreeSpace k)
    (hg : Set.range g ⊆ (opensAwayPQ k : Set (projectiveThreeSpace k))) :
    Set.range (g ≫ σ) ⊆ (opensAwayPQ k : Set (projectiveThreeSpace k)) := by
  rintro _ ⟨z, rfl⟩
  have h : g z ∈ opensAwayQ k ⊓ opensAwayP k := by
    rw [opensAwayQ_inf_opensAwayP]
    exact hg ⟨z, rfl⟩
  rw [TopologicalSpace.Opens.mem_inf] at h
  have h₁ : g z ∈ σ ⁻¹ᵁ opensAwayQ k := by
    rw [hQ]
    exact h.2
  have h₂ : g z ∈ σ ⁻¹ᵁ opensAwayP k := by
    rw [hP]
    exact h.1
  change (g ≫ σ) z ∈ opensAwayPQ k
  rw [← opensAwayQ_inf_opensAwayP, TopologicalSpace.Opens.mem_inf, Scheme.Hom.comp_apply]
  exact ⟨h₁, h₂⟩

include hσσ hQ in
/-- The two lifts of `σ` agree on the overlap of the two charts. -/
theorem overlap_chartIso_compat :
    (overlapOpens k).ι ≫ (chartIso k σ hC hD hP).hom ≫ ιAwayP k =
      overlapToChartP k ≫ (chartIso k σ hC hD hP).inv ≫ ιAwayQ k := by
  refine hom_ext_of_range_subset_opensAwayPQ k ?_ ?_
  · simp only [Category.assoc]
    rw [ιAwayP_hironakaMorphism, chartIso_hom_towerAwayP, ιAwayQ_hironakaMorphism,
      chartIso_inv_towerAwayQ k σ hσσ]
    have h := congrArg (· ≫ σ) (overlapToChartP_towerAwayP k)
    simp only [Category.assoc] at h ⊢
    exact h.symm
  · have hr : Set.range ((overlapOpens k).ι ≫ towerAwayQ k ≫ (opensAwayQ k).ι) ⊆
        (opensAwayPQ k : Set (projectiveThreeSpace k)) := by
      have h := (gluingDatum k).range_overlap_subset
      rw [Scheme.Opens.range_ι] at h
      rw [← opensAwayQ_inf_opensAwayP]
      exact h
    have h := range_comp_subset_opensAwayPQ k σ hQ hP _ hr
    simp only [Category.assoc]
    rw [ιAwayP_hironakaMorphism, chartIso_hom_towerAwayP]
    simpa only [Category.assoc] using h

/-- **The lift of `σ` to Hironaka's threefold**: on the chart over `Y - {Q}` it is the
identification `chartIso` with the chart over `Y - {P}`, and on the chart over `Y - {P}` its
inverse. -/
def threefoldInvolution : hironakaThreefold k ⟶ hironakaThreefold k :=
  Scheme.gluePairDesc ((gluingDatum k).overlap₁).ι (gluingDatum k).overlapι₂
    ((chartIso k σ hC hD hP).hom ≫ ιAwayP k) ((chartIso k σ hC hD hP).inv ≫ ιAwayQ k)
    (overlap_chartIso_compat k σ hσσ hC hD hQ hP)

/-- On the chart over `Y - {Q}`, the lift of `σ` is `chartIso`. -/
@[reassoc]
theorem ιAwayQ_threefoldInvolution :
    ιAwayQ k ≫ threefoldInvolution k σ hσσ hC hD hQ hP = (chartIso k σ hC hD hP).hom ≫ ιAwayP k :=
  Scheme.gluePairInl_desc ((gluingDatum k).overlap₁).ι (gluingDatum k).overlapι₂ _ _ _

/-- On the chart over `Y - {P}`, the lift of `σ` is the inverse of `chartIso`. -/
@[reassoc]
theorem ιAwayP_threefoldInvolution :
    ιAwayP k ≫ threefoldInvolution k σ hσσ hC hD hQ hP = (chartIso k σ hC hD hP).inv ≫ ιAwayQ k :=
  Scheme.gluePairInr_desc ((gluingDatum k).overlap₁).ι (gluingDatum k).overlapι₂ _ _ _

/-- **The lift of `σ` lies over `σ`.** -/
@[reassoc]
theorem threefoldInvolution_hironakaMorphism :
    threefoldInvolution k σ hσσ hC hD hQ hP ≫ hironakaMorphism k = hironakaMorphism k ≫ σ := by
  refine Scheme.gluePair_hom_ext _ _ ?_ ?_
  · change ιAwayQ k ≫ _ = ιAwayQ k ≫ _
    simp only [ιAwayQ_threefoldInvolution_assoc, ιAwayP_hironakaMorphism,
      ιAwayQ_hironakaMorphism_assoc]
    rw [chartIso_hom_towerAwayP]
    try simp only [Category.assoc]
  · change ιAwayP k ≫ _ = ιAwayP k ≫ _
    simp only [ιAwayP_threefoldInvolution_assoc, ιAwayQ_hironakaMorphism,
      ιAwayP_hironakaMorphism_assoc]
    rw [chartIso_inv_towerAwayQ k σ hσσ]
    try simp only [Category.assoc]

/-- **The lift of `σ` is an involution.** -/
@[reassoc]
theorem threefoldInvolution_comp_self :
    threefoldInvolution k σ hσσ hC hD hQ hP ≫ threefoldInvolution k σ hσσ hC hD hQ hP = 𝟙 _ := by
  refine Scheme.gluePair_hom_ext _ _ ?_ ?_
  · change ιAwayQ k ≫ _ = ιAwayQ k ≫ _
    simp only [ιAwayQ_threefoldInvolution_assoc, ιAwayP_threefoldInvolution,
      Iso.hom_inv_id_assoc, Category.comp_id]
  · change ιAwayP k ≫ _ = ιAwayP k ≫ _
    simp only [ιAwayP_threefoldInvolution_assoc, ιAwayQ_threefoldInvolution,
      Iso.inv_hom_id_assoc, Category.comp_id]

/-- **The lift of `σ` is an isomorphism**, being its own inverse. -/
instance isIso_threefoldInvolution : IsIso (threefoldInvolution k σ hσσ hC hD hQ hP) :=
  ⟨⟨threefoldInvolution k σ hσσ hC hD hQ hP, threefoldInvolution_comp_self k σ hσσ hC hD hQ hP,
    threefoldInvolution_comp_self k σ hσσ hC hD hQ hP⟩⟩

/-- **The lift of `σ` is an involution over `Y - {P, Q}`**, the part of `V` lying over
`Y - {P, Q}`. -/
theorem threefoldInvolution_comp_self_overlap :
    (hironakaMorphism k ⁻¹ᵁ opensAwayPQ k).ι ≫ threefoldInvolution k σ hσσ hC hD hQ hP ≫
      threefoldInvolution k σ hσσ hC hD hQ hP = (hironakaMorphism k ⁻¹ᵁ opensAwayPQ k).ι := by
  rw [threefoldInvolution_comp_self, Category.comp_id]

end Stacks.Examples.HironakaInvolution

end
