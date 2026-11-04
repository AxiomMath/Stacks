module

public import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupOpenCover
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCover
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChainLength
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModelSingularPoint

/-!
# Resolving the standard nodal model by a chain of blowups at closed points

Let `R` be a discrete valuation ring with uniformizer `π`, let `S = Spec R`, and for `n ≥ 0` let
`X = Spec R[x, y]/(xy - πⁿ)` be the standard nodal model of [Stacks, Tag 0CDC]. This file carries
out the induction on `n` that closes the tag: there is a sequence of blowups at closed points
```
X_{⌊n/2⌋} → … → X₁ → X₀ = X
```
such that `X_{⌊n/2⌋} → S` is at-worst-nodal of relative dimension one and `X_{⌊n/2⌋}` is
regular.

## Main results

* `Stacks.exists_pointBlowupChainOfLength_nodalModel` — **the chain, for every `n`.**

## Implementation notes

The induction is not on the model itself but on a *patch*: a scheme `X` over `S`, at-worst-nodal
of relative dimension one, carrying the standard nodal model of exponent `m` as an open
subscheme over `S` and covered by that chart together with a regular open which avoids the
origin of the chart. For `m ≤ 1` the chart is itself regular, so `X` is regular and the chain is
empty. For `m ≥ 2` the origin of the chart is a closed point of `X`, and blowing `X` up there
produces a patch of exponent `m - 2`:

* over the chart, the blowup is the blowup of the standard nodal model at its origin
  (`Stacks.nonempty_over_iso_blowUpToBase_nodalModelOriginPoint`), that is
  `Stacks.nodalModelBlowup`; this is flat base change along the chart,
  `AlgebraicGeometry.exists_isOpenImmersion_blowUp_comap` ([Stacks, Tag 0805]), together with
  `AlgebraicGeometry.pointIdeal_comap_isOpenImmersion`;
* over the regular open the blowup is an isomorphism, the centre being disjoint from it
  ([Stacks, Tag 02OS]), so that open survives as a regular open of the blowup;
* the new chart is the central chart of `Stacks.nodalModelBlowup`, which is the standard nodal
  model of exponent `m - 2` (`Stacks.exists_isOpenImmersion_nodalModel_sub_two`), and the two
  outer charts are regular, so they join the regular open;
* the new origin is again outside the new regular open, because its local ring is not regular
  (`Stacks.not_isRegularLocalRing_stalk_of_asIdeal_eq_nodalModelOrigin`) while every local ring
  of a regular open is.

Since `1 + ⌊(m - 2)/2⌋ = ⌊m/2⌋` for `m ≥ 2`, the lengths add up. The count is carried by
`Stacks.ResolutionOfSurfaces.PointBlowupChainOfLength`, the length-indexed form of
`Stacks.ResolutionOfSurfaces.PointBlowupChain`.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A *patch of exponent `m`*: a scheme `X` over `S = Spec R`, at-worst-nodal of relative
dimension one, carrying the standard nodal model of exponent `m` as an open subscheme over `S`,
and covered by that chart together with a regular open which — when the chart is singular, that
is when `m ≥ 2` — avoids the origin of the chart. This is the hypothesis the induction on `m`
of [Stacks, Tag 0CDC] propagates. -/
private structure Patch (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {π : R} (hπ : Irreducible π) (m : ℕ) (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of R)) where
  /-- The nodal chart. -/
  chart : nodalModel R π m ⟶ X
  /-- The chart is an open subscheme. -/
  isOpenImmersion_chart : IsOpenImmersion chart
  /-- The chart lies over `S` by the structure morphism of the model. -/
  chart_comp : chart ≫ f = nodalModelHom R π m
  /-- `X ⟶ S` is at-worst-nodal of relative dimension one. -/
  nodal : IsAtWorstNodalOfRelativeDimensionOne f
  /-- The regular open. -/
  reg : X.Opens
  /-- It is regular. -/
  isRegular_reg : IsRegular reg.toScheme
  /-- The chart and the regular open cover `X`. -/
  cover : chart.opensRange ⊔ reg = ⊤
  /-- When the chart is singular its origin lies outside the regular open. -/
  origin_notMem : ∀ h1 : 1 ≤ m, 2 ≤ m →
    chart.base (nodalModelOriginPoint (isMaximal_span_singleton_of_irreducible hπ) h1) ∉ reg

/-- The empty open of a scheme is regular: it has no points. -/
private theorem isRegular_bot (X : Scheme.{u}) : IsRegular (⊥ : X.Opens).toScheme :=
  fun x ↦ absurd x.2 (by simp)

/-- **The induction of [Stacks, Tag 0CDC].** A patch of exponent `m` is resolved by `⌊m/2⌋`
blowups at closed points. -/
private theorem exists_chain_of_patch {π : R} (hπ : Irreducible π) (m : ℕ) :
    ∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)), Patch R hπ m X f →
      ∃ (Y : Scheme.{u}) (g : Y ⟶ X),
        PointBlowupChainOfLength X Set.univ (m / 2) Y g ∧
        IsAtWorstNodalOfRelativeDimensionOne (g ≫ f) ∧ IsRegular Y := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro X f P
  have := P.isOpenImmersion_chart
  rcases Nat.lt_or_ge m 2 with hmlt | hm
  · refine ⟨X, 𝟙 X, ?_, ?_, ?_⟩
    · rw [show m / 2 = 0 by omega]
      exact .refl
    · rw [Category.id_comp]
      exact P.nodal
    · refine isRegular_of_sup_eq_top P.chart.opensRange P.reg
        (isRegular_opensRange P.chart ?_) P.isRegular_reg P.cover
      interval_cases m
      · exact isRegular_nodalModel_zero R π
      · exact isRegular_nodalModel_one hπ
  -- The inductive step.
  set hmax := isMaximal_span_singleton_of_irreducible hπ with hmaxdef
  have h1 : 1 ≤ m := by omega
  set ι := P.chart with hιdef
  set o := nodalModelOriginPoint hmax h1 with hodef
  have hoC : IsClosed ({o} : Set (nodalModel R π m)) :=
    isClosed_singleton_nodalModelOriginPoint hmax h1
  have hpW : ι.base o ∉ P.reg := P.origin_notMem h1 hm
  have hor : ∀ {Z : Scheme.{u}} (U V : Z.Opens), U ⊔ V = ⊤ → ∀ z, z ∈ U ∨ z ∈ V :=
    fun U V h z ↦ show z ∈ U ⊔ V by rw [h]; trivial
  -- The origin of the chart is a closed point of `X`.
  have hpC : IsClosed ({ι.base o} : Set X) := by
    rw [← isOpen_compl_iff]
    have hset : ({ι.base o}ᶜ : Set X) = ι.base '' ({o}ᶜ) ∪ (P.reg : Set X) := by
      refine Set.Subset.antisymm (fun z hz ↦ ?_) ?_
      · rcases hor _ _ P.cover z with hzi | hzr
        · obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hzi
          refine Or.inl ⟨y, fun hyo ↦ ?_, hy⟩
          exact hz (by rw [Set.mem_singleton_iff, ← hy, hyo])
        · exact Or.inr hzr
      · rintro z (⟨y, hy, rfl⟩ | hzr)
        · exact fun hz ↦ hy (ι.isOpenEmbedding.injective (Set.mem_singleton_iff.mp hz))
        · exact fun hz ↦ hpW (by rw [← Set.mem_singleton_iff.mp hz]; exact hzr)
    rw [hset]
    exact (ι.isOpenEmbedding.isOpenMap _ hoC.isOpen_compl).union P.reg.isOpen
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{ι.base o}, hpC⟩ : Closeds X) with hMdef
  set b := AlgebraicGeometry.blowUpToBase M with hbdef
  have hsupp : (M.support : Set X) = {ι.base o} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  -- The blowup at that point is one step of a chain.
  have hstep : PointBlowupChainOfLength X Set.univ 1 (AlgebraicGeometry.blowUp M) b := by
    have hs := (PointBlowupChainOfLength.refl (X := X) (T := Set.univ)).step
      (ι.base o) hpC (Set.mem_univ _)
    simpa using hs
  -- Over the chart, the blowup is the blowup of the model at its origin.
  obtain ⟨hcmp, hcmpoi, hcmpw, hcmprange⟩ :
      ∃ hj : AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal
            (⟨{o}, hoC⟩ : Closeds (nodalModel R π m))) ⟶ AlgebraicGeometry.blowUp M,
        IsOpenImmersion hj ∧
        AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
            (⟨{o}, hoC⟩ : Closeds (nodalModel R π m))) ≫ ι = hj ≫ b ∧
        Set.range hj.base = b ⁻¹' Set.range ι.base := by
    rw [← pointIdeal_comap_isOpenImmersion ι o hoC hpC]
    exact exists_isOpenImmersion_blowUp_comap M ι
  have := hcmpoi
  obtain ⟨κ⟩ := nonempty_over_iso_blowUpToBase_nodalModelOriginPoint hmax h1
  set e := (Over.forget (nodalModel R π m)).mapIso κ with hedef
  set j₁ := e.hom ≫ hcmp with hj1def
  have : IsOpenImmersion j₁ := IsOpenImmersion.comp _ _
  have hj1w : j₁ ≫ b = nodalModelBlowupHom R π m ≫ ι := by
    rw [hj1def, Category.assoc, ← hcmpw, ← Category.assoc]
    exact congrArg (· ≫ ι) (Over.w κ.hom)
  have hj1toBase : j₁ ≫ (b ≫ f) = nodalModelBlowupToBase R π m := by
    rw [← Category.assoc, hj1w, Category.assoc, P.chart_comp]
    rfl
  have hj1range : Set.range j₁.base = Set.range hcmp.base := by
    rw [hj1def]
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    rw [(surjective_base_of_isIso e.hom).range_eq, Set.image_univ]
  -- The new chart: the central chart of the blowup, the model of exponent `m - 2`.
  obtain ⟨jc, hjcoi, hjcw, hjcrange⟩ := exists_isOpenImmersion_nodalModel_sub_two hπ.ne_zero hm
  have := hjcoi
  set ι₁ := jc ≫ j₁ with hι₁def
  have : IsOpenImmersion ι₁ := IsOpenImmersion.comp _ _
  have hι₁comp : ι₁ ≫ (b ≫ f) = nodalModelHom R π (m - 2) := by
    rw [hι₁def, Category.assoc, hj1toBase]
    exact hjcw
  -- The new regular open: the old one pulled back, plus the two outer charts.
  have hregsub : (P.reg : Set X) ⊆ (M.support : Set X)ᶜ := by
    rw [hsupp]
    intro z hz hz'
    exact hpW (by rw [← Set.mem_singleton_iff.mp hz']; exact hz)
  have hbiso : IsIso (b ∣_ P.reg) :=
    isIso_blowUpToBase_restrict_of_subset_compl_support M P.reg hregsub
  have hregpre : IsRegular (b ⁻¹ᵁ P.reg).toScheme :=
    IsRegular.of_iso (asIso (b ∣_ P.reg)) P.isRegular_reg
  have houter : ∀ i : Fin 3, i ≠ 0 →
      IsRegular (Spec (CommRingCat.of
        (affineBlowup (nodalCenter R π (π ^ m)) (nodalCenterGen R π m i)))) := by
    intro i hi
    have hring : IsRegularRing
        (affineBlowup (nodalCenter R π (π ^ m)) (nodalCenterGen R π m i)) := by
      fin_cases i
      · exact absurd rfl hi
      · obtain ⟨ee, -⟩ := exists_ringEquiv_affineBlowup_nodalCenterGen_one hπ.ne_zero hm
        exact (isRegularRing_nodalChartRing hπ).of_ringEquiv ee.symm
      · obtain ⟨ee, -⟩ := exists_ringEquiv_affineBlowup_nodalCenterGen_two hπ.ne_zero hm
        exact (isRegularRing_nodalChartRing hπ).of_ringEquiv ee.symm
    exact @isRegular_spec_of_isRegularRing _ _ hring
  set Ω : ULift.{u} (Fin 3) → (AlgebraicGeometry.blowUp M).Opens := fun k =>
    if k.down = 0 then b ⁻¹ᵁ P.reg
    else (nodalModelBlowupChart R π m k.down ≫ j₁).opensRange with hΩdef
  set W₁ := ⨆ k, Ω k with hW1def
  have hΩreg : ∀ k, IsRegular (Ω k).toScheme := by
    intro k
    by_cases hk : k.down = 0
    · simpa [hΩdef, hk] using hregpre
    · have : Ω k = (nodalModelBlowupChart R π m k.down ≫ j₁).opensRange := by
        simp [hΩdef, hk]
      rw [this]
      exact isRegular_opensRange _ (houter k.down hk)
  have hW1reg : IsRegular W₁.toScheme := isRegular_iSup_opens Ω hΩreg
  -- The new chart and the new regular open cover the blowup.
  have hj1cover : j₁.opensRange ⊔ (b ⁻¹ᵁ P.reg) = ⊤ := by
    refine le_antisymm le_top fun z _ ↦ ?_
    rcases hor _ _ P.cover (b.base z) with hz | hz
    · refine Or.inl ?_
      have hz' : b.base z ∈ Set.range ι.base := Scheme.Hom.mem_opensRange.mp hz
      have hzr : z ∈ Set.range j₁.base := by rw [hj1range, hcmprange]; exact hz'
      exact Scheme.Hom.mem_opensRange.mpr hzr
    · exact Or.inr hz
  have hcover₁ : ι₁.opensRange ⊔ W₁ = ⊤ := by
    refine le_antisymm le_top fun z _ ↦ ?_
    rcases hor _ _ hj1cover z with hz | hz
    · obtain ⟨v, hv⟩ := Scheme.Hom.mem_opensRange.mp hz
      obtain ⟨i, u, hu⟩ := exists_mem_range_nodalModelBlowupChart π m v
      by_cases hi : i = 0
      · subst hi
        have hvjc : v ∈ Set.range jc.base := by
          rw [hjcrange]
          exact ⟨u, hu⟩
        obtain ⟨w, hw⟩ := hvjc
        exact Or.inl (Scheme.Hom.mem_opensRange.mpr ⟨w, by rw [← hv, ← hw]; rfl⟩)
      · refine Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨ULift.up i, ?_⟩)
        have hΩi : Ω (ULift.up i) = (nodalModelBlowupChart R π m i ≫ j₁).opensRange := by
          simp [hΩdef, hi]
        rw [hΩi]
        exact Scheme.Hom.mem_opensRange.mpr ⟨u, by rw [← hv, ← hu]; rfl⟩
    · exact Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨ULift.up 0, by simpa [hΩdef] using hz⟩)
  -- The blowup is again at-worst-nodal over `S`.
  have hnodal₁ : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f) := by
    set Λ : ULift.{u} Bool → (AlgebraicGeometry.blowUp M).Opens := fun c =>
      if c.down then j₁.opensRange else b ⁻¹ᵁ P.reg with hΛdef
    have hΛcover : ⨆ c, Λ c = ⊤ := by
      refine le_antisymm le_top fun z _ ↦ ?_
      rcases hor _ _ hj1cover z with hz | hz
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ULift.up true, by simpa [hΛdef] using hz⟩
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ULift.up false, by simpa [hΛdef] using hz⟩
    have hcov : Presieve.ofArrows (fun c : ULift.{u} Bool => (Λ c).toScheme)
        (fun c => (Λ c).ι) ∈ Scheme.etalePrecoverage (AlgebraicGeometry.blowUp M) := by
      refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr ⟨fun z => ?_, fun c => ?_⟩
      · obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp
          (show z ∈ ⨆ c, Λ c from by rw [hΛcover]; trivial)
        exact ⟨c, ⟨z, hc⟩, rfl⟩
      · infer_instance
    refine (isAtWorstNodalOfRelativeDimensionOne_iff_of_etaleCovering _ _ hcov).mpr fun c => ?_
    by_cases hc : c.down
    · have hΛc : Λ c = j₁.opensRange := by simp [hΛdef, hc]
      rw [hΛc]
      have h0 : (Scheme.Hom.isoOpensRange j₁).hom ≫ (j₁.opensRange.ι ≫ (b ≫ f))
          = nodalModelBlowupToBase R π m := by
        rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
        exact hj1toBase
      have hfac : (Scheme.Hom.isoOpensRange j₁).inv ≫ nodalModelBlowupToBase R π m
          = j₁.opensRange.ι ≫ (b ≫ f) := by
        rw [← h0, Iso.inv_hom_id_assoc]
      rw [← hfac]
      exact isAtWorstNodalOfRelativeDimensionOne_comp_etale _ _
        (isAtWorstNodalOfRelativeDimensionOne_nodalModelBlowupToBase hπ.ne_zero hm)
    · have hΛc : Λ c = b ⁻¹ᵁ P.reg := by simp [hΛdef, hc]
      rw [hΛc]
      have hfac : (b ⁻¹ᵁ P.reg).ι ≫ (b ≫ f) = (b ∣_ P.reg) ≫ (P.reg.ι ≫ f) := by
        rw [← Category.assoc, ← morphismRestrict_ι b P.reg, Category.assoc]
      rw [hfac]
      exact isAtWorstNodalOfRelativeDimensionOne_comp_etale _ (b ∣_ P.reg)
        (isAtWorstNodalOfRelativeDimensionOne_comp_etale f P.reg.ι P.nodal)
  -- The new origin is outside the new regular open.
  have horigin₁ : ∀ h1' : 1 ≤ m - 2, 2 ≤ m - 2 →
      ι₁.base (nodalModelOriginPoint hmax h1') ∉ W₁ := by
    intro h1' hm' hmem
    have hst : IsRegularLocalRing
        ((AlgebraicGeometry.blowUp M).presheaf.stalk
          (ι₁.base (nodalModelOriginPoint hmax h1'))) :=
      (isRegularLocalRing_stalk_iff_of_isOpenImmersion W₁.ι
        ⟨ι₁.base (nodalModelOriginPoint hmax h1'), hmem⟩).mp
        (hW1reg.isRegularLocalRing_stalk _)
    exact not_isRegularLocalRing_stalk_of_asIdeal_eq_nodalModelOrigin hπ hm'
      (nodalModelOriginPoint hmax h1') rfl
      ((isRegularLocalRing_stalk_iff_of_isOpenImmersion ι₁ _).mpr hst)
  -- Apply the inductive hypothesis to the blowup.
  obtain ⟨Y, g, hchain, hnodalY, hregY⟩ := ih (m - 2) (by omega)
    (AlgebraicGeometry.blowUp M) (b ≫ f)
    { chart := ι₁
      isOpenImmersion_chart := inferInstance
      chart_comp := hι₁comp
      nodal := hnodal₁
      reg := W₁
      isRegular_reg := hW1reg
      cover := hcover₁
      origin_notMem := horigin₁ }
  refine ⟨Y, g ≫ b, ?_, ?_, hregY⟩
  · have hc := hstep.comp hchain (fun y _ => Set.mem_univ _)
    rw [show 1 + (m - 2) / 2 = m / 2 by omega] at hc
    exact hc
  · rw [Category.assoc]
    exact hnodalY

/-- **Stacks Project, Tag 0CDC.** Using induction on `n` there is a sequence of blowups at closed
points
```
X_{⌊n/2⌋} → … → X₁ → X₀ = X
```
of the standard nodal model `X = Spec R[x, y]/(xy - πⁿ)` over `S = Spec R` such that
`X_{⌊n/2⌋} → S` is at-worst-nodal of relative dimension one and `X_{⌊n/2⌋}` is regular. -/
@[stacks 0CDC "using induction on n we conclude that there is a sequence of blowing ups in \
closed points X_{⌊n/2⌋} → … → X₁ → X₀ = X such that X_{⌊n/2⌋} → S is at-worst-nodal of relative \
dimension 1 and X_{⌊n/2⌋} is regular"]
public theorem exists_pointBlowupChainOfLength_nodalModel {π : R} (hπ : Irreducible π) (n : ℕ) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ nodalModel R π n),
      PointBlowupChainOfLength (nodalModel R π n) Set.univ (n / 2) Y g ∧
      IsAtWorstNodalOfRelativeDimensionOne (g ≫ nodalModelHom R π n) ∧ IsRegular Y :=
  exists_chain_of_patch hπ n (nodalModel R π n) (nodalModelHom R π n)
    { chart := 𝟙 _
      isOpenImmersion_chart := inferInstance
      chart_comp := Category.id_comp _
      nodal := isAtWorstNodalOfRelativeDimensionOne_nodalModelHom π n
      reg := ⊥
      isRegular_reg := isRegular_bot _
      cover := le_antisymm le_top fun z _ ↦
        Or.inl (Scheme.Hom.mem_opensRange.mpr ⟨z, by simp⟩)
      origin_notMem := fun _ _ => by simp }

end Stacks

end
