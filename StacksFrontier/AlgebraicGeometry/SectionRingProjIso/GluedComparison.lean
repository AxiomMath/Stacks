module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedRingFunctoriality
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjRegrading

/-!
# The morphism of Tag 01NK for the full section ring is the morphism of Tag 01PZ

Let `Y` be a scheme and `M` an invertible `𝒪_Y`-module. The repository constructs the canonical
morphism to the projective spectrum of a graded ring of sections twice:

* `Stacks.SectionRingProjMorphism.projHom` (and `projHomOfIsAmple`), the morphism
  `⋃_a Y_a ⟶ Proj Γ_*(Y, M)` of [Stacks, Tag 01PZ], glued from the charts
  `Stacks.SectionRingChartMap.chartHom`; [Stacks, Tag 01Q1] (open immersion, dense image) and the
  affine-base isomorphism `Stacks.SectionRingProjMorphism.ToSpecZero.isIso_projHomOfIsAmple` are
  proved for it;
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued`, the morphism
  `U(ψ) ⟶ Proj A` of [Stacks, Tag 01NK] for an arbitrary graded ring `A` and graded map
  `ψ : A → Γ_*(Y, M)`; this is the morphism the relative construction of [Stacks, Tag 01O9] is
  glued from, over the affine opens of a base.

This file identifies the two. `canonicalSections M` is the identity of `Γ_*(Y, M)` read as a datum
of [Stacks, Tag 01NK]; its covering open is `⋃_a Y_a` and its glued morphism is `projHom`
(`ι_comp_projHomOfIsAmple_eq_glued`, for `M` ample). It then transports the result along a graded
ring isomorphism `A ≅ Γ_*(Y, M)`: for such an isomorphism the covering open does not change and the
glued morphism of the transported datum is an isomorphism as soon as that of `canonicalSections M`
is (`isIso_glued_comap`). Together these say: **the morphism of [Stacks, Tag 01NK] attached to a
graded ring isomorphic to `Γ_*(Y, M)`, `M` ample and `Y ⟶ Spec Γ(Y, 𝒪_Y)` universally closed, is
an isomorphism.** This is the affine-local input of [Stacks, Tag 0C6J].

## Main results

* `Stacks.SectionRingGluedComparison.coveringOpen_canonicalSections`: `U(ψ) = ⋃_a Y_a`.
* `Stacks.SectionRingGluedComparison.lift_eq_chartRingMap`: on the chart at a homogeneous element
  of positive degree the two constructions use the same ring map out of the degree-zero
  localization.
* `Stacks.SectionRingGluedComparison.ι_comp_projHomOfIsAmple_eq_glued`: **the two morphisms
  agree.**
* `Stacks.SectionRingGluedComparison.isIso_glued_canonicalSections`: for `M` ample and
  `Y ⟶ Spec Γ(Y, 𝒪_Y)` universally closed the glued morphism is an isomorphism.
* `Stacks.SectionRingGluedComparison.coveringOpen_comap_of_comp_eq_id` and
  `Stacks.SectionRingGluedComparison.isIso_glued_comap`: transport along a graded ring isomorphism.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite HomogeneousLocalization
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections sectionRing mul)
open Stacks.SectionProduct (globalSection)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.SectionExtension (powSec)

universe u

namespace Stacks.SectionRingGluedComparison

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {Y : Scheme.{u}} (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]

/-- **The identity of `Γ_*(Y, M)`, as a datum of [Stacks, Tag 01NK].** In degree `n` it reads a
homogeneous element of `Γ_*(Y, M)`, a morphism `𝒪_Y ⟶ M^{⊗ n}`, as a global section of
`M^{⊗ n}`. -/
def canonicalSections : GradedSections (grading M) M where
  toFun n := (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
      (natTensorPow M n)).toAddMonoidHom.comp
    (Stacks.ExternalGrading.summandEquiv (powSections M) n).symm.toAddMonoidHom
  map_mul n m a b ab hab := by
    obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    have hab' : (ab : sectionRing M) = DirectSum.of (powSections M) (n + m) (mul a' b') := by
      rw [hab, ← ha, ← hb, Stacks.SectionRingChartMap.of_mul_eq]
    change globalSection Y _ ((ab : sectionRing M) (n + m))
      = Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections M
          (globalSection Y _ ((a : sectionRing M) n)) (globalSection Y _ ((b : sectionRing M) m))
    rw [hab', ← ha, ← hb, DirectSum.of_eq_same, DirectSum.of_eq_same, DirectSum.of_eq_same,
      Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections_globalSection]

/-- The value of `canonicalSections M` on a homogeneous element. -/
theorem canonicalSections_toFun (n : ℕ) (x : grading M n) :
    (canonicalSections M).toFun n x = globalSection Y _ ((x : sectionRing M) n) := rfl

/-- The value of `canonicalSections M` on the homogeneous element named by a section. -/
theorem canonicalSections_toFun_of (n : ℕ) (s : powSections M n)
    (h : DirectSum.of (powSections M) n s ∈ grading M n) :
    (canonicalSections M).toFun n ⟨_, h⟩ = globalSection Y _ s := by
  rw [canonicalSections_toFun, DirectSum.of_eq_same]

/-- The nonvanishing open of a value of `canonicalSections M` is the open `Y_s` of
[Stacks, Tag 01PZ]. -/
theorem nonvanishingOpen_canonicalSections_of (n : ℕ) (s : powSections M n)
    (h : DirectSum.of (powSections M) n s ∈ grading M n) :
    nonvanishingOpen Y (natTensorPow M n) ((canonicalSections M).toFun n ⟨_, h⟩) = nvOpen M s := by
  rw [canonicalSections_toFun_of]
  rfl

/-- **The covering open of `canonicalSections M` is `⋃_a Y_a`**, the source of the morphism of
[Stacks, Tag 01PZ]. -/
theorem coveringOpen_canonicalSections :
    (canonicalSections M).coveringOpen = Stacks.SectionRingProjMorphism.nvUnion M := by
  refine le_antisymm (iSup_le ?_) (iSup_le ?_)
  · rintro ⟨e, ⟨_, s, rfl⟩⟩
    exact (le_of_eq (nonvanishingOpen_canonicalSections_of M (e + 1) s _)).trans
      (Stacks.SectionRingProjMorphism.nvOpen_le_nvUnion M s (Nat.succ_pos e))
  · rintro ⟨d, hd, s⟩
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    exact (le_of_eq (nonvanishingOpen_canonicalSections_of M (e + 1) s
      (Stacks.ExternalGrading.of_mem_summand _ s)).symm).trans
      ((canonicalSections M).nonvanishingOpenAt_le_coveringOpen e
        ⟨_, Stacks.ExternalGrading.of_mem_summand _ s⟩)

omit [Ample.IsInvertibleModule Y M] in
/-- A homogeneous element of the section ring is the inclusion of its own component. -/
theorem of_apply_of_mem {i : ℕ} {z : sectionRing M} (hz : z ∈ grading M i) :
    DirectSum.of (powSections M) i (z i) = z := by
  obtain ⟨z', rfl⟩ := hz
  rw [DirectSum.of_eq_same]

/-- **The chart ring maps of the two constructions agree.** At a homogeneous `s` of positive
degree `e` and on an open `V ⊆ Y_s`, the ring map `Γ_*(Y, M)_{(s)} ⟶ Γ(Y, V)` of
[Stacks, Tag 01NK] for `canonicalSections M`, `x / sⁿ ↦ x / sⁿ`, is
`Stacks.SectionRingChartMap.chartRingMap`, which is `x / sⁿ ↦ (s x) / s^{n+1}`. -/
theorem lift_eq_chartRingMap {e : ℕ} (s : powSections M e) (he : 0 < e)
    (hf : DirectSum.of (powSections M) e s ∈ grading M e) {V : Y.Opens}
    (hV : V ≤ nonvanishingOpen Y (natTensorPow M e) ((canonicalSections M).toFun e ⟨_, hf⟩))
    (hV' : V ≤ nvOpen M s) :
    ((canonicalSections M).homogeneousRatios hf hV).lift he
      = Stacks.SectionRingChartMap.chartRingMap M s hV' := by
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext (grading M) hf fun n x hx => ?_
  have hx' : x ∈ grading M (n * e) := hx
  rw [(canonicalSections M).lift_mk hf hV he n x hx ⟨x, hx'⟩ rfl,
    Stacks.SectionRingChartMap.chartRingMap_mk, Stacks.SectionRingChartMap.chartFamily_apply,
    Stacks.SectionRingChartMap.numMapR_def]
  let g : powSections M (n * e) :=
    ((DirectSum.of (powSections M) e s ^ n : sectionRing M)) (n * e)
  have hg : V ≤ nvOpen M g := (canonicalSections M).le_nonvanishingOpen_pow hf hV n
  have hgs : V ≤ nvOpen M (mul g s) := Stacks.SectionRingChartMap.le_nvOpen_mul M hg hV'
  have key := Stacks.SectionRingChartMap.ratioR_mul M g s hg hV' hgs hx'
    (Stacks.ExternalGrading.of_mem_summand e s)
  rw [Stacks.SectionRingChartMap.ratioR_of_self, mul_one] at key
  have hgg : DirectSum.of (powSections M) (n * e + e) (mul g s)
      = DirectSum.of (powSections M) (e * (n + 1)) (powSec M s (n + 1)) := by
    have hpow : (DirectSum.of (powSections M) e s ^ n : sectionRing M) ∈ grading M (n * e) :=
      SetLike.pow_mem_graded n hf
    have hgdef : DirectSum.of (powSections M) (n * e) g = DirectSum.of (powSections M) e s ^ n :=
      of_apply_of_mem M hpow
    rw [Stacks.SectionRingChartMap.of_mul_eq, hgdef,
      Stacks.SectionRingChartMap.of_powSec_eq_pow, pow_succ]
  have hcong := Stacks.SectionRingChartMap.ratioR_congr M (show n * e + e = e * (n + 1) by ring)
    (mul g s) (powSec M s (n + 1)) hgs
    (Stacks.SectionRingChartMap.le_nvOpen_powSec M s hV' (n + 1) (by omega)) hgg
    (x * DirectSum.of (powSections M) e s)
  refine Eq.trans (?_ : _ = Stacks.SectionRingChartMap.ratioR M g hg x)
    ((key.symm.trans hcong).trans ?_)
  · rfl
  · exact congrArg _ (mul_comm _ _)

/-- **On an open inside `Y_s` the morphism of [Stacks, Tag 01PZ] is the chart of
[Stacks, Tag 01NK] at `s`.** -/
theorem ι_comp_projHomOfIsAmple_eq_chartToProj (hM : Stacks.Ample.IsAmple Y M) {e : ℕ}
    (s : powSections M e) (he : 0 < e) (hf : DirectSum.of (powSections M) e s ∈ grading M e)
    {V : Y.Opens}
    (hV : V ≤ nonvanishingOpen Y (natTensorPow M e) ((canonicalSections M).toFun e ⟨_, hf⟩)) :
    V.ι ≫ Stacks.SectionRingProjMorphism.projHomOfIsAmple M hM
      = (canonicalSections M).chartToProj hf hV he := by
  have hV' : V ≤ nvOpen M s := hV.trans (le_of_eq (nonvanishingOpen_canonicalSections_of M e s hf))
  have h1 : V.ι = Y.homOfLE hV' ≫ (nvOpen M s).ι := (Scheme.homOfLE_ι _ _).symm
  rw [h1, Category.assoc, Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple M hM s he,
    ← Stacks.SectionRingChartOpen.chartHomOn_self M s he,
    Stacks.SectionRingChartOpen.homOfLE_chartHomOn M s he le_rfl hV' hV',
    Stacks.SectionRingChartOpen.chartHomOn_val M s he hV']
  show _ = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (((canonicalSections M).homogeneousRatios hf hV).lift he)) ≫
    AlgebraicGeometry.Proj.awayι (grading M) _ hf he
  rw [lift_eq_chartRingMap M s he hf hV hV']

/-- **The morphism of [Stacks, Tag 01NK] for `canonicalSections M` is the morphism of
[Stacks, Tag 01PZ]**, for `M` ample: restricted to the covering open, `projHomOfIsAmple` is
`glued`. -/
theorem ι_comp_projHomOfIsAmple_eq_glued (hM : Stacks.Ample.IsAmple Y M) :
    (canonicalSections M).coveringOpen.ι ≫ Stacks.SectionRingProjMorphism.projHomOfIsAmple M hM
      = (canonicalSections M).glued := by
  refine (canonicalSections M).eq_glued_of_homOfLE_eq fun e f hf he => ?_
  rw [← Category.assoc, Scheme.homOfLE_ι]
  obtain ⟨s, rfl⟩ := hf
  exact ι_comp_projHomOfIsAmple_eq_chartToProj M hM s he _ le_rfl

/-- For `M` ample the covering open of `canonicalSections M` is all of `Y`. -/
theorem coveringOpen_canonicalSections_eq_top (hM : Stacks.Ample.IsAmple Y M) :
    (canonicalSections M).coveringOpen = ⊤ :=
  (coveringOpen_canonicalSections M).trans
    (Stacks.SectionRingProjMorphism.nvUnion_eq_top_of_isAmple M hM)

/-- **For `M` ample and `Y ⟶ Spec Γ(Y, 𝒪_Y)` universally closed, the morphism of
[Stacks, Tag 01NK] for `canonicalSections M` is an isomorphism.** This is
`Stacks.SectionRingProjMorphism.ToSpecZero.isIso_projHomOfIsAmple` read through
`ι_comp_projHomOfIsAmple_eq_glued`. -/
theorem isIso_glued_canonicalSections (hM : Stacks.Ample.IsAmple Y M)
    (h : UniversallyClosed Y.toSpecΓ) : IsIso (canonicalSections M).glued := by
  rw [← ι_comp_projHomOfIsAmple_eq_glued M hM]
  have : IsIso (canonicalSections M).coveringOpen.ι := by
    rw [coveringOpen_canonicalSections_eq_top M hM]
    exact (inferInstance : IsIso (Scheme.topIso Y).hom)
  have := Stacks.SectionRingProjMorphism.ToSpecZero.isIso_projHomOfIsAmple M hM h
  infer_instance

section Comap

open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

omit [Ample.IsInvertibleModule T L] in
/-- Two data of [Stacks, Tag 01NK] with the same components are equal. -/
theorem gradedSections_ext {ψ χ : GradedSections ℬ L} (h : ∀ n b, ψ.toFun n b = χ.toFun n b) :
    ψ = χ := by
  obtain ⟨g, hg⟩ := ψ
  obtain ⟨g', hg'⟩ := χ
  obtain rfl : g = g' := funext fun n => AddMonoidHom.ext (h n)
  rfl

/-- **Pulling a datum back along a graded ring homomorphism with a section does not change its
covering open.** -/
theorem coveringOpen_comap_of_comp_eq_id (φ : 𝒜 →+*ᵍ ℬ) (φ' : ℬ →+*ᵍ 𝒜)
    (h : φ.comp φ' = GradedRingHom.id ℬ) (ψ : GradedSections ℬ L) :
    (comap φ ψ).coveringOpen = ψ.coveringOpen := by
  refine le_antisymm (coveringOpen_le φ ψ) (iSup_le fun p => ?_)
  have hb : φ.gradedAddHom (p.1 + 1) (φ'.gradedAddHom (p.1 + 1) p.2) = p.2 :=
    Subtype.ext congr($h (p.2 : B))
  calc ψ.nonvanishingOpenAt (p.1 + 1) p.2
      = (comap φ ψ).nonvanishingOpenAt (p.1 + 1) (φ'.gradedAddHom (p.1 + 1) p.2) := by
        rw [nonvanishingOpenAt_comap, hb]
    _ ≤ (comap φ ψ).coveringOpen := (comap φ ψ).nonvanishingOpenAt_le_coveringOpen _ _

/-- **Pulling a datum back along a graded ring isomorphism preserves isomorphy of its glued
morphism**: the pulled-back morphism is the original one followed by `Proj` of the isomorphism
(`Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.homOfLE_glued_comp_projMap`), on the
same covering open. -/
theorem isIso_glued_comap (φ : 𝒜 →+*ᵍ ℬ) (φ' : ℬ →+*ᵍ 𝒜)
    (h₁ : φ'.comp φ = GradedRingHom.id 𝒜) (h₂ : φ.comp φ' = GradedRingHom.id ℬ)
    (ψ : GradedSections ℬ L) [IsIso ψ.glued] : IsIso (comap φ ψ).glued := by
  rw [← homOfLE_glued_comp_projMap φ (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id h₂) ψ]
  have : IsIso (T.homOfLE (coveringOpen_le φ ψ)) :=
    (inferInstance : IsIso (T.isoOfEq (coveringOpen_comap_of_comp_eq_id φ φ' h₂ ψ)).hom)
  have := AlgebraicGeometry.Proj.isIso_map
    (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id h₂)
    (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id h₁) h₁ h₂
  infer_instance

end Comap

end Stacks.SectionRingGluedComparison

end
