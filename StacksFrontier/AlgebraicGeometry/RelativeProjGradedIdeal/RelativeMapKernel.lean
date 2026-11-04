module

public import StacksFrontier.AlgebraicGeometry.Morphism.ChartPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualSurjective
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.Identification
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.IsoClause

/-!
# The morphism induced by a surjection of graded algebras cuts out the quotient by its kernel

Let `ψ : 𝒜 ⟶ ℬ` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras which is surjective on
the homogeneous sections over the affine opens of the base. Then the morphism
`r_ψ : U(ψ) ⟶ Proj_S(𝒜)` of Tag 07ZG is a closed immersion with the same ideal sheaf as
`Proj_S(𝒜/ker ψ) ⟶ Proj_S(𝒜)`: the two closed subschemes of `Proj_S(𝒜)` agree.

## Main results

* `gradedLiftOfSurjective`: a graded ring homomorphism factors through a degreewise surjective
  one with smaller kernel.
* `ker_projMap_le_of_ker_le`: the kernel of `Proj.map` is monotone in the kernel, for degreewise
  surjective graded ring homomorphisms.
* `isClosedImmersion_relativeMapHom_of_surjective`: `r_ψ` is a closed immersion.
* `ker_relativeMapHom_eq_ker_kernelAmbientHom`: `r_ψ` and `Proj_S(𝒜/ker ψ) ⟶ Proj_S(𝒜)` have the
  same ideal sheaf.
* `ker_relativeMapHom_eq_ker_projQuotientHom`: `r_ψ` and `Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)` have the same
  ideal sheaf, for any quasi-coherent graded ideal `ℐ` with the sections of `ker ψ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

/-! ### Graded rings -/

section GradedRing

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  {σ τ ρ : Type u} [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ρ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- **A graded ring homomorphism factors through a degreewise surjective one with smaller
kernel.** -/
def gradedLiftOfSurjective (f : 𝒜 →+*ᵍ ℬ) (g : 𝒜 →+*ᵍ 𝒞)
    (hf : ∀ d, Function.Surjective (GradedRingHom.gradedAddHom f d))
    (hfs : Function.Surjective f) (hker : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom) :
    ℬ →+*ᵍ 𝒞 where
  toRingHom := RingHom.liftOfSurjective f.toRingHom hfs ⟨g.toRingHom, hker⟩
  map_mem {i x} hx := by
    obtain ⟨a, ha⟩ := hf i ⟨x, hx⟩
    have hax : f (a : A) = x := congrArg Subtype.val ha
    rw [← hax]
    have h := RingHom.liftOfRightInverse_comp_apply f.toRingHom _
      (Function.rightInverse_surjInv hfs) ⟨g.toRingHom, hker⟩ (a : A)
    exact h ▸ g.map_mem a.2

omit [AddSubgroupClass ρ C] [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞] in
/-- The lift `gradedLiftOfSurjective f g` composed with `f` is `g`. -/
theorem gradedLiftOfSurjective_comp (f : 𝒜 →+*ᵍ ℬ) (g : 𝒜 →+*ᵍ 𝒞)
    (hf : ∀ d, Function.Surjective (GradedRingHom.gradedAddHom f d))
    (hfs : Function.Surjective f) (hker : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom) :
    (gradedLiftOfSurjective f g hf hfs hker).comp f = g := by
  ext a
  exact RingHom.liftOfRightInverse_comp_apply f.toRingHom _
    (Function.rightInverse_surjInv hfs) ⟨g.toRingHom, hker⟩ a

/-- **The kernel of `Proj.map` is monotone in the kernel.** For a degreewise surjective graded ring
homomorphism `f` and a graded ring homomorphism `g` with `ker f ⊆ ker g`, the morphism `Proj.map g`
factors through `Proj.map f`, so its ideal sheaf contains that of `Proj.map f`. -/
theorem ker_projMap_le_of_ker_le (f : 𝒜 →+*ᵍ ℬ) (g : 𝒜 →+*ᵍ 𝒞)
    (hf : ∀ d, Function.Surjective (GradedRingHom.gradedAddHom f d))
    (hfs : Function.Surjective f) (hker : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom)
    (hfi : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hgi : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    (Proj.map f hfi).ker ≤ (Proj.map g hgi).ker := by
  set e := gradedLiftOfSurjective f g hf hfs hker
  have hcomp : e.comp f = g := gradedLiftOfSurjective_comp f g hf hfs hker
  have hfirr : (HomogeneousIdeal.irrelevant 𝒜).map f ≤ HomogeneousIdeal.irrelevant ℬ := by
    rw [HomogeneousIdeal.map_le_iff_le_comap]
    refine (HomogeneousIdeal.irrelevant_le 𝒜).2 fun i hi x hx => ?_
    exact HomogeneousIdeal.mem_irrelevant_of_mem ℬ hi (f.map_mem hx)
  have hei : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map e := by
    refine hgi.trans ?_
    rw [← hcomp, HomogeneousIdeal.map_comp]
    exact HomogeneousIdeal.map_mono _ hfirr
  have key : ∀ (g' : 𝒜 →+*ᵍ 𝒞) (h' : g' = g)
      (hg' : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map g'),
      Proj.map g hgi = Proj.map g' hg' := by
    rintro _ rfl _
    rfl
  have hmap : Proj.map g hgi = Proj.map e hei ≫ Proj.map f hfi :=
    (key _ hcomp _).trans (Proj.map_comp f e hfi hei)
  rw [hmap]
  exact Scheme.Hom.le_ker_comp _ _

end GradedRing

/-! ### Sheaves of graded algebras -/

section Sheaf

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)
  (hψ : ProjBundleSurjection.SurjectiveOnAffineSections ψ)

include hψ in
/-- **`r_ψ` is a closed immersion** for `ψ` surjective on the sections over the affine opens of
the base: on each chart it is the absolute morphism of a surjection of graded rings. -/
theorem isClosedImmersion_relativeMapHom_of_surjective :
    IsClosedImmersion (Tag07ZGMorphism.relativeMapHom ψ) :=
  Tag07ZGMorphism.of_forall_chart ψ (P := @IsClosedImmersion) fun V =>
    RelativeProjChain.isClosedImmersion_mapHom_of_eventually_surjective (A.grading V.1)
      (B.grading V.1) (ψ.sectionHom V.1)
      (Filter.Eventually.of_forall fun d => ProjBundleSurjection.surjective_gradedAddHom hψ V.2 d)

include hψ in
/-- The absolute morphism of a surjection on a chart has the ideal sheaf of `Proj.map`. -/
theorem ker_mapHom_eq_ker_projMap (U : AffineOpen S) :
    (ProjTwistChain.mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ker =
      (AlgebraicGeometry.Proj.map (ψ.sectionHom U.1)
        (ProjBundleSurjection.irrelevant_le_map_sectionHom hψ U.2)).ker := by
  rw [← ProjBundleSurjection.chartMap_eq_map hψ U.1 U.2, ProjBundleSurjection.chartMap,
    mapHomOfTop, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp_of_isIso]

/-- The base change of `r_ψ` to a chart of `Proj_S(𝒜)` has the ideal sheaf of the absolute
morphism there. -/
theorem ker_pullback_snd_chart_relativeMapHom (U : AffineOpen S) :
    (pullback.snd (Tag07ZGMorphism.relativeMapHom ψ) ((relativeProj A).chart U.1 U.2)).ker =
      (ProjTwistChain.mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ker := by
  rw [← (Tag07ZGMorphism.isPullback_chart_relativeMapHom ψ U).isoPullback_hom_snd,
    Scheme.Hom.ker_comp_of_isIso]

/-- The induced homomorphism of section rings and that of the quotient by `ker ψ` have the same
kernel. -/
theorem ker_sectionHom_quotMkKernel (U : S.Opens) :
    RingHom.ker ((quotMkKernel ψ).sectionHom U).toRingHom =
      RingHom.ker (ψ.sectionHom U).toRingHom := by
  ext w
  rw [RingHom.mem_ker, RingHom.mem_ker]
  show (quotMkKernel ψ).sectionHom U w = 0 ↔ ψ.sectionHom U w = 0
  rw [sectionHom_eq_zero_iff, sectionHom_eq_zero_iff]
  exact forall_congr' fun n => quotMkKernel_app_eq_zero_iff ψ n U (w n)

include hψ in
/-- **`r_ψ` cuts out `Proj_S(𝒜/ker ψ)`**: for `ψ` surjective on the sections over the affine
opens of the base, the closed immersions `r_ψ : U(ψ) ⟶ Proj_S(𝒜)` and
`Proj_S(𝒜/ker ψ) ⟶ Proj_S(𝒜)` have the same ideal sheaf. -/
theorem ker_relativeMapHom_eq_ker_kernelAmbientHom :
    (Tag07ZGMorphism.relativeMapHom ψ).ker = (kernelAmbientHom ψ).ker := by
  have := isClosedImmersion_relativeMapHom_of_surjective ψ hψ
  have hq := surjectiveOnAffineSections_quotMkKernel ψ
  have hchart : ∀ U : AffineOpen S,
      (pullback.snd (Tag07ZGMorphism.relativeMapHom ψ) ((relativeProj A).chart U.1 U.2)).ker =
        (ProjBundleSurjection.chartMap hq U.1 U.2).ker := by
    intro U
    have h1 : (AlgebraicGeometry.Proj.map (ψ.sectionHom U.1)
          (ProjBundleSurjection.irrelevant_le_map_sectionHom hψ U.2)).ker ≤
        (AlgebraicGeometry.Proj.map ((quotMkKernel ψ).sectionHom U.1)
          (ProjBundleSurjection.irrelevant_le_map_sectionHom hq U.2)).ker :=
      ker_projMap_le_of_ker_le (ψ.sectionHom U.1) ((quotMkKernel ψ).sectionHom U.1)
        (ProjBundleSurjection.surjective_gradedAddHom hψ U.2)
        (ProjBundleSurjection.surjective_sectionHom hψ U.2)
        (ker_sectionHom_quotMkKernel ψ U.1).ge _ _
    have h2 : (AlgebraicGeometry.Proj.map ((quotMkKernel ψ).sectionHom U.1)
          (ProjBundleSurjection.irrelevant_le_map_sectionHom hq U.2)).ker ≤
        (AlgebraicGeometry.Proj.map (ψ.sectionHom U.1)
          (ProjBundleSurjection.irrelevant_le_map_sectionHom hψ U.2)).ker :=
      ker_projMap_le_of_ker_le ((quotMkKernel ψ).sectionHom U.1) (ψ.sectionHom U.1)
        (ProjBundleSurjection.surjective_gradedAddHom hq U.2)
        (ProjBundleSurjection.surjective_sectionHom hq U.2)
        (ker_sectionHom_quotMkKernel ψ U.1).le _ _
    rw [ker_pullback_snd_chart_relativeMapHom, ker_mapHom_eq_ker_projMap ψ hψ,
      ProjBundleSurjection.chartMap_eq_map hq]
    exact le_antisymm h1 h2
  exact ker_eq_kernelAmbientHom_of_forall_chart A ψ (Tag07ZGMorphism.relativeMapHom ψ) hchart

include hψ in
/-- **`r_ψ` cuts out `Proj_S(𝒜/ℐ)` for any quasi-coherent graded ideal `ℐ` with the sections of
`ker ψ`**: if a homogeneous local section of `𝒜` lies in `ℐ` exactly when `ψ` kills it, then
`r_ψ : U(ψ) ⟶ Proj_S(𝒜)` and `Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)` have the same ideal sheaf. -/
theorem ker_relativeMapHom_eq_ker_projQuotientHom [QuasiCompact (relativeProj A).toBase]
    (ℐ : QcohGradedIdeal A)
    (hℐ : ∀ (n : ℤ) (U : S.Opens) (a : Γ(A.piece n, U)),
      a ∈ (ℐ.piece n).toSubmodule.obj (op U) ↔ (ψ.app n).app U a = 0) :
    (Tag07ZGMorphism.relativeMapHom ψ).ker = (projQuotientHom A ℐ).ker := by
  have := isClosedImmersion_relativeMapHom_of_surjective ψ hψ
  have hq := surjectiveOnAffineSections_quotHom A ℐ
  have hkerq : ∀ U : S.Opens, RingHom.ker ((quotHom A ℐ).sectionHom U).toRingHom =
      RingHom.ker (ψ.sectionHom U).toRingHom := by
    intro U
    ext w
    rw [RingHom.mem_ker, RingHom.mem_ker]
    show (quotHom A ℐ).sectionHom U w = 0 ↔ ψ.sectionHom U w = 0
    rw [sectionHom_eq_zero_iff, sectionHom_eq_zero_iff]
    exact forall_congr' fun n => (quotProj_app_eq_zero_iff A ℐ n U (w n)).trans (hℐ n U (w n))
  refine ker_eq_ker_projQuotientHom_of_ker_chart A (Tag07ZGMorphism.relativeMapHom ψ) ℐ
    fun U hU => ?_
  let V : AffineOpen S := ⟨U, hU⟩
  have hpb₁ := AlgebraicGeometry.IsOpenImmersion.isPullback _ _ _ _
    (ChartBaseChange.chartRestrict_comp ((relativeProj A).chart U hU)
      (Tag07ZGMorphism.relativeMapHom ψ)).symm
    (by rw [Scheme.Opens.opensRange_ι, Scheme.Hom.image_top_eq_opensRange])
  have hpb₂ := Tag07ZGMorphism.isPullback_chart_relativeMapHom ψ V
  have h1 : (ChartBaseChange.chartRestrict ((relativeProj A).chart U hU)
      (Tag07ZGMorphism.relativeMapHom ψ)).ker =
        (ProjTwistChain.mapHom (A.grading U) (B.grading U) (ψ.sectionHom U)).ker := by
    rw [← hpb₂.isoIsPullback_hom_snd _ _ hpb₁.flip, Scheme.Hom.ker_comp_of_isIso]
  have h2 : (AlgebraicGeometry.Proj.map (ψ.sectionHom U)
        (ProjBundleSurjection.irrelevant_le_map_sectionHom hψ hU)).ker ≤
      (AlgebraicGeometry.Proj.map ((quotHom A ℐ).sectionHom U)
        (ProjBundleSurjection.irrelevant_le_map_sectionHom hq hU)).ker :=
    ker_projMap_le_of_ker_le (ψ.sectionHom U) ((quotHom A ℐ).sectionHom U)
      (ProjBundleSurjection.surjective_gradedAddHom hψ hU)
      (ProjBundleSurjection.surjective_sectionHom hψ hU) (hkerq U).ge _ _
  have h3 : (AlgebraicGeometry.Proj.map ((quotHom A ℐ).sectionHom U)
        (ProjBundleSurjection.irrelevant_le_map_sectionHom hq hU)).ker ≤
      (AlgebraicGeometry.Proj.map (ψ.sectionHom U)
        (ProjBundleSurjection.irrelevant_le_map_sectionHom hψ hU)).ker :=
    ker_projMap_le_of_ker_le ((quotHom A ℐ).sectionHom U) (ψ.sectionHom U)
      (ProjBundleSurjection.surjective_gradedAddHom hq hU)
      (ProjBundleSurjection.surjective_sectionHom hq hU) (hkerq U).le _ _
  rw [h1, ker_mapHom_eq_ker_projMap ψ hψ V, ProjBundleSurjection.chartMap_eq_map hq]
  exact le_antisymm h2 h3

end Sheaf

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal
