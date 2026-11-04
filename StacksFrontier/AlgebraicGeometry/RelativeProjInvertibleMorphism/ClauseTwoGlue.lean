module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwoParts
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseThreeMorphism
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedPullback

/-!
# Clause (2) of Stacks Tag 01O9 from its parts over the affine opens of the base

Let `W` be an open of `X` on which `ψ` is surjective in degree `k`. Suppose that over every affine
open `V` of the base the pulled-back [Stacks, Tag 01NK] datum on `W ∩ f^{-1}(V)` generates
everywhere, and that there the morphism the relative homogeneous spectrum attaches to the
quadruple of `W` is the morphism of Tag 01NK followed by the chart `i_V`. Then `W ⊆ U(ψ)` and
`r_{ℒ,ψ}|_W` is that morphism. Both are read off over the affine opens of the base, where the
part of `r_{ℒ,ψ}` is clause (3) and the morphism of the pulled-back datum is the restriction of
the morphism of the datum (`…ProjChartGradedPullback.resLE_glued`).

## Main results

* `…RelativeProjInvertibleMorphism.clauseTwo_of_parts`.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : Twisting f (situationAlgebra A) 1 L) {W : T.Opens}

/-- The covering open of the pulled-back datum is the preimage of that of the datum. -/
theorem coveringOpen_partDatum (V : S.Opens) :
    (partDatum (W := W) ψ V).coveringOpen
      = partInclusion (W := W) V ⁻¹ᵁ ((toGradedPowerMap ψ).affineDatum V).coveringOpen :=
  Stacks.AlgebraicGeometry.ProjChartGradedPullback.coveringOpen_eq (partInclusion V) _
    ((toGradedPowerMap ψ).affineDatum V) (partDatum ψ V) fun _ _ => rfl

/-- **The part of `W` over an affine `V` lies in `U(ψ)`** once the pulled-back datum generates
there. -/
theorem partOver_le_coveringOpen (V : S.affineOpens)
    (hcov : (partDatum (W := W) ψ V.1).coveringOpen = ⊤) :
    (W.ι ≫ f) ⁻¹ᵁ V.1 ≤ W.ι ⁻¹ᵁ (toGradedPowerMap ψ).coveringOpen := by
  intro y hy
  have h1 : (⟨y, hy⟩ : ((W.ι ≫ f) ⁻¹ᵁ V.1).toScheme) ∈ (partDatum (W := W) ψ V.1).coveringOpen := by
    rw [hcov]; trivial
  rw [coveringOpen_partDatum] at h1
  have h2 : (f ⁻¹ᵁ V.1).ι (partInclusion (W := W) V.1 ⟨y, hy⟩)
      ∈ (f ⁻¹ᵁ V.1).ι ''ᵁ ((toGradedPowerMap ψ).affineDatum V.1).coveringOpen :=
    ⟨_, h1, rfl⟩
  rw [(toGradedPowerMap ψ).image_coveringOpen_affineDatum_eq V.2] at h2
  have h3 : (f ⁻¹ᵁ V.1).ι (partInclusion (W := W) V.1 ⟨y, hy⟩) = W.ι y := by
    show (partInclusion (W := W) V.1 ≫ (f ⁻¹ᵁ V.1).ι) ⟨y, hy⟩ = W.ι y
    rw [partInclusion_ι]
    rfl
  rw [h3] at h2
  exact h2.1

/-- **Clause (2) of [Stacks, Tag 01O9] from its parts over the affine opens of the base.** -/
theorem clauseTwo_of_parts {k : ℕ} (hk : 0 < k) [Epi ((ψ.pullback W.ι).app (k : ℤ))]
    (hcov : ∀ V : S.affineOpens, (partDatum (W := W) ψ V.1).coveringOpen = ⊤)
    (hloc : ∀ V : S.affineOpens, (partDatum (W := W) ψ V.1).coveringOpen.ι
        ≫ ((W.ι ≫ f) ⁻¹ᵁ V.1).ι
        ≫ F.classifyingMorphism A (F.mk (W.ι ≫ f) (by exact_mod_cast hk)
          (restrictQuadruple ψ W k))
      = (partDatum (W := W) ψ V.1).glued ≫ (relativeProj A).chart V.1 V.2) :
    ∃ h : W ≤ (toGradedPowerMap ψ).coveringOpen,
      T.homOfLE h ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A)
        = F.classifyingMorphism A (F.mk (W.ι ≫ f) (by exact_mod_cast hk)
          (restrictQuadruple ψ W k)) := by
  have hW : W ≤ (toGradedPowerMap ψ).coveringOpen := by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    have hy : (⟨x, hx⟩ : W.toScheme) ∈ (W.ι ≫ f) ⁻¹ᵁ V := hxV
    exact partOver_le_coveringOpen ψ ⟨V, hV⟩ (hcov ⟨V, hV⟩) hy
  refine ⟨hW, Scheme.hom_ext_of_affinePreimages (W.ι ≫ f) fun V => ?_⟩
  have : IsIso (partDatum (W := W) ψ V.1).coveringOpen.ι := by
    rw [← Scheme.isoOfEq_hom_ι _ (hcov V)]
    exact IsIso.comp_isIso' inferInstance (inferInstanceAs (IsIso (Scheme.topIso _).hom))
  have hle := (coveringOpen_partDatum (W := W) ψ V.1).le
  have hq : (partInclusion (W := W) V.1).resLE _ _ hle ≫ (toGradedPowerMap ψ).affineDatumInclusion V
      = (partDatum (W := W) ψ V.1).coveringOpen.ι ≫ ((W.ι ≫ f) ⁻¹ᵁ V.1).ι ≫ T.homOfLE hW := by
    refine (cancel_mono (toGradedPowerMap ψ).coveringOpen.ι).mp ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((toGradedPowerMap ψ).affineDatumInclusion_ι V)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (f ⁻¹ᵁ V.1).ι) (Scheme.Hom.resLE_comp_ι _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (partInclusion_ι V.1)).trans ?_
    exact (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (T.homOfLE_ι hW).symm)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm
  refine (cancel_epi (partDatum (W := W) ψ V.1).coveringOpen.ι).mp ((hloc V).symm ▸ ?_)
  refine Eq.trans ?_ (congrArg (· ≫ (relativeProj A).chart V.1 V.2)
    (Stacks.AlgebraicGeometry.ProjChartGradedPullback.resLE_glued
      (partInclusion (W := W) V.1) _ ((toGradedPowerMap ψ).affineDatum V.1) (partDatum ψ V.1)
      (fun _ _ => rfl)))
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) ((toGradedPowerMap ψ).affineDatumInclusion_globalMorphism
    (relativeProj A) V))
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A)) hq).symm
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
