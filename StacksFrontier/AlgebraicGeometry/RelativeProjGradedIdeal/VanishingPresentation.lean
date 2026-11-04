module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedIdealMultiple
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.IsoClause
public import StacksFrontier.AlgebraicGeometry.ProjQuotientChartIdeal.Graded
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.ChartUnit
public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 0801 in the relative case: the chart comparison, and the presentation it produces

Work in Situation 01NN. This file closes the last input of Tag 0801's `iso` clause — the
comparison, over an affine open `U` of the base, of Tag 0801's graded ideal with the absolute
ideal of equations of the chart — and assembles the whole of
`…RelativeProjGradedIdeal.VanishingIdealPresentation` out of it.

## Main definitions

* `…RelativeProjTwists.gradedQuotientPresentationOfTwistData` and
  `…RelativeProjTwists.gradedQuotientPresentation`: **Tag 0801's graded-quotient presentation in
  the relative case**, the five-field form Tag 0802 consumes, the second carrying no twist datum.
* `…RelativeProjTwists.vanishingIdealPresentationOfTwistData` and
  `…RelativeProjTwists.vanishingIdealPresentation`: **all eight fields of the vanishing-ideal
  presentation**, the form Tag 0803 consumes.

## Main results

* `…RelativeProjTwists.pullbackGlobalSections_degreeSection_eq_zero_iff`: **the chart
  comparison.** The global section of `𝒪(n)` on the chart over `U` determined by a homogeneous
  local section `a` of `𝒜_n` pulls back to zero on the part of `Z` lying over the chart exactly
  when Tag 0801's `ψ` kills `a`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

namespace Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-! ### Transport along an equality of opens -/

/-- Vanishing of a local section under a morphism of modules is unaffected by a transport along
an equality of opens: both sides say that the same element dies. -/
theorem app_eq_zero_iff_of_opens_eq {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {W W' : X.Opens} (h : W = W') (s : Γ(M, W')) (u : Γ(M, W)) (hu : u = h.symm ▸ s) :
    φ.app W u = 0 ↔ φ.app W' s = 0 := by
  subst h
  subst hu
  exact Iff.rfl

/-! ### Tag 0801's homomorphism on sections -/

variable (D : TwistData A) {Z : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme)
  [IsClosedImmersion i] [QuasiCompact (relativeProj A).toBase]

/-- **Tag 0801's `ψ` on a homogeneous local section**: the homogeneous-section map of the
relative Proj followed by the quotient of the twists by `ℐ_Z · 𝒪(n)`. -/
theorem psiClosedHom_app_app (U : S.Opens) (n : ℕ) (a : Γ(A.piece (n : ℤ), U)) :
    ((psiClosedHom D (closedIdealDegreeZero D i)
            (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i)).app
          (n : ℤ)).app U a =
      ((restrictionHom D (closedIdealDegreeZero D i)
            (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i)).app
          (n : ℤ)).app ((relativeProj A).toBase ⁻¹ᵁ U) ((D.ψ n).app U a) :=
  rfl

/-- **Tag 0801's `ψ` kills a homogeneous local section exactly when the twisted section it
determines restricts to zero on the closed subscheme.** -/
theorem psiClosedHom_app_eq_zero_iff (U : S.Opens) (n : ℕ) (a : Γ(A.piece (n : ℤ), U)) :
    ((psiClosedHom D (closedIdealDegreeZero D i)
            (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i)).app
          (n : ℤ)).app U a = 0 ↔
      (restrictionToClosed i ((twistSheafGradedAlgebra D).piece (n : ℤ))).app
        ((relativeProj A).toBase ⁻¹ᵁ U) ((D.ψ n).app U a) = 0 := by
  rw [psiClosedHom_app_app]
  exact restrictionHom_app_eq_zero_iff_restrictionToClosed D i (n : ℤ) _ _

/-! ### The chart comparison -/

/-- The twisted section attached by `ψ_chart` to a homogeneous local section restricts to zero on
the closed subscheme exactly when `ψ` kills that section. -/
theorem restrictionToClosed_chartIso_eq_zero_iff (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (a : Γ(A.piece (n : ℤ), U)) :
    letI := D.chartData.chart_isOpenImmersion U hU
    (restrictionToClosed i (D.algebra.piece (n : ℤ))).app
        ((relativeProj A).chart U hU ''ᵁ ⊤)
        ((D.chartData.chartIso U hU (n : ℤ)).inv.app ⊤
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) n
            ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩)) = 0 ↔
      ((psiClosedHom D (closedIdealDegreeZero D i)
            (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i)).app
          (n : ℤ)).app U a = 0 := by
  let := D.chartData.chart_isOpenImmersion U hU
  refine Iff.trans ?_ (psiClosedHom_app_eq_zero_iff D i U n a).symm
  exact app_eq_zero_iff_of_opens_eq (restrictionToClosed i (D.algebra.piece (n : ℤ)))
    (D.chartData.chart_range U hU) ((D.ψ n).app U a) _ (D.ψ_chart U hU n a)

/-- **The chart comparison of Tag 0801.** Over an affine open `U` of the base, the global section
of `𝒪(n)` on the chart determined by a homogeneous local section `a` of `𝒜_n` pulls back to zero
on the part of `Z` lying over the chart exactly when Tag 0801's `ψ` kills `a`.

Three identifications compose. The chart identification of the twists carries the absolute
twisted section to the relative one and `…TwistData.ψ_chart` names it as `ψ`; the base change of
the unit `M ⟶ i_* i^* M` along the chart
(`Stacks.AlgebraicGeometry.ChartUnit.pullbackGlobalSections_restrict_eq_zero_iff`) identifies
pulling back to the fibre of `i` over the chart with restricting to `Z` over the chart's image;
and `…restrictionHom_app_eq_zero_iff_restrictionToClosed` identifies that with `ψ`. -/
theorem pullbackGlobalSections_degreeSection_eq_zero_iff (U : S.Opens) (hU : IsAffineOpen U)
    (n : ℕ) (a : Γ(A.piece (n : ℤ), U)) :
    pullbackGlobalSections (pullback.snd i ((relativeProj A).chart U hU))
        (twistingSheaf (A.grading U) (n : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩) = 0 ↔
      ((psiClosedHom D (closedIdealDegreeZero D i)
            (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i)).app
          (n : ℤ)).app U a = 0 := by
  let := D.chartData.chart_isOpenImmersion U hU
  have hnat := Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
    (pullback.snd i ((relativeProj A).chart U hU))
    (D.chartData.chartIso U hU (n : ℤ)).inv
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) n
      ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩)
  have hiso := RestrictUnit.isIso_iso_hom_app
    ((Scheme.Modules.pullback (pullback.snd i ((relativeProj A).chart U hU))).mapIso
      (D.chartData.chartIso U hU (n : ℤ)).symm) ⊤
  refine Iff.trans ?_ (restrictionToClosed_chartIso_eq_zero_iff D i U hU n a)
  refine Iff.trans ?_ (ChartUnit.pullbackGlobalSections_restrict_eq_zero_iff i
    ((relativeProj A).chart U hU) (D.algebra.piece (n : ℤ))
    ((D.chartData.chartIso U hU (n : ℤ)).inv.app ⊤
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) n
        ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩)))
  rw [hnat]
  exact (RestrictUnit.apply_eq_zero_iff_of_isIso _ hiso _).symm

/-! ### The chart comparison as an equality of ideals -/

/-- A homogeneous local section over an affine open of the base lies in Tag 0801's graded ideal
exactly when the twisted section it determines on the chart pulls back to zero on the part of the
closed subscheme lying over that chart. -/
theorem mem_closedVanishingIdeal_iff_chart (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (a : Γ(A.piece (n : ℤ), U)) :
    a ∈ ((closedVanishingIdeal D (closedIdealDegreeZero D i)
          (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i)).piece
        (n : ℤ)).toSubmodule.obj (op U) ↔
      pullbackGlobalSections (pullback.snd i ((relativeProj A).chart U hU))
        (twistingSheaf (A.grading U) (n : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) n
          ⟨DirectSum.of (A.sectionPieces U) n a, A.of_mem_grading U a⟩) = 0 :=
  (mem_closedVanishingIdeal_iff D (closedIdealDegreeZero D i)
      (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i) (n : ℤ) U a).trans
    (pullbackGlobalSections_degreeSection_eq_zero_iff D i U hU n a).symm

/-- The part of the closed subscheme lying over a chart is a closed subscheme of the chart. -/
instance isClosedImmersion_pullback_snd_chart (U : S.Opens) (hU : IsAffineOpen U) :
    IsClosedImmersion (pullback.snd i ((relativeProj A).chart U hU)) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (IsPullback.of_hasPullback i ((relativeProj A).chart U hU)) inferInstance

/-- **The last input of Tag 0801's `iso` clause.** Over an affine open `U` of the base, the
homogeneous ideal of `Γ(U, 𝒜)` cut out by Tag 0801's graded ideal is the absolute ideal of
equations of the part of the closed subscheme lying over the chart.

Both sides are described degreewise — the left by `…mem_sectionGradedIdeal_iff`, the right by
`…mem_idealOfClosedSubscheme_iff` — and the chart comparison identifies the two conditions on a
homogeneous local section. The comparison is carried out on homogeneous elements and extended by
the span: a section of `Γ(U, 𝒜)` is the sum of its homogeneous summands. -/
theorem sectionGradedIdeal_eq_idealOfClosedSubscheme (U : S.Opens) (hU : IsAffineOpen U) :
    (sectionGradedIdeal A
        (closedVanishingIdeal D (closedIdealDegreeZero D i)
          (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i))
        (isQuasicoherentQuotPieces_kernelGradedIdeal _) U).toIdeal =
      Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme (A.grading U)
        (pullback.snd i ((relativeProj A).chart U hU)) := by
  classical
  refine le_antisymm (fun w hw => ?_) (Ideal.span_le.2 ?_)
  · replace hw := (mem_sectionGradedIdeal_iff A _ _ U w).1 hw
    rw [← DirectSum.sum_support_of w]
    refine Ideal.sum_mem _ fun m _ => Ideal.subset_span
      ⟨m, ⟨DirectSum.of (A.sectionPieces U) m (w m), A.of_mem_grading U (w m)⟩, rfl, ?_⟩
    exact (mem_closedVanishingIdeal_iff_chart D i U hU m (w m)).1 (hw m)
  · rintro x ⟨m, b, rfl, hb⟩
    obtain ⟨y, hy⟩ := b.2
    simp only [SetLike.mem_coe]
    refine (mem_sectionGradedIdeal_iff A _ _ U (b : A.sectionRing U)).2 fun k => ?_
    rcases eq_or_ne m k with rfl | hmk
    · rw [← hy, DirectSum.of_eq_same]
      refine (mem_closedVanishingIdeal_iff_chart D i U hU m y).2 ?_
      rw [show (⟨DirectSum.of (A.sectionPieces U) m y, A.of_mem_grading U y⟩ :
        A.grading U m) = b from Subtype.ext hy]
      exact hb
    · rw [← hy, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hmk)]
      exact Submodule.zero_mem _

/-! ### Tag 0801's `iso` clause, and the whole presentation -/

/-- **Tag 0801's `iso` clause on one chart.** Over an affine open of the base, the part of the
closed subscheme lying over the chart and the chart map of `𝒜 ⟶ 𝒜/ℐ` cut out the same ideal
sheaf of the chart.

The chart is quasi-compact (`…compactSpace_proj_grading`), so the absolute case of Tag 0801 at an
`AddSubgroup`-valued grading (`Stacks.ProjChartKerQuotient.ker_eq_ker_projMap_quotientMk`)
applies, with the ideal of equations identified by
`…sectionGradedIdeal_eq_idealOfClosedSubscheme`; and `…chartMap_quotMk_eq` identifies the chart
map with the same `AlgebraicGeometry.Proj.map`, up to an isomorphism of the source which a kernel
ideal sheaf does not see. -/
theorem ker_eq_chartMap_ker (U : S.Opens) (hU : IsAffineOpen U) :
    (pullback.snd i ((relativeProj A).chart U hU)).ker =
      (ProjBundleSurjection.chartMap
        (surjectiveOnAffineSections_quotMk A
          (closedVanishingIdeal D (closedIdealDegreeZero D i)
            (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i))
          (isQuasicoherentQuotPieces_kernelGradedIdeal _)
          (isQuasicoherent_kernelGradedIdeal_piece _))
        U hU).ker := by
  have : CompactSpace (AlgebraicGeometry.Proj (A.grading U)) :=
    compactSpace_proj_grading A U hU
  rw [chartMap_quotMk_eq A
      (closedVanishingIdeal D (closedIdealDegreeZero D i)
        (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i))
      (isQuasicoherentQuotPieces_kernelGradedIdeal _) (isQuasicoherent_kernelGradedIdeal_piece _)
      hU,
    Scheme.Hom.ker_comp_of_isIso]
  exact Stacks.ProjChartKerQuotient.ker_eq_ker_projMap_quotientMk (A.grading U)
    (pullback.snd i ((relativeProj A).chart U hU)) _
    (sectionGradedIdeal_eq_idealOfClosedSubscheme D i U hU) _

/-- **Tag 0801's graded-quotient presentation in the relative case**, with every clause
discharged: the chart comparison holds on every chart, so the two closed immersions into
`Proj_S(𝒜)` have the same kernel ideal sheaf. -/
def gradedQuotientPresentationOfTwistData : GradedQuotientPresentation A i :=
  gradedQuotientPresentation_kernel_of_forall_chart A
    (psiClosedHom D (closedIdealDegreeZero D i)
      (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i))
    i fun U => ker_eq_chartMap_ker D i U.1 U.2

/-- The restriction of the degree-`n` twist to the closed subscheme, as a module on it. -/
def restrictedTwist (n : ℕ) : Z.Modules :=
  (Scheme.Modules.pullback i).obj ((twistSheafGradedAlgebra D).piece (n : ℤ))

/-- **Restriction of the homogeneous sections of degree `n` to the closed subscheme**: the
homogeneous-section map of the relative Proj followed by the restriction `𝒪(n) ⟶ i_*i^*𝒪(n)`,
with the two direct images composed. -/
def restrictionOfDegree (n : ℕ) :
    (A.piece (n : ℤ) : S.Modules) ⟶
      (Scheme.Modules.pushforward (i ≫ (relativeProj A).toBase)).obj (restrictedTwist D i n) :=
  D.ψ n ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (restrictionToClosed i ((twistSheafGradedAlgebra D).piece (n : ℤ))) ≫
    (Scheme.Modules.pushforwardComp i (relativeProj A).toBase).hom.app (restrictedTwist D i n)

omit [IsClosedImmersion i] [QuasiCompact (relativeProj A).toBase] in
/-- The restriction map on sections is the restriction of the twisted section to the closed
subscheme: the comparison of the two direct images is the identity on sections. -/
theorem restrictionOfDegree_app (n : ℕ) (W : S.Opens) (a : Γ(A.piece (n : ℤ), W)) :
    (restrictionOfDegree D i n).app W a =
      (restrictionToClosed i ((twistSheafGradedAlgebra D).piece (n : ℤ))).app
        ((relativeProj A).toBase ⁻¹ᵁ W) ((D.ψ n).app W a) :=
  rfl

/-- **Tag 0801 in the relative case: the vanishing-ideal presentation of a closed subscheme of a
quasi-compact relative `Proj`.**

All eight clauses: the graded ideal is the degreewise kernel of `ψ`, its quotient pieces are
quasi-coherent and the quotient homomorphism is degreewise surjective on the sections over the
affine opens of the base (`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Kernel.lean`);
the identification of `Z` with `Proj_S(𝒜/ℐ)` over `Proj_S(𝒜)` is
`…gradedQuotientPresentationOfTwistData`; and the restricted sections are the twisted sections
restricted to `Z`, whose vanishing is membership in `ℐ` by the definition of `ψ`. -/
@[ega "II 3.6.2"]
def vanishingIdealPresentationOfTwistData : VanishingIdealPresentation A i where
  ideal :=
    closedVanishingIdeal D (closedIdealDegreeZero D i)
      (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i)
  quotQc := isQuasicoherentQuotPieces_kernelGradedIdeal _
  surjective := (gradedQuotientPresentationOfTwistData D i).surjective
  iso := (gradedQuotientPresentationOfTwistData D i).iso
  iso_comp := (gradedQuotientPresentationOfTwistData D i).iso_comp
  restricted n := restrictedTwist D i n
  restriction n := restrictionOfDegree D i n
  mem_ideal n W a h := by
    refine (mem_closedVanishingIdeal_iff D (closedIdealDegreeZero D i)
      (isQuasicoherentQuotPieces_closedGradedIdeal_closedIdealDegreeZero D i)
      (n : ℤ) W a).2 ?_
    refine (psiClosedHom_app_eq_zero_iff D i W n a).2 ?_
    rw [← restrictionOfDegree_app D i n W a]
    exact h

/-- **Tag 0801 in the relative case, with no twist datum carried**: the twists of a relative
`Proj` exist unconditionally (`…GluedTwistAlgebra.twistDataOfGradedAlgebra`), so a closed
subscheme of a quasi-compact relative `Proj` has a vanishing-ideal presentation on no hypothesis
beyond Tag 0801's own. -/
def vanishingIdealPresentation : VanishingIdealPresentation A i :=
  vanishingIdealPresentationOfTwistData (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i

/-- **Tag 0801's graded-quotient presentation, with no twist datum carried.** This is the
five-field form of the presentation — the one Tag 0802 consumes — at the unconditional twists of
`…GluedTwistAlgebra.twistDataOfGradedAlgebra`. It is the graded-quotient part of
`…vanishingIdealPresentation`, whose `surjective`, `iso` and `iso_comp` fields are read off the
same term. -/
def gradedQuotientPresentation : GradedQuotientPresentation A i :=
  gradedQuotientPresentationOfTwistData (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i

end Stacks.AlgebraicGeometry.RelativeProjTwists

end
