module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreePresenter
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreeSandwich
import all StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedSubscheme

/-!
# Enlarging a presenting submodule inside the graded ideal of a closed subscheme

Work in Situation 01NN: a scheme `S`, a quasi-coherent graded `𝒪_S`-algebra `𝒜`, a closed
immersion `i : Z ⟶ Proj_S(𝒜)` with `Proj_S(𝒜) ⟶ S` quasi-compact, and Tag 0801's graded ideal
`ℐ` of `Z` (`twistKerGradedIdeal`).  The submodule `ℱ ⊆ 𝒜_d` produced by the case of schemes of
Stacks 0803 cuts `Z` out on the charts.  This file records that property and the step of the proof
of Stacks 085N that uses it: **any quasi-coherent `𝒢` with `ℱ ⊆ 𝒢 ⊆ ℐ_d` also presents `Z`**,
`Z = Proj_S(𝒜/𝒢𝒜)`.  In the source this is the sandwich `Z ⊆ Proj(𝒜/𝒢𝒜) ⊆ Proj(𝒜/ℱ𝒜) = Z`
over an étale chart: `𝒢𝒜 ⊆ ℐ` gives the first inclusion, `ℱ ⊆ 𝒢` the second.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_finiteType_presentation_supp_cutsOut`:
  Stacks 0803's submodule, with its two defining properties for Tag 0801's presentation recorded:
  its sections are equations for `Z` and it cuts `Z` out on the charts.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.degreeQuotientPresentation_of_le_twistKer`:
  **the sandwich.**

## References

* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) {Z : Scheme.{u}}
  (i : Z ⟶ (relativeProj A).scheme)

/-- **Stacks 0803's submodule cuts the closed subscheme out on the charts.**  The construction of
`exists_finiteType_presentation_supp_of_presenter`, read for Tag 0801's own presentation
(`gradedQuotientPresentation_twistKer`): besides its quasi-coherence, finite type and the support
condition over `U`, the submodule consists of equations for `Z` and cuts `Z` out on the charts. -/
theorem exists_finiteType_presentation_supp_cutsOut (U : S.Opens)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase]
    (hi : AlgebraicGeometry.FinitePresentation i)
    (hU : (U : Set S) ∩ Set.range (i ≫ (relativeProj A).toBase).base = ∅)
    (hUc : IsCompact (U : Set S))
    (hA : ∀ n : ℕ, SheafOfModules.IsFiniteType.{u, u, u} (A.piece (n : ℤ))) :
    ∃ d : ℕ, 0 < d ∧ ∃ ℱ : (A.piece (d : ℤ)).Submodule,
      ℱ.toSheafOfModules.IsQuasicoherent ∧
        SheafOfModules.IsFiniteType.{u, u, u} ℱ.toSheafOfModules ∧
          (U : Set S) ∩ (⟨(cokernel ℱ.ι).val, (cokernel ℱ.ι).isSheaf⟩ :
              RingedSpace.ModuleSheaf.{u} S.toRingedSpace).supp = ∅ ∧
            IsEquationSubmodule A ℱ
              (quotHom A (twistKerGradedIdeal A
                (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A) i)) ∧
            CutsOutOnCharts A ℱ
              (quotHom A (twistKerGradedIdeal A
                (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A) i)) := by
  classical
  let P := gradedQuotientPresentation_twistKer A
    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A) i
  have hvan : VanishesOver A P U := vanishesOver_twistKer A
    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A) i U hU
  obtain ⟨d, hdpos, G, hGqc, hGft, hcut⟩ := exists_degreeSubobject A P hi.1
  obtain ⟨G', hG'qc, hG'ft, hG'surj⟩ := exists_subobject_full_over P hUc hvan hA d
  have hKqc : (kernelModule A P.hom d).IsQuasicoherent :=
    (_root_.SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (Stacks.Algebraization.kernelSubmoduleIso (P.hom.app (d : ℤ))).symm
      (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _)
  set T : Finset (FiniteTypeQuasicoherentSubobject (kernelModule A P.hom d)) :=
    {⟨G, hGqc, hGft⟩, ⟨G', hG'qc, hG'ft⟩} with hT
  set H := IsFiltered.sup T ∅ with hH
  have hleH : ∀ x ∈ T, x.1 ≤ H.1 := fun x hx => leOfHom (IsFiltered.toSup T ∅ hx).hom
  have hGH : G ≤ H.1 := hleH ⟨G, hGqc, hGft⟩ (by simp [hT])
  have hG'H : G' ≤ H.1 := hleH ⟨G', hG'qc, hG'ft⟩ (by simp [hT])
  refine ⟨d, hdpos, kernelSubobjectSubmodule A P.hom d H.1,
    isQuasicoherent_kernelSubobjectSubmodule A P.hom d H.1 H.2.1,
    isFiniteType_kernelSubobjectSubmodule A P.hom d H.1 H.2.2, ?_,
    isEquationSubmodule_kernelSubobjectSubmodule A P.hom d H.1, hcut H.1 hGH⟩
  refine supp_cokernel_disjoint (A.isQuasicoherent (d : ℤ)) _
    (isQuasicoherent_kernelSubobjectSubmodule A P.hom d H.1 H.2.1) U fun W hW a => ?_
  rw [kernelSubobjectSubmodule_obj A P.hom d H.1 W]
  have hmemK := mem_kernelSubmodule_of_vanishesOver P hvan d hW a
  obtain ⟨y, hy⟩ : a ∈ LinearMap.range (((kernelInclusion A P.hom d).val.app (op W))).hom := by
    rw [range_kernelInclusion_app A P.hom d W]
    exact hmemK
  obtain ⟨z, hz⟩ := hG'surj W hW y
  refine ⟨(Subobject.ofLE G' H.1 hG'H).val.app (op W) z, ?_⟩
  rw [← hy, ← hz]
  exact congrArg (fun f => ((f ≫ kernelInclusion A P.hom d).val.app (op W)).hom z)
    (Subobject.ofLE_arrow hG'H)

/-- **The sandwich of the proof of Stacks 085N.**  Let `ℱ ⊆ 𝒜_d` cut the closed subscheme `Z`
out on the charts of Tag 0801's presentation, and let `𝒢 ⊆ 𝒜_d` be quasi-coherent with
`ℱ ⊆ 𝒢 ⊆ ℐ_d`, `ℐ` Tag 0801's graded ideal of `Z`.  Then `Z = Proj_S(𝒜/𝒢𝒜)`: every section of `𝒢`
is an equation for `Z`, and `𝒢` cuts `Z` out on the charts because `ℱ` does
(`degreeQuotientPresenter_twistKer`). -/
theorem degreeQuotientPresentation_of_le_twistKer [IsClosedImmersion i]
    [QuasiCompact (relativeProj A).toBase] {d : ℕ} (hd : 0 < d)
    {ℱ 𝒢 : (A.piece (d : ℤ)).Submodule} (hle : ℱ ≤ 𝒢)
    (hcut : CutsOutOnCharts A ℱ
      (quotHom A (twistKerGradedIdeal A
        (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A) i)))
    (h𝒢 : 𝒢.toSheafOfModules.IsQuasicoherent)
    (h𝒢ℐ : 𝒢 ≤ (twistKerGradedIdeal A
      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A) i).piece (d : ℤ)) :
    Nonempty (DegreeQuotientPresentation A i 𝒢) :=
  degreeQuotientPresenter_twistKer A
    (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra A) i d hd 𝒢 h𝒢
    (fun U a ha => (quotProj_app_eq_zero_iff A _ (d : ℤ) U a).2 (h𝒢ℐ (op U) ha))
    (cutsOutOnCharts_mono A hle _ hcut)

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
