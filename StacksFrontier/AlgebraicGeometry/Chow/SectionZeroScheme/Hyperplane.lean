module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.RegularEquation
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleZeroScheme
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.ProjMapTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.UnitSection

/-!
# The hyperplane section of a projective bundle attached to a section

Let `ℰ` be finite locally free on a scheme `X`, `π : P = 𝐏(ℰ) ⟶ X` its projective bundle with
tautological quotient `π^*ℰ ⟶ 𝒪_P(1)`, and `s ∈ Γ(X, ℰ)`. The image `t ∈ Γ(P, 𝒪_P(1))` of `π^*s`
is the section of [Stacks, Tag 0FA9]'s proof. Over an affine open `V` of `X` its zero scheme is,
on the chart `Proj Γ(V, Sym ℰ)`, the zero scheme of the degree-one element `s|_V`.

If `x ∉ Z(s)`, then on an affine neighbourhood `V` of `x` some linear form takes the value `1` at
`s|_V`, so `s|_V` is a nonzerodivisor of `Γ(V, Sym ℰ)` and its hyperplane is an effective Cartier
divisor: at every point `ξ` of `Z(t)` over `x` the ideal of `Z(t)` contains a nonzerodivisor.

## Main definitions

* `Stacks.Chow.SectionZeroScheme.bundleSection` — the section `t` of `𝒪_P(1)`.

## Main results

* `Stacks.Chow.SectionZeroScheme.comap_chart_zeroScheme_bundleSection` — `Z(t)` on a chart.
* `Stacks.Chow.SectionZeroScheme.exists_nonZeroDivisor_mem_stalkIdeal_bundleSection` — the
  regular local equations of `Z(t)` off `π⁻¹(Z(s))`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne

universe u

namespace Stacks.Chow.SectionZeroScheme

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)

/-- **The section `t` of `𝒪(1)`**: the image of `π^*s` under the tautological quotient. -/
def bundleSectionOf (s : Γ(E, ⊤)) :
    Γ(Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc, ⊤) :=
  (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).app ⊤
    (pullbackGlobalSections (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E s)

omit [E.IsQuasicoherent] in
/-- The section `t` restricted over `π⁻¹(V)` is the image of the pulled-back section `s|_V`. -/
theorem bundleSectionOf_restrict (s : Γ(E, ⊤)) (V : X.Opens) :
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.map
        (homOfLE (le_top : (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V ≤ ⊤)).op
        (bundleSectionOf E hqc s) =
      ((projectiveBundleTwistData E hqc).ψ 1).val.app (op V)
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)
          (E.presheaf.map (homOfLE le_top).op s)) := by
  set π := (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
  have h1 : (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.map
      (homOfLE (le_top : π ⁻¹ᵁ V ≤ ⊤)).op (bundleSectionOf E hqc s) =
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app (op (π ⁻¹ᵁ V))
        (((Scheme.Modules.pullback π).obj E).val.map (homOfLE (le_top : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ ⊤)).op
          (unitSection π E ⊤ s)) := by
    refine (PresheafOfModules.naturality_apply
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val
      (homOfLE (le_top : π ⁻¹ᵁ V ≤ ⊤)).op _).symm.trans ?_
    exact congrArg (fun w => (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
      (op (π ⁻¹ᵁ V)) (((Scheme.Modules.pullback π).obj E).val.map
        (homOfLE (le_top : π ⁻¹ᵁ V ≤ ⊤)).op w))
      (Stacks.Chow.FreeTower.pullbackGlobalSections_eq_unitSection π E s)
  refine h1.trans ?_
  refine (congrArg (fun w => (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).val.app
    (op (π ⁻¹ᵁ V)) w)
      (Stacks.Chow.GenuineChern.unitSection_restrict π E (le_top : V ≤ ⊤) s).symm).trans ?_
  exact Stacks.Chow.GenuineChern.tautologicalMap_unitSection E hqc V _

/-- **The zero scheme of `t` on a chart.** Over an affine open `V` of `X`, the inverse image of
`Z(t)` along the chart `Proj Γ(V, Sym ℰ) ⟶ 𝐏(ℰ)` is the zero scheme of the global section of
`𝒪(1)` attached to the degree-one element `s|_V` of `Γ(V, Sym ℰ)`. -/
theorem comap_chart_zeroScheme_bundleSectionOf (s : Γ(E, ⊤)) (V : X.Opens) (hV : IsAffineOpen V) :
    letI := Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
      (relativeProj (schemeSheafGradedAlgebra E hqc)) V hV
    haveI := algebraicGeometry_isInvertible_twistingSheaf
      ((schemeSheafGradedAlgebra E hqc).grading V)
      (Stacks.SymGraded.adjoin_grading_one_eq_top E V hqc hV) ((1 : ℕ) : ℤ)
    (Stacks.Divisors.zeroScheme _ (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
        (bundleSectionOf E hqc s)).comap
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart V hV) =
      Stacks.Divisors.zeroScheme (Proj ((schemeSheafGradedAlgebra E hqc).grading V))
        (twistingSheafModule ((schemeSheafGradedAlgebra E hqc).grading V) ((1 : ℕ) : ℤ))
        (degreeSection ((schemeSheafGradedAlgebra E hqc).grading V) 1
          ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) 1
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)
              (E.presheaf.map (homOfLE le_top).op s)),
            (schemeSheafGradedAlgebra E hqc).of_mem_grading V _⟩) := by
  let := Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
    (relativeProj (schemeSheafGradedAlgebra E hqc)) V hV
  have := algebraicGeometry_isInvertible_twistingSheaf
    ((schemeSheafGradedAlgebra E hqc).grading V)
    (Stacks.SymGraded.adjoin_grading_one_eq_top E V hqc hV) ((1 : ℕ) : ℤ)
  set c := (relativeProj (schemeSheafGradedAlgebra E hqc)).chart V hV
  set π := (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
  set B := Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc
  set t := bundleSectionOf E hqc s
  rw [← Stacks.Divisors.zeroScheme_pullback c B t]
  refine AlgebraicGeometry.zeroScheme_eq_of_iso
    (((Scheme.Modules.restrictFunctorIsoPullback c).app B).symm ≪≫
      (projectiveBundleTwistData E hqc).chartData.chartIso V hV ((1 : ℕ) : ℤ)) ?_
  have hle : c ''ᵁ ⊤ ≤ π ⁻¹ᵁ V := by
    rintro _ ⟨y, -, rfl⟩
    exact Stacks.Chow.GenuineChern.top_le_chart_preimage E hqc V hV trivial
  -- the pulled-back section, read on the chart's image
  have hb : ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app B).val.app (op ⊤)
      (pullbackGlobalSections c B t) =
      B.val.map (homOfLE hle).op (B.presheaf.map (homOfLE (le_top : π ⁻¹ᵁ V ≤ ⊤)).op t) := by
    refine (congrArg (fun w => ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app B).val.app
      (op ⊤) w) (Stacks.Chow.FreeTower.pullbackGlobalSections_eq_unitSection c B t)).trans ?_
    exact (Stacks.Chow.GenuineChern.restrictFunctorIsoPullback_inv_unitSection' c B ⊤ t).trans
      (Stacks.Chow.GenuineChern.map_map_homOfLE' B hle le_top t).symm
  have he5 := Stacks.Chow.GenuineChern.chartIso_inv_degreeSection (E := E) (hqc := hqc) V hV
    ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)
      (E.presheaf.map (homOfLE le_top).op s)) hle
  have hinv := congrArg (fun ψ => ψ.val.app (op ⊤)
      (degreeSection ((schemeSheafGradedAlgebra E hqc).grading V) 1
        ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) 1
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)
            (E.presheaf.map (homOfLE le_top).op s)),
          (schemeSheafGradedAlgebra E hqc).of_mem_grading V _⟩))
    ((projectiveBundleTwistData E hqc).chartData.chartIso V hV ((1 : ℕ) : ℤ)).inv_hom_id
  have key : ((projectiveBundleTwistData E hqc).chartData.chartIso V hV ((1 : ℕ) : ℤ)).hom.val.app
      (op ⊤) (((Scheme.Modules.restrictFunctorIsoPullback c).inv.app B).val.app (op ⊤)
        (pullbackGlobalSections c B t)) =
      degreeSection ((schemeSheafGradedAlgebra E hqc).grading V) 1
        ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V) 1
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V)
            (E.presheaf.map (homOfLE le_top).op s)),
          (schemeSheafGradedAlgebra E hqc).of_mem_grading V _⟩ := by
    rw [hb, bundleSectionOf_restrict E hqc s V]
    exact (congrArg _ he5.symm).trans hinv
  exact key

/-- Transporting a nonzerodivisor of the ideal at a point along an equality of ideal sheaves. -/
theorem exists_nonZeroDivisor_mem_stalkIdeal_congr {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    (hIJ : I = J) {y : Y} (hy : y ∈ I.support) (hy' : y ∈ J.support)
    (h : ∃ a ∈ nonZeroDivisors (Y.presheaf.stalk y),
      a ∈ Stacks.AlgebraicGeometry.stalkIdeal I y hy) :
    ∃ a ∈ nonZeroDivisors (Y.presheaf.stalk y),
      a ∈ Stacks.AlgebraicGeometry.stalkIdeal J y hy' := by
  subst hIJ
  exact h

/-- Transporting a nonzerodivisor of the ideal at a point along an equality of points. -/
theorem exists_nonZeroDivisor_mem_stalkIdeal_of_eq {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {y y' : Y} (hyy : y = y') (hy : y ∈ I.support) (hy' : y' ∈ I.support)
    (h : ∃ a ∈ nonZeroDivisors (Y.presheaf.stalk y),
      a ∈ Stacks.AlgebraicGeometry.stalkIdeal I y hy) :
    ∃ a ∈ nonZeroDivisors (Y.presheaf.stalk y'),
      a ∈ Stacks.AlgebraicGeometry.stalkIdeal I y' hy' := by
  subst hyy
  exact h

/-- **Off the inverse image of `Z(s)`, the ideal of `Z(t)` contains a nonzerodivisor at every
point of `Z(t)`.** Near a point `x ∉ Z(s)` some linear form takes the value `1` at `s`, so `s` is
a nonzerodivisor of degree one of `Γ(V, Sym ℰ)` and `Z(t)` is its hyperplane on the chart. -/
theorem exists_nonZeroDivisor_mem_stalkIdeal_bundleSectionOf
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (s : Γ(E, ⊤))
    (ξ : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme)
    (hξ : ξ ∈ (Stacks.Divisors.zeroScheme _
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) (bundleSectionOf E hqc s)).support)
    (hx : (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ξ ∉
      (zeroSchemeOfSection X E s).supportSet) :
    ∃ a ∈ nonZeroDivisors ((relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf.stalk ξ),
      a ∈ Stacks.AlgebraicGeometry.stalkIdeal (Stacks.Divisors.zeroScheme _
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) (bundleSectionOf E hqc s))
        ξ hξ := by
  obtain ⟨V, hxV, -, l, hl⟩ := exists_linearForm_eq_one E s hx (W := ⊤) trivial
  let := Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
    (relativeProj (schemeSheafGradedAlgebra E hqc)) V.1 V.2
  have := algebraicGeometry_isInvertible_twistingSheaf
    ((schemeSheafGradedAlgebra E hqc).grading V.1)
    (Stacks.SymGraded.adjoin_grading_one_eq_top E V.1 hqc V.2) ((1 : ℕ) : ℤ)
  set c := (relativeProj (schemeSheafGradedAlgebra E hqc)).chart V.1 V.2
  -- the point lies on the chart
  obtain ⟨ξ', -, hξ'⟩ : ξ ∈ c ''ᵁ ⊤ :=
    Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top
      (relativeProj (schemeSheafGradedAlgebra E hqc)) V.1 V.2 ▸ hxV
  have hcξ : c ξ' = ξ := hξ'
  -- the degree-one element `s|_V` is a nonzerodivisor
  let u : (schemeSheafGradedAlgebra E hqc).grading V.1 1 :=
    ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces V.1) 1
      ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op V.1)
        (E.presheaf.map (homOfLE le_top).op s)),
      (schemeSheafGradedAlgebra E hqc).of_mem_grading V.1 _⟩
  have hu : IsRegular (u : (schemeSheafGradedAlgebra E hqc).sectionRing V.1) := by
    have h := Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of_symmetricAlgebraGen E V.2 hqc
      (E.presheaf.map (homOfLE le_top).op s)
    have hr := Stacks.Chow.GenuineChern.isRegular_ringEquiv
      (Stacks.SymGraded.AffinePieces.symSectionRingEquiv E V.2 hqc).symm
      (Stacks.Chow.GenuineChern.isRegular_ι_of_eq_one (E.presheaf.map (homOfLE le_top).op s) l hl)
    rwa [← h, RingEquiv.symm_apply_apply] at hr
  have hcomap := comap_chart_zeroScheme_bundleSectionOf E hqc s V.1 V.2
  have hξ'' : ξ' ∈ ((Stacks.Divisors.zeroScheme _
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
        (bundleSectionOf E hqc s)).comap c).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change c ξ' ∈ (Stacks.Divisors.zeroScheme _
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) (bundleSectionOf E hqc s)).support
    rwa [hcξ]
  have hdeg := exists_nonZeroDivisor_mem_stalkIdeal_degreeSection
    ((schemeSheafGradedAlgebra E hqc).grading V.1)
    (Stacks.SymGraded.adjoin_grading_one_eq_top E V.1 hqc V.2) u hu ξ' (hcomap ▸ hξ'')
  exact exists_nonZeroDivisor_mem_stalkIdeal_of_eq _ hcξ _ hξ
    (exists_nonZeroDivisor_mem_stalkIdeal_of_comap _ c ξ' (hcξ ▸ hξ) hξ''
      (exists_nonZeroDivisor_mem_stalkIdeal_congr hcomap.symm _ hξ'' hdeg))

end Stacks.Chow.SectionZeroScheme

end
