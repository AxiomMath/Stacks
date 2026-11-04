module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceOfStepSquares
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquareAtCut
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The two squares of Section 0FMK on the step of the filtration

`Stacks.DeRhamSmooth.StepSquares` is the conjunction, at every cut `k`, of the square of
[Stacks, Section 0FMK] in the degree of the cut and the squares above it. The squares above the
cut are `Stacks.DeRhamSmooth.grMapπ_f_comp_gradedPieceXIsoGradedTargetX_hom_comp_d`; this file
reduces `Stacks.DeRhamSmooth.StepSquares` to the square at the cut, proves that square
(`Stacks.DeRhamSmooth.filtrationXIsoCutWedgeSource_hom_comp_comp_d`) and concludes
`Stacks.DeRhamSmooth.stepSquares`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.DeRhamDirectImage

universe u

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **`Stacks.DeRhamSmooth.StepSquares` from the square at the cut**: the squares above the cut
hold at every cut (`Stacks.DeRhamSmooth.grMapπ_f_comp_gradedPieceXIsoGradedTargetX_hom_comp_d`),
so the square in the degree of the cut is all that is left. -/
theorem stepSquares_of_atCut [Smooth f]
    (hcut : ∀ k : ℕ,
      (filtrationXIsoCutWedgeSource f g k).hom ≫
          (pushforward (toInverseImageBase (f ≫ g))).map
              (cutWedgeSourceIsoPullbackTensor f g k).hom ≫
            (gradedSourceMixedTensorCoefficientIso f g k
                (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ))).inv ≫
              ((-1 : ℤ) ^ k • (coefficientRestriction f g).map
                  ((pulledBackTargetFormsTensor f g k).map
                    ((deRhamCochainXIso f 0).inv ≫
                      (deRhamCochainComplex f).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) ≫
                        (deRhamCochainXIso f (0 + 1)).hom))) ≫
                (gradedTargetXIso f g k (0 + 1) (k + 1 + 0) (by omega)).inv =
        ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d
            ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) ≫
          (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
              (deRhamSmoothFiltration f g)).f ((k + 1 + 0 : ℕ) : ℤ) ≫
            (gradedPieceXIsoGradedTargetX f g k 0).hom) :
    StepSquares f g :=
  fun k => ⟨hcut k, fun j => grMapπ_f_comp_gradedPieceXIsoGradedTargetX_hom_comp_d f g k j⟩

/-- **The square of Section 0FMK at the cut**: on the `k`-th graded piece, in degree `k`, the
comparison through `Stacks.DeRhamSmooth.filtrationXIsoCutWedgeSource`,
`Stacks.DeRhamSmooth.cutWedgeSourceIsoPullbackTensor` and
`Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso` carries the differential of the step
into degree `k + 1` to `(-1)^k (1 ⊗ d_{X/Y})`. Both sides are read on the epimorphism
`w ≫ (filtrationXIsoCutWedgeSource f g k).inv` (`Stacks.DeRhamSmooth.epi_cutSource_comp_inv`) and
after the monomorphism `gradedTargetXToStepQuotient f g k 0`: the left side by (ii) and (iii)
(`Stacks.DeRhamSmooth.cutSource_comp_cutWedgeSource_comp_mixedTensor_inv`,
`Stacks.DeRhamSmooth.cutSourceToTarget_comp_d`), the right side by
`Stacks.DeRhamSmooth.comp_d_comp_grMapπ_f_comp_toStepQuotient_atCut`, and the Leibniz rule modulo
`F^{k+1}` (`AlgebraicGeometry.SheafOfModules.summandOfEq_d_comp_of_comp_eq_zero`) matches them
(`Stacks.CategoryTheory.eq_comp_comp_comp_of_leibniz`). -/
theorem filtrationXIsoCutWedgeSource_hom_comp_comp_d [Smooth f] (k : ℕ) :
    (filtrationXIsoCutWedgeSource f g k).hom ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
            (cutWedgeSourceIsoPullbackTensor f g k).hom ≫
          (gradedSourceMixedTensorCoefficientIso f g k
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ))).inv ≫
            ((-1 : ℤ) ^ k • (coefficientRestriction f g).map
                ((pulledBackTargetFormsTensor f g k).map
                  ((deRhamCochainXIso f 0).inv ≫
                    (deRhamCochainComplex f).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) ≫
                      (deRhamCochainXIso f (0 + 1)).hom))) ≫
              (gradedTargetXIso f g k (0 + 1) (k + 1 + 0) (by omega)).inv =
      ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d
          ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + 0 : ℕ) : ℤ) ≫
          (gradedPieceXIsoGradedTargetX f g k 0).hom := by
  have H1 := Stacks.CategoryTheory.comp_inv_comp_comp_smul_eq
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
      CommRingCat.{u} (f ≫
      g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
      ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
      g)))).X 0) ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
      CommRingCat.{u} (f ≫
      g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
      ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
      g)).exteriorPower 0))) (filtrationXIsoCutWedgeSource f g k)
    _ _ _ _ (gradedTargetXToStepQuotient f g k 0) _ _ _ ((-1 : ℤ) ^ k)
    (cutSource_comp_cutWedgeSource_comp_mixedTensor_inv f g k) (cutSourceToTarget_comp_d f g k)
  have hL := AlgebraicGeometry.SheafOfModules.summandOfEq_d_comp_of_comp_eq_zero
    (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))
    (pulledBackDifferentialsAlgebras f g) (Scheme.Hom.relativeDifferentialsShortComplex f g).f
    (pulledBackDeRhamComplex f g) (Stacks.DeRhamPullback.deRhamPullbackChain f g)
    (pulledBackFormsComparison f g) (deRhamPullbackChain_f_eq_pulledBackFormsComparison_comp f g)
    k 0 k (Nat.add_zero k) _
    (restrictScalars_map_prodWedgeHomOfEq_comp_toStepQuotient_atCut f g k)
  have hstar := congrArg (fun t => (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
      S.sheaf)).obj ((pulledBackDeRhamComplex f g).X k)).map (formsDifferential (f ≫ g) 0)) ≫ t)
      (stepSummandToGradedTarget_comp_toStepQuotient f g k 0)
  have H3 := comp_d_comp_grMapπ_f_comp_toStepQuotient_atCut f g k _
    (cutSource_comp_inv_comp_ι_app_f_comp_extendXIso_hom f g k)
  have h4 := Stacks.CategoryTheory.eq_comp_comp_comp_of_leibniz (h₃ := H3) (hE := H1)
    (hstar := hstar) (hL := hL) (hiL := fun _ => by kernel_rfl) (hR := by kernel_rfl) (hQ := by
        kernel_rfl)
    (hA := by kernel_rfl) (hB := by kernel_rfl) (hW := by kernel_rfl) (hd := by kernel_hrfl)
    (ha := by kernel_hrfl) (hb := by kernel_hrfl) (hx := by kernel_hrfl) (hv := by kernel_hrfl)
    (hσ := rfl)
  exact Stacks.CategoryTheory.eq_comp_comp_of_cancel _ (epi_cutSource_comp_inv f g k) _ _ _ _ _
    (mono_gradedTargetXToStepQuotient f g k 0) _ _ H1 H3 h4

/-- **The two squares of Section 0FMK on the step of the filtration**, for `f` smooth: the square
at the cut (`Stacks.DeRhamSmooth.filtrationXIsoCutWedgeSource_hom_comp_comp_d`) and the squares
above it (`Stacks.DeRhamSmooth.grMapπ_f_comp_gradedPieceXIsoGradedTargetX_hom_comp_d`). With
`Stacks.DeRhamSmooth.exists_boundedDeRhamSpectralSequence_of_stepSquares` this makes
[Stacks, Tag 0FMM] unconditional. -/
theorem stepSquares [Smooth f] : StepSquares f g :=
  stepSquares_of_atCut f g (filtrationXIsoCutWedgeSource_hom_comp_comp_d f g)

end Stacks.DeRhamSmooth

end
