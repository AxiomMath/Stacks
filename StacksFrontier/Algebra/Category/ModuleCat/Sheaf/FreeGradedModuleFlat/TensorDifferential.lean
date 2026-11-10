module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleCoefficients
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleFlat.SignDegreeRaising

/-!
# The differential of `A[S] ⊗_A N`

Condition (2) is the source's argument. Under the identification with `N[S]` the differential of
`A[S] ⊗_A N` becomes `(-1)^{deg s}` times the differential of `N` on the summand of `s`, the
canonical generators of `A[S]` being closed; that identification is
`SheafOfModules.freeTensorCoeff_dgTensorDiff`, proved from the Leibniz rule of `N`. Acyclicity is
then `SheafOfModules.coeffPiece_exact_sign` degree by degree — the sign, which the source
dismisses in a clause, being an isomorphism of short complexes — applied to
`SheafOfModules.coeffPiece_exact`, which has to be preservation of exactness and not merely of
short exactness because the short complexes computing the homology of a complex are not short
exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w t a m z v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### The differential of `A[S] ⊗_A N`

On a local section `s · a ⊗ y` the differential of `A[S] ⊗_A N` is `d(s · a) ⊗ y` corrected by
`(-1)^{deg (s · a)} s · a ⊗ dy`; the generators are closed, so the first term is
`(-1)^{deg s} s · (da) ⊗ y`, and the Leibniz rule of `N` turns the sum into
`(-1)^{deg s} s · d(ay)`. That is the signed degree-raising map of `N[S]`. -/

section FreeDifferential

variable [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)] [HasSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] {Osharp : Sheaf J CommRingCat.{t}}
  (S : SheafOfGradedSets.{m} J) (D : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp))
  (N : LeftDifferentialGradedModule.{t, m, m} D)

/-- The differential of a left differential graded module, read on the pieces of the underlying
left graded module. -/
noncomputable abbrev gNDiff {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
    (M : LeftDifferentialGradedModule.{t, m, m} A) :
    ∀ k k' : ℤ, (RelativeTensor.gN M).piece k ⟶ (RelativeTensor.gN M).piece k' :=
  M.complex.d

omit [HasWeakSheafify J (Type m)] [HasSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- **The Leibniz rule on the summand of a generator.** The differential of `N` applied to the
coefficient `ay` of the summand of a generator of degree `j` of `A[S] ⊗_A N`, transported into
the degree that summand has in total degree `n + 1`, is `(da)y` corrected by
`(-1)^{deg a} a (dy)`, each transported into the same degree. -/
theorem smul_leibniz_castHom (p q mm j : ℤ) (h : p + q = mm) (U : Cᵒᵖ)
    (a : (D.toGradedAlgebra.piece (p - j)).val.obj U)
    (y : ((RelativeTensor.gN N).piece q).val.obj U) :
    castHom (RelativeTensor.gN N).piece (show mm - j + 1 = mm + 1 - j by omega) U
        (homSections (gNDiff N (mm - j) (mm - j + 1)) U
          (castHom (RelativeTensor.gN N).piece (show p - j + q = mm - j by omega) U
            ((RelativeTensor.gN N).smul (p - j) q U a y))) =
      castHom (RelativeTensor.gN N).piece (show p + 1 - j + q = mm + 1 - j by omega) U
          ((RelativeTensor.gN N).smul (p + 1 - j) q U
            (castHom D.toGradedAlgebra.piece (show p - j + 1 = p + 1 - j by omega) U
              (homSections (D.complex.d (p - j) (p - j + 1)) U a)) y) +
        (Int.negOnePow (p - j) : ℤ) •
          castHom (RelativeTensor.gN N).piece (show p - j + (q + 1) = mm + 1 - j by omega) U
            ((RelativeTensor.gN N).smul (p - j) (q + 1) U a
              (homSections (gNDiff N q (q + 1)) U y)) := by
  have hleib : homSections (gNDiff N (p - j + q) (p - j + q + 1)) U
        ((RelativeTensor.gN N).smul (p - j) q U a y) =
      castHom (RelativeTensor.gN N).piece
            (show p - j + 1 + q = p - j + q + 1 by omega) U
            ((RelativeTensor.gN N).smul (p - j + 1) q U
              (homSections (D.complex.d (p - j) (p - j + 1)) U a) y) +
          (Int.negOnePow (p - j) : ℤ) •
            castHom (RelativeTensor.gN N).piece
              (show p - j + (q + 1) = p - j + q + 1 by omega) U
              ((RelativeTensor.gN N).smul (p - j) (q + 1) U a
                (homSections (gNDiff N q (q + 1)) U y)) := by
    rw [castHom_apply, castHom_apply]
    exact N.leibniz (p - j) q U a y
  rw [homSections_castHom (RelativeTensor.gN N).piece (gNDiff N)
      (show p - j + q = mm - j by omega) (show p - j + q + 1 = mm - j + 1 by omega) U,
    Cofree.castHom_castHom, hleib, map_add, AddMonoidHom.map_zsmul, Cofree.castHom_castHom,
    Cofree.castHom_castHom, LeftGradedModule.smul_castHom_alg]

omit [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- **The differential of `A[S] ⊗_A N` on the coefficients of a section of the presentation.**
The coefficients of `d(ζ ⊗ y)`, for `ζ` a section of the presentation of `A[S]^p` and `y` a
section of `N^q`, are the signed degree-raising map applied to the coefficients of `ζ ⊗ y`. This
is the Leibniz rule of `N` summand by summand, the canonical generators of `A[S]` being
closed. -/
theorem freeTensorCoeffPres_dPres (p q mm : ℤ) (h : p + q = mm) (U : Cᵒᵖ)
    (y : ((RelativeTensor.gN N).piece q).val.obj U)
    (ζ : freeSections D.toGradedAlgebra S p U) :
    freeTensorCoeffPres D.toGradedAlgebra S (RelativeTensor.gN N) (p + 1) q (mm + 1)
          (by omega) U y (dPres S D p U ζ) +
        (Int.negOnePow p : ℤ) • freeTensorCoeffPres D.toGradedAlgebra S (RelativeTensor.gN N) p
          (q + 1) (mm + 1) (by omega) U (homSections (gNDiff N q (q + 1)) U y) ζ =
      coeffSignDiffAddHom S (RelativeTensor.gN N).piece (gNDiff N) mm U
        (freeTensorCoeffPres D.toGradedAlgebra S (RelativeTensor.gN N) p q mm h U y ζ) := by
  induction ζ using freeSections_induction with
  | hzero => simp only [map_zero, smul_zero, add_zero]
  | hof j s hs a =>
    rw [dPres_freeOf, AddMonoidHom.map_zsmul]
    simp only [freeTensorCoeffPres_freeOf, coeffSignDiffAddHom_coeffOf]
    rw [← coeffOf_zsmul, ← coeffOf_zsmul, ← coeffOf_add]
    refine coeffOf_congr S (RelativeTensor.gN N).piece (mm + 1) U j _ _ rfl ?_
    rw [smul_leibniz_castHom D N p q mm j h U a y, smul_add, smul_smul, ← Units.val_mul,
      ← Int.negOnePow_add, show j + (p - j) = p by omega]
  | hadd ζ ζ' hζ hζ' =>
    simp only [map_add, smul_add]
    rw [← hζ, ← hζ']
    abel

omit [HasWeakSheafify J (Type m)] in
/-- The differential of `P ⊗_A N` on a local section `x ⊗ y`:
`d(x ⊗ y) = dx ⊗ y + (-1)^{deg x} x ⊗ dy`. This is Tag 0FRM read on a local section, which this
file needs for the free differential graded module and which the module registering that tag
does not state; no `@[stacks 0FRM]` attribute is carried here. -/
private theorem dgTensorDiff_tmul (P : DifferentialGradedModule.{t, m, m} D) (mm : ℤ)
    (p : TensorIndex mm) (X : Cᵒᵖ)
    (x : ((RelativeTensor.gP P).piece p.1.1).val.obj X)
    (y : ((RelativeTensor.gN N).piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app ((RelativeTensor.dgTensor P N).d mm (mm + 1)).val X
        (RelativeTensor.tmul (RelativeTensor.gP P) (RelativeTensor.gN N) mm p X x y) =
      RelativeTensor.tmul (RelativeTensor.gP P) (RelativeTensor.gN N) (mm + 1)
            (RelativeTensor.tensorIndexShiftLeft p) X
            ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X x) y +
          (Int.negOnePow p.1.1 : ℤ) • RelativeTensor.tmul (RelativeTensor.gP P)
            (RelativeTensor.gN N) (mm + 1) (RelativeTensor.tensorIndexShiftRight p) X x
            ((N.complex.d p.1.2 (p.1.2 + 1)).val.app X y) := by
  have hd : (RelativeTensor.dgTensor P N).d mm (mm + 1) =
      (PresheafOfModules.sheafification (R := toRingCat J Osharp)
        (𝟙 (toRingCat J Osharp).obj)).map (RelativeTensor.dgTensorDiffPre P N mm) :=
    congrArg (fun φ : RelativeTensor.gradedTensorPre (RelativeTensor.gP P)
        (RelativeTensor.gN N) mm ⟶ RelativeTensor.gradedTensorPre (RelativeTensor.gP P)
          (RelativeTensor.gN N) (mm + 1) ↦
      (PresheafOfModules.sheafification (R := toRingCat J Osharp)
        (𝟙 (toRingCat J Osharp).obj)).map φ) (CochainComplex.of_d _ _ mm)
  rw [hd]
  refine (PresheafOfModules.unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    (RelativeTensor.dgTensorDiffPre P N mm) X _).trans ?_
  have hstep : PresheafOfModules.Hom.app (RelativeTensor.dgTensorDiffPre P N mm) X
        (PresheafOfModules.Hom.app (RelativeTensor.gradedTensorπ (RelativeTensor.gP P)
          (RelativeTensor.gN N) mm) X
          (PresheafOfModules.Hom.app (RelativeTensor.tensorSumι (RelativeTensor.gP P)
            (RelativeTensor.gN N) p) X (x ⊗ₜ y))) =
      PresheafOfModules.Hom.app (RelativeTensor.gradedTensorπ (RelativeTensor.gP P)
        (RelativeTensor.gN N) (mm + 1)) X
        (PresheafOfModules.Hom.app (RelativeTensor.tensorSumι (RelativeTensor.gP P)
            (RelativeTensor.gN N) (RelativeTensor.tensorIndexShiftLeft p)) X
            ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X x ⊗ₜ y) +
          (Int.negOnePow p.1.1 : ℤ) •
            PresheafOfModules.Hom.app (RelativeTensor.tensorSumι (RelativeTensor.gP P)
              (RelativeTensor.gN N) (RelativeTensor.tensorIndexShiftRight p)) X
              (x ⊗ₜ (N.complex.d p.1.2 (p.1.2 + 1)).val.app X y)) :=
    ((PresheafOfModules.comp_app_apply (RelativeTensor.gradedTensorπ (RelativeTensor.gP P)
      (RelativeTensor.gN N) mm) (RelativeTensor.dgTensorDiffPre P N mm) X _).symm.trans
        ((PresheafOfModules.hom_congr_apply' (RelativeTensor.gradedTensorπ_dgTensorDiffPre N mm)
          X _).trans
          (PresheafOfModules.comp_app_apply (RelativeTensor.dgTensorSumDiff P N mm)
            (RelativeTensor.gradedTensorπ (RelativeTensor.gP P)
              (RelativeTensor.gN N) (mm + 1)) X _))).trans
      (congrArg (fun z ↦ PresheafOfModules.Hom.app (RelativeTensor.gradedTensorπ
          (RelativeTensor.gP P) (RelativeTensor.gN N) (mm + 1)) X z)
        (RelativeTensor.dgTensorSumDiff_tensorSumι_apply P N p X x y))
  rw [hstep, map_add, map_zsmul, map_add, map_zsmul]
  rfl

/-- The differential of `A[S] ⊗_A N` on a local section `x ⊗ y`, with the differential of `A[S]`
written as `SheafOfModules.freeD`. -/
theorem freeDgTensorDiff_tmul (mm : ℤ) (p : TensorIndex mm) (X : Cᵒᵖ)
    (x : ((freeGradedModule D.toGradedAlgebra S).piece p.1.1).val.obj X)
    (y : ((RelativeTensor.gN N).piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app
        ((RelativeTensor.dgTensor (freeDGModule S D) N).d mm (mm + 1)).val X
        (RelativeTensor.tmul (freeGradedModule D.toGradedAlgebra S)
          (RelativeTensor.gN N) mm p X x y) =
      RelativeTensor.tmul (freeGradedModule D.toGradedAlgebra S) (RelativeTensor.gN N) (mm + 1)
            (RelativeTensor.tensorIndexShiftLeft p) X ((freeD S D p.1.1).val.app X x) y +
          (Int.negOnePow p.1.1 : ℤ) • RelativeTensor.tmul
            (freeGradedModule D.toGradedAlgebra S) (RelativeTensor.gN N) (mm + 1)
            (RelativeTensor.tensorIndexShiftRight p) X x
            (homSections (gNDiff N p.1.2 (p.1.2 + 1)) X y) := by
  refine Eq.trans (dgTensorDiff_tmul D N (freeDGModule S D) mm p X x y) ?_
  rw [freeDGModule_complex_d]
  rfl

/-- **The identification `A[S] ⊗_A N = N[S]` carries the differential to the signed
degree-raising map, on a local section `x ⊗ y`.** The computation is on a local lift of `x` to
the presentation of `A[S]^{deg x}`, where the differential of `A[S]` is
`SheafOfModules.dPres` and the coefficients are `SheafOfModules.freeTensorCoeffPres`, and there
it is `freeTensorCoeffPres_dPres`. -/
theorem freeTensorCoeff_dgTensorDiff_tmul (mm : ℤ) (p : TensorIndex mm) (X : Cᵒᵖ)
    (x : ((freeGradedModule D.toGradedAlgebra S).piece p.1.1).val.obj X)
    (y : ((RelativeTensor.gN N).piece p.1.2).val.obj X) :
    (freeTensorCoeff D.toGradedAlgebra S (RelativeTensor.gN N) (mm + 1)).val.app X
        (PresheafOfModules.Hom.app
          ((RelativeTensor.dgTensor (freeDGModule S D) N).d mm (mm + 1)).val X
          (RelativeTensor.tmul (freeGradedModule D.toGradedAlgebra S)
            (RelativeTensor.gN N) mm p X x y)) =
      (coeffSignDiffPiece S (RelativeTensor.gN N).piece (gNDiff N) mm).val.app X
        ((freeTensorCoeff D.toGradedAlgebra S (RelativeTensor.gN N) mm).val.app X
          (RelativeTensor.tmul (freeGradedModule D.toGradedAlgebra S)
            (RelativeTensor.gN N) mm p X x y)) := by
  have h₁ := freeTensorCoeff_tmul D.toGradedAlgebra S (RelativeTensor.gN N) (mm + 1)
    (RelativeTensor.tensorIndexShiftLeft p) X ((freeD S D p.1.1).val.app X x) y
  have h₂ := freeTensorCoeff_tmul D.toGradedAlgebra S (RelativeTensor.gN N) (mm + 1)
    (RelativeTensor.tensorIndexShiftRight p) X x (homSections (gNDiff N p.1.2 (p.1.2 + 1)) X y)
  have h₃ := freeTensorCoeff_tmul D.toGradedAlgebra S (RelativeTensor.gN N) mm p X x y
  rw [freeDgTensorDiff_tmul S D N mm p X x y, map_add, map_zsmul, h₁, h₂, h₃]
  refine Stacks.eq_of_forall_lift
    (coeffPiece S (RelativeTensor.gN N).piece (mm + 1)).isSheaf.isSeparated
    (freeUnit D.toGradedAlgebra S p.1.1) x _ _ ?_
  intro Y f ζ hζ
  have hζ' : (freeUnit D.toGradedAlgebra S (p.1.1 + 1)).app Y (dPres S D p.1.1 Y ζ) =
      (freePiece D.toGradedAlgebra S (p.1.1 + 1)).val.map f ((freeD S D p.1.1).val.app X x) :=
    (freeD_unit S D p.1.1 Y ζ).symm.trans
      ((congrArg (fun z ↦ (freeD S D p.1.1).val.app Y z) hζ).trans
        (PresheafOfModules.naturality_apply (freeD S D p.1.1).val f x))
  have e₁ := freeTensorCoeffBilin_lift D.toGradedAlgebra S (RelativeTensor.gN N) (p.1.1 + 1)
    p.1.2 (mm + 1) (by have hp := p.2; omega) X ((freeD S D p.1.1).val.app X x) y f
    (dPres S D p.1.1 Y ζ) hζ'
  have e₂ := freeTensorCoeffBilin_lift D.toGradedAlgebra S (RelativeTensor.gN N) p.1.1
    (p.1.2 + 1) (mm + 1) (by have hp := p.2; omega) X x
    (homSections (gNDiff N p.1.2 (p.1.2 + 1)) X y) f ζ hζ
  have e₃ := freeTensorCoeffBilin_lift D.toGradedAlgebra S (RelativeTensor.gN N) p.1.1 p.1.2 mm
    p.2 X x y f ζ hζ
  have hnat : sectionRestrict (coeffPiece S (RelativeTensor.gN N).piece (mm + 1)).val f
        ((coeffSignDiffPiece S (RelativeTensor.gN N).piece (gNDiff N) mm).val.app X
          ((freeTensorCoeffBilin D.toGradedAlgebra S (RelativeTensor.gN N) p.1.1 p.1.2 mm
            p.2).app X x y)) =
      (coeffSignDiffPiece S (RelativeTensor.gN N).piece (gNDiff N) mm).val.app Y
        (sectionRestrict (coeffPiece S (RelativeTensor.gN N).piece mm).val f
          ((freeTensorCoeffBilin D.toGradedAlgebra S (RelativeTensor.gN N) p.1.1 p.1.2 mm
            p.2).app X x y)) :=
    (PresheafOfModules.naturality_apply
      (coeffSignDiffPiece S (RelativeTensor.gN N).piece (gNDiff N) mm).val f
      ((freeTensorCoeffBilin D.toGradedAlgebra S (RelativeTensor.gN N) p.1.1 p.1.2 mm
        p.2).app X x y)).symm
  have hdy : sectionRestrict ((RelativeTensor.gN N).piece (p.1.2 + 1)).val f
        (homSections (gNDiff N p.1.2 (p.1.2 + 1)) X y) =
      homSections (gNDiff N p.1.2 (p.1.2 + 1)) Y
        (sectionRestrict ((RelativeTensor.gN N).piece p.1.2).val f y) :=
    homSections_naturality (gNDiff N p.1.2 (p.1.2 + 1)) f y
  have hu := coeffSignDiffPiece_coeffUnit S (RelativeTensor.gN N).piece (gNDiff N) mm Y
    (freeTensorCoeffPres D.toGradedAlgebra S (RelativeTensor.gN N) p.1.1 p.1.2 mm p.2 Y
      (sectionRestrict ((RelativeTensor.gN N).piece p.1.2).val f y) ζ)
  change sectionRestrict (coeffPiece S (RelativeTensor.gN N).piece (mm + 1)).val f _ =
    sectionRestrict (coeffPiece S (RelativeTensor.gN N).piece (mm + 1)).val f _
  rw [map_add, map_zsmul, e₁, e₂, hnat, e₃, hu, hdy]
  refine Eq.trans ?_ (congrArg
    (fun z ↦ (coeffUnit S (RelativeTensor.gN N).piece (mm + 1)).app Y z)
    (freeTensorCoeffPres_dPres S D N p.1.1 p.1.2 mm p.2 Y
      (sectionRestrict ((RelativeTensor.gN N).piece p.1.2).val f y) ζ))
  rw [coeffUnit_add, coeffUnit_zsmul]

/-- **The identification `A[S] ⊗_A N = N[S]` carries the differential of the relative tensor
product to the signed degree-raising map of `N[S]`.** -/
theorem freeTensorCoeff_dgTensorDiff (mm : ℤ) :
    (RelativeTensor.dgTensor (freeDGModule S D) N).d mm (mm + 1) ≫
        (freeTensorCoeffIso D.toGradedAlgebra S (RelativeTensor.gN N) (mm + 1)).hom =
      (freeTensorCoeffIso D.toGradedAlgebra S (RelativeTensor.gN N) mm).hom ≫
        coeffSignDiffPiece S (RelativeTensor.gN N).piece (gNDiff N) mm :=
  RelativeTensor.gradedTensor_hom_ext (freeGradedModule D.toGradedAlgebra S)
    (RelativeTensor.gN N) fun p X x y ↦
      freeTensorCoeff_dgTensorDiff_tmul S D N mm p X x y

end FreeDifferential

end SheafOfModules

end
