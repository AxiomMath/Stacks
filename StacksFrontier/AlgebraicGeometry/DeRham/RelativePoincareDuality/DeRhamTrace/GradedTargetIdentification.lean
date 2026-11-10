module

public import
StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedComplexIdentities
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamPushData
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModel
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceExistence
public import
  StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedPerfectOnX
public import
StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetTopInclusion
public import
  StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetCupProduct
public import
  StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetNaiveCup

/-!
# The pushed pairings of the graded pieces, through the trace of [Stacks, Tag 0G8I]

Let `t : Rf_*(Ω^•[2n]) ⟶ 𝒪_S` restrict on the top piece to `Rf_*ψ ≫ Tr` for an isomorphism
`ψ : Ω^n[n] ≅ ω^•_{X/S}`. For complexes `A`, `B'` of `𝒪_X`-modules and a pairing
`h : Tot(A ⊗ B') ⟶ Ω^n[-n][2n]`, the pairing of `ι_*A` and `ι_*B'` into `Ω^•_{X/S}[2n]` given by
the naive cup product, `ι_*h` and the inclusion of the top piece, pushed down to `S` along the
relative cup product of `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)` and `t`, is — up to isomorphisms of the paired
objects — the pairing `Rf_*QA ⊗^L Rf_*QB' ⟶ 𝒪_S` of the relative cup product along `f`, `Rf_*` of
`h` followed by `Ω^n[-n][2n] ≅ Ω^n[n]` and `ψ`, and the trace. It is stated for `B' = B[2n]` and
the shift `h` of a pairing `Tot(A ⊗ B) ⟶ Ω^n[-n]` in its second variable, the case the proof
uses. This is the target identification
of the proof of [Stacks, Tag 0G8K]: it combines [Stacks, Tag 0FP3] for `ι`, [Stacks, Tag 0FP6]
for `f = ι ≫ π` and the description of the inclusion of the top piece
(`AlgebraicGeometry.RelativeDualitySituation.topInclusion`).

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.exists_pushedPairing_eq_relativeCupProduct`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DeRhamDirectImage (inverseImageBase toInverseImageBase inverseImageBaseProjection)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex naiveCupProduct)
open Stacks.Cohomology.DerivedPullbackTensor (tensorComplexBifunctorOn)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable (D : RelativeDualitySituation.{u})

/-- The restriction `hs` of a trace to the top piece, as an equation in the derived category of
`𝒪_S`-modules on the ringed site. -/
theorem topInclusion_comp_eq_map_comp_trace (D : RelativeDualitySituation.{u}) (ψ :
    (D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧ ≅ (Stacks.Duality.relativeDualizingComplex D.f
      (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0)).obj) (s : D.deRhamDirectImageTop ⟶
          (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj) (hs : D.topInclusion ≫ s =
          (Stacks.Duality.derivedPushforward D.f).map ψ.hom ≫
      (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace D.f
        (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
        (Stacks.Duality.derivedStructureSheafInDegree D.S 0))) :
    (@CategoryStruct.comp (Stacks.DerivedTensor.RingedSite.DerivedModules D.S.toRingedSpace.sheaf) _
        _ _ _ D.topInclusion s) = (@CategoryStruct.comp
        (Stacks.DerivedTensor.RingedSite.DerivedModules D.S.toRingedSpace.sheaf) _ _ _ _
        ((derivedPushforward D.f.toLRSHom.toShHom).map ψ.hom) ((ObjectProperty.ι _).map
        (Stacks.Duality.relativeDualizingComplexTrace D.f
            (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
            (Stacks.Duality.derivedStructureSheafInDegree D.S 0)))) :=
  hs
/-- `duality_map_topComplexShiftHom_comp_topInclusion`, as an equation in the derived category of
`𝒪_S`-modules on the ringed site. -/
theorem map_topComplexShiftHom_comp_topInclusion_derivedModules (D : RelativeDualitySituation.{u}) :
    (@CategoryStruct.comp (Stacks.DerivedTensor.RingedSite.DerivedModules D.S.toRingedSpace.sheaf) _
        _ _ _ ((Stacks.Duality.derivedPushforward D.f).map D.topComplexShiftHom) D.topInclusion) =
        (@CategoryStruct.comp (Stacks.DerivedTensor.RingedSite.DerivedModules
        D.S.toRingedSpace.sheaf) _ _ _ _ ((Scheme.Hom.inverseImageBaseFactorIso D.f
        D.f.toLRSHom.toShHom (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f)).hom.app
        (DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧))) ((derivedPushforward
        (inverseImageBaseProjection D.f)).map ((@inv _ _ _ _ (pushforwardComparisonQ
        (toInverseImageBase D.f) (D.topComplexX⟦(2 * D.n : ℤ)⟧))
        (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f _)) ≫
        (DerivedCategory.Q.map D.topComplexToDeRhamShift) ≫ ((DerivedCategory.Q.commShiftIso (2 *
        D.n : ℤ)).hom.app (D.deRhamCx.extend ComplexShape.embeddingUpNat))))) :=
  duality_map_topComplexShiftHom_comp_topInclusion D
/-- `Rf_*` of the composite of the shifted pairing, `topComplexShiftHom` and `ψ`. -/
theorem map_shiftedFormsPairing_comp_comp (D : RelativeDualitySituation.{u}) (ψ :
    (D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧ ≅ (Stacks.Duality.relativeDualizingComplex D.f
      (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0)).obj) {A B : CochainComplex (ModulesOn
          D.X.toRingedSpace) ℤ} (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶
          D.topComplexX) :
    ((Stacks.Duality.derivedPushforward D.f).map ((D.shiftedFormsPairing h) ≫ D.topComplexShiftHom ≫
        ψ.hom)) = (@CategoryStruct.comp (Stacks.DerivedTensor.RingedSite.DerivedModules
        D.S.toRingedSpace.sheaf) _ _ _ _ ((Stacks.Duality.derivedPushforward D.f).map
        (D.shiftedFormsPairing h)) (@CategoryStruct.comp
        (Stacks.DerivedTensor.RingedSite.DerivedModules D.S.toRingedSpace.sheaf) _ _ _ _
        ((Stacks.Duality.derivedPushforward D.f).map D.topComplexShiftHom)
        ((Stacks.Duality.derivedPushforward D.f).map ψ.hom))) :=
  ((Stacks.Duality.derivedPushforward D.f).map_comp _ _).trans (congrArg _
      ((Stacks.Duality.derivedPushforward D.f).map_comp _ _))
/-- The two derived direct images along `f` agree on the shifted pairing. -/
theorem duality_map_shiftedFormsPairing_eq (D : RelativeDualitySituation.{u}) {A B : CochainComplex
    (ModulesOn D.X.toRingedSpace) ℤ} (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B
    ⟶ D.topComplexX) :
    ((Stacks.Duality.derivedPushforward D.f).map (D.shiftedFormsPairing h)) = ((derivedPushforward
        D.f.toLRSHom.toShHom).map (D.shiftedFormsPairing h)) := rfl
/-- **The pushed pairings of the graded pieces are pairings of [Stacks, Tag 0G81] for `f`.** -/
theorem exists_pushedPairing_eq_relativeCupProduct
    (ψ : (D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧ ≅ (Stacks.Duality.relativeDualizingComplex D.f
      (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0)).obj)
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj)
    (hs : D.topInclusion ≫ s = (Stacks.Duality.derivedPushforward D.f).map ψ.hom ≫
      (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace D.f
        (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
        (Stacks.Duality.derivedStructureSheafInDegree D.S 0)))
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    ∃ (u : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          (inverseImageBaseProjection D.f)).obj
          (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj A)) ≅
        (Stacks.Duality.derivedPushforward D.f).obj (DerivedCategory.Q.obj A))
      (v : (Stacks.Duality.derivedPushforward D.f).obj
          (DerivedCategory.Q.obj (B⟦(2 * D.n : ℤ)⟧)) ≅
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          (inverseImageBaseProjection D.f)).obj
          (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj
            (B⟦(2 * D.n : ℤ)⟧))))
      (θ : DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧) ⟶
        (D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧) (_ : IsIso θ),
      (Scheme.Hom.deRhamPushDataBase D.f).pushedPairing s (D.inducedShiftedDeRhamPairing h) =
        ((derivedTensorProductFunctor D.S.toRingedSpace.sheaf).map u.hom).app _ ≫
          ((derivedTensorProductFunctor D.S.toRingedSpace.sheaf).obj _).map v.inv ≫
          Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct D.f.toLRSHom.toShHom
            (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj (B⟦(2 * D.n : ℤ)⟧)) ≫
          (Stacks.Duality.derivedPushforward D.f).map (D.shiftedFormsPairing h ≫ θ ≫ ψ.hom) ≫
          (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace D.f
            (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
            (Stacks.Duality.derivedStructureSheafInDegree D.S 0)) := by
  have iA := Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f A
  have iB := Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f
    (B⟦(2 * D.n : ℤ)⟧)
  refine ⟨@asIso _ _ _ _ (Scheme.Hom.projectionPushforwardComparison D.f D.f.toLRSHom.toShHom
      (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f)
      (pushforwardComparisonQ (toInverseImageBase D.f) A))
      (Scheme.Hom.isIso_projectionPushforwardComparison D.f _ _ _ (ha := iA)),
    (@asIso _ _ _ _ (Scheme.Hom.projectionPushforwardComparison D.f D.f.toLRSHom.toShHom
      (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f)
      (pushforwardComparisonQ (toInverseImageBase D.f) (B⟦(2 * D.n : ℤ)⟧)))
      (Scheme.Hom.isIso_projectionPushforwardComparison D.f _ _ _ (ha := iB))).symm,
    D.topComplexShiftHom,
    (IsIso.comp_isIso' inferInstance (Iso.isIso_hom (DerivedCategory.singleShiftTwoMulIso
      (ModulesOn D.X.toRingedSpace) (Scheme.Hom.relativeDifferentialForms D.f D.n) (D.n : ℤ))) :
        IsIso D.topComplexShiftHom), ?_⟩
  have hL : (Scheme.Hom.deRhamPushDataBase D.f).pushedPairing s (D.inducedShiftedDeRhamPairing h) =
      (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct (inverseImageBaseProjection
          D.f) (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj A))
          (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj (B⟦(2 * D.n :
          ℤ)⟧)))) ≫ (derivedPushforward (inverseImageBaseProjection D.f)).map
          (((canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor
          ((pushforwardComplex (toInverseImageBase D.f)).obj A) ((pushforwardComplex
          (toInverseImageBase D.f)).obj (B⟦(2 * D.n : ℤ)⟧))) ≫ DerivedCategory.Q.map
          ((naiveCupProduct (toInverseImageBase D.f) A (B⟦(2 * D.n : ℤ)⟧)) ≫ (pushforwardComplex
          (toInverseImageBase D.f)).map (D.rightShiftedPairingX h (2 * D.n : ℤ)) ≫
          D.topComplexToDeRhamShift) ≫ ((DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app
          (D.deRhamCx.extend ComplexShape.embeddingUpNat))) ≫ s := rfl
  have e12 : DerivedCategory.Q.map ((naiveCupProduct (toInverseImageBase D.f) A (B⟦(2 * D.n : ℤ)⟧))
      ≫ (pushforwardComplex (toInverseImageBase D.f)).map (D.rightShiftedPairingX h (2 * D.n : ℤ)) ≫
      D.topComplexToDeRhamShift) =
      DerivedCategory.Q.map ((naiveCupProduct (toInverseImageBase D.f) A (B⟦(2 * D.n : ℤ)⟧)) ≫
          (pushforwardComplex (toInverseImageBase D.f)).map (D.rightShiftedPairingX h (2 * D.n :
          ℤ))) ≫ DerivedCategory.Q.map D.topComplexToDeRhamShift :=
    (congrArg DerivedCategory.Q.map (Category.assoc _ _ _).symm).trans (Functor.map_comp _ _ _)
  have hcW : (pushforwardComparisonQ (toInverseImageBase D.f) (D.topComplexX⟦(2 * D.n : ℤ)⟧)) ≫
      (@inv _ _ _ _ (pushforwardComparisonQ (toInverseImageBase D.f) (D.topComplexX⟦(2 * D.n : ℤ)⟧))
      (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f _)) = 𝟙 _ :=
    @IsIso.hom_inv_id _ _ _ _ _
        (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f _)
  have S1 := open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces in
    toTensor_naiveCupProduct_map_comp_pushforwardComparisonQ
      (toInverseImageBase D.f) (D.rightShiftedPairingX h (2 * D.n : ℤ))
  have hφ : ((derivedPushforward (toInverseImageBase D.f)).map ((canonicalDerivedTensorProduct
      D.X.toRingedSpace.sheaf).toTensor A (B⟦(2 * D.n : ℤ)⟧))) ≫ ((derivedPushforward
      (toInverseImageBase D.f)).map (DerivedCategory.Q.map (D.rightShiftedPairingX h (2 * D.n :
      ℤ)))) = ((derivedPushforward (toInverseImageBase D.f)).map (D.shiftedFormsPairing h)) :=
      (Functor.map_comp _ _ _).symm
  have S2 := Scheme.Hom.relativeCupProduct_map_relativeCupProduct_projectionPushforwardComparison
      D.f
    D.f.toLRSHom.toShHom (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f)
    (pushforwardComparisonQ (toInverseImageBase D.f) A)
    (pushforwardComparisonQ (toInverseImageBase D.f) (B⟦(2 * D.n : ℤ)⟧)) (D.shiftedFormsPairing h)
    ((@inv _ _ _ _ (pushforwardComparisonQ (toInverseImageBase D.f) (D.topComplexX⟦(2 * D.n : ℤ)⟧))
      (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f _)) ≫
      DerivedCategory.Q.map D.topComplexToDeRhamShift ≫
      (DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app (D.deRhamCx.extend
          ComplexShape.embeddingUpNat))
  have key := Stacks.GradedTargetChase.key_chase
    (x3 := (DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app (D.deRhamCx.extend
        ComplexShape.embeddingUpNat))
    e12 hcW S1 hφ
  have G1 := Stacks.GradedTargetChase.comp_comp_congr
    (μ := Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct (inverseImageBaseProjection
        D.f)
      (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj A))
      (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj (B⟦(2 * D.n :
          ℤ)⟧))))
    (s := s) (congrArg (derivedPushforward (inverseImageBaseProjection D.f)).map key)
  have G2 := Stacks.GradedTargetChase.comp_tail_assoc (C :=
      Stacks.DerivedTensor.RingedSite.DerivedModules D.S.toRingedSpace.sheaf) s S2
  have HF := Stacks.GradedTargetChase.trace_chase (C :=
      Stacks.DerivedTensor.RingedSite.DerivedModules D.S.toRingedSpace.sheaf)
    (D.map_shiftedFormsPairing_comp_comp ψ h) (D.topInclusion_comp_eq_map_comp_trace ψ s hs)
        D.map_topComplexShiftHom_comp_topInclusion_derivedModules
  have G3 := Stacks.GradedTargetChase.comp_tail_swap G2 HF (eq_of_heq (heq_comp rfl rfl rfl
      ((Functor.heq_map rfl rfl rfl HEq.rfl).trans (heq_of_eq (D.duality_map_shiftedFormsPairing_eq
      h).symm)) (heq_comp rfl rfl rfl (NatTrans.heq_app rfl rfl HEq.rfl rfl) (heq_comp rfl rfl rfl
      (Functor.heq_map rfl rfl rfl (heq_comp rfl rfl rfl HEq.rfl (heq_comp rfl rfl rfl
      (Functor.heq_map rfl rfl rfl HEq.rfl) HEq.rfl))) HEq.rfl))))
  have H01 := hL.trans G1
  have H02 := H01.trans G3
  refine H02.trans ?_
  exact eq_of_heq (heq_comp rfl rfl rfl
    (NatTrans.heq_app rfl rfl (Functor.heq_map rfl rfl rfl (asIso_hom_heq _).symm) rfl)
    (heq_comp rfl rfl rfl
      (Functor.heq_map rfl rfl rfl (asIso_symm_inv_heq _).symm)
      (heq_comp rfl rfl rfl HEq.rfl
        (heq_comp rfl rfl rfl
          (Functor.heq_map rfl rfl rfl (heq_comp rfl rfl rfl HEq.rfl
            (heq_comp rfl rfl rfl HEq.rfl HEq.rfl)))
          HEq.rfl))))


end AlgebraicGeometry.RelativeDualitySituation
