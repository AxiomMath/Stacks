module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCoproductsBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCoproductsWeakSerre
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingGlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraAffineTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardCoproductQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QuasicoherentDerivedTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections

/-!
# Global sections of a direct image from an affine space commute with direct sums in `D_QCoh`

Let `y : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` with `Y` affine, and let
`RF` be a right derived functor of `Γ(X, y_* −) : Mod(𝒪_Y) ⥤ Ab`. Then `RF` commutes with direct
sums of families of objects of `D_QCoh(𝒪_Y)`. This is the affine case of [Stacks, Tag 08FB] for
the morphism from an algebraic space to a point, in the induction of
`AlgebraicGeometry.Space.isIso_sigmaComparison_derivedPushforward_of_affine_quasicoherent`.

The proof is the source's. `Γ(X, y_* −)` is the sections functor at the terminal chart `Y ≅ h_T`
of `Y` (`AlgebraicGeometry.Space.isTerminal_isoChart`,
`AlgebraicGeometry.Space.pushforwardGlobalSectionsIsoOfIsTerminal`), so it commutes with
all direct sums (`T` is quasi-compact, Stacks 0935) and has no higher derived functors on
quasi-coherent modules (`T` is affine, Stacks 03DW). Hence `RF` commutes with direct sums of
quasi-coherent modules placed in one degree, and by dévissage with direct sums of uniformly
bounded below families in `D_QCoh(𝒪_Y)`
(`Stacks.DerivedFunctor.Coproducts.isIso_sigmaComparison_of_isGE_of_weakSerre`). The uniform
bound `H^n(RF E) = 0` for `n ≥ 1` and `E ∈ D^{≤ 0}_QCoh(𝒪_Y)` is Stacks 08F7 (3) with `N = 1`,
and it reduces unbounded families to bounded below ones
(`Stacks.DerivedFunctor.Coproducts.preservesColimitsOfShape_ι_comp_of_bounded_of_uniform_bound`).

## Main results

* `AlgebraicGeometry.Space.isWeakSerre_quasicoherentSheaves_ringUniverse`: quasi-coherent
  `𝒪_X`-modules form a weak Serre subcategory (Stacks 03M1), with no hypothesis.
* `Space.isIso_sigmaComparison_rightDerived_pushforwardGlobalSections_of_isAffineSpace`: the
  affine case.

## References

* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
-- The locally small model's instances are for small sites; they leave universes undetermined
-- at the small étale site, whose objects live one universe up.
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] hasCoproducts_derivedCategory_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Quasi-coherent `𝒪_X`-modules form a weak Serre subcategory** (Stacks 03M1, clauses (3) and
(4)), at the module universe of the structure rings and with no hypothesis. -/
theorem isWeakSerre_quasicoherentSheaves_ringUniverse (X : AlgebraicSpaces B S hS) :
    WeakSerre.IsWeakSerre (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :=
  let := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS X.1 X.2
  let := isClosedUnderCokernels_quasicoherentSheaves B S hS X.1 X.2
  let := isClosedUnderExtensions_quasicoherentSheaves_of_h03DW B S hS X.1 X.2
    (fun q hq hk W hW =>
      surjective_val_app_of_epi_of_kernel_isCartesian_unconditional B S hS X q hq hk W hW)
  isWeakSerre_quasicoherentSheaves B S hS X.1 X.2

variable {X Y : AlgebraicSpaces B S hS} (y : Y ⟶ X) {R : Type u} [CommRing R]
  (φ : R →+* modelGlobalFunctions B S hS X)

/-- **Global sections of a direct image from an affine space commute with direct sums in
`D_QCoh`** (the affine case of Stacks 08FB, for the morphism to a point). Let `y : Y ⟶ X` with
`Y` affine and let `RF` be a right derived functor of `Γ(X, y_* −)`. Then `RF` commutes with the
direct sum of every family of objects of `D(𝒪_Y)` with quasi-coherent cohomology. -/
theorem isIso_sigmaComparison_rightDerived_pushforwardGlobalSections_of_isAffineSpace
    (hY : IsAffineSpace B S hS Y.1)
    (RF : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤ DerivedCategory AddCommGrpCat.{u})
    (α : (modulePushforward B S hS y ⋙
        baseRingGlobalSectionsAddCommGrp B S hS X φ).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    {J : Type u} (K : J → DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : ∀ j, qcohDerivedProp B S hS Y (K j)) :
    IsIso (sigmaComparison RF K) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hY
  have hU := isTerminal_isoChart B S hS e.symm
  have hUaff : IsAffineChart B S hS Y.1 (isoChart B S hS e.symm) := hT
  let F := modulePushforward B S hS y ⋙ baseRingGlobalSectionsAddCommGrp B S hS X φ
  let eF : F ≅ Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS Y.1 Y.2) (isoChart B S hS e.symm) :=
    pushforwardGlobalSectionsIsoOfIsTerminal B S hS y φ hU
  have hgr := isGrothendieckAbelian_modules B S hS Y.1 Y.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have hres := exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2
  have := (modulePullbackAdjunction B S hS y).isRightAdjoint
  have := (baseRingTensorModuleAdjunction B S hS X φ).isRightAdjoint
  have : PreservesFiniteLimits F := inferInstanceAs (PreservesFiniteLimits
    (modulePushforward B S hS y ⋙ baseRingGlobalSectionsModule B S hS X φ ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
  have : PreservesLimitsOfShape (Discrete ℕ) F := inferInstanceAs (PreservesLimitsOfShape
    (Discrete ℕ) (modulePushforward B S hS y ⋙ baseRingGlobalSectionsModule B S hS X φ ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF α
  have hcomp : ∀ I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ, I.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := fun I hI ↦
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).2
        DerivedCategory.Qh RF α I hI
  -- the higher derived functors of `F` vanish on quasi-coherent modules
  have hvan : ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
      ∀ n : ℕ, 0 < n → IsZero ((F.rightDerived n).obj M) := fun M hM n hn ↦
    (isZero_rightDerived_sectionsFunctor_of_isAffineChart B S hS Y.1 Y.2 M hM _ hUaff n hn).of_iso
      { hom := (NatTrans.rightDerived eF.hom n).app M
        inv := (NatTrans.rightDerived eF.inv n).app M
        hom_inv_id := by
          rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, eF.hom_inv_id,
            NatTrans.rightDerived_id, NatTrans.id_app]
        inv_hom_id := by
          rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, eF.inv_hom_id,
            NatTrans.rightDerived_id, NatTrans.id_app] }
  -- `F` commutes with direct sums
  have hsum : ∀ M : J → Modules.{u, u} B S hS Y.1 Y.2, IsIso (sigmaComparison F M) := by
    intro M
    have hS : PreservesColimitsOfShape (Discrete J)
        (Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
          (smallEtaleRingedSite B S hS Y.1 Y.2) (isoChart B S hS e.symm)) :=
      Stacks.Sites.sheafOfModules_sections_preserves_coproducts _ _ _
        (isQuasiCompactObject_of_isAffine B S hS Y.1 _ hUaff) J
    have : PreservesColimitsOfShape (Discrete J) F := preservesColimitsOfShape_of_natIso eF.symm
    exact isIso_sigmaComparison_of_preservesColimit _ M inferInstance
  -- quasi-coherence, `D_QCoh` and the instances on direct sums
  let 𝒜 := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
  have hWS := isWeakSerre_quasicoherentSheaves_ringUniverse B S hS Y
  let P := qcohDerivedProp B S hS Y
  have hsumq : ∀ M : J → Modules.{u, u} B S hS Y.1 Y.2, (∀ j, (M j).IsQuasicoherentOnSite) →
      (∐ M).IsQuasicoherentOnSite := fun M hM ↦
    isQuasicoherentOnSite_of_isColimit_cofan B S hS Y.1 Y.2 _ (colimit.isColimit _) hM
  have : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    isClosedUnderCoproducts_quasicoherentDerivedCategory B S hS Y.1 Y.2 J hsumq
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    AddCommGrpCat.{u} J
  have : ∀ n : ℤ, PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n) := fun n ↦
    Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor _ n
  have : ∀ n : ℤ, PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n) := fun n ↦
    Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor _ n
  have : ∀ a : ℤ, PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) a) := fun a ↦ by
    have := preservesColimitsOfShape_discrete_derivedCategoryQ_modules B S hS Y J
    have : PreservesColimitsOfShape (Discrete J)
        (CochainComplex.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) a) :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete J)
        (HomologicalComplex.single (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ) a))
    exact preservesColimitsOfShape_of_natIso
      (DerivedCategory.singleFunctorIsoCompQ (Modules.{u, u} B S hS Y.1 Y.2) a).symm
  -- the inputs of the dévissage
  have hGE : ∀ (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (b : ℤ), E.IsGE b →
      (RF.obj E).IsGE b := fun E b hE ↦
    Stacks.SmallDerivedCategory.isGE_obj_of_isGE F RF α hcomp E b hE
  have hsingle : ∀ (a : ℤ) (M : J → Modules.{u, u} B S hS Y.1 Y.2), (∀ j, 𝒜 (M j)) →
      IsIso (sigmaComparison RF fun j ↦
        (DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) a).obj (M j)) :=
    fun a M hM ↦
      Stacks.DerivedFunctor.Coproducts.isIso_sigmaComparison_singleFunctor_of_rightDerived
        F RF α hres a M (hsum M)
        (fun n hn ↦ ⟨fun j ↦ hvan _ (hM j) n hn, hvan _ (hsumq M hM) n hn⟩)
  have hRF : ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
      ∀ p : ℤ, ((1 : ℕ) : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M) := by
    intro M hM p hp
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    exact (hvan M hM n (by omega)).of_iso (CategoryTheory.rightDerivedPlusObjIso F M n)
  have hdiag : ∀ K' : J → P.FullSubcategory,
      PreservesColimit (Discrete.functor fun i ↦ (K' i).obj) RF ↔
        PreservesColimit (Discrete.functor K' ⋙ P.ι) RF := fun K' ↦
    preservesColimit_iff_of_iso_diagram RF (Discrete.natIso fun _ ↦ Iso.refl _)
  have hpres : PreservesColimitsOfShape (Discrete J) (P.ι ⋙ RF) :=
    Stacks.DerivedFunctor.Coproducts.preservesColimitsOfShape_ι_comp_of_bounded_of_uniform_bound
      P RF J (fun E a hE ↦ P.le_shift a E hE)
      (fun E a hE ↦ DerivedCategoryB.derivedCategoryB_truncLT_obj 𝒜 hWS (a + 1) E hE)
      (fun E a hE ↦ DerivedCategoryB.derivedCategoryB_truncGE_obj 𝒜 hWS a E hE) 1
      (fun E hE hle n hn ↦ isZero_homology_rightDerived_of_isZero_gt_unbounded B S hS Y.1 Y.2
        F RF α 1 hRF E hE 0 (fun j hj ↦ DerivedCategory.isZero_of_isLE E 0 j hj) n (by omega))
      (fun K' a hK' ↦ by
        have h := Stacks.DerivedFunctor.Coproducts.isIso_sigmaComparison_of_isGE_of_weakSerre
          RF 𝒜 hWS hGE hsingle a (fun i ↦ (K' i).obj) (fun i ↦ (K' i).property) hK'
        have := (hdiag K').1 (preservesColimit_discreteFunctor_of_isIso_sigmaComparison _ _ h)
        infer_instance)
  -- back from `D_QCoh` to `D(𝒪_Y)`
  let K' : J → P.FullSubcategory := fun j ↦ ⟨K j, hK j⟩
  have h₃ : PreservesColimit (Discrete.functor K' ⋙ P.ι) RF :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves P.ι (colimit.isColimit (Discrete.functor K')))
      (isColimitOfPreserves (P.ι ⋙ RF) (colimit.isColimit (Discrete.functor K')))
  exact isIso_sigmaComparison_of_preservesColimit RF K ((hdiag K').2 h₃)

end AlgebraicGeometry.Space

end
