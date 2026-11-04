module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleChartGood

/-!
# Goodness on an affine algebraic space, from a K-flat quasi-coherent model

On an affine algebraic space `Y` every object `K` of `D_QCoh(Y_{spaces,étale}, 𝒪_Y)` is
represented by a K-flat complex `C` of flat quasi-coherent modules. Then `Lπ_Y^*K` is computed
degreewise, `Lπ_Y^*K ≅ π_Y^*C` (Stacks 06YY), and its cohomology sheaves are good on the affine
objects of the big sites of `Y` by Stacks 0DGQ.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.locallyGood_of_kFlatModel`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- An algebraic space of the big fppf site represented by an affine scheme is, read in the big
étale site, represented by an affine scheme. -/
theorem exists_isAffine_etaleSpace {Y : T.Spaces}
    (hY : ∃ W : T.Schemes, IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W) ∧
      Nonempty ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ Y)) :
    ∃ W : BigFppfOver E.fppfSite S E.fppf_mem,
      IsAffine ((BigFppfOver.toScheme E.fppfSite S E.fppf_mem).obj W) ∧
        Nonempty ((schemeSpaceFunctor E.fppfSite S E.fppf_mem).obj W ≅ etaleSpace T E h Y) := by
  cases E with
  | mk e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 =>
    change T.schemeSite = e3 at h
    cases h
    exact hY

/-- **Goodness of the cohomology sheaves of `Lπ_Y^*K_Y` on an affine algebraic space `Y`**, given
K-flat quasi-coherent models of objects of `D_QCoh` on affine algebraic spaces. -/
theorem locallyGood_of_kFlatModel
    (hmodel : ∀ (Y : AlgebraicSpaces E.fppfSite S E.fppf_mem),
      (∃ W : BigFppfOver E.fppfSite S E.fppf_mem,
        IsAffine ((BigFppfOver.toScheme E.fppfSite S E.fppf_mem).obj W) ∧
        Nonempty ((schemeSpaceFunctor E.fppfSite S E.fppf_mem).obj W ≅ Y)) →
      ∀ K : DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O)),
      (∀ q, ((DerivedCategory.homologyFunctor _ q).obj K).IsQuasicoherentOnSite) →
      ∃ C : CochainComplex (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O)) ℤ,
        (∀ n, (C.X n).IsQuasicoherentOnSite) ∧
        (letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u + 1, u + 1, u + 1,
            u + 1} (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O;
          @CochainComplex.KFlatBifunctor.KFlat
            (_root_.SheafOfModules.{u + 1}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O))
            (_root_.SheafOfModules.{u + 1}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O))
            (_root_.SheafOfModules.{u + 1}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O))
            inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
              (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O)
            (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u + 1, u + 1, u + 1, u + 1, u + 1}
              (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O)
            (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u + 1, u + 1, u + 1,
              u + 1} (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O)
            inferInstance C) ∧
        (∀ i : ℤ, SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
          (O := (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O) (C.X i)) ∧
        Nonempty (DerivedCategory.Q.obj C ≅ K))
    (Y : T.Spaces)
    (hY : ∃ W : T.Schemes, IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W) ∧
      Nonempty ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ Y))
    (KY : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h Y)).O)))
    (hKY : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj KY).IsQuasicoherentOnSite) (q : ℤ) :
    LocallyGood T E h Y ((DerivedCategory.homologyFunctor (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (E.bigEtaleRingedSite (etaleSpace T E h Y))).O)) q).obj
      ((derivedPullback (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h Y)).toRingedToposSiteHom).obj KY)) := by
  obtain ⟨C, hqc, hKf, hflat, ⟨eQ⟩⟩ :=
    hmodel (etaleSpace T E h Y) (exists_isAffine_etaleSpace T E h hY) KY hKY
  let π := BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E (etaleSpace T E h Y)
  have := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.isIso_derivedPullbackComparison_app_kFlat
    π.toRingedToposSiteHom π.isMorphismOfSites C hKf hflat
  refine good_homology_of_iso_pullback_quasicoherent T E h Y C hqc _ ?_ q
  exact (derivedPullback π.toRingedToposSiteHom).mapIso
      (eQ.symm ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app C) ≪≫
    asIso ((derivedPullbackComparison π.toRingedToposSiteHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

end AlgebraicGeometry.BigFppfSpaceSite

end
