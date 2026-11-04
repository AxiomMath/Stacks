module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAffineLocallyGood
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineKFlatModel
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DGR: unbounded cohomological descent of `D_QCoh` from the small étale site to the
big fppf site

Let `X` be an algebraic space over a scheme `S` and `K` an object of `D_QCoh(𝒪_X)`. Then

* the map `Lπ_X^*K ⟶ Rε_{X,*}(La_X^*K)`, the unit of `Lε_X^* ⊣ Rε_{X,*}` at `Lπ_X^*K` followed by
  `Rε_{X,*}` of the comparison `Lε_X^*Lπ_X^*K ⟶ La_X^*K` of Stacks 0D6D, and
* the unit `K ⟶ Ra_{X,*}(La_X^*K)` of `La_X^* ⊣ Ra_{X,*}`

are isomorphisms. Here `π_X : (Spaces/X)_étale ⟶ X_{spaces,étale}`,
`ε_X : (Spaces/X)_fppf ⟶ (Spaces/X)_étale` and `a_X = π_X ∘ ε_X` are the morphisms of ringed sites
of Stacks 0DGM, and `D_QCoh(𝒪_X)` is the full subcategory of `D(X_{spaces,étale}, 𝒪_X)` of the
objects all of whose cohomology sheaves are quasi-coherent.

## The proof

It is the source's. The cohomology sheaves of `Lπ_X^*K` are good: étale locally on `X`, on an
affine chart `Y`, `K` is represented by a K-flat complex `C` of flat quasi-coherent modules, so
`Lπ_Y^*K = π_Y^*C` and its cohomology sheaves are those of a complex of modules `π_Y^*𝓕`, to which
Stacks 0DGQ applies
(`AlgebraicGeometry.BigFppfSpaceSite.homologyIn_good_derivedPullback_of_locallyGood`). Then the
unit of `ε_X` is invertible at `Lπ_X^*K` by the truncation argument through Stacks 0D6P
(`AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToBigEtale_derivedAdjunction_unit_app`), which is
the first map; the second is the unit of `π_X` (invertible, `π_{X,*}` being exact with invertible
underived unit) followed by `Rπ_{X,*}` of the first map
(`Stacks.Cohomology.CompositeAdjunctionUnit.isIso_derivedAdjunction_comp_unit_app`).

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_derivedUnits_of_quasicoherent`: **Stacks 0DGR**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- `La_X^*` exists, `a_X = π_X ∘ ε_X`. -/
instance hasLeftDerivedFunctor_fppfToSmallEtale (X : T.Spaces) :
    (pullbackOnHomotopy ((BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).toRingedToposSiteHom.comp (epsilonHom T E h X))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h X))).O))
        (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy.{u + 1} _
    (RingedToposSiteHom.isMorphismOfSites_comp_u _ _
      (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites
      (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).isMorphismOfSites)

/-- **Stacks 0DGR, granted K-flat quasi-coherent models on affine algebraic spaces.** -/
theorem isIso_derivedUnits_of_kFlatModel
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
    (X : T.Spaces)
    (K : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h X)).O)))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherentOnSite) :
    IsIso ((derivedAdjunction (epsilonHom T E h X)
        (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites).unit.app
          ((derivedPullback (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
            (etaleSpace T E h X)).toRingedToposSiteHom).obj K) ≫
      (derivedPushforward (epsilonHom T E h X)).map
        ((derivedPullbackCompComparison (epsilonHom T E h X)
          (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
            (etaleSpace T E h X)).toRingedToposSiteHom).app K)) ∧
    IsIso ((derivedAdjunction ((BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).toRingedToposSiteHom.comp (epsilonHom T E h X))
        (RingedToposSiteHom.isMorphismOfSites_comp_u _ _
          (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites
          (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
            (etaleSpace T E h X)).isMorphismOfSites)).unit.app K) := by
  have hM := homologyIn_good_derivedPullback_of_locallyGood
    (locallyGood_of_kFlatModel T E h hmodel) K hK
  have := isIso_fppfToBigEtale_derivedAdjunction_unit_app T E h X _
    (fun U ↦ by
      obtain ⟨𝒰, h𝒰, hi⟩ := exists_preZeroHypercover_of_generate_mem
        (generate_etale_isAffineOverAffineEtale_mem U)
      exact ⟨𝒰, h𝒰, fun i ↦ (hi i).elim fun _ h ↦ h⟩)
    (fun U ↦ exists_fppf_cover_isAffineOverAffineEtale U) _ hM
  have := isIso_derivedPullbackCompComparison (epsilonHom T E h X)
    (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).toRingedToposSiteHom
    (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites
    (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E (etaleSpace T E h X)).isMorphismOfSites
  refine ⟨inferInstance, ?_⟩
  have := BigEtaleSpaceSite.isIso_spacesEtaleRestriction_unit E (etaleSpace T E h X)
  have : PreservesFiniteLimits (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).toRingedToposSiteHom.pushforwardTopos :=
    BigEtaleSpaceSite.spacesEtaleRestrictionRingedHom_preservesFiniteLimits E _
  have : PreservesFiniteColimits (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).toRingedToposSiteHom.pushforwardTopos :=
    BigEtaleSpaceSite.spacesEtaleRestrictionRingedHom_preservesFiniteColimits E _
  have := Stacks.Cohomology.CompositeAdjunctionUnit.isIso_derivedAdjunction_unit_app_of_isIso_unit
    (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).toRingedToposSiteHom
    (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).isMorphismOfSites K
  exact Stacks.Cohomology.CompositeAdjunctionUnit.isIso_derivedAdjunction_comp_unit_app
    (epsilonHom T E h X)
    (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).toRingedToposSiteHom
    (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites
    (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
      (etaleSpace T E h X)).isMorphismOfSites K

/-- **Stacks 0DGR.** Let `S` be a scheme and `X` an algebraic space over `S`. For `K` in
`D_QCoh(𝒪_X)`, an object of `D(X_{spaces,étale}, 𝒪_X)` all of whose cohomology sheaves are
quasi-coherent, the maps

`Lπ_X^*K ⟶ Rε_{X,*}(La_X^*K)` and `K ⟶ Ra_{X,*}(La_X^*K)`

are isomorphisms, where `a_X = π_X ∘ ε_X : ((Spaces/X)_fppf, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)`.
The first map is the unit of `Lε_X^* ⊣ Rε_{X,*}` at `Lπ_X^*K` followed by `Rε_{X,*}` of the
comparison `Lε_X^*Lπ_X^*K ⟶ La_X^*K` of Stacks 0D6D; the second is the unit of `La_X^* ⊣ Ra_{X,*}`
at `K`. -/
@[stacks 0DGR]
theorem isIso_derivedUnits_of_quasicoherent
    (X : T.Spaces)
    (K : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h X)).O)))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherentOnSite) :
    IsIso ((derivedAdjunction (epsilonHom T E h X)
        (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites).unit.app
          ((derivedPullback (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
            (etaleSpace T E h X)).toRingedToposSiteHom).obj K) ≫
      (derivedPushforward (epsilonHom T E h X)).map
        ((derivedPullbackCompComparison (epsilonHom T E h X)
          (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
            (etaleSpace T E h X)).toRingedToposSiteHom).app K)) ∧
    IsIso ((derivedAdjunction ((BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).toRingedToposSiteHom.comp (epsilonHom T E h X))
        (RingedToposSiteHom.isMorphismOfSites_comp_u _ _
          (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites
          (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
            (etaleSpace T E h X)).isMorphismOfSites)).unit.app K) :=
  isIso_derivedUnits_of_kFlatModel T E h
    (fun Y hY K hK ↦ Space.exists_kFlat_isQuasicoherentOnSite_model_spacesEtale E.fppfSite S
      E.fppf_mem Y hY K hK) X K hK

end AlgebraicGeometry.BigFppfSpaceSite

end
