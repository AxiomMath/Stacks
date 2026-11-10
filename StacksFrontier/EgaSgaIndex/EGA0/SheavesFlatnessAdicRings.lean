module  -- shake: keep-all

import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Algebra.Colimit.Ring
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.PowerSeries.Restricted
import Mathlib.RingTheory.QuasiFinite.Weakly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Category.UniformSpace
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Skyscraper
import StacksCore.RingTheory.Flat.TorsionFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA 0, §§3–7: references registered by name

Declarations realizing numbered items of EGA 0, §3 (sheaves), §4 (ringed spaces), §5
(quasi-coherent and coherent sheaves), §6 (flatness) and §7 (adic rings), from the EGA/SGA
concept index, that are not tagged where they are declared: Mathlib and core declarations
without an `add_to_stacks` pointer in this library, and (with `--draft-only`) those of
`StacksCore/`.
Part of the EGA 0 index, split by section.
-/

add_to_ega "0 3.1.1" "more general" CategoryTheory.Limits.HasMultiequalizer
add_to_ega "0 3.1.1" "more general" CategoryTheory.Limits.IsLimit
add_to_ega "0 3.1.1" "more general" CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso
add_to_ega "0 3.1.1" "partial" CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp
add_to_ega "0 3.1.1" "partial" CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp_assoc
add_to_ega "0 3.1.1" "partial" CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp
add_to_ega "0 3.1.1" "partial" CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp_assoc
add_to_ega "0 3.1.1" "partial" CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp
add_to_ega "0 3.1.1" "partial" CategoryTheory.Limits.limit.conePointUniqueUpToIso_inv_comp
add_to_ega "0 3.1.2" "more general" CategoryTheory.Presheaf.IsSheaf'
add_to_ega "0 3.1.2" "Set-valued coefficients" CategoryTheory.Presieve.IsSheaf
add_to_ega "0 3.1.2" "(F)" CategoryTheory.Presieve.IsSheafFor
add_to_ega "0 3.1.2" CategoryTheory.Sheaf
add_to_ega "0 3.1.2" "Set-valued coefficients" CategoryTheory.isSheaf_iff_isSheaf_of_type
add_to_ega "0 3.1.2" TopCat.Presheaf.IsSheaf
add_to_ega "0 3.1.2" TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections
add_to_ega "0 3.1.2" TopCat.Presheaf.IsSheaf.isSheafPreservesLimitPairwiseIntersections
add_to_ega "0 3.1.2" TopCat.Presheaf.IsSheafPairwiseIntersections
add_to_ega "0 3.1.2" TopCat.Presheaf.IsSheafPreservesLimitPairwiseIntersections
add_to_ega "0 3.1.2" TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections
add_to_ega "0 3.1.2" TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections
add_to_ega "0 3.1.3" CategoryTheory.Limits.PreservesLimit
add_to_ega "0 3.1.3" "special case" CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget
add_to_ega "0 3.1.4" "rings" AlgEquiv.ofBijective
add_to_ega "0 3.1.4" "more general" CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget
add_to_ega "0 3.1.4" "groups" MulEquiv.ofBijective
add_to_ega "0 3.1.4" "rings" RingEquiv.ofBijective
add_to_ega "0 3.1.4" TopCat.Presheaf.IsSheaf
add_to_ega "0 3.1.4" "more general" TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
add_to_ega "0 3.1.4" TopCommRingCat
add_to_ega "0 3.1.4" TopCommRingCat.instCategory
add_to_ega "0 3.1.5" AlgebraicGeometry.PresheafedSpace.restrict
add_to_ega "0 3.1.5" TopologicalSpace.Opens.sheafRestrict
add_to_ega "0 3.1.5" "partial" TopologicalSpace.Opens.sheafRestrict_map_hom_app
add_to_ega "0 3.1.5" "partial" TopologicalSpace.Opens.sheafRestrict_obj_obj_map
add_to_ega "0 3.1.5" "partial" TopologicalSpace.Opens.sheafRestrict_obj_obj_obj
add_to_ega "0 3.1.6" TopCat.Presheaf.germ
add_to_ega "0 3.1.6" TopCat.Presheaf.restrict
add_to_ega "0 3.1.6" TopCat.Presheaf.restrictOpen
add_to_ega "0 3.1.6" TopCat.Presheaf.stalk
add_to_ega "0 3.1.6" TopCat.Presheaf.stalkFunctor
add_to_ega "0 3.1.6" "germs of global sections" TopCat.Presheaf.Γgerm
add_to_ega "0 3.2.1" CategoryTheory.Limits.HasLimits
add_to_ega "0 3.2.1" CategoryTheory.Limits.HasLimitsOfSize
add_to_ega "0 3.2.4" TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open
add_to_ega "0 3.2.4" "more general" TopologicalSpace.IsTopologicalBasis.isOpen_iff
add_to_ega "0 3.2.4" "more general" TopologicalSpace.Opens.isBasis_iff_nbhd
add_to_ega "0 3.2.5" "existence" TopCat.Sheaf.extend_hom_app
add_to_ega "0 3.2.5" "uniqueness" TopCat.Sheaf.hom_ext
add_to_ega "0 3.2.5" "more general" TopCat.Sheaf.restrictHomEquivHom
add_to_ega "0 3.2.6" "more general" CategoryTheory.Limits.limMap_mono
add_to_ega "0 3.2.6" "more general" CategoryTheory.Limits.limMap_mono'
add_to_ega "0 3.2.6" "more general" CategoryTheory.Sheaf.createsLimitsOfShape
add_to_ega "0 3.2.6" "special case" CategoryTheory.Sheaf.instHasFiniteLimits
add_to_ega "0 3.2.6" "partial" CategoryTheory.Sheaf.instHasLimitsOfShape
add_to_ega "0 3.2.6" "partial"
  CategoryTheory.Sheaf.instIsClosedUnderLimitsOfShapeFunctorOppositeIsSheaf
add_to_ega "0 3.2.6" "partial" CategoryTheory.Sheaf.isSheaf_of_isLimit
add_to_ega "0 3.2.6" TopCat.instCreatesLimitsSheafPresheafForgetOfHasLimits
add_to_ega "0 3.2.6" "partial" TopCat.instHasLimitsOfShapeSheaf
add_to_ega "0 3.2.6" "partial" TopCat.instHasLimitsOfSizeSheafOfHasLimits
add_to_ega "0 3.2.6" "(F)" TopCat.isSheaf_of_isLimit
add_to_ega "0 3.2.6" "(F)" TopCat.limit_isSheaf
add_to_ega "0 3.4.1" "sections on an open" TopCat.Presheaf.pushforward_obj_obj
add_to_ega "0 3.4.1" TopCat.Sheaf.pushforward
add_to_ega "0 3.4.2" "special case" AlgebraicGeometry.Scheme.Modules.pushforward_map_app
add_to_ega "0 3.4.2" TopCat.Presheaf.pushforward_map_app'
add_to_ega "0 3.4.2" TopCat.Sheaf.pushforward
add_to_ega "0 3.4.3" "partial" TopCat.Presheaf.Pushforward.comp
add_to_ega "0 3.4.3" "partial" TopCat.Presheaf.Pushforward.comp_eq
add_to_ega "0 3.4.4" TopCat.Presheaf.stalkPushforward
add_to_ega "0 3.4.4" TopCat.Presheaf.stalkPushforward.comp
add_to_ega "0 3.4.4" "partial" TopCat.Presheaf.stalkPushforward_germ
add_to_ega "0 3.4.4" "partial" TopCat.Presheaf.stalkPushforward_germ_apply
add_to_ega "0 3.4.4" "partial" TopCat.Presheaf.stalkPushforward_germ_assoc
add_to_ega "0 3.5.1" "special case" AlgebraicGeometry.Scheme.Hom.appLE
add_to_ega "0 3.5.1" "special case" AlgebraicGeometry.Scheme.Hom.stalkMap
add_to_ega "0 3.5.1" "special case" TopCat.Presheaf.stalkPushforward
add_to_ega "0 3.5.1" "partial" TopCat.Sheaf.hom_ext
add_to_ega "0 3.5.2" AlgebraicGeometry.PresheafedSpace
add_to_ega "0 3.5.2" AlgebraicGeometry.PresheafedSpace.Hom.mk
add_to_ega "0 3.5.2" AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces
add_to_ega "0 3.5.2" AlgebraicGeometry.PresheafedSpace.mk
add_to_ega "0 3.5.2" "category of pairs (X,F)" AlgebraicGeometry.SheafedSpace.instCategory
add_to_ega "0 3.5.3" "more general" CategoryTheory.Adjunction.homEquiv
add_to_ega "0 3.5.3" "partial, special case" TopCat.Sheaf.pullback
add_to_ega "0 3.5.4" "more general" CategoryTheory.Adjunction.eq_unit_comp_map_iff
add_to_ega "0 3.5.4" "more general" CategoryTheory.Adjunction.homEquiv_counit
add_to_ega "0 3.5.4" "more general" CategoryTheory.Adjunction.homEquiv_naturality_left
add_to_ega "0 3.5.4" "more general" CategoryTheory.Adjunction.homEquiv_naturality_right_square_assoc
add_to_ega "0 3.5.4" "more general" CategoryTheory.Adjunction.homEquiv_symm_id
add_to_ega "0 3.5.4" "more general" CategoryTheory.Adjunction.mkOfHomEquiv_counit_app
add_to_ega "0 3.5.4" "more general" CategoryTheory.Adjunction.unit_naturality
add_to_ega "0 3.5.4" "special case"
  CategoryTheory.Functor.IsDenseSubsite.sheafifyHomEquivOfIsEquivalence_naturality_left
add_to_ega "0 3.5.4" "(3.5.4.1) for ψ = id_X" CategoryTheory.sheafToPresheaf_isRightAdjoint
add_to_ega "0 3.5.4" "special case" TopCat.Sheaf.pullback
add_to_ega "0 3.5.4" "special case" TopCat.Sheaf.pullbackPushforwardAdjunction
add_to_ega "0 3.5.5" "special case" AlgebraicGeometry.Scheme.Modules.pushforwardComp_inv_app_app
add_to_ega "0 3.5.5" "special case"
  CategoryTheory.Functor.sheafPushforwardContinuousComp_inv_app_hom_app
add_to_ega "0 3.5.5" TopCat.Presheaf.Pushforward.comp_inv_app
add_to_ega "0 3.5.6" "more general" CategoryTheory.sheafificationAdjunction
add_to_ega "0 3.5.6" CategoryTheory.sheafify
add_to_ega "0 3.5.6" "partial" CategoryTheory.sheafifyLift_unique
add_to_ega "0 3.5.6" "partial" CategoryTheory.sheafify_hom_ext
add_to_ega "0 3.5.6" "partial" CategoryTheory.toSheafify_sheafifyLift
add_to_ega "0 3.6.1" AlgebraicGeometry.PresheafedSpace.const
add_to_ega "0 3.6.2" "partial, special case" skyscraperPresheaf_isSheaf
add_to_ega "0 3.7.1" "partial" TopCat.Presheaf.Sheafify.isLocallyGerm
add_to_ega "0 3.7.1" "special case" TopCat.Presheaf.toSheafify
add_to_ega "0 3.7.1" "more general" TopCat.Sheaf.pullback
add_to_ega "0 3.7.1" "special case" TopCat.Sheaf.pullbackPushforwardAdjunction
add_to_ega "0 4.1.1" "special case" AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.mono
add_to_ega "0 4.1.1" "special case" AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono
add_to_ega "0 4.1.1" "special case" AlgebraicGeometry.SheafedSpace.IsOpenImmersion.instMono
add_to_ega "0 4.1.1" "more general"
  AlgebraicGeometry.SheafedSpace.mono_of_base_injective_of_stalk_epi
add_to_ega "0 4.1.1" "more general" TopCat.Presheaf.stalk
add_to_ega "0 4.1.2" "special case" AlgebraicGeometry.SheafedSpace.IsOpenImmersion.instMono
add_to_ega "0 4.1.3" "special case" AlgebraicGeometry.Scheme.Modules
add_to_ega "0 4.1.3" "partial" SheafOfModules.Submodule
add_to_ega "0 4.1.4" AlgebraicGeometry.IsReduced
add_to_ega "0 4.1.4" IsRegularRing
add_to_ega "0 4.1.4" "special case" isRegularRing_iff
add_to_ega "0 4.1.5" "special case" CategoryTheory.sheafHom
add_to_ega "0 4.1.5" "special case" CategoryTheory.sheafHomSectionsEquiv
add_to_ega "0 4.1.5" "special case" exteriorPower.map
add_to_ega "0 4.1.5" "special case" exteriorPower.map_comp
add_to_ega "0 4.1.5" "special case" exteriorPower.map_id
add_to_ega "0 4.1.5" "special case" lTensor.equiv
add_to_ega "0 4.1.5" "special case" lTensor_exact
add_to_ega "0 4.1.5" "special case" rTensor_exact
add_to_ega "0 4.1.7" "special case" AlgebraicGeometry.LocallyRingedSpace.GlueData
add_to_ega "0 4.1.7" "Overlap identification"
  AlgebraicGeometry.LocallyRingedSpace.GlueData.vPullbackConeIsLimit
add_to_ega "0 4.1.7" "partial" AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion
add_to_ega "0 4.1.7" "more general" AlgebraicGeometry.PresheafedSpace.GlueData
add_to_ega "0 4.1.7" "Overlap identification"
  AlgebraicGeometry.PresheafedSpace.GlueData.vPullbackConeIsLimit
add_to_ega "0 4.1.7" "special case" AlgebraicGeometry.Scheme.GlueData.gluedScheme
open AlgebraicGeometry.Scheme.GlueData in
add_to_ega "0 4.1.7" "partial"
  instIsOpenImmersionιLocallyRingedSpaceToLocallyRingedSpaceGlueData
add_to_ega "0 4.1.7" "more general" AlgebraicGeometry.SheafedSpace.GlueData
add_to_ega "0 4.1.7" "partial" AlgebraicGeometry.SheafedSpace.GlueData.ιIsOpenImmersion
add_to_ega "0 4.1.7" "partial" TopCat.GlueData
add_to_ega "0 4.1.7" "partial" TopCat.GlueData.MkCore
add_to_ega "0 4.1.7" "partial" TopCat.GlueData.image_inter
add_to_ega "0 4.2.1" "special case" AlgebraicGeometry.Scheme.Modules.pushforward
add_to_ega "0 4.2.5" "more general" CategoryTheory.Mod.scalarRestriction
add_to_ega "0 4.2.6" "special case" AlgebraicGeometry.Scheme.Modules.pushforwardComp
add_to_ega "0 4.3.1" "special case" AlgebraicGeometry.Scheme.Modules.pullback
add_to_ega "0 4.3.1" "special case" AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso
add_to_ega "0 4.3.2" "special case" AlgebraicGeometry.Scheme.Modules.instAdditivePullback
add_to_ega "0 4.3.2" "special case" TensorProduct.directLimitLeft
add_to_ega "0 4.3.2" "special case" TensorProduct.directLimitRight
add_to_ega "0 4.3.2" "more general" instIsLeftAdjointSheafCompPresheafForgetStalkFunctor
add_to_ega "0 4.3.4" "special case" Algebra.TensorProduct.lmul'
add_to_ega "0 4.3.4" "special case" Algebra.TensorProduct.lmul''
add_to_ega "0 4.3.4" "special case" LinearMap.mul'
add_to_ega "0 4.3.4" "special case" LinearMap.mul''
add_to_ega "0 4.3.5" "special case" FractionalIdeal.extended
add_to_ega "0 4.3.5" "special case" FractionalIdeal.extended_mul
add_to_ega "0 4.3.5" "special case" Ideal.map
add_to_ega "0 4.3.5" "special case" Ideal.map_mul
add_to_ega "0 4.3.5" "special case" TwoSidedIdeal.map
add_to_ega "0 4.3.6" "schemes" AlgebraicGeometry.Scheme.Modules.pullbackComp
add_to_ega "0 4.3.6" "more general" SheafOfModules.pullbackComp
add_to_ega "0 4.4.1" "special case" AlgebraicGeometry.Scheme.Modules.Hom
add_to_ega "0 4.4.3" "special case" AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap
add_to_ega "0 4.4.3" "partial" AlgebraicGeometry.PresheafedSpace.stalkMap_germ
add_to_ega "0 4.4.3" "special case" AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply
add_to_ega "0 4.4.3" "special case" AlgebraicGeometry.Scheme.Hom.stalkMap
add_to_ega "0 4.4.3" "special case" ModuleCat.ExtendRestrictScalarsAdj.unit_app
add_to_ega "0 4.4.4" "Ψ, special case" TensorProduct.map
add_to_ega "0 5.1.1" "more general" SheafOfModules.GeneratingSections
add_to_ega "0 5.1.1" SheafOfModules.free
add_to_ega "0 5.1.1" SheafOfModules.freeCofan
add_to_ega "0 5.1.1" "(1)" SheafOfModules.freeHomEquiv
add_to_ega "0 5.1.1" "partial" SheafOfModules.freeHomEquiv_apply
add_to_ega "0 5.1.1" "partial" SheafOfModules.isColimitFreeCofan
add_to_ega "0 5.1.1" "partial" SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
add_to_ega "0 5.1.1" "partial" SheafOfModules.unitHomEquiv_apply_coe
add_to_ega "0 5.1.1" "partial" SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
add_to_ega "0 5.1.1" SheafOfModules.ιFree
add_to_ega "0 5.1.3" SheafOfModules.IsQuasicoherent
add_to_ega "0 5.1.3" SheafOfModules.isQuasicoherent
add_to_ega "0 5.1.4" "special case" AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor
add_to_ega "0 5.1.4" "partial" SheafOfModules.freeFunctorCompPullbackIso
add_to_ega "0 5.1.4" "partial" SheafOfModules.pullbackObjFreeIso
add_to_ega "0 5.2.1" "special case" FGModuleCat.instFiniteCarrierSigmaObjModuleCatOfFinite
add_to_ega "0 5.2.1" "special case" Module.Finite.instDFinsupp
add_to_ega "0 5.2.1" "special case" Module.Finite.instDirectSum
add_to_ega "0 5.2.1" "special case" Module.Finite.prod
add_to_ega "0 5.2.1" "special case" Module.Finite.tensorProduct
add_to_ega "0 5.2.1" "special case" PiTensorProduct.finite
add_to_ega "0 5.2.2" "special case" AlgebraicGeometry.RingedSpace.exists_res_eq_zero_of_germ_eq_zero
add_to_ega "0 5.2.2" "special case" AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ
add_to_ega "0 5.2.2" "special case" Module.support_eq_zeroLocus
add_to_ega "0 5.2.4" "Global case of 5.2.4" SheafOfModules.instIsFiniteTypeMap
add_to_ega "0 5.2.5" "the local model" SheafOfModules.Presentation.IsFinite
add_to_ega "0 5.2.5" "special case" SheafOfModules.Presentation.isQuasicoherent
add_to_ega "0 5.2.5" "partial" SheafOfModules.QuasicoherentData.IsFinitePresentation
add_to_ega "0 5.2.5" "more general" SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
add_to_ega "0 5.2.5" "more general" SheafOfModules.instIsQuasicoherentOfIsFinitePresentation
add_to_ega "0 5.2.5" SheafOfModules.isFinitePresentation
add_to_ega "0 5.3.7" "special case" Module.annihilator
add_to_ega "0 5.4.1" "special case" Module.isLocallyConstant_rankAtStalk
add_to_ega "0 5.4.1" "special case" Module.isLocallyConstant_rankAtStalk_freeLocus
add_to_ega "0 5.4.1" Module.rankAtStalk
add_to_ega "0 5.4.2" "special case" dualTensorHomEquiv
add_to_ega "0 5.4.2" "special case" dualTensorHomEquivOfBasis
add_to_ega "0 5.4.3" "special case" Algebra.lsmul
add_to_ega "0 5.4.3" "Nakayama step" IsLocalRing.map_tensorProduct_mk_eq_top
add_to_ega "0 5.4.3" "Nakayama step: M = Az" IsLocalRing.span_eq_top_of_tmul_eq_basis
add_to_ega "0 5.4.3" "special case" Module.Invertible.finrank_eq_one
add_to_ega "0 5.4.3" "special case" Module.Invertible.instDual
add_to_ega "0 5.4.3" "Module case" Module.Invertible.toModuleEnd_bijective
add_to_ega "0 5.4.3" "special case" RestrictScalars.lsmul
add_to_ega "0 5.4.4" "affine case" Module.Invertible.instTensorProduct
add_to_ega "0 5.4.4" "affine case" Module.Invertible.instTensorProduct_2
add_to_ega "0 5.4.4" "special case" TensorPower
add_to_ega "0 5.4.4" "special case" TensorPower.algebraMap₀
add_to_ega "0 5.4.5" "special case" AlgebraicGeometry.Scheme.Modules.instAdditivePullback
add_to_ega "0 5.4.5" "more general" SheafOfModules.freeFunctorCompPullbackIso
add_to_ega "0 5.4.5" "more general" SheafOfModules.pullbackObjFreeIso
add_to_ega "0 5.4.7" "partial" CategoryTheory.PresheafOfGroups.OneCocycle.IsCohomologous
add_to_ega "0 5.4.7" "partial" CategoryTheory.PresheafOfGroups.OneCocycle.mk
add_to_ega "0 5.4.7" "special case" CommRing.Pic.ext_iff
add_to_ega "0 5.4.7" "special case" CommRing.Pic.mk.linearEquiv
add_to_ega "0 5.4.7" "special case" CommRing.Pic.mk_eq_iff
add_to_ega "0 5.4.7" "special case" CommRing.Pic.mk_eq_mk_iff
add_to_ega "0 5.4.7" "special case" CommRing.Pic.mk_tensor
add_to_ega "0 5.4.7" "special case" CommRing.Pic.mul_eq_tensor
add_to_ega "0 5.4.7" "special case" instCommGroupPic
add_to_ega "0 5.5.1" AlgebraicGeometry.LocallyRingedSpace
add_to_ega "0 5.5.1" "special case"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "0 5.5.1" "special case"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "0 5.5.1" AlgebraicGeometry.LocallyRingedSpace.instFieldCarrierResidueField
add_to_ega "0 5.5.1" AlgebraicGeometry.LocallyRingedSpace.mk
add_to_ega "0 5.5.1" AlgebraicGeometry.LocallyRingedSpace.residueField
add_to_ega "0 5.5.1" "special case"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "0 5.5.1" "special case" AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "0 5.5.1" "field structure on k(x)" AlgebraicGeometry.Scheme.instFieldCarrierResidueField
add_to_ega "0 5.5.1" "special case" AlgebraicGeometry.Scheme.residueField
add_to_ega "0 5.5.1" IsLocalRing.ResidueField
add_to_ega "0 5.5.1" IsLocalRing.ResidueField.field
add_to_ega "0 5.5.1" "special case" IsLocalRing.ker_residue
add_to_ega "0 5.5.1" IsLocalRing.maximalIdeal
add_to_ega "0 5.5.1" "special case" IsLocalRing.residue_eq_zero_iff
add_to_ega "0 5.5.2" "a⇔b for L=O_X"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "0 5.5.2" "a⇔b for L=O_X"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "0 5.5.2" "a⇔b for L=O_X"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "0 5.5.2" "a⇔b for L=O_X"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_ne_zero_iff_mem_basicOpen
add_to_ega "0 5.5.2" AlgebraicGeometry.RingedSpace.basicOpen
add_to_ega "0 5.5.2" "a⇒c for L=O_X" AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen
add_to_ega "0 5.5.2" "a⇒c for L=O_X" AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ
add_to_ega "0 5.5.2" "special case" AlgebraicGeometry.RingedSpace.zeroLocus_isClosed
add_to_ega "0 5.5.2" AlgebraicGeometry.Scheme.basicOpen
add_to_ega "0 5.5.2" "special case" AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "0 5.5.2" "special case" AlgebraicGeometry.Scheme.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "0 5.5.2" "special case" AlgebraicGeometry.Scheme.zeroLocus_isClosed
add_to_ega "0 5.5.3" "special case" AlgebraicGeometry.RingedSpace.basicOpen_mul
add_to_ega "0 5.5.3" "special case" AlgebraicGeometry.Scheme.basicOpen_mul
add_to_ega "0 5.5.3" "special case" AlgebraicGeometry.Scheme.zeroLocus_setMul
add_to_ega "0 5.5.4" "partial" LinearEquiv.ofIsUnitDet_symm_apply
add_to_ega "0 5.5.4" "partial" Matrix.det_smul_inv_mulVec_eq_cramer
add_to_ega "0 5.5.4" "partial" Matrix.det_smul_inv_vecMul_eq_cramer_transpose
add_to_ega "0 5.5.4" Matrix.inv
add_to_ega "0 5.5.4" "partial" Matrix.invOf_eq
add_to_ega "0 5.5.4" "partial" Matrix.invertibleEquivDetInvertible
add_to_ega "0 5.5.4" "Cramer solution identity" Matrix.mulVec_cramer
add_to_ega "0 5.5.4" "partial" Matrix.nonsing_inv_apply
add_to_ega "0 5.5.4" "partial" Matrix.nonsing_inv_mul
add_to_ega "0 5.5.4" "free case" Module.Basis.exteriorPower
add_to_ega "0 5.5.4" "dimension C(n, free case" exteriorPower.finrank_eq
add_to_ega "0 5.5.4" "free case" exteriorPower.instFree
add_to_ega "0 5.5.4" "free case" exteriorPower.subsingleton_of_span_eq_top_of_card_lt
add_to_ega "0 5.5.4" "partial" exteriorPower.ιMulti_family_linearIndependent_field
add_to_ega "0 5.5.5" "special case" IsLocalRing.split_injective_iff_lTensor_residueField_injective
add_to_ega "0 5.5.5" SheafOfModules.free.generatingSections
add_to_ega "0 5.5.5" SheafOfModules.freeSection
add_to_ega "0 6.0" CommRing
add_to_ega "0 6.0" "more general" TensorProduct.map
add_to_ega "0 6.0" TensorProduct.mapIncl
add_to_ega "0 6.1.1" "ι →₀ R with ι nonempty" Module.FaithfullyFlat.finsupp
add_to_ega "0 6.1.1" "nontrivial free modules" Module.FaithfullyFlat.instOfNontrivialOfFree
add_to_ega "0 6.1.1" "rank-one free module" Module.FaithfullyFlat.self
add_to_ega "0 6.1.1" Module.Flat
add_to_ega "0 6.1.1" "special case" Module.Flat.finsupp
add_to_ega "0 6.1.1" Module.Flat.iff_lTensor_exact'
add_to_ega "0 6.1.1" "more general" Module.Flat.iff_lTensor_injective
add_to_ega "0 6.1.1" "special case" Module.Flat.iff_lTensor_injective'
add_to_ega "0 6.1.1" Module.Flat.iff_lTensor_injectiveₛ
add_to_ega "0 6.1.1" Module.Flat.iff_lTensor_preserves_shortComplex_exact
add_to_ega "0 6.1.1" "more general" Module.Flat.iff_lift_lsmul_comp_subtype_injective
add_to_ega "0 6.1.1" Module.Flat.iff_rTensor_exact
add_to_ega "0 6.1.1" Module.Flat.iff_rTensor_exact'
add_to_ega "0 6.1.1" "more general" Module.Flat.iff_rTensor_injective
add_to_ega "0 6.1.1" "special case" Module.Flat.iff_rTensor_injective'
add_to_ega "0 6.1.1" Module.Flat.iff_rTensor_injectiveₛ
add_to_ega "0 6.1.1" Module.Flat.iff_rTensor_preserves_injective_linearMap
add_to_ega "0 6.1.1" Module.Flat.iff_rTensor_preserves_shortComplex_exact
add_to_ega "0 6.1.1" "flat ⇒ M ⊗ − exact" Module.Flat.lTensor_exact
add_to_ega "0 6.1.1" "flat ⇒ tensor exact" Module.Flat.lTensor_shortComplex_exact
add_to_ega "0 6.1.1" "more general" Module.Flat.of_free
add_to_ega "0 6.1.1" "more general" Module.Flat.of_projective
add_to_ega "0 6.1.1" "flat ⇒ tensor exact" Module.Flat.rTensor_exact
add_to_ega "0 6.1.1" "rank-one free module" Module.Flat.self
add_to_ega "0 6.1.1" "entries 1–2 of the TFAE" Module.Flat.tfae_equational_criterion
add_to_ega "0 6.1.2" "partial" LinearMap.lTensor_injective_of_exact_of_flat
add_to_ega "0 6.1.2" "sufficiency" Module.Flat.dfinsupp
add_to_ega "0 6.1.2" "more general" Module.Flat.dfinsupp_iff
add_to_ega "0 6.1.2" "sufficiency" Module.Flat.directSum
add_to_ega "0 6.1.2" "more general" Module.Flat.directSum_iff
add_to_ega "0 6.1.2" "free modules are flat" Module.Flat.of_free
add_to_ega "0 6.1.2" "more general" Module.Flat.of_projective
add_to_ega "0 6.1.2" "more general" lTensor_exact
add_to_ega "0 6.1.4" "special case" Ideal.inf_eq_mul_of_pure
add_to_ega "0 6.1.4" "special case" TensorProduct.submodule_tensor_inf_tensor_submodule
add_to_ega "0 6.2.1" "special case" Localization.flat
add_to_ega "0 6.2.1" "more general" Module.Flat.instTensorProduct
add_to_ega "0 6.2.1" ModuleCat.ExtendScalars.obj'
add_to_ega "0 6.2.1" ModuleCat.extendScalars
add_to_ega "0 6.2.2" "special case" IsBaseChange.linearMapLeftRight
add_to_ega "0 6.2.2" "special case" IsBaseChange.linearMapRightBaseChangeEquiv
add_to_ega "0 6.2.2" IsBaseChange.linearMapRightBaseChangeHom
add_to_ega "0 6.2.2" "special case" LinearMap.tensorProductEnd
add_to_ega "0 6.2.2" Module.FinitePresentation.isBaseChange_map
add_to_ega "0 6.2.3" CategoryTheory.Limits.IsColimit.module
add_to_ega "0 6.2.3" CategoryTheory.Limits.filteredColimitsModule
add_to_ega "0 6.2.3" "special case" Module.DirectLimit
add_to_ega "0 6.2.3" "special case" ModuleCat.FilteredColimits.colimit
add_to_ega "0 6.2.3" "special case" ModuleCat.FilteredColimits.colimitModule
add_to_ega "0 6.3.1" "A-flat implies S⁻¹A-flat" Algebra.FormallyUnramified.flat_of_restrictScalars
add_to_ega "0 6.3.1" "more general" IsLocalization.flat
add_to_ega "0 6.3.1" IsLocalization.moduleLid
add_to_ega "0 6.3.1" "special case" IsLocalization.tensor
add_to_ega "0 6.3.1" "special case" IsLocalization.tensorProduct_tensorProduct_right
add_to_ega "0 6.3.1" "more general" IsLocalizedModule.map_exact
add_to_ega "0 6.3.1" "more general" Localization.flat
add_to_ega "0 6.3.1" LocalizedModule.equivTensorProduct
add_to_ega "0 6.3.1" "more general" LocalizedModule.map_exact
add_to_ega "0 6.3.1" "special case" Module.Flat.instLocalizationAlgebraMapSubmonoid
add_to_ega "0 6.3.1" "S⁻¹M is S⁻¹A-flat" Module.Flat.localizedModule
add_to_ega "0 6.3.1" "S⁻¹M is S⁻¹A-flat" Module.Flat.of_isLocalizedModule
add_to_ega "0 6.3.1" "more general" Module.flat_iff_of_isLocalization
add_to_ega "0 6.3.1" "left exactness"
  ModuleCat.instPreservesFiniteLimitsLocalizationLocalizedModuleFunctor
add_to_ega "0 6.3.1" ModuleCat.localizedModuleFunctor_map_exact
add_to_ega "0 6.3.1" "principal localization" RingHom.Flat.holdsForLocalizationAway
add_to_ega "0 6.3.1" "special case" RingHom.Flat.propertyIsLocal
add_to_ega "0 6.3.2" "B = A" IsLocalization.Away.tensor
add_to_ega "0 6.3.2" "B = A" IsLocalization.Away.tensorEquiv
add_to_ega "0 6.3.2" "P = B" IsLocalization.Away.tensorProductEquivTMulRight
add_to_ega "0 6.3.2" "B = A" IsLocalization.Away.tensorRight
add_to_ega "0 6.3.2" "B = A" IsLocalization.Away.tensorRightEquiv
add_to_ega "0 6.3.2" "T⁻¹P = S⁻¹(T⁻¹P)" IsLocalization.algebraLid
add_to_ega "0 6.3.2" "A = B, P = B" IsLocalization.flat
add_to_ega "0 6.3.2" "B = A" IsLocalization.tensor
add_to_ega "0 6.3.2" "P = B, N an A-algebra" IsLocalization.tensorProductEquivOfMapIncludeRight
add_to_ega "0 6.3.2" "P = B, N an A-algebra" IsLocalization.tensorProduct_tensorProduct
add_to_ega "0 6.3.2" "P = B, N an A-algebra" IsLocalization.tensorProduct_tensorProduct_right
add_to_ega "0 6.3.2" "B = A" IsLocalization.tensorRight
add_to_ega "0 6.3.2" "more general" IsLocalizedModule.rTensor
add_to_ega "0 6.3.2" "P = B" Localization.flat
add_to_ega "0 6.3.2" "P = B, T = image of S" Module.Flat.instLocalizationAlgebraMapSubmonoid
add_to_ega "0 6.3.2" "B = A, T = S" Module.Flat.localizedModule
add_to_ega "0 6.3.2" "B = A, T = S" Module.Flat.of_isLocalizedModule
add_to_ega "0 6.3.2" "A = B = P" RingHom.Flat.holdsForLocalizationAway
add_to_ega "0 6.3.2" "P = B" RingHom.Flat.localRingHom
add_to_ega "0 6.3.2" "special case" RingHom.Flat.propertyIsLocal
add_to_ega "0 6.3.2" "Final clause with P = B" instFlatAtPrimeOfIsScalarTower
add_to_ega "0 6.3.3" "special case" IsLocalization.tensorProductEquivOfMapIncludeRight
add_to_ega "0 6.3.3" "special case" IsLocalization.tensorProduct_tensorProduct
add_to_ega "0 6.3.3" "special case" IsLocalization.tensorProduct_tensorProduct_right
add_to_ega "0 6.3.3" "partial" IsLocalizedModule.map_lTensor
add_to_ega "0 6.3.3" "(M ⊗_A N)_n ≅ M_n ⊗_A N" IsLocalizedModule.rTensor
add_to_ega "0 6.3.3" "a ⇒ b for M = B" Localization.flat
add_to_ega "0 6.3.3" "partial" LocalizedModule.equivTensorProduct
add_to_ega "0 6.3.3" "b ⇔ c" Module.flat_iff_of_isLocalization
add_to_ega "0 6.3.3" "b ⇒ a" Module.flat_of_isLocalized_maximal
add_to_ega "0 6.3.3" "b ⇒ a in the case B = A" Module.flat_of_localized_maximal
add_to_ega "0 6.3.3" "more general" injective_of_isLocalized_maximal
add_to_ega "0 6.3.3" "more general" injective_of_localized_maximal
add_to_ega "0 6.3.4" "special case" IsDedekindDomain.flat_iff_torsion_eq_bot
add_to_ega "0 6.3.4" "special case" Module.Flat.flat_iff_torsion_eq_bot_of_isBezout
add_to_ega "0 6.3.4" "more general"
  Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
add_to_ega "0 6.3.4" "special case" Module.Flat.instOfIsDedekindDomainOfIsTorsionFree
add_to_ega "0 6.3.4" "more general" Module.Flat.isSMulRegular_of_isRegular
add_to_ega "0 6.3.4" Module.Flat.isSMulRegular_of_nonZeroDivisors
add_to_ega "0 6.3.4" "more general" Module.Flat.torsion_eq_bot
add_to_ega "0 6.3.4" Module.fgSystem.equiv
add_to_ega "0 6.3.4" "more general" Module.free_of_finite_type_torsion_free
add_to_ega "0 6.3.4" "more general" Module.free_of_finite_type_torsion_free'
add_to_ega "0 6.3.4" Submodule.FG.directLimit
add_to_ega "0 6.3.4" "partial" Submodule.instIsTorsionFree
add_to_ega "0 6.4.1" "partial" IsTensorProduct.map_id_injective_of_flat_left
add_to_ega "0 6.4.1" "special case" Module.FaithfullyFlat.bijective_of_tensorProduct
add_to_ega "0 6.4.1" "special case" Module.FaithfullyFlat.faithfulSMul
add_to_ega "0 6.4.1" Module.FaithfullyFlat.iff_exact_iff_rTensor_exact
add_to_ega "0 6.4.1" Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top
add_to_ega "0 6.4.1" Module.FaithfullyFlat.iff_flat_and_lTensor_faithful
add_to_ega "0 6.4.1" Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality
add_to_ega "0 6.4.1" Module.FaithfullyFlat.iff_flat_and_proper_ideal
add_to_ega "0 6.4.1" Module.FaithfullyFlat.iff_flat_and_rTensor_faithful
add_to_ega "0 6.4.1" Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality
add_to_ega "0 6.4.1" "special case" Module.FaithfullyFlat.injective_of_tensorProduct
add_to_ega "0 6.4.1" "partial" Module.FaithfullyFlat.lTensor_bijective_iff_bijective
add_to_ega "0 6.4.1" "faithful flatness ⇒ a)" Module.FaithfullyFlat.lTensor_exact_iff_exact
add_to_ega "0 6.4.1" "partial" Module.FaithfullyFlat.lTensor_injective_iff_injective
add_to_ega "0 6.4.1" "b)" Module.FaithfullyFlat.lTensor_nontrivial
add_to_ega "0 6.4.1" "a)" Module.FaithfullyFlat.lTensor_reflects_exact
add_to_ega "0 6.4.1" "b)" Module.FaithfullyFlat.lTensor_reflects_triviality
add_to_ega "0 6.4.1" "partial" Module.FaithfullyFlat.lTensor_surjective_iff_surjective
add_to_ega "0 6.4.1" "b)" Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left
add_to_ega "0 6.4.1" "b)" Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
add_to_ega "0 6.4.1" "faithful flatness ⇒ a)" Module.FaithfullyFlat.rTensor_exact_iff_exact
add_to_ega "0 6.4.1" "b)" Module.FaithfullyFlat.rTensor_nontrivial
add_to_ega "0 6.4.1" "a)" Module.FaithfullyFlat.rTensor_reflects_exact
add_to_ega "0 6.4.1" "b)" Module.FaithfullyFlat.rTensor_reflects_triviality
add_to_ega "0 6.4.1" "b)" Module.FaithfullyFlat.subsingleton_tensorProduct_iff_left
add_to_ega "0 6.4.1" "b): M ⊗ N = 0 iff N = 0"
  Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
add_to_ega "0 6.4.1" "c)" Module.FaithfullyFlat.zero_iff_lTensor_zero
add_to_ega "0 6.4.1" "c)" Module.FaithfullyFlat.zero_iff_rTensor_zero
add_to_ega "0 6.4.1" "partial" Module.Flat.lTensor_preserves_injective_linearMap
add_to_ega "0 6.4.1" "special case" RingHom.FaithfullyFlat.injective
add_to_ega "0 6.4.2" "Parenthetical" IsLocalization.self
add_to_ega "0 6.4.2" "special case" Module.FaithfullyFlat.directSum
add_to_ega "0 6.4.2" "special case" Module.FaithfullyFlat.finsupp
add_to_ega "0 6.4.2" Module.FaithfullyFlat.instOfNontrivialOfFree
add_to_ega "0 6.4.2" "more general" Module.FaithfullyFlat.isLocalHom
add_to_ega "0 6.4.2" "Rank-one free module A" Module.FaithfullyFlat.self
add_to_ega "0 6.4.4" "special case" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_ega "0 6.4.5" "partial" Module.Flat.localizedModule
add_to_ega "0 6.4.5" "partial" Module.Flat.of_isLocalizedModule
add_to_ega "0 6.4.5" "partial" Module.flat_of_isLocalized_maximal
add_to_ega "0 6.4.5" "partial" Module.flat_of_localized_maximal
add_to_ega "0 6.5.1" "special case" Ideal.comap_map_eq_self_of_faithfullyFlat
add_to_ega "0 6.5.1" "special case" Ideal.comap_surjective_of_faithfullyFlat
add_to_ega "0 6.5.1" "special case" Ideal.exists_isPrime_liesOver_of_faithfullyFlat
add_to_ega "0 6.5.1" "special case" Module.FaithfullyFlat.faithfulSMul
add_to_ega "0 6.5.1" "special case" Module.FaithfullyFlat.one_tmul_eq_zero_iff
add_to_ega "0 6.5.1" "special case" Module.FaithfullyFlat.tensorProduct_mk_injective
add_to_ega "0 6.5.1" "special case" PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective
add_to_ega "0 6.5.1" "special case" RingHom.FaithfullyFlat.injective
add_to_ega "0 6.5.2" "φ⁻¹(aB) = a" Ideal.comap_map_eq_self_of_faithfullyFlat
add_to_ega "0 6.5.2" "special case" Ideal.map_injective_of_faithfullyFlat
add_to_ega "0 6.5.2" "a ↦ aB is increasing" Ideal.map_mono
add_to_ega "0 6.5.2" "special case" Module.FaithfullyFlat.faithfulSMul
add_to_ega "0 6.5.2" "special case" Module.FaithfullyFlat.tensorProduct_mk_injective
add_to_ega "0 6.5.2" "special case"
  Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
add_to_ega "0 6.6.1" "(a) ⇒ φ⁻¹(aB) = a in (d)" Ideal.comap_map_eq_self_of_faithfullyFlat
add_to_ega "0 6.6.1" "(a)" Module.FaithfullyFlat.faithfulSMul
add_to_ega "0 6.6.1" "(e) ⇒ (a), special case" Module.FaithfullyFlat.of_comap_surjective
add_to_ega "0 6.6.1" RingHom.FaithfullyFlat
add_to_ega "0 6.6.1" "(a)" RingHom.FaithfullyFlat.injective
add_to_ega "0 6.6.3" "M = A, M′ = I an ideal" Ideal.comap_map_eq_self_of_faithfullyFlat
add_to_ega "0 6.6.3" "sufficiency" Module.Flat.of_flat_tensorProduct
add_to_ega "0 6.6.3" "special case" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_ega "0 6.7.1" "f flat, special case" AlgebraicGeometry.Flat.iff_flat_stalkMap
add_to_ega "0 6.7.3" "partial" Module.Flat.iff_lTensor_injective
add_to_ega "0 6.7.3" "Algebraic reduction" Module.Flat.iff_lift_lsmul_comp_subtype_injective
add_to_ega "0 6.7.3" "Algebraic reduction" Module.Flat.iff_rTensor_injective
add_to_ega "0 6.7.4" "partial" LinearMap.lTensor_injective_of_exact_of_flat
add_to_ega "0 6.7.5" "Schemes (EGA preschemes)" AlgebraicGeometry.Flat.instIsMultiplicativeScheme
add_to_ega "0 6.7.5" "Schemes (EGA preschemes)"
  AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme
add_to_ega "0 6.7.5" "Affine schemes" RingHom.Flat.stableUnderComposition
add_to_ega "0 7.1.1" "necessarily open" IsLinearTopology.hasBasis_open_ideal
add_to_ega "0 7.1.1" "necessarily open" IsLinearTopology.hasBasis_open_twoSidedIdeal
add_to_ega "0 7.1.1" PowerSeries.HasEval
add_to_ega "0 7.1.1" "necessarily open" isLinearTopology_iff_hasBasis_open_ideal
add_to_ega "0 7.1.1" "necessarily open" isLinearTopology_iff_hasBasis_open_twoSidedIdeal
add_to_ega "0 7.1.2" "special case" IsAdicComplete
add_to_ega "0 7.1.3" "(i)" IsTopologicallyNilpotent.add
add_to_ega "0 7.1.3" "(i)" IsTopologicallyNilpotent.add_of_commute
add_to_ega "0 7.1.3" IsTopologicallyNilpotent.mem_topologicalNilradical_iff
add_to_ega "0 7.1.3" "(i)" IsTopologicallyNilpotent.mul_left
add_to_ega "0 7.1.3" "(i)" IsTopologicallyNilpotent.mul_left_of_commute
add_to_ega "0 7.1.3" "(i)" IsTopologicallyNilpotent.mul_right
add_to_ega "0 7.1.3" "(i)" IsTopologicallyNilpotent.mul_right_of_commute
add_to_ega "0 7.1.3" "(i), 0 ∈ T" IsTopologicallyNilpotent.zero
add_to_ega "0 7.1.3" "(i), 0 ∈ T" PowerSeries.HasEval.zero
add_to_ega "0 7.1.3" PowerSeries.coe_hasEvalIdeal
add_to_ega "0 7.1.3" PowerSeries.hasEvalIdeal
add_to_ega "0 7.1.3" coe_topologicalNilradical
add_to_ega "0 7.1.4" "(ii)" WithIdeal.isTopologicallyNilpotent_of_mem
add_to_ega "0 7.1.9" Ideal.adicTopology
add_to_ega "0 7.1.9" IsAdic
add_to_ega "0 7.1.9" IsAdicComplete
add_to_ega "0 7.1.9" WithIdeal.instTopologicalSpace
add_to_ega "0 7.1.9" "more general" isAdic_iff
add_to_ega "0 7.1.10" "adic case" IsAdicComplete.le_jacobson_bot
add_to_ega "0 7.1.11" "special case" IsNilpotent.isUnit_add_one
add_to_ega "0 7.1.11" "special case" IsNilpotent.isUnit_one_add
add_to_ega "0 7.1.13" "special case" IsLocalRing.subsingleton_tensorProduct
add_to_ega "0 7.1.13" "more general" Submodule.FG.eq_bot_of_le_jacobson_smul
add_to_ega "0 7.1.13" "more general" Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator
add_to_ega "0 7.1.13" "special case"
  Submodule.eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator
add_to_ega "0 7.1.13" "more general" Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
add_to_ega "0 7.1.13" "more general" Submodule.eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator
add_to_ega "0 7.1.13" "more general" Submodule.eq_smul_of_le_smul_of_le_jacobson
add_to_ega "0 7.1.13" "more general" Submodule.le_of_le_smul_of_le_jacobson_bot
add_to_ega "0 7.1.13" "more general" Submodule.smul_le_of_le_smul_of_le_jacobson_bot
add_to_ega "0 7.1.13" "more general" Submodule.sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson
add_to_ega "0 7.1.13" "partial" TensorProduct.quotTensorEquivQuotSMul
add_to_ega "0 7.1.13" "partial" TensorProduct.tensorQuotEquivQuotSMul
add_to_ega "0 7.1.14" "sufficiency" LinearMap.surjective_of_surjective_comp_mkQ
add_to_ega "0 7.2.3" "partial" AbstractCompletion.inseparable_extend_coe
add_to_ega "0 7.2.3" AdicCompletion
add_to_ega "0 7.2.3" ContinuousLinearMap.fromCompletion
add_to_ega "0 7.2.3" Ideal.adicTopology
add_to_ega "0 7.2.3" "partial" Ideal.adic_basis
add_to_ega "0 7.2.3" "more general" Ideal.hasBasis_nhds_adic
add_to_ega "0 7.2.3" "more general" Ideal.hasBasis_nhds_zero_adic
add_to_ega "0 7.2.3" "partial" Ideal.openAddSubgroup
add_to_ega "0 7.2.3" Ideal.ringFilterBasis
add_to_ega "0 7.2.3" "more general" IsAdic.hasBasis_nhds
add_to_ega "0 7.2.3" "more general" IsAdic.hasBasis_nhds_zero
add_to_ega "0 7.2.3" UniformSpace.Completion.coeRingHom
add_to_ega "0 7.2.3" "continuity of v" UniformSpace.Completion.continuous_extension
add_to_ega "0 7.2.3" UniformSpace.Completion.extension
add_to_ega "0 7.2.3" "partial" UniformSpace.Completion.extensionHom_coe
add_to_ega "0 7.2.3" "partial" UniformSpace.Completion.extension_coe
add_to_ega "0 7.2.3" "partial" UniformSpace.Completion.inseparable_extension_coe
add_to_ega "0 7.2.3" "continuity of v" UniformSpace.Completion.uniformContinuous_extension
add_to_ega "0 7.2.3" WithIdeal.instTopologicalSpace
add_to_ega "0 7.2.3" "more general" isAdic_iff
add_to_ega "0 7.2.8" "necessity" Ideal.Quotient.isNoetherianRing
add_to_ega "0 7.2.8" "necessity" isNoetherian_of_liesOver
add_to_ega "0 7.2.9" "partial" TensorProduct.quotTensorEquivQuotSMul
add_to_ega "0 7.2.9" "partial" TensorProduct.tensorQuotEquivQuotSMul
add_to_ega "0 7.2.11" "partial" AdicCompletion.ofAlgEquiv
add_to_ega "0 7.2.12" AdicCompletion
add_to_ega "0 7.2.12" "special case" AdicCompletion.instIsAdicCompleteMaximalIdeal
add_to_ega "0 7.2.12" "special case" AdicCompletion.isAdicComplete
add_to_ega "0 7.2.12" "special case" AdicCompletion.isAdicComplete_self
add_to_ega "0 7.2.12" AdicCompletion.module
add_to_ega "0 7.3.1" AdicCompletion
add_to_ega "0 7.3.1" AdicCompletion.map
add_to_ega "0 7.3.1" AdicCompletion.subalgebra
add_to_ega "0 7.3.1" AdicCompletion.subring
add_to_ega "0 7.3.1" "special case" QuotSMulTop.map_exact
add_to_ega "0 7.3.1" "partial" TensorProduct.quotTensorEquivQuotSMul
add_to_ega "0 7.3.1" "partial" TensorProduct.tensorQuotEquivQuotSMul
add_to_ega "0 7.3.2.1" Ideal.exists_pow_inf_eq_pow_smul
add_to_ega "0 7.3.3" AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
add_to_ega "0 7.3.3" "special case" AdicCompletion.ofTensorProductEquivOfPiFintype
add_to_ega "0 7.3.3" "special case" AdicCompletion.ofTensorProduct_bijective_of_pi_of_fintype
add_to_ega "0 7.3.3" "partial" AdicCompletion.tensor_map_id_left_injective_of_injective
add_to_ega "0 7.3.5" "a⇒c" Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
add_to_ega "0 7.3.5" "a⇒c" IsHausdorff.of_le_jacobson
add_to_ega "0 7.4.2" "partial" instIsHausdorffMaximalIdeal
add_to_ega "0 7.4.3" "special case" Algebra.QuasiFinite.iff_of_isArtinianRing
add_to_ega "0 7.4.3" "special case" Module.Finite.of_quasiFinite
add_to_ega "0 7.4.4" "(ii)" Algebra.QuasiFinite.instFiniteResidueField
add_to_ega "0 7.4.4" "special case" Algebra.QuasiFinite.instQuotientIdeal
add_to_ega "0 7.4.4" "(ii)" Algebra.WeaklyQuasiFiniteAt.finite_residueField
add_to_ega "0 7.4.4" "(ii)" Algebra.instFiniteResidueFieldOfQuasiFiniteAt
add_to_ega "0 7.5.1" "special case" MvPowerSeries.IsRestricted
add_to_ega "0 7.5.1" "partial" MvPowerSeries.IsRestricted.addSubgroup
add_to_ega "0 7.5.1" "special case" MvPowerSeries.IsRestricted.subring
add_to_ega "0 7.5.1" "partial" MvPowerSeries.isRestricted.add
add_to_ega "0 7.5.1" "partial" MvPowerSeries.isRestricted.mul
add_to_ega "0 7.5.1" "partial" MvPowerSeries.isRestricted.neg
add_to_ega "0 7.5.1" "special case" PowerSeries.IsRestricted
add_to_ega "0 7.5.1" "partial" PowerSeries.IsRestricted.addSubgroup
add_to_ega "0 7.5.1" "special case" PowerSeries.IsRestricted.subring
add_to_ega "0 7.5.1" "additive closure" PowerSeries.isRestricted.add
add_to_ega "0 7.5.1" "multiplicative closure" PowerSeries.isRestricted.mul
add_to_ega "0 7.5.1" "negation closure" PowerSeries.isRestricted.neg
add_to_ega "0 7.6.4" "Discrete topology on A" IsLocalization.subsingleton_iff
add_to_ega "0 7.6.4" "Discrete topology on A" OreLocalization.nontrivial_iff
add_to_ega "0 7.6.4" "Discrete topology on A" Submonoid.LocalizationMap.nontrivial
add_to_ega "0 7.6.6" "continuity of u′" AbstractCompletion.continuous_extend
add_to_ega "0 7.6.6" "uniqueness of u′" AbstractCompletion.extend_comp_coe
add_to_ega "0 7.6.6" "uniqueness of u′" AbstractCompletion.extend_unique
add_to_ega "0 7.6.6" "partial" AbstractCompletion.inseparable_extend_coe
add_to_ega "0 7.6.6" "uniqueness of u′" ContinuousLinearMap.fromCompletion_unique
add_to_ega "0 7.6.6" IsLocalization.lift
add_to_ega "0 7.6.6" UniformSpace.Completion.coeRingHom
add_to_ega "0 7.6.6" "continuity of u′" UniformSpace.Completion.continuous_extension
add_to_ega "0 7.6.6" "uniqueness of u′" UniformSpace.Completion.ext
add_to_ega "0 7.6.6" "uniqueness of u′" UniformSpace.Completion.ext'
add_to_ega "0 7.6.6" UniformSpace.Completion.extensionHom
add_to_ega "0 7.6.6" "partial" UniformSpace.Completion.extensionHom_coe
add_to_ega "0 7.6.6" "partial" UniformSpace.Completion.extension_coe
add_to_ega "0 7.6.6" "uniqueness of u′" UniformSpace.Completion.extension_comp_coe
add_to_ega "0 7.6.6" "uniqueness of u′" UniformSpace.Completion.extension_unique
add_to_ega "0 7.6.6" "partial" UniformSpace.Completion.inseparable_extension_coe
add_to_ega "0 7.6.6" "continuity of u′" UniformSpace.Completion.uniformContinuous_extension
add_to_ega "0 7.6.6" "uniqueness of u′" UniformSpaceCat.extension_comp_hom
add_to_ega "0 7.6.7" "special case" IsFractionRing.ringEquivOfRingEquiv
add_to_ega "0 7.6.7" "partial" IsFractionRing.ringEquivOfRingEquiv_algebraMap
add_to_ega "0 7.6.7" "partial" IsFractionRing.semilinearEquivOfRingEquiv_algebraMap
add_to_ega "0 7.6.7" "special case" IsLocalization.map
add_to_ega "0 7.6.7" "partial" IsLocalization.map_comp
add_to_ega "0 7.6.8" "partial" IsLocalization.Away.mul
add_to_ega "0 7.6.8" "partial" IsLocalization.localizationLocalizationAtPrimeIsoLocalization
add_to_ega "0 7.6.8" "partial" IsLocalization.localization_localization_isLocalization
add_to_ega "0 7.6.10" "special case" IsFractionRing.instAtPrimeFractionRing
add_to_ega "0 7.6.10" "special case" IsLocalization.AtPrime.equivQuotMaximalIdeal
add_to_ega "0 7.6.10" "special case" IsLocalization.AtPrime.orderIsoOfPrime
add_to_ega "0 7.6.10" "special case" IsLocalization.AtPrime.primeSpectrumOrderIso
add_to_ega "0 7.6.10" "special case" IsLocalization.orderIsoOfPrime
add_to_ega "0 7.6.10" "Discrete case" PrimeSpectrum.localization_comap_range
add_to_ega "0 7.6.10" "special case" instIsFractionRingAtPrimeFractionRing
add_to_ega "0 7.6.10" "special case"
  instIsFractionRingLocalizationAlgebraMapSubmonoidPrimeComplFractionRing
add_to_ega "0 7.6.13" "special case" IsLocalization.flat
add_to_ega "0 7.6.13" "special case" Localization.flat
add_to_ega "0 7.6.13" "special case" RingHom.Flat.holdsForLocalizationAway
add_to_ega "0 7.6.14" "special case" IsLocalization.flat
add_to_ega "0 7.6.14" "special case" Localization.flat
add_to_ega "0 7.6.14" "special case" RingHom.Flat.holdsForLocalizationAway
add_to_ega "0 7.6.15" "special case" AdicCompletion
add_to_ega "0 7.6.15" "partial" CategoryTheory.Limits.colimit
add_to_ega "0 7.6.15" "partial" CategoryTheory.Limits.colimit.desc
add_to_ega "0 7.6.15" "special case" Ideal.map
add_to_ega "0 7.6.15" "special case" IsLocalization.Away.awayToAwayLeft
add_to_ega "0 7.6.15" "partial" IsLocalization.map
add_to_ega "0 7.6.15" "special case" Localization.Away
add_to_ega "0 7.6.15" "partial" Ring.DirectLimit
add_to_ega "0 7.6.15" "partial" Submonoid.powers
add_to_ega "0 7.6.17" "Locality of A{S⁻¹} only"
  AdicCompletion.instIsLocalRingMaximalIdealOfIsNoetherianRing
add_to_ega "0 7.6.17" "Residue field of A{S⁻¹}" AdicCompletion.residueField_map_bijective
add_to_ega "0 7.6.17" "Residue field of A{S⁻¹}" AdicCompletion.residueField_map_bijective_of_fg
add_to_ega "0 7.6.17" "special case" IsLocalization.AtPrime.equivQuotMaximalIdeal
add_to_ega "0 7.6.17" "special case" IsLocalization.AtPrime.isLocalRing
add_to_ega "0 7.6.17" "special case" Localization.AtPrime.isLocalRing
add_to_ega "0 7.7.1" "special case" AdicCompletion
add_to_ega "0 7.7.1" "special case" AdicCompletion.module
add_to_ega "0 7.7.2" "B⊗_A(A/I) ≅ B/IB" Algebra.TensorProduct.quotIdealMapEquivTensorQuotAux
add_to_ega "0 7.7.2" "algebra case W = 0" Algebra.TensorProduct.quotientTensorEquiv
add_to_ega "0 7.7.2" "algebra case V = 0" Algebra.TensorProduct.tensorQuotientEquiv
add_to_ega "0 7.7.2" "M/rM ≅ (R/(r))⊗_R M" QuotSMulTop.equivQuotTensor
add_to_ega "0 7.7.2" "special case" QuotSMulTop.quotSMulTopTensorEquivQuotSMulTop
add_to_ega "0 7.7.2" "special case" QuotSMulTop.tensorQuotSMulTopEquivQuotSMulTop
add_to_ega "0 7.7.2" "case V = 0" TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
add_to_ega "0 7.7.2" "(R/I)⊗_R M ≅ M/IM" TensorProduct.quotTensorEquivQuotSMul
add_to_ega "0 7.7.2" "case W = 0" TensorProduct.quotientTensorEquiv
add_to_ega "0 7.7.2" "partial" TensorProduct.quotientTensorQuotientEquiv
add_to_ega "0 7.7.2" "M⊗_R(R/I) ≅ M/IM" TensorProduct.tensorQuotEquivQuotSMul
add_to_ega "0 7.7.2" "special case" TensorProduct.tensorQuotMapSMulEquivTensorQuot
add_to_ega "0 7.7.2" "case V = 0" TensorProduct.tensorQuotientEquiv
add_to_ega "0 7.7.6" "uniqueness of w₀" Algebra.TensorProduct.ext
add_to_ega "0 7.7.6" Algebra.TensorProduct.includeLeft
add_to_ega "0 7.7.6" Algebra.TensorProduct.includeRight
add_to_ega "0 7.7.6" Algebra.TensorProduct.lift
add_to_ega "0 7.7.6" Algebra.TensorProduct.productLeftAlgHom
add_to_ega "0 7.7.8" "B = Â" AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
add_to_ega "0 7.8.1" AdicCompletion.instModuleQuotientIdealHSMulTopSubmodule
add_to_ega "0 7.8.1" "Hom_A(M, special case" ContinuousLinearMap.finiteDimensional
add_to_ega "0 7.8.1" "more general" ContinuousLinearMap.instModuleFinite
add_to_ega "0 7.8.1" "Hom_A(M, special case" FGModuleCat.instFiniteHom
add_to_ega "0 7.8.1" "Hom_A(M, special case" FGModuleCat.instFiniteHomModuleCatObjIsFG
add_to_ega "0 7.8.1" "partial" Submodule.mapQ
add_to_ega "0 7.8.1" "more general" isNoetherian_linearMap
