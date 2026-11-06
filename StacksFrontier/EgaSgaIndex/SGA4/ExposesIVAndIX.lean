module  -- shake: keep-all

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.CategoryTheory.Functor.FunctorHom
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Monoidal.Closed.Zero
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Sites.LocalSite
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Map
import Mathlib.CategoryTheory.Sites.Point.Monoidal
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Sites.Point.Presheaf
import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.CategoryTheory.Sites.Types
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Subterminal
import Mathlib.Condensed.Discrete.Characterization
import Mathlib.Data.PNat.Factors
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Partition.Basic
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.PUnit
import Mathlib.Topology.Specialization
import Mathlib.Topology.Spectral.ConstructibleTopology
import StacksCore.Algebra.Algebra.Opposite
import StacksCore.RingTheory.Morita.End
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 4, Exposés IV and IX: references registered by name

The `add_to_sga` registrations of `StacksFrontier.EgaSgaIndex.SGA4` for Exposés IV and IX
of SGA 4, in the order of that file. See its module docstring.
-/

add_to_sga "4 IV 0.1" "partial" AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv
add_to_sga "4 IV 0.1" "comparison lemma"
  CategoryTheory.Functor.sheafInducedTopologyEquivOfIsCoverDense
add_to_sga "4 IV 0.1" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "4 IV 0.1" CategoryTheory.GrothendieckTopology.yoneda
add_to_sga "4 IV 0.1" CategoryTheory.Sheaf
add_to_sga "4 IV 0.1" "partial" CategoryTheory.coherentTopology.equivalence
add_to_sga "4 IV 0.1" "partial" CategoryTheory.regularTopology.equivalence
add_to_sga "4 IV 0.3" CategoryTheory.Sheaf
add_to_sga "4 IV 1.1.1" CategoryTheory.Sheaf.canonicalTopology
add_to_sga "4 IV 1.1.2" CategoryTheory.EffectiveEquivalenceRelation
add_to_sga "4 IV 1.1.2" CategoryTheory.IsEffectiveEquivalenceRelation
add_to_sga "4 IV 1.1.2" CategoryTheory.IsUniversallyEffectiveEquivalenceRelation
add_to_sga "4 IV 1.1.2" CategoryTheory.Limits.CoproductDisjoint
add_to_sga "4 IV 1.1.2" CategoryTheory.Limits.CoproductsOfShapeDisjoint
add_to_sga "4 IV 1.1.2" CategoryTheory.Limits.HasCoproduct
add_to_sga "4 IV 1.1.2" CategoryTheory.Limits.HasCoproducts
add_to_sga "4 IV 1.1.2" CategoryTheory.Limits.HasCoproductsOfShape
add_to_sga "4 IV 1.1.2" CategoryTheory.Limits.HasFiniteLimits
add_to_sga "4 IV 1.3" "special case" CategoryTheory.typeEquiv
add_to_sga "4 IV 1.3" "special case" not_small_type
add_to_sga "4 IV 1.5" CategoryTheory.Adjunction
add_to_sga "4 IV 1.5" CategoryTheory.Functor.IsLeftAdjoint
add_to_sga "4 IV 1.5" "necessity" CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint
add_to_sga "4 IV 1.5" "necessity" CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint
add_to_sga "4 IV 1.5" CategoryTheory.Limits.PreservesColimits
add_to_sga "4 IV 1.6" CategoryTheory.Functor.IsContinuous
add_to_sga "4 IV 1.6" CategoryTheory.Functor.IsLeftAdjoint
add_to_sga "4 IV 1.6" "(ii) ⇒ (i)" CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint
add_to_sga "4 IV 1.6" CategoryTheory.Limits.PreservesColimits
add_to_sga "4 IV 1.8" "partial" CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint
add_to_sga "4 IV 1.8" "partial" CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint
add_to_sga "4 IV 1.8" "the topos of U-sets" CategoryTheory.Injective.Type.enoughInjectives
add_to_sga "4 IV 1.8" "special case" CategoryTheory.IsCoseparator
add_to_sga "4 IV 1.8" CategoryTheory.ObjectProperty.IsCoseparating
add_to_sga "4 IV 2.1" "partial" TopCat.Presheaf.IsSheaf
add_to_sga "4 IV 2.1" "objects of Ouv(X)" TopologicalSpace.Opens
add_to_sga "4 IV 2.2" "Forward implication"
  CategoryTheory.Presieve.isTerminal_of_isSheafFor_empty_presieve
add_to_sga "4 IV 2.2" "Forward implication" CategoryTheory.Sheaf.isTerminalOfBotCover
add_to_sga "4 IV 2.2" "more general" TopCat.Presheaf.isSheaf_iff_isTerminal_of_indiscrete
add_to_sga "4 IV 2.2" "Necessity" TopCat.Sheaf.isTerminalOfEmpty
add_to_sga "4 IV 2.2" "Necessity" TopCat.Sheaf.isTerminalOfEqEmpty
add_to_sga "4 IV 2.4" "(G), special case" CategoryTheory.Over.grpObjMkPullbackSnd
add_to_sga "4 IV 2.4" "In the point topos" grpTypeEquivalenceGrp
add_to_sga "4 IV 2.6" "partial" Action
add_to_sga "4 IV 2.6" Action.FunctorCategoryEquivalence.functor
add_to_sga "4 IV 2.6" Action.FunctorCategoryEquivalence.inverse
add_to_sga "4 IV 2.6" "more general" Action.abelianAux
add_to_sga "4 IV 2.6" "more general" Action.functorCategoryEquivalence
add_to_sga "4 IV 2.6" "more general" Action.instIsEquivalenceFunctorSingleObjFunctor
add_to_sga "4 IV 2.6" "more general" Action.instIsEquivalenceFunctorSingleObjInverse
add_to_sga "4 IV 2.6" "partial" CategoryTheory.Groupoid.invEquivalence
add_to_sga "4 IV 2.6" "partial" CategoryTheory.Presheaf.isSheaf_bot
add_to_sga "4 IV 2.6" "partial" CategoryTheory.Presheaf.isStrongGenerator
add_to_sga "4 IV 2.6" "partial"
  CategoryTheory.Projective.projective_iff_preservesEpimorphisms_coyoneda_obj
add_to_sga "4 IV 2.6" "partial" CategoryTheory.isProjective
add_to_sga "4 IV 2.7.2" ProfiniteAddGrp
add_to_sga "4 IV 2.7.2" "partial"
  ProfiniteAddGrp.instAddGroupCarrierToTopTotallyDisconnectedSpacePtProfiniteLimitConeCompForget₂ContinuousAddMonoidHomToProfiniteContinuousMap
add_to_sga "4 IV 2.7.2" "compactness of lim G_i"
  ProfiniteAddGrp.instCompactSpaceSubtypeForallCarrierToTopTotallyDisconnectedSpaceToProfiniteObjMemAddSubgroupLimitConePtAux
add_to_sga "4 IV 2.7.2" "partial"
  ProfiniteAddGrp.instIsTopologicalAddGroupCarrierToTopTotallyDisconnectedSpacePtProfiniteLimitConeCompForget₂ContinuousAddMonoidHomToProfiniteContinuousMap
add_to_sga "4 IV 2.7.2" "special case" ProfiniteGrp.ProfiniteCompletion.completion
add_to_sga "4 IV 2.7.2" "compactness of lim G_i"
  ProfiniteGrp.instCompactSpaceSubtypeForallCarrierToTopTotallyDisconnectedSpaceToProfiniteObjMemSubgroupLimitConePtAux
add_to_sga "4 IV 2.7.2" "partial"
  ProfiniteGrp.instGroupCarrierToTopTotallyDisconnectedSpacePtProfiniteLimitConeCompForget₂ContinuousMonoidHomToProfiniteContinuousMap
add_to_sga "4 IV 2.7.2" "partial"
  ProfiniteGrp.instIsTopologicalGroupCarrierToTopTotallyDisconnectedSpacePtProfiniteLimitConeCompForget₂ContinuousMonoidHomToProfiniteContinuousMap
add_to_sga "4 IV 2.7.2" "more general" ProfiniteGrp.limit
add_to_sga "4 IV 2.7.2" "more general" continuousSMul_iff_stabilizer_isOpen
add_to_sga "4 IV 2.7.2" "partial" stabilizer_isOpen
add_to_sga "4 IV 2.7.4" IsCoveringMap
add_to_sga "4 IV 2.7.4" IsCoveringMapOn
add_to_sga "4 IV 2.7.4" IsEvenlyCovered
add_to_sga "4 IV 2.7.5" "special case" Condensed.IsDiscrete
add_to_sga "4 IV 3.1" "more general" CategoryTheory.Adjunction
add_to_sga "4 IV 3.1" "more general" CategoryTheory.Adjunction.CoreHomEquiv
add_to_sga "4 IV 3.1" CategoryTheory.Adjunction.homEquiv
add_to_sga "4 IV 3.1" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.leftAdjointUniq
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.leftAdjointUniq_hom_counit
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.rightAdjointUniq
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.unit_leftAdjointUniq_hom
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.unit_rightAdjointUniq_hom
add_to_sga "4 IV 3.1.1" "partial" CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app
add_to_sga "4 IV 3.1.2" "more general" CategoryTheory.Adjunction.rightAdjoint_preservesLimits
add_to_sga "4 IV 3.1.2" "more general"
  CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint
add_to_sga "4 IV 3.1.2" "more general"
  CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint
add_to_sga "4 IV 3.1.2" "more general"
  CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint
add_to_sga "4 IV 3.1.2" "more general"
  CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint
add_to_sga "4 IV 3.1.3" "partial" CategoryTheory.Adjunction.leftAdjoint_preservesColimits
add_to_sga "4 IV 3.1.3" "partial" CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint
add_to_sga "4 IV 3.1.3" "partial" CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint
add_to_sga "4 IV 3.1.3" "partial" CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint
add_to_sga "4 IV 3.2" "more general" CategoryTheory.Bicategory.mateEquiv
add_to_sga "4 IV 3.2" "more general" CategoryTheory.conjugateEquiv
add_to_sga "4 IV 3.3.1" "composite adjunction" CategoryTheory.Adjunction.comp
add_to_sga "4 IV 3.3.1" "partial" CategoryTheory.Adjunction.comp_homEquiv
add_to_sga "4 IV 3.3.1" "partial" CategoryTheory.Adjunction.id
add_to_sga "4 IV 3.3.1" "more general" CategoryTheory.Limits.comp_preservesFiniteLimits
add_to_sga "4 IV 3.3.2" "more general" CategoryTheory.NatTrans.hcomp
add_to_sga "4 IV 4.1.1" "more general" CategoryTheory.Adjunction.leftAdjointUniq
add_to_sga "4 IV 4.1.1" "partial" TopCat.Sheaf.pullback
add_to_sga "4 IV 4.1.1" TopCat.Sheaf.pushforward
add_to_sga "4 IV 4.1.1" "the functor f^{-1}" TopologicalSpace.Opens.map
add_to_sga "4 IV 4.1.2" "special case" Action.Hom
add_to_sga "4 IV 4.1.2" "special case" Action.Hom.mk
add_to_sga "4 IV 4.1.2" "partial" Action.res
add_to_sga "4 IV 4.1.2" "partial" Action.res_obj_ρ
add_to_sga "4 IV 4.1.2" "partial" MulAction.compHom
add_to_sga "4 IV 4.2.1" "partial" QuasiSober
add_to_sga "4 IV 4.2.2" "more general" Pi.preorder
add_to_sga "4 IV 4.2.2" "special case" Specialization.instPartialOrder
add_to_sga "4 IV 4.2.2" Specialization.instPreorder
add_to_sga "4 IV 4.2.2" Specialization.ofEquiv_specializes_ofEquiv
add_to_sga "4 IV 4.2.2" closure_singleton_eq_Iic
add_to_sga "4 IV 4.2.2" "T₀ partial order" specializationOrder
add_to_sga "4 IV 4.2.2" specializationPreorder
add_to_sga "4 IV 4.2.2" specializes_iff_closure_subset
add_to_sga "4 IV 4.2.2" specializes_iff_mem_closure
add_to_sga "4 IV 4.3" "necessity" CategoryTheory.Limits.IsTerminal.isTerminalObj
add_to_sga "4 IV 4.3" CategoryTheory.Limits.PreservesColimits
add_to_sga "4 IV 4.3" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 IV 4.3" CategoryTheory.Limits.sigmaConst
add_to_sga "4 IV 4.3" CategoryTheory.Limits.sigmaFunctor
add_to_sga "4 IV 4.3" "special case" CategoryTheory.constantPresheafAdj
add_to_sga "4 IV 4.3" "special case" CategoryTheory.constantSheafAdj
add_to_sga "4 IV 4.3.4" "special case" Condensed.IsDiscrete
add_to_sga "4 IV 4.3.5" "partial" CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit
add_to_sga "4 IV 4.3.5" CategoryTheory.Adjunction.unit
add_to_sga "4 IV 4.3.5" "partial" CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful
add_to_sga "4 IV 4.3.5" "special case" CategoryTheory.Functor.instFaithfulConstOfNonempty
add_to_sga "4 IV 4.3.5" "footnote" CategoryTheory.HasSubobjectClassifier.reflectsIsomorphisms
add_to_sga "4 IV 4.3.6" CategoryTheory.Sheaf.Γ
add_to_sga "4 IV 4.3.6" CategoryTheory.Sheaf.ΓNatIsoCoyoneda
add_to_sga "4 IV 4.4" "partial" CategoryTheory.Functor.preservesLimitsOfShape_of_isZero
add_to_sga "4 IV 4.4" "partial" CategoryTheory.uniqueHomsetOfInitialIsoUnit
add_to_sga "4 IV 4.5.1" "special case" Action.res
add_to_sga "4 IV 4.5.1" "special case" Action.resComp
add_to_sga "4 IV 4.5.1" "more general" CategoryTheory.Adjunction.leftAdjoint_preservesColimits
add_to_sga "4 IV 4.5.1" "partial" CategoryTheory.Adjunction.rightAdjoint_preservesLimits
add_to_sga "4 IV 4.5.1" "more general"
  CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint
add_to_sga "4 IV 4.5.1" "more general"
  CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint
add_to_sga "4 IV 4.5.1" "partial" CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint
add_to_sga "4 IV 4.5.1" "partial" CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint
add_to_sga "4 IV 4.5.1" "special case" MulAction.compHom
add_to_sga "4 IV 4.5.1" "(X)" MulActionHom
add_to_sga "4 IV 4.5.1" "special case" MulDistribMulAction.compHom
add_to_sga "4 IV 4.5.1" "(A), special case" Rep.coind
add_to_sga "4 IV 4.5.1" "special case" Rep.res
add_to_sga "4 IV 4.5.1" "special case" Rep.resFunctor
add_to_sga "4 IV 4.5.1" "special case" Rep.resMap
add_to_sga "4 IV 4.5.1" "(A), special case" Representation.coind
add_to_sga "4 IV 4.5.1" "special case" Representation.coindMap
add_to_sga "4 IV 4.5.1" "(A)" Representation.coindV
add_to_sga "4 IV 4.5.2" "partial" Action.res
add_to_sga "4 IV 4.5.2" "partial" Action.resComp
add_to_sga "4 IV 4.5.2" "partial" Action.resId
add_to_sga "4 IV 4.6.1" "partial" Action.abelianAux
add_to_sga "4 IV 4.6.1" "partial" Action.functorCategoryEquivalence
add_to_sga "4 IV 4.6.1" "partial" Action.instIsEquivalenceFunctorSingleObjFunctor
add_to_sga "4 IV 4.6.1" "partial" Action.instIsEquivalenceFunctorSingleObjInverse
add_to_sga "4 IV 4.6.1" "partial"
  CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeYonedaYonedaMap
add_to_sga "4 IV 4.6.1" "partial"
  CategoryTheory.Presheaf.instUniqueHomLeftExtensionOppositeOpObjFunctorTypeUliftYonedaMkUliftYonedaMap
add_to_sga "4 IV 4.6.1" "partial"
  CategoryTheory.Presheaf.instUniqueHomLeftExtensionOppositeOpObjFunctorTypeYonedaMkYonedaMap
add_to_sga "4 IV 4.6.1" "more general" CategoryTheory.Presheaf.isExtensionAlongULiftYoneda
add_to_sga "4 IV 4.6.1" "more general" CategoryTheory.Presheaf.uliftYonedaAdjunction
add_to_sga "4 IV 4.6.2" "From u" CategoryTheory.Functor.sheafPushforwardContinuousNatTrans
add_to_sga "4 IV 4.6.2" "partial" CategoryTheory.GrothendieckTopology.pointBotFunctor
add_to_sga "4 IV 4.6.2" "more general" CategoryTheory.mateEquiv
add_to_sga "4 IV 4.6.3" "partial" CategoryTheory.Functor.currying
add_to_sga "4 IV 4.6.3" "partial" CategoryTheory.Limits.preservesColimit_of_evaluation
add_to_sga "4 IV 4.6.3" "partial" CategoryTheory.Limits.preservesColimitsOfShape_of_evaluation
add_to_sga "4 IV 4.6.3" "partial" CategoryTheory.Limits.preservesColimits_of_evaluation
add_to_sga "4 IV 4.6.3" "partial" CategoryTheory.Limits.preservesLimit_of_evaluation
add_to_sga "4 IV 4.6.3" "partial" CategoryTheory.Limits.preservesLimitsOfShape_of_evaluation
add_to_sga "4 IV 4.6.3" "partial" CategoryTheory.Limits.preservesLimits_of_evaluation
add_to_sga "4 IV 4.6.3" "If every evaluation F(X)"
  CategoryTheory.preservesFiniteLimits_of_evaluation
add_to_sga "4 IV 4.6.4" CategoryTheory.nerve
add_to_sga "4 IV 4.6.4" CategoryTheory.nerveFunctor
add_to_sga "4 IV 4.7" CategoryTheory.Functor.IsCocontinuous
add_to_sga "4 IV 4.7" "partial" CategoryTheory.Functor.sheafAdjunctionCocontinuous
add_to_sga "4 IV 4.7" "partial"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
add_to_sga "4 IV 4.7" CategoryTheory.Functor.sheafPushforwardCocontinuous
add_to_sga "4 IV 4.7" "more general"
  CategoryTheory.Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso
add_to_sga "4 IV 4.7" "Forward implication" CategoryTheory.ran_isSheaf_of_isCocontinuous
add_to_sga "4 IV 4.7.4" "partial" CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint
add_to_sga "4 IV 4.8" "more general"
  CategoryTheory.Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso
add_to_sga "4 IV 4.8" "partial"
  CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification
add_to_sga "4 IV 4.8" "partial"
  CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_sheafification
add_to_sga "4 IV 4.8" "more general"
  CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
add_to_sga "4 IV 4.8" "partial" CategoryTheory.preservesFiniteLimits_presheafToSheaf
add_to_sga "4 IV 4.8" "partial" CategoryTheory.preservesLimitsOfShape_presheafToSheaf
add_to_sga "4 IV 4.8" CategoryTheory.sheafToPresheaf
add_to_sga "4 IV 4.8" "partial" CategoryTheory.sheafToPresheaf_isRightAdjoint
add_to_sga "4 IV 4.9.1" CategoryTheory.Functor.IsContinuous
add_to_sga "4 IV 4.9.1" "partial" CategoryTheory.Functor.sheafAdjunctionCocontinuous
add_to_sga "4 IV 4.9.1" "partial"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
add_to_sga "4 IV 4.9.1" CategoryTheory.Functor.sheafPushforwardContinuous
add_to_sga "4 IV 4.9.1" "special case" TopCat.Sheaf.pullbackPushforwardAdjunction
add_to_sga "4 IV 4.9.4" "more general" CategoryTheory.Functor.isContinuous_iff_coverPreserving
add_to_sga "4 IV 4.9.4" "partial" CategoryTheory.Functor.isContinuous_of_coverPreserving
add_to_sga "4 IV 4.10" CategoryTheory.Sheaf
add_to_sga "4 IV 4.10.6" "partial" AlgebraicGeometry.Scheme.Etale
add_to_sga "4 IV 4.10.6" "partial" AlgebraicGeometry.Scheme.ProEt
add_to_sga "4 IV 5.1" CategoryTheory.GrothendieckTopology.over
add_to_sga "4 IV 5.2" CategoryTheory.Over.forget
add_to_sga "4 IV 5.2" "partial" CategoryTheory.Over.instIsLeftAdjointForget
add_to_sga "4 IV 5.3" "partial" CategoryTheory.Over.equivalenceOfIsTerminal_functor
add_to_sga "4 IV 5.3" "partial" CategoryTheory.Over.mono_left_of_mono
add_to_sga "4 IV 5.5" "more general" CategoryTheory.Over.iteratedSliceEquiv
add_to_sga "4 IV 5.8" MulAction.quotient
add_to_sga "4 IV 5.8" "partial" QuotientGroup.instHasQuotientSubgroup
add_to_sga "4 IV 5.8.4" "partial" AddSubgroup.isOpen_of_isClosed_of_finiteIndex
add_to_sga "4 IV 5.8.4" "partial" OpenNormalAddSubgroup.toFiniteIndexNormalAddSubgroup
add_to_sga "4 IV 5.8.4" "partial" OpenNormalSubgroup.toFiniteIndexNormalSubgroup
add_to_sga "4 IV 5.8.4" OpenSubgroup
add_to_sga "4 IV 5.8.4" "partial" OpenSubgroup.isClopen
add_to_sga "4 IV 5.8.4" "partial"
  Subgroup.instFiniteQuotientSubtypeMemOpenSubgroupOfIsTopologicalGroupOfCompactSpace
add_to_sga "4 IV 5.8.4" "partial" Subgroup.isOpen_of_isClosed_of_finiteIndex
add_to_sga "4 IV 5.8.4" "partial" Subgroup.quotient_finite_of_isOpen
add_to_sga "4 IV 5.8.4" "partial" Subgroup.quotient_finite_of_isOpen'
add_to_sga "4 IV 5.9" "special case" AddTorsor.mk
add_to_sga "4 IV 5.9" "(H), special case" MulActionHom.toQuotient
add_to_sga "4 IV 5.10" "more general" CategoryTheory.Over.createsColimitsOfSize
add_to_sga "4 IV 5.11.1" CategoryTheory.LeftExactFunctor
add_to_sga "4 IV 5.11.1" CategoryTheory.Limits.HasFiniteLimits
add_to_sga "4 IV 5.11.1" "special case"
  CategoryTheory.Limits.IsLimit.pullbackConeEquivBinaryFanInverse
add_to_sga "4 IV 5.11.1" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 IV 5.11.1" CategoryTheory.Limits.PreservesLimitsOfShape
add_to_sga "4 IV 5.11.1" "special case" CategoryTheory.Limits.pullback_lift_diagonal_isPullback
add_to_sga "4 IV 5.11.1" "special case" CategoryTheory.Limits.pullback_map_diagonal_isPullback
add_to_sga "4 IV 5.11.1" "special case" CategoryTheory.Over.isLimitLiftCone
add_to_sga "4 IV 5.11.1" "special case" CategoryTheory.Over.sections
add_to_sga "4 IV 5.11.2" CategoryTheory.LeftExactFunctor
add_to_sga "4 IV 5.11.2" "partial" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 IV 5.11.2" "partial" CategoryTheory.leftExactFunctor
add_to_sga "4 IV 6.2" "Clause of Definition 6.2" CategoryTheory.Limits.PreservesColimits
add_to_sga "4 IV 6.2" "Clause of Definition 6.2" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 IV 6.3" CategoryTheory.CategoryOfElements.costructuredArrowULiftYonedaEquivalence
add_to_sga "4 IV 6.3" "Presheaf case"
  CategoryTheory.Functor.Elements.isColimitCoconeπOpCompShrinkYonedaFlip
add_to_sga "4 IV 6.3" "more general"
  CategoryTheory.GrothendieckTopology.Point.instIsIsoMapFunctorOppositePresheafFiberToSheafify
add_to_sga "4 IV 6.3" "left exactness"
  CategoryTheory.GrothendieckTopology.Point.instPreservesFiniteLimitsFiber
add_to_sga "4 IV 6.3" "more general"
  CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso
add_to_sga "4 IV 6.3" CategoryTheory.GrothendieckTopology.Point.sheafFiber
add_to_sga "4 IV 6.3" "special case" CategoryTheory.Presheaf.colimitOfRepresentable
add_to_sga "4 IV 6.3" CategoryTheory.Functor.Elements.instCategory
add_to_sga "4 IV 6.4.0" "special case" CategoryTheory.Functor.ReflectsIsomorphisms
add_to_sga "4 IV 6.4.0" "partial" CategoryTheory.HasSubobjectClassifier.reflectsIsomorphisms
add_to_sga "4 IV 6.4.0" CategoryTheory.JointlyReflectIsomorphisms
add_to_sga "4 IV 6.4.1" CategoryTheory.GrothendieckTopology.HasEnoughPoints
add_to_sga "4 IV 6.4.1" CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints
add_to_sga "4 IV 6.4.3" "special case" CategoryTheory.Functor.isInitial
add_to_sga "4 IV 6.4.3" "special case" CategoryTheory.Functor.isTerminal
add_to_sga "4 IV 6.4.3" "Monomorphism clause"
  CategoryTheory.GrothendieckTopology.Point.fiber_map_injective_of_mono
add_to_sga "4 IV 6.4.3" "Terminal-object clause"
  CategoryTheory.GrothendieckTopology.Point.isTerminalFiberObj
add_to_sga "4 IV 6.4.3" "Subterminal clause"
  CategoryTheory.GrothendieckTopology.Point.subsingleton_fiber_obj
add_to_sga "4 IV 6.4.3" "Terminal-object clause"
  CategoryTheory.GrothendieckTopology.Point.uniqueFiberObj
add_to_sga "4 IV 6.4.3" "Epimorphism clause"
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectEpimorphisms
add_to_sga "4 IV 6.4.3" "Monomorphism clause"
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonomorphisms
add_to_sga "4 IV 6.5" "6.5(a)"
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem
add_to_sga "4 IV 6.5" "6.5(a)"
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem_of_small
add_to_sga "4 IV 6.5" "6.5(a)" CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mk'
add_to_sga "4 IV 6.5.2" CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered.fiber
add_to_sga "4 IV 6.6" "partial" CategoryTheory.GrothendieckTopology.Point.comap
add_to_sga "4 IV 6.6" "partial" CategoryTheory.GrothendieckTopology.Point.map
add_to_sga "4 IV 6.7" "partial" CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber
add_to_sga "4 IV 6.7" "partial" CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber_comp
add_to_sga "4 IV 6.7" "partial" CategoryTheory.GrothendieckTopology.Point.Hom.presheafFiber_id
add_to_sga "4 IV 6.7" "partial" CategoryTheory.GrothendieckTopology.Point.sheafFiber
add_to_sga "4 IV 6.7.3" "special case"
  CategoryTheory.GrothendieckTopology.instHasEnoughPointsOverOverOfWEqualsLocallyBijectiveFunOfHasSheafifyType
add_to_sga "4 IV 6.7.3" "special case"
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.over
add_to_sga "4 IV 6.7.4" "special case"
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.over
add_to_sga "4 IV 6.8" "more general" CategoryTheory.StructuredArrow.createsFiniteLimits
add_to_sga "4 IV 6.8.2" CategoryTheory.GrothendieckTopology.Point.fiber
add_to_sga "4 IV 6.8.2" "more general"
  CategoryTheory.GrothendieckTopology.Point.instIsIsoMapFunctorOppositePresheafFiberToSheafify
add_to_sga "4 IV 6.8.2" "more general"
  CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso
add_to_sga "4 IV 6.8.2" "special case" TopologicalSpace.OpenNhds
add_to_sga "4 IV 6.8.6" "special case"
  CategoryTheory.GrothendieckTopology.IsLocalSite.pointPresheafFiberNatIso
add_to_sga "4 IV 6.8.6" CategoryTheory.GrothendieckTopology.pointBot
add_to_sga "4 IV 6.8.6" "more general" CategoryTheory.GrothendieckTopology.pointBotPresheafFiberIso
add_to_sga "4 IV 6.8.6" "more general" CategoryTheory.Presheaf.isSheaf_bot
add_to_sga "4 IV 6.8.6" "more general" CategoryTheory.Presieve.isSheaf_bot
add_to_sga "4 IV 6.8.7" "(iii) ⇒ (ii)" CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
add_to_sga "4 IV 6.8.7" "special case" CategoryTheory.GrothendieckTopology.Point.presheafFiber
add_to_sga "4 IV 6.8.7" "special case" CategoryTheory.GrothendieckTopology.Point.sheafFiber
add_to_sga "4 IV 6.10" "more general" CategoryTheory.GrothendieckTopology.Point.presheafFiber
add_to_sga "4 IV 6.10" CategoryTheory.GrothendieckTopology.Point.sheafFiber
add_to_sga "4 IV 7.1.5" Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology
add_to_sga "4 IV 7.1.5" "more general" TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso
add_to_sga "4 IV 7.1.5" "more general" TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
add_to_sga "4 IV 7.1.9" "(b)" Opens.instHasEnoughPointsOpensGrothendieckTopology
add_to_sga "4 IV 7.1.9" "(b)" Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology
add_to_sga "4 IV 7.5" CategoryTheory.Idempotents.Karoubi
add_to_sga "4 IV 7.5" CategoryTheory.Idempotents.Karoubi.Hom
add_to_sga "4 IV 7.5" CategoryTheory.Idempotents.Karoubi.Hom.mk
add_to_sga "4 IV 7.5" CategoryTheory.Idempotents.Karoubi.coe
add_to_sga "4 IV 7.5" CategoryTheory.Idempotents.Karoubi.instCategory
add_to_sga "4 IV 7.5" CategoryTheory.Idempotents.Karoubi.mk
add_to_sga "4 IV 7.5" "φ is fully faithful" CategoryTheory.Idempotents.fullyFaithfulToKaroubi
add_to_sga "4 IV 7.5" "φ is faithful" CategoryTheory.Idempotents.instFaithfulKaroubiToKaroubi
add_to_sga "4 IV 7.5" "φ is full" CategoryTheory.Idempotents.instFullKaroubiToKaroubi
add_to_sga "4 IV 7.5"
  CategoryTheory.Idempotents.instIsEquivalenceFunctorKaroubiObjWhiskeringLeftToKaroubi
add_to_sga "4 IV 7.5" "kar(C) is Karoubian"
  CategoryTheory.Idempotents.instIsIdempotentCompleteKaroubi
add_to_sga "4 IV 7.5"
  CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent
add_to_sga "4 IV 7.5" CategoryTheory.Idempotents.karoubiUniversal
add_to_sga "4 IV 7.5" "special case" CategoryTheory.Idempotents.karoubiUniversal₁
add_to_sga "4 IV 7.5" CategoryTheory.Idempotents.toKaroubi
add_to_sga "4 IV 7.5" "partial" CategoryTheory.Idempotents.whiskeringLeftObjToKaroubiFullyFaithful
add_to_sga "4 IV 7.5" CategoryTheory.IsIdempotentComplete
add_to_sga "4 IV 7.5" "more general" CategoryTheory.IsSplitCoequalizer.map
add_to_sga "4 IV 7.5" "more general" CategoryTheory.IsSplitEqualizer.map
add_to_sga "4 IV 7.5" CategoryTheory.Limits.HasCoequalizer
add_to_sga "4 IV 7.5" CategoryTheory.Limits.coequalizer
add_to_sga "4 IV 7.5" CategoryTheory.Limits.coequalizer.π
add_to_sga "4 IV 7.5" CategoryTheory.Limits.equalizer
add_to_sga "4 IV 7.5" "more general" CategoryTheory.Limits.preservesSplitCoequalizers
add_to_sga "4 IV 7.5" "more general" CategoryTheory.Limits.preservesSplitEqualizers
add_to_sga "4 IV 7.5" CategoryTheory.Retract
add_to_sga "4 IV 7.5" "more general" CategoryTheory.map_is_split_pair
add_to_sga "4 IV 7.5" IsIdempotentElem
add_to_sga "4 IV 7.6" CategoryTheory.Functor.IsRightAdjoint
add_to_sga "4 IV 7.6" "more general"
  CategoryTheory.Projective.projective_iff_preservesEpimorphisms_coyoneda_obj
add_to_sga "4 IV 7.6" CategoryTheory.isProjective
add_to_sga "4 IV 7.6" "partial" IsOpen.connectedComponentIn
add_to_sga "4 IV 7.6" LocallyConnectedSpace
add_to_sga "4 IV 7.6" "Exercise IV 7.6 i)" connectedComponentIn_mem_nhds
add_to_sga "4 IV 7.6" locallyConnectedSpace_iff_connectedComponentIn_open
add_to_sga "4 IV 7.7" "more general" CategoryTheory.GrothendieckTopology.pointBot
add_to_sga "4 IV 7.8" "(c)" Opens.instHasEnoughPointsOpensGrothendieckTopology
add_to_sga "4 IV 7.8" "(c)" Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology
add_to_sga "4 IV 8.2" "partial, special case" TopCat.LocalPredicate
add_to_sga "4 IV 8.2" "partial" TopCat.subpresheafToTypes.isSheaf
add_to_sga "4 IV 8.2" "partial" TopCat.subsheafToTypes
add_to_sga "4 IV 8.3" CategoryTheory.Subobject
add_to_sga "4 IV 8.3" CategoryTheory.Subterminals
add_to_sga "4 IV 8.4.2" "finite infima of opens" CategoryTheory.Subobject.completeSemilatticeInf
add_to_sga "4 IV 8.4.2" "partial" CategoryTheory.Subobject.completeSemilatticeSup
add_to_sga "4 IV 8.4.2" "partial" CategoryTheory.Subobject.instCompleteLattice
add_to_sga "4 IV 8.5.4" "more general"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst
add_to_sga "4 IV 8.5.5" "special case"
  Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway
add_to_sga "4 IV 8.5.5" "special case" AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget
add_to_sga "4 IV 8.5.5" "special case" AlgebraicGeometry.IsProper.instIsZariskiLocalAtTarget
add_to_sga "4 IV 8.5.5" "special case" AlgebraicGeometry.IsSeparated.instIsZariskiLocalAtTarget
add_to_sga "4 IV 8.5.5" AlgebraicGeometry.Scheme.fppfPrecoverage
add_to_sga "4 IV 8.5.5" "special case"
  AlgebraicGeometry.Scheme.instIsLocalAtTargetIsomorphismsZariskiPrecoverage
add_to_sga "4 IV 8.5.5" "special case" AlgebraicGeometry.UniversallyOpen.instIsZariskiLocalAtTarget
add_to_sga "4 IV 8.5.5" "Target"
  AlgebraicGeometry.instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "4 IV 8.5.5" "Target"
  AlgebraicGeometry.instDescendsAlongSchemeLocallyOfFiniteTypeMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "4 IV 8.5.5" "Target"
  AlgebraicGeometry.instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "4 IV 8.5.5" "special case"
  AlgebraicGeometry.instIsZariskiLocalAtTargetMonomorphismsScheme
add_to_sga "4 IV 8.5.5" "special case" AlgebraicGeometry.isOpenImmersion_isZariskiLocalAtTarget
add_to_sga "4 IV 8.5.5" "special case" AlgebraicGeometry.surjective_isZariskiLocalAtTarget
add_to_sga "4 IV 8.5.5" "special case" Module.flat_of_isLocalized_span
add_to_sga "4 IV 8.5.5" "special case" RingHom.Etale.ofLocalizationSpan
add_to_sga "4 IV 8.5.5" "special case" RingHom.Etale.ofLocalizationSpanTarget
add_to_sga "4 IV 8.5.5" "étaleness, special case" RingHom.Etale.propertyIsLocal
add_to_sga "4 IV 8.5.5" "flatness, special case" RingHom.Flat.propertyIsLocal
add_to_sga "4 IV 8.5.5" "special case" RingHom.Smooth.ofLocalizationSpanTarget
add_to_sga "4 IV 8.5.5" "smoothness, special case" RingHom.Smooth.propertyIsLocal
add_to_sga "4 IV 8.5.5" "special case" RingHom.finitePresentation_ofLocalizationSpanTarget
add_to_sga "4 IV 8.5.5" "special case" RingHom.finiteType_isLocal
add_to_sga "4 IV 8.5.5" "special case" RingHom.finiteType_ofLocalizationSpanTarget
add_to_sga "4 IV 8.5.5" "special case" RingHom.isIntegral_ofLocalizationSpan
add_to_sga "4 IV 8.7" "more general" Partition
add_to_sga "4 IV 8.7" "partial" Partition.instPartialOrder
add_to_sga "4 IV 9.1.1" "partial" CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful
add_to_sga "4 IV 9.1.1" "partial" CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit
add_to_sga "4 IV 9.1.2" "For T' finer than T" CategoryTheory.Presheaf.IsSheaf.of_le
add_to_sga "4 IV 9.1.2" "Binary case" CategoryTheory.Presheaf.isSheaf_sup
add_to_sga "4 IV 9.1.2" "Inclusion (C" CategoryTheory.Presieve.isSheaf_of_le
add_to_sga "4 IV 9.1.2" "Binary case of d)" CategoryTheory.Presieve.isSheaf_sup
add_to_sga "4 IV 9.1.2" CategoryTheory.Sheaf.finestTopology
add_to_sga "4 IV 9.1.2" "9.1.2 d), special case" CategoryTheory.Sheaf.finestTopologySingle
add_to_sga "4 IV 9.1.2" "9.1.2 d)" CategoryTheory.Sheaf.le_finestTopology
add_to_sga "4 IV 9.1.2" "9.1.2 d)" CategoryTheory.Sheaf.sheaf_for_finestTopology
add_to_sga "4 IV 9.1.7" "a)" CategoryTheory.Adjunction.hasLeftCalculusOfFractions'
add_to_sga "4 IV 9.1.7" "a)" CategoryTheory.Adjunction.isLocalization_leftAdjoint
add_to_sga "4 IV 9.1.7" "a)" CategoryTheory.Adjunction.isLocalization_leftAdjoint'
add_to_sga "4 IV 9.1.7"
  CategoryTheory.Localization.instInhabitedStrictUniversalPropertyFixedTargetLocalizationQ
add_to_sga "4 IV 9.1.7" CategoryTheory.MorphismProperty.HasLocalization.standard
add_to_sga "4 IV 9.1.7" CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty
add_to_sga "4 IV 9.1.7" "ST1" CategoryTheory.MorphismProperty.IsStableUnderComposition
add_to_sga "4 IV 9.1.7" CategoryTheory.MorphismProperty.Localization
add_to_sga "4 IV 9.1.7" "f)" CategoryTheory.MorphismProperty.coproducts
add_to_sga "4 IV 9.1.7" "c)"
  CategoryTheory.MorphismProperty.instHasTwoOutOfThreePropertyInverseImage
add_to_sga "4 IV 9.1.7" "e)" CategoryTheory.MorphismProperty.instHasTwoOutOfThreePropertyMin
add_to_sga "4 IV 9.1.7" CategoryTheory.MorphismProperty.inverseImage
add_to_sga "4 IV 9.1.7" "c)" CategoryTheory.MorphismProperty.isInvertedBy_isomorphisms
add_to_sga "4 IV 9.1.8" TopologicalSpace.induced
add_to_sga "4 IV 9.1.8" "d)" Topology.IsInducing.isEmbedding
add_to_sga "4 IV 9.1.8" "d)" isEmbedding_iff_isInducing
add_to_sga "4 IV 9.1.9" FrameHom
add_to_sga "4 IV 9.1.9" FrameHomClass
add_to_sga "4 IV 9.1.9" Order.Frame
add_to_sga "4 IV 9.1.11" CategoryTheory.IsNoetherianObject
add_to_sga "4 IV 9.1.11" "forward direction"
  CategoryTheory.isEventuallyConstant_of_isNoetherianObject
add_to_sga "4 IV 9.1.11" CategoryTheory.isNoetherianObject
add_to_sga "4 IV 9.1.11" "more general" CategoryTheory.isNoetherianObject_iff_isEventuallyConstant
add_to_sga "4 IV 9.1.11" "more general"
  CategoryTheory.isNoetherianObject_iff_monotone_chain_condition
add_to_sga "4 IV 9.1.11" "9.1.11 a), special case" TopologicalSpace.NoetherianSpace.inter_of_left
add_to_sga "4 IV 9.1.11" "9.1.11 a), special case" TopologicalSpace.NoetherianSpace.inter_of_right
add_to_sga "4 IV 9.1.11" "9.1.11 a), special case" TopologicalSpace.NoetherianSpace.of_subset
add_to_sga "4 IV 9.1.11" "9.1.11 a), special case" TopologicalSpace.NoetherianSpace.set
add_to_sga "4 IV 9.1.11" "9.1.11 g)" compactSpace_withConstructibleTopology
add_to_sga "4 IV 9.1.11" constructibleTopology
add_to_sga "4 IV 9.1.13" "c)" Complementeds.instComplementedLattice
add_to_sga "4 IV 9.1.13" "c)" Complementeds.instDistribLattice
add_to_sga "4 IV 9.1.13" "c)" Complementeds.instMax
add_to_sga "4 IV 9.1.13" "d)" DistribLattice.ofInfSupLe
add_to_sga "4 IV 9.1.13" IsCompl
add_to_sga "4 IV 9.1.13" "a): Heyting-algebra case" IsCompl.compl_eq
add_to_sga "4 IV 9.1.13" "more general" IsCompl.disjoint_left_iff
add_to_sga "4 IV 9.1.13" "more general" IsCompl.disjoint_right_iff
add_to_sga "4 IV 9.1.13" "a): Heyting-algebra case" IsCompl.eq_compl
add_to_sga "4 IV 9.1.13" "more general" IsCompl.inf_left_eq_bot_iff
add_to_sga "4 IV 9.1.13" "more general" IsCompl.inf_right_eq_bot_iff
add_to_sga "4 IV 9.1.13" "c), d)" IsCompl.inf_sup
add_to_sga "4 IV 9.1.13" "more general" IsCompl.le_left_iff
add_to_sga "4 IV 9.1.13" "more general" IsCompl.le_right_iff
add_to_sga "4 IV 9.1.13" "more general" IsCompl.le_sup_right_iff_inf_left_le
add_to_sga "4 IV 9.1.13" "d): dual of a)" IsCompl.left_le_iff
add_to_sga "4 IV 9.1.13" "d): dual of a)" IsCompl.right_le_iff
add_to_sga "4 IV 9.1.13" "c), d)" IsCompl.sup_inf
add_to_sga "4 IV 9.1.13" "c)" IsCompl.symm
add_to_sga "4 IV 9.1.13" IsComplemented
add_to_sga "4 IV 9.1.13" "c)" IsComplemented.inf
add_to_sga "4 IV 9.1.13" "d)" OrderDual.instDistribLattice
add_to_sga "4 IV 9.1.13" "(c), special case" compl_iInf
add_to_sga "4 IV 9.1.13" "(c), special case" compl_iSup
add_to_sga "4 IV 9.1.13" "(c), special case" compl_inf
add_to_sga "4 IV 9.1.13" "(c), special case" compl_sSup
add_to_sga "4 IV 9.1.13" "(c), special case" compl_sup
add_to_sga "4 IV 9.1.13" "(a) in Boolean lattices" disjoint_compl_left_iff
add_to_sga "4 IV 9.1.13" "(a) in Boolean lattices" disjoint_compl_right_iff
add_to_sga "4 IV 9.1.13" "(a) in Boolean lattices" isGreatest_compl
add_to_sga "4 IV 9.1.13" "(a) in Boolean lattices" le_compl_iff_disjoint_left
add_to_sga "4 IV 9.1.13" "(a) in Boolean lattices" le_compl_iff_disjoint_right
add_to_sga "4 IV 9.2.1" CategoryTheory.IsSubterminal
add_to_sga "4 IV 9.2.1" "more general" CategoryTheory.Subobject
add_to_sga "4 IV 9.2.1" CategoryTheory.Subterminals
add_to_sga "4 IV 9.2.4" "more general"
  CategoryTheory.Limits.instPreservesCofilteredLimitsOfSizeOverForget
add_to_sga "4 IV 9.3.3" CategoryTheory.Limits.PreservesColimitsOfShape
add_to_sga "4 IV 9.3.3" CategoryTheory.Limits.PreservesFilteredColimits
add_to_sga "4 IV 9.3.3" CategoryTheory.Limits.PreservesFilteredColimitsOfSize
add_to_sga "4 IV 9.3.3" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 IV 9.3.3" CategoryTheory.leftExactFunctor
add_to_sga "4 IV 9.5.1" "more general" CategoryTheory.Comma
add_to_sga "4 IV 9.5.1" "partial" CategoryTheory.Comma.comp_right
add_to_sga "4 IV 9.5.1" "more general" CategoryTheory.Comma.mk
add_to_sga "4 IV 9.5.1" "more general" CategoryTheory.CommaMorphism
add_to_sga "4 IV 9.5.1" "more general" CategoryTheory.CommaMorphism.mk
add_to_sga "4 IV 9.5.1" "more general" CategoryTheory.MorphismProperty.Comma.instCategory
add_to_sga "4 IV 9.5.1" "more general" CategoryTheory.commaCategory
add_to_sga "4 IV 9.5.2" "more general" CategoryTheory.Comma.map
add_to_sga "4 IV 9.5.2" "more general" CategoryTheory.Comma.mapRight
add_to_sga "4 IV 9.5.2" "partial" CategoryTheory.Comma.mapRightComp
add_to_sga "4 IV 9.5.2" "partial" CategoryTheory.Comma.mapRightId
add_to_sga "4 IV 9.5.4" "partial" CategoryTheory.Functor.IsAccessible
add_to_sga "4 IV 9.5.4" "partial" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 IV 9.5.5" CategoryTheory.Comma
add_to_sga "4 IV 9.5.8.1" CategoryTheory.Comma.fst
add_to_sga "4 IV 9.5.8.1" "Object formula i^*(X" CategoryTheory.Comma.fst_obj
add_to_sga "4 IV 9.5.8.4" "more general" CategoryTheory.Comma.snd
add_to_sga "4 IV 9.6" "special case" CategoryTheory.Adjunction.representableBy
add_to_sga "4 IV 9.6" "special case"
  CategoryTheory.Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top
add_to_sga "4 IV 9.6" "special case"
  CategoryTheory.Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top
add_to_sga "4 IV 9.6" "special case"
  CategoryTheory.Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
add_to_sga "4 IV 9.8.1" TopCat.Sheaf.pullback
add_to_sga "4 IV 9.8.2" CategoryTheory.EquivalenceRelation
add_to_sga "4 IV 9.8.2" "f), special case" Opens.instHasEnoughPointsOpensGrothendieckTopology
add_to_sga "4 IV 9.8.2" "g), special case" Opens.instIsThinPointOpensGrothendieckTopology
add_to_sga "4 IV 9.8.2" "f), special case"
  Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology
add_to_sga "4 IV 10.2" CategoryTheory.Functor.functorHom
add_to_sga "4 IV 10.2" "copresheaf topos" CategoryTheory.Functor.functorHomEquiv
add_to_sga "4 IV 10.2" CategoryTheory.MonoidalClosed.internalHom
add_to_sga "4 IV 10.2" "more general" CategoryTheory.MonoidalClosed.internalHomAdjunction₂
add_to_sga "4 IV 10.2" CategoryTheory.ihom
add_to_sga "4 IV 10.2" "more general"
  CategoryTheory.ihom.instPreservesLimitsOfShapeOppositeObjFunctorFlipInternalHom
add_to_sga "4 IV 10.4" "special case" CategoryTheory.Presheaf.IsSheaf.hom
add_to_sga "4 IV 10.4" "special case" CategoryTheory.Presheaf.isSheaf_functorEnrichedHom
add_to_sga "4 IV 10.4" "special case" CategoryTheory.sheafHom
add_to_sga "4 IV 10.4" "special case" CategoryTheory.sheafHom'Iso
add_to_sga "4 IV 10.4.1" "more general"
  CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
add_to_sga "4 IV 10.4.1" "more general" CategoryTheory.instHasSheafifyType
add_to_sga "4 IV 10.4.1" CategoryTheory.sheafToPresheaf
add_to_sga "4 IV 10.4.1" "partial" CategoryTheory.sheafToPresheaf_isRightAdjoint
add_to_sga "4 IV 10.4.1" CategoryTheory.sheafificationAdjunction
add_to_sga "4 IV 10.4.1" CategoryTheory.smallSheafificationAdjunction
add_to_sga "4 IV 10.4.1" CategoryTheory.smallSheafify
add_to_sga "4 IV 10.5" "more general" CategoryTheory.frobeniusMorphism
add_to_sga "4 IV 10.5.2" CategoryTheory.frobeniusMorphism
add_to_sga "4 IV 10.5.4" "more general" CategoryTheory.expComparison
add_to_sga "4 IV 10.8" "Clause 2), special case" CategoryTheory.presheafHomSectionsEquiv
add_to_sga "4 IV 10.8" "Clause 2), special case" CategoryTheory.sheafHomSectionsEquiv
add_to_sga "4 IV 11.1.2" "partial" AddCommGrpCat.Hom
add_to_sga "4 IV 11.1.2" "special case" AlgebraicGeometry.Scheme.Modules
add_to_sga "4 IV 11.1.2" "special case" AlgebraicGeometry.Scheme.Modules.Hom
add_to_sga "4 IV 11.1.2" "special case" AlgebraicGeometry.Scheme.Modules.instAbelian
add_to_sga "4 IV 11.1.2" "special case" AlgebraicGeometry.Scheme.instAbelianSheafAffineEtaleTopology
add_to_sga "4 IV 11.1.2" "special case"
  AlgebraicGeometry.Scheme.instAbelianSheafEtaleSmallEtaleTopology
add_to_sga "4 IV 11.1.2" "special case" ModuleCat
add_to_sga "4 IV 11.1.2" "special case" ModuleCat.abelian
add_to_sga "4 IV 11.1.2" "special case" PresheafOfModules.instAbelian
add_to_sga "4 IV 11.1.2" "special case" PresheafOfModules.instAddCommGroupHom
add_to_sga "4 IV 11.1.2" SheafOfModules.instAddCommGroupHom
add_to_sga "4 IV 11.1.2" "more general" SheafOfModules.instPreadditive
add_to_sga "4 IV 11.1.2" SheafOfModules.mk
add_to_sga "4 IV 11.1.2" "special case" TopCat.Sheaf.instAbelian
add_to_sga "4 IV 11.1.2" "special case" instAbelianCondensedMod
add_to_sga "4 IV 11.1.3" "special case" AlgEquiv.moduleEndSelf
add_to_sga "4 IV 11.1.3" "special case" AlgEquiv.moduleEndSelfOp
add_to_sga "4 IV 11.1.3" "special case" Algebra.rmul
add_to_sga "4 IV 11.1.3" "special case" RingEquiv.moduleEndSelf
add_to_sga "4 IV 11.1.3" "special case" RingEquiv.moduleEndSelfOp
add_to_sga "4 IV 11.1.3" "special case" toEndEndAlgHom
add_to_sga "4 IV 11.1.4" "special case" ModuleCat.RestrictScalars.obj'
add_to_sga "4 IV 11.1.4" "special case" ModuleCat.restrictScalars
add_to_sga "4 IV 11.1.5" "special case" Int.castRingHom
add_to_sga "4 IV 11.1.5" "punctual topos" ModuleCat.restrictScalars
add_to_sga "4 IV 11.1.6" "special case" ModuleCat.instReflectsIsomorphismsRestrictScalars
add_to_sga "4 IV 11.1.6" "special case" ModuleCat.preservesColimit_restrictScalars
add_to_sga "4 IV 11.1.6" "special case" ModuleCat.preservesLimit_restrictScalars
add_to_sga "4 IV 11.1.6" "special case" instPreservesFiniteColimitsModuleCatRestrictScalars
add_to_sga "4 IV 11.1.6" "special case" instPreservesFiniteLimitsModuleCatRestrictScalars
add_to_sga "4 IV 11.2.2" "special case"
  AlgebraicGeometry.Scheme.Modules.instIsLeftAdjointRestrictFunctor
add_to_sga "4 IV 11.2.2" "special case"
  AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
add_to_sga "4 IV 11.2.2" "special case" AlgebraicGeometry.Scheme.Modules.restrict
add_to_sga "4 IV 11.2.2" "special case" AlgebraicGeometry.Scheme.Modules.restrictAdjunction
add_to_sga "4 IV 11.2.2" "special case"
  AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app
add_to_sga "4 IV 11.2.2" SheafOfModules.Hom.over
add_to_sga "4 IV 11.2.2" "special case" SheafOfModules.overMapPushforwardAdj
add_to_sga "4 IV 11.2.2" SheafOfModules.overPushforwardOverAdj
add_to_sga "4 IV 11.2.3" "special case" PresheafOfModules.pushforwardCompToPresheaf
add_to_sga "4 IV 11.3.3" "special case" CategoryTheory.Sheaf.freeYoneda
add_to_sga "4 IV 11.3.3" "special case" SheafOfModules.free
add_to_sga "4 IV 11.3.3" "special case" SheafOfModules.freeFunctor
add_to_sga "4 IV 11.3.3" "Hom_A(A_X, special case" SheafOfModules.freeHomEquiv
add_to_sga "4 IV 11.3.5" CategoryTheory.GrothendieckTopology.Point.over
add_to_sga "4 IV 12.3" "(a)" SheafOfModules.overPushforwardOverAdj
add_to_sga "4 IV 12.4" "special case" CategoryTheory.Presheaf.IsSheaf.hom
add_to_sga "4 IV 12.4" "partial" PresheafOfModules.Sheafify.module
add_to_sga "4 IV 12.7" "special case" PresheafOfModulesOfCommRing.Monoidal.tensorObj
add_to_sga "4 IV 12.7" "special case" TensorProduct
add_to_sga "4 IV 12.8" "special case" ModuleCat.monoidalClosedHomEquiv
add_to_sga "4 IV 12.8" "special case" Rep.MonoidalClosed.linearHomEquiv
add_to_sga "4 IV 12.8" "special case" TensorProduct.LieModule.lift
add_to_sga "4 IV 12.9" "special case"
  PresheafOfModulesOfCommRing.instPreservesColimitsOfSizeTensorLeft
add_to_sga "4 IV 12.9" "special case"
  PresheafOfModulesOfCommRing.instPreservesColimitsOfSizeTensorRight
add_to_sga "4 IV 12.10" "special case" PresheafOfModulesOfCommRing.Monoidal.tensorObj
add_to_sga "4 IV 12.12" "more general" Bimod.tensorBimod
add_to_sga "4 IV 12.12" "special case" TensorProduct.instModule
add_to_sga "4 IV 12.14" "special case" ModuleCat.monoidalClosedHomEquiv
add_to_sga "4 IV 13.2.1" "special case" ModuleCat.RestrictScalars.obj'
add_to_sga "4 IV 13.2.1" "special case" ModuleCat.restrictScalars
add_to_sga "4 IV 13.2.2" "special case" ModuleCat.ExtendScalars.obj'
add_to_sga "4 IV 13.2.2" "special case" ModuleCat.extendScalars
add_to_sga "4 IV 13.4" "special case" AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
add_to_sga "4 IV 13.4" "special case" SheafOfModules.freeFunctorCompPullbackIso
add_to_sga "4 IV 13.4" "partial" SheafOfModules.pullbackObjFreeIso
add_to_sga "4 IV 13.4" "(13.4.3)" SheafOfModules.pullbackObjFreeIso_hom_naturality
add_to_sga "4 IV 13.4" "(13.4.3)" SheafOfModules.pullbackObjFreeIso_hom_naturality_assoc
add_to_sga "4 IV 13.5" "special case"
  CategoryTheory.GrothendieckTopology.Point.instMonoidalFunctorOppositePresheafFiber
add_to_sga "4 IV 13.5" "special case"
  CategoryTheory.GrothendieckTopology.Point.instMonoidalSheafSheafFiber
add_to_sga "4 IV 13.6" "special case" instPreservesFiniteLimitsModuleCatRestrictScalars
add_to_sga "4 IV 13.9" "a), special case" AlgebraicGeometry.RingedSpace.basicOpen
add_to_sga "4 IV 13.9" "special case" AlgebraicGeometry.Scheme.affineBasicOpen
add_to_sga "4 IV 14.2" "special case" AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
add_to_sga "4 IV 14.2" "special case" AlgebraicGeometry.Scheme.Modules.restrictAdjunction
add_to_sga "4 IX 1.1" "special case" Nat.mem_factoredNumbers'
add_to_sga "4 IX 1.1" Nat.mem_primeFactors
add_to_sga "4 IX 1.1" Nat.primeFactors
add_to_sga "4 IX 1.1" Nat.primeFactors_eq_to_filter_divisors_prime
add_to_sga "4 IX 1.1" PNat.mem_factorMultiset
add_to_sga "4 IX 3.3" "special case" CommRing.Pic
add_to_sga "4 IX 3.3" "special case" instCommGroupPic
add_to_sga "4 IX 3.3.1" "special case" AlgebraicGeometry.Scheme.germToFunctionField_injective
add_to_sga "4 IX 3.3.1" "special case" AlgebraicGeometry.germ_injective_of_isIntegral
add_to_sga "4 IX 4.0" AlgebraicGeometry.Scheme.functionField
add_to_sga "4 IX 4.0" "special case" AlgebraicGeometry.instFieldCarrierFunctionField
add_to_sga "4 IX 5.1" "more general" CategoryTheory.Adjunction.unit
