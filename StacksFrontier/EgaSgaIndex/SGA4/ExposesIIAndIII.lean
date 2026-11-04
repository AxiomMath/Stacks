module  -- shake: keep-all

import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.MonCat.Adjunctions
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.Types
import Mathlib.Condensed.Limits
import Mathlib.Topology.Sheaves.Abelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 4, Exposés II and III: references registered by name

The `add_to_sga` registrations of `StacksFrontier.EgaSgaIndex.SGA4` for Exposés II and III
of SGA 4, in the order of that file. See its module docstring.
-/

add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology
add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology.Cover.pullback
add_to_sga "4 II 1.1" "more general" CategoryTheory.GrothendieckTopology.arrow_max
add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology.covering_of_eq_top
add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology.mk
add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology.pullback_stable
add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology.pullback_stable'
add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology.top_mem
add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology.top_mem'
add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology.transitive
add_to_sga "4 II 1.1" CategoryTheory.GrothendieckTopology.transitive'
add_to_sga "4 II 1.1.1" "special case" CategoryTheory.Coverage.saturate_of_superset
add_to_sga "4 II 1.1.1" CategoryTheory.GrothendieckTopology.Cover
add_to_sga "4 II 1.1.1" "nonemptiness" CategoryTheory.GrothendieckTopology.Cover.instInhabited
add_to_sga "4 II 1.1.1" "partial" CategoryTheory.GrothendieckTopology.Cover.instOrderTop
add_to_sga "4 II 1.1.1" "partial" CategoryTheory.GrothendieckTopology.Cover.instSemilatticeInf
add_to_sga "4 II 1.1.1" "partial" CategoryTheory.GrothendieckTopology.arrow_intersect
add_to_sga "4 II 1.1.1" "empty intersection" CategoryTheory.GrothendieckTopology.covering_of_eq_top
add_to_sga "4 II 1.1.1" "more general" CategoryTheory.GrothendieckTopology.intersection_covering_iff
add_to_sga "4 II 1.1.1" CategoryTheory.GrothendieckTopology.sieves
add_to_sga "4 II 1.1.1" CategoryTheory.GrothendieckTopology.superset_covering
add_to_sga "4 II 1.1.1" "empty intersection" CategoryTheory.GrothendieckTopology.top_mem
add_to_sga "4 II 1.1.1" "empty intersection" CategoryTheory.GrothendieckTopology.top_mem'
add_to_sga "4 II 1.1.1" "partial" CategoryTheory.isCofilteredOrEmpty_of_directed_ge
add_to_sga "4 II 1.1.1" "partial" CategoryTheory.isCofilteredOrEmpty_of_semilatticeInf
add_to_sga "4 II 1.1.1" "more general" CategoryTheory.isCofiltered_of_directed_ge_nonempty
add_to_sga "4 II 1.1.1" "more general" CategoryTheory.isCofiltered_of_semilatticeInf_nonempty
add_to_sga "4 II 1.1.2" CategoryTheory.GrothendieckTopology.instLEGrothendieckTopology
add_to_sga "4 II 1.1.2" CategoryTheory.GrothendieckTopology.instPartialOrder
add_to_sga "4 II 1.1.2" CategoryTheory.GrothendieckTopology.le_def
add_to_sga "4 II 1.1.3" CategoryTheory.GrothendieckTopology.instCompleteLattice
add_to_sga "4 II 1.1.3" CategoryTheory.GrothendieckTopology.instInfSet
add_to_sga "4 II 1.1.3" CategoryTheory.GrothendieckTopology.isGLB_sInf
add_to_sga "4 II 1.1.3" "covering criterion" CategoryTheory.GrothendieckTopology.mem_sInf
add_to_sga "4 II 1.1.4" "partial" CategoryTheory.GrothendieckTopology.bot_covering
add_to_sga "4 II 1.1.4" "partial" CategoryTheory.GrothendieckTopology.bot_covers
add_to_sga "4 II 1.1.4" CategoryTheory.GrothendieckTopology.discrete
add_to_sga "4 II 1.1.4" "partial" CategoryTheory.GrothendieckTopology.discrete_eq_top
add_to_sga "4 II 1.1.4" "partial" CategoryTheory.GrothendieckTopology.top_covering
add_to_sga "4 II 1.1.4" "partial" CategoryTheory.GrothendieckTopology.top_covers
add_to_sga "4 II 1.1.4" CategoryTheory.GrothendieckTopology.trivial
add_to_sga "4 II 1.1.4" "partial" CategoryTheory.GrothendieckTopology.trivial_covering
add_to_sga "4 II 1.1.5" CategoryTheory.GrothendieckTopology
add_to_sga "4 II 1.1.6" "partial" CategoryTheory.Precoverage.generate_mem_toGrothendieck
add_to_sga "4 II 1.1.6" CategoryTheory.Precoverage.toGrothendieck
add_to_sga "4 II 1.1.6" CategoryTheory.Precoverage.toGrothendieck_eq_sInf
add_to_sga "4 II 1.3" "more general" CategoryTheory.Functor.relativelyRepresentable
add_to_sga "4 II 1.3" CategoryTheory.Limits.HasPullbacksAlong
add_to_sga "4 II 1.3" "more general" CategoryTheory.MorphismProperty.HasPullbacks
add_to_sga "4 II 1.3" CategoryTheory.Precoverage.HasPullbacks
add_to_sga "4 II 1.3" CategoryTheory.Precoverage.IsStableUnderBaseChange
add_to_sga "4 II 1.3" CategoryTheory.Precoverage.IsStableUnderComposition
add_to_sga "4 II 1.3" CategoryTheory.Pretopology
add_to_sga "4 II 1.3" CategoryTheory.Pretopology.transitive
add_to_sga "4 II 1.3.1" CategoryTheory.GrothendieckTopology.toPretopology
add_to_sga "4 II 1.3.1" "more general" CategoryTheory.Precoverage.toGrothendieck
add_to_sga "4 II 1.3.1" "more general" CategoryTheory.Pretopology.gi
add_to_sga "4 II 1.3.1" "special case" CategoryTheory.Pretopology.toGrothendieck
add_to_sga "4 II 1.4" "special case" CategoryTheory.Pretopology.toGrothendieck_toCoverage
add_to_sga "4 II 2.1" CategoryTheory.Presheaf.IsSheaf'
add_to_sga "4 II 2.1" "partial" CategoryTheory.Presieve.IsSeparatedFor
add_to_sga "4 II 2.1" CategoryTheory.Presieve.IsSheaf
add_to_sga "4 II 2.1" "partial" CategoryTheory.Presieve.IsSheafFor
add_to_sga "4 II 2.1" CategoryTheory.Sheaf
add_to_sga "4 II 2.2" "partial, special case" CategoryTheory.Sheaf.canonicalTopology
add_to_sga "4 II 2.2" CategoryTheory.Sheaf.finestTopology
add_to_sga "4 II 2.2" "partial, special case" CategoryTheory.Sheaf.finestTopologySingle
add_to_sga "4 II 2.2" "partial" CategoryTheory.Sheaf.le_finestTopology
add_to_sga "4 II 2.2" "partial" CategoryTheory.Sheaf.mem_finestTopology_of_forall_isSheafFor
add_to_sga "4 II 2.2" "partial" CategoryTheory.Sheaf.sheaf_for_finestTopology
add_to_sga "4 II 2.3" "more general" CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff
add_to_sga "4 II 2.3" "special case" CategoryTheory.Presheaf.isSheaf_iff_isLimit_pretopology
add_to_sga "4 II 2.3" "partial" CategoryTheory.Presieve.IsSheaf.isSheafFor_of_mem_precoverage
add_to_sga "4 II 2.3" "more general" CategoryTheory.Presieve.isSheaf_coverage
add_to_sga "4 II 2.3" "special case" CategoryTheory.Presieve.isSheaf_pretopology
add_to_sga "4 II 2.4" "local clause" CategoryTheory.Equalizer.Presieve.Arrows.sheaf_condition
add_to_sga "4 II 2.4" "partial" CategoryTheory.Equalizer.Presieve.isSheafFor_singleton_iff
add_to_sga "4 II 2.4" "partial" CategoryTheory.Equalizer.Presieve.sheaf_condition
add_to_sga "4 II 2.4" "partial" CategoryTheory.Presieve.isSheaf_pretopology
add_to_sga "4 II 2.5" CategoryTheory.GrothendieckTopology.Cover
add_to_sga "4 II 2.5" "more general"
  CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
add_to_sga "4 II 2.5" "partial"
  CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
add_to_sga "4 II 2.5" CategoryTheory.GrothendieckTopology.toCoverage
add_to_sga "4 II 2.5" CategoryTheory.Sheaf.canonicalTopology
add_to_sga "4 II 2.5" "partial" CategoryTheory.Sheaf.isSheaf_of_isRepresentable
add_to_sga "4 II 2.5" "partial" CategoryTheory.Sheaf.isSheaf_yoneda_obj
add_to_sga "4 II 2.5" "more general" CategoryTheory.Sheaf.le_finestTopology
add_to_sga "4 II 2.5" "more general" CategoryTheory.Sheaf.sheaf_for_finestTopology
add_to_sga "4 II 2.5.1" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "4 II 2.5.1" "partial"
  CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
add_to_sga "4 II 2.5.1" "partial"
  CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
add_to_sga "4 II 2.5.1" "special case" CategoryTheory.Sheaf.isSheaf_of_isRepresentable
add_to_sga "4 II 2.5.1" "special case" CategoryTheory.Sheaf.isSheaf_yoneda_obj
add_to_sga "4 II 2.5.1" "partial" CategoryTheory.Sheaf.le_finestTopology
add_to_sga "4 II 2.7" CategoryTheory.Presheaf.IsSeparated
add_to_sga "4 II 2.7" CategoryTheory.Presieve.IsSheaf
add_to_sga "4 II 2.7" "more general" CategoryTheory.Presieve.isSheafFor_comp_uliftFunctor_iff
add_to_sga "4 II 2.7" "more general" CategoryTheory.Presieve.isSheafFor_iff_of_nat_equiv
add_to_sga "4 II 2.7" "forward implication" CategoryTheory.Presieve.isSheaf_comp_uliftFunctor
add_to_sga "4 II 2.7" "more general" CategoryTheory.Presieve.isSheaf_comp_uliftFunctor_iff
add_to_sga "4 II 2.7" CategoryTheory.Sheaf.canonicalTopology
add_to_sga "4 II 3.0.2" CategoryTheory.SmallCategory
add_to_sga "4 II 3.0.5" "nonemptiness of J(X)"
  CategoryTheory.GrothendieckTopology.Cover.instOrderTop
add_to_sga "4 II 3.0.5" "partial" CategoryTheory.GrothendieckTopology.Cover.instSemilatticeInf
add_to_sga "4 II 3.0.5" CategoryTheory.GrothendieckTopology.Plus.mk
add_to_sga "4 II 3.0.5" "more general"
  CategoryTheory.GrothendieckTopology.Plus.res_mk_eq_mk_pullback
add_to_sga "4 II 3.0.5" "(X)" CategoryTheory.GrothendieckTopology.Plus.toPlus_eq_mk
add_to_sga "4 II 3.0.5" "(X)" CategoryTheory.GrothendieckTopology.Plus.toPlus_mk
add_to_sga "4 II 3.0.5" CategoryTheory.GrothendieckTopology.plusFunctor
add_to_sga "4 II 3.0.5" "partial" CategoryTheory.GrothendieckTopology.plusMap_id
add_to_sga "4 II 3.0.5" CategoryTheory.GrothendieckTopology.plusObj
add_to_sga "4 II 3.0.5" CategoryTheory.GrothendieckTopology.toPlus
add_to_sga "4 II 3.1" "more general" CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists
add_to_sga "4 II 3.1" "more general" CategoryTheory.GrothendieckTopology.Plus.exists_rep
add_to_sga "4 II 3.1" "more general" CategoryTheory.GrothendieckTopology.Plus.toPlus_apply
add_to_sga "4 II 3.2" "clause 3" CategoryTheory.GrothendieckTopology.Plus.exists_of_sep
add_to_sga "4 II 3.2" "clause 3, special case"
  CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus
add_to_sga "4 II 3.2" "clause 4, (ii) ⇒ (i)" CategoryTheory.GrothendieckTopology.isoToPlus
add_to_sga "4 II 3.2" CategoryTheory.GrothendieckTopology.plusFunctor
add_to_sga "4 II 3.2" CategoryTheory.GrothendieckTopology.plusObj
add_to_sga "4 II 3.2" "more general"
  CategoryTheory.GrothendieckTopology.preserveFiniteLimits_plusFunctor
add_to_sga "4 II 3.2" "more general"
  CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_plusFunctor
add_to_sga "4 II 3.2" CategoryTheory.GrothendieckTopology.toPlus
add_to_sga "4 II 3.2" CategoryTheory.IsIso
add_to_sga "4 II 3.2" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 II 3.2" CategoryTheory.Presheaf.IsSeparated
add_to_sga "4 II 3.2" CategoryTheory.leftExactFunctor
add_to_sga "4 II 3.4" "more general"
  CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification
add_to_sga "4 II 3.4" "more general"
  CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
add_to_sga "4 II 3.4" "more general" CategoryTheory.plusPlusFunctorIsoSheafification
add_to_sga "4 II 3.4" "partial" CategoryTheory.plusPlusIsoSheafify
add_to_sga "4 II 3.4" "more general" CategoryTheory.plusPlusSheafIsoPresheafToSheaf
add_to_sga "4 II 3.4" "more general" CategoryTheory.preservesFiniteLimits_presheafToSheaf
add_to_sga "4 II 3.4" "more general" CategoryTheory.sheafToPresheaf_isRightAdjoint
add_to_sga "4 II 3.4" "more general" CategoryTheory.toSheafify_plusPlusIsoSheafify_hom
add_to_sga "4 II 3.4" "more general" CategoryTheory.toSheafify_plusPlusIsoSheafify_hom_assoc
add_to_sga "4 II 3.5" CategoryTheory.presheafToSheaf
add_to_sga "4 II 3.5" CategoryTheory.sheafification
add_to_sga "4 II 3.5" CategoryTheory.sheafify
add_to_sga "4 II 3.6" "more general"
  CategoryTheory.GrothendieckTopology.instIsIsoSheafAppFunctorOppositeSheafComposeNatTransPlusPlusAdjunction
add_to_sga "4 II 3.6" "partial" CategoryTheory.GrothendieckTopology.sheafifyCompIso
add_to_sga "4 II 4.1" "more general" CategoryTheory.Sheaf.createsLimitsOfShape
add_to_sga "4 II 4.1" "special case" CategoryTheory.Sheaf.hasFilteredColimitsOfSize
add_to_sga "4 II 4.1" "partial" CategoryTheory.Sheaf.instHasColimitsOfShape
add_to_sga "4 II 4.1" "partial" CategoryTheory.Sheaf.instHasColimitsOfSize
add_to_sga "4 II 4.1" "special case" CategoryTheory.Sheaf.instHasFiniteColimits
add_to_sga "4 II 4.1" "special case" CategoryTheory.Sheaf.instHasFiniteLimits
add_to_sga "4 II 4.1" "more general" CategoryTheory.Sheaf.instHasLimitsOfShape
add_to_sga "4 II 4.1" "partial"
  CategoryTheory.Sheaf.instIsClosedUnderLimitsOfShapeFunctorOppositeIsSheaf
add_to_sga "4 II 4.1" "partial" CategoryTheory.Sheaf.isColimitSheafifyCocone
add_to_sga "4 II 4.1" "partial"
  CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
add_to_sga "4 II 4.1" "partial" CategoryTheory.preservesFiniteLimits_presheafToSheaf
add_to_sga "4 II 4.1" "partial" CategoryTheory.preservesLimitsOfShape_presheafToSheaf
add_to_sga "4 II 4.1" "Clause 3, special case"
  TopCat.instCreatesLimitsOfShapeSheafPresheafForgetOfHasLimitsOfShape
add_to_sga "4 II 4.1" "Clause 3, special case"
  TopCat.instCreatesLimitsSheafPresheafForgetOfHasLimits
add_to_sga "4 II 4.1" "Clause 3, special case" TopCat.instHasLimitsOfShapeSheaf
add_to_sga "4 II 4.1" "Clause 3, special case" TopCat.instHasLimitsOfSizeSheafOfHasLimits
add_to_sga "4 II 4.1" "Clause 3, special case" TopCat.isSheaf_of_isLimit
add_to_sga "4 II 4.1" "Clause 3, special case" TopCat.limit_isSheaf
add_to_sga "4 II 4.3" "special case" CategoryTheory.Limits.filtered_colim_preservesFiniteLimits
add_to_sga "4 II 4.3" "more general" CategoryTheory.Sheaf.ab5ofSize
add_to_sga "4 II 4.3" "more general" CategoryTheory.Sheaf.hasExactColimitsOfShape
add_to_sga "4 II 4.3.1" "more general" CategoryTheory.isIso_of_mono_of_strongEpi
add_to_sga "4 II 4.3.1" "more general" CategoryTheory.isIso_of_regularEpi_of_mono
add_to_sga "4 II 4.4.0" "faithfulness"
  CategoryTheory.GrothendieckTopology.instFaithfulSheafTypeYoneda
add_to_sga "4 II 4.4.0" "fullness" CategoryTheory.GrothendieckTopology.instFullSheafTypeYoneda
add_to_sga "4 II 4.4.0" "partial, special case"
  CategoryTheory.GrothendieckTopology.preservesLimitsOfSize_yoneda
add_to_sga "4 II 4.4.0" CategoryTheory.GrothendieckTopology.yoneda
add_to_sga "4 II 4.4.4" CategoryTheory.Sheaf.finestTopology
add_to_sga "4 II 4.5" "special case" CategoryTheory.Limits.BinaryCoproductDisjoint
add_to_sga "4 II 4.5" CategoryTheory.Limits.CoproductDisjoint
add_to_sga "4 II 4.5" "Strict initial object" CategoryTheory.Limits.HasStrictInitialObjects
add_to_sga "4 II 4.5" CategoryTheory.Limits.IsInitial
add_to_sga "4 II 4.5" "partial" CategoryTheory.Limits.IsInitial.ofUnique
add_to_sga "4 II 4.5" "partial" CategoryTheory.Limits.IsInitial.ofUniqueHom
add_to_sga "4 II 4.5" CategoryTheory.Limits.isInitialEquivUnique
add_to_sga "4 II 4.6" "Part 2), special case"
  CategoryTheory.GrothendieckTopology.isColimitCofanMkYoneda
add_to_sga "4 II 4.6" "more general" CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono
add_to_sga "4 II 4.6" "more general" CategoryTheory.MorphismProperty.diagonal_isomorphisms
add_to_sga "4 II 4.6.1" "Clause 1" CategoryTheory.Sheaf.isTerminalOfBotCover
add_to_sga "4 II 4.6.2" "partial" CategoryTheory.Presieve.isTerminal_of_isSheafFor_empty_presieve
add_to_sga "4 II 4.6.2" "partial" CategoryTheory.Sheaf.isTerminalOfBotCover
add_to_sga "4 II 4.6.3" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "4 II 4.6.3" CategoryTheory.Limits.CoproductDisjoint
add_to_sga "4 II 4.8" CategoryTheory.EffectiveEquivalenceRelation
add_to_sga "4 II 4.8" CategoryTheory.IsEffectiveEquivalenceRelation
add_to_sga "4 II 4.8" CategoryTheory.IsUniversallyEffectiveEquivalenceRelation
add_to_sga "4 II 4.8" CategoryTheory.Limits.CoproductDisjoint
add_to_sga "4 II 4.8" CategoryTheory.Limits.CoproductsOfShapeDisjoint
add_to_sga "4 II 4.8" CategoryTheory.Limits.HasCoproduct
add_to_sga "4 II 4.8" CategoryTheory.Limits.HasCoproducts
add_to_sga "4 II 4.8" CategoryTheory.Limits.HasCoproductsOfShape
add_to_sga "4 II 4.8" CategoryTheory.Limits.HasFiniteLimits
add_to_sga "4 II 4.8" "more general" CategoryTheory.Sheaf.instHasColimitsOfShape
add_to_sga "4 II 4.8" "more general" CategoryTheory.Sheaf.instHasColimitsOfSize
add_to_sga "4 II 4.8" "b), special case" CategoryTheory.Sheaf.instHasFiniteColimits
add_to_sga "4 II 4.8" "b), special case" CategoryTheory.Sheaf.instHasFiniteCoproducts
add_to_sga "4 II 4.8" "more general" CategoryTheory.Sheaf.instHasFiniteLimits
add_to_sga "4 II 4.8" "a), special case" CategoryTheory.Sheaf.instHasFiniteProducts
add_to_sga "4 II 4.8" "more general" CategoryTheory.Sheaf.instHasLimitsOfShape
add_to_sga "4 II 4.8" CategoryTheory.UniversallyEffectiveEquivalenceRelation
add_to_sga "4 II 4.8" "Clause a), special case" TopCat.instHasLimitsOfShapeSheaf
add_to_sga "4 II 4.8" "Clause a), special case" TopCat.instHasLimitsOfSizeSheafOfHasLimits
add_to_sga "4 II 4.8" "Clause a), special case" instHasFiniteLimitsCondensed
add_to_sga "4 II 5.1" "special case" CategoryTheory.Sheaf.epi_of_isLocallySurjective
add_to_sga "4 II 5.1" "special case" CategoryTheory.Sheaf.epi_of_isLocallySurjective'
add_to_sga "4 II 5.1" "special case" CategoryTheory.Sheaf.isLocallySurjective_iff_epi
add_to_sga "4 II 5.3.1" "special case" CategoryTheory.Sheaf.isColimitSheafifyCocone
add_to_sga "4 II 5.4" "special case" CategoryTheory.typesGrothendieckTopology_eq_canonical
add_to_sga "4 II 5.5.0" CategoryTheory.GrothendieckTopology
add_to_sga "4 II 5.5.0" "Caf membership" CategoryTheory.Reflective
add_to_sga "4 II 5.5.0" CategoryTheory.Sheaf
add_to_sga "4 II 5.5.0" "Membership Φ(J) ∈ Caf" CategoryTheory.instHasSheafifyType
add_to_sga "4 II 5.5.0" "Caf membership" CategoryTheory.leftExactFunctor
add_to_sga "4 II 5.5.0" CategoryTheory.sheafToPresheaf
add_to_sga "4 II 6.0" CategoryTheory.Functor
add_to_sga "4 II 6.1" "special case" CategoryTheory.Presieve.IsSheaf
add_to_sga "4 II 6.1" CategoryTheory.Sheaf
add_to_sga "4 II 6.2" "partial" CategoryTheory.Presheaf.IsSheaf.isLimitMultifork
add_to_sga "4 II 6.2" "partial" CategoryTheory.Presheaf.IsSheaf.isSheafFor
add_to_sga "4 II 6.2" "partial" CategoryTheory.Presheaf.isLimitOfIsSheaf
add_to_sga "4 II 6.2" "more general" CategoryTheory.Presheaf.isLimit_iff_isSheafFor
add_to_sga "4 II 6.2" "more general" CategoryTheory.Presheaf.isLimit_iff_isSheafFor_presieve
add_to_sga "4 II 6.2" "more general" CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf
add_to_sga "4 II 6.2" CategoryTheory.Presheaf.isSheaf_iff_isLimit
add_to_sga "4 II 6.2" "more general" CategoryTheory.Presheaf.isSheaf_iff_isLimit_coverage
add_to_sga "4 II 6.2" "special case" CategoryTheory.Presheaf.isSheaf_iff_isLimit_pretopology
add_to_sga "4 II 6.2" "special case" CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget
add_to_sga "4 II 6.2" CategoryTheory.Presheaf.isSheaf_iff_multifork
add_to_sga "4 II 6.2" "more general" CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
add_to_sga "4 II 6.2" CategoryTheory.isSheaf_iff_isSheaf_of_type
add_to_sga "4 II 6.2" "special case" TopCat.Presheaf.IsSheaf.isSheafOpensLeCover
add_to_sga "4 II 6.3.0" "special case" CategoryTheory.Grp
add_to_sga "4 II 6.3.0" "special case" CategoryTheory.Mon
add_to_sga "4 II 6.3.0" "partial" CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf
add_to_sga "4 II 6.3.0" "partial" CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget
add_to_sga "4 II 6.3.0" CategoryTheory.forget
add_to_sga "4 II 6.3.0" "partial" CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
add_to_sga "4 II 6.3.0" CategoryTheory.sheafCompose
add_to_sga "4 II 6.3.2" CategoryTheory.Sheaf
add_to_sga "4 II 6.3.3" "more general"
  CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification
add_to_sga "4 II 6.3.3" CategoryTheory.Sheaf
add_to_sga "4 II 6.3.3" "more general"
  CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
add_to_sga "4 II 6.3.3" "special case" CategoryTheory.instHasSheafifyType
add_to_sga "4 II 6.3.3" "more general" CategoryTheory.preservesFiniteLimits_presheafToSheaf
add_to_sga "4 II 6.4" "left exactness of a_γ"
  CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification
add_to_sga "4 II 6.4" "more general"
  CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
add_to_sga "4 II 6.4" "left exactness of a_γ" CategoryTheory.preservesFiniteLimits_presheafToSheaf
add_to_sga "4 II 6.5" "special case" AddCommGrpCat.adj
add_to_sga "4 II 6.5" "special case" AddCommGrpCat.instIsRightAdjointForgetAddMonoidHomCarrier
add_to_sga "4 II 6.5" "special case" AddMonCat.adj
add_to_sga "4 II 6.5" CategoryTheory.Adjunction
add_to_sga "4 II 6.5" "special case" CommMonCat.instIsRightAdjointForgetMonoidHomCarrier
add_to_sga "4 II 6.5" "special case" Condensed.freeForgetAdjunction
add_to_sga "4 II 6.5" "special case" Condensed.setAbAdjunction
add_to_sga "4 II 6.5" "special case" GrpCat.adj
add_to_sga "4 II 6.5" "special case" GrpCat.instIsRightAdjointForgetMonoidHomCarrier
add_to_sga "4 II 6.5" "special case" MonCat.instIsRightAdjointForgetMonoidHomCarrier
add_to_sga "4 II 6.5" "special case" PresheafOfModules.freeAdjunction
add_to_sga "4 II 6.7" "special case" AlgebraicGeometry.Scheme.Modules.instAbelian
add_to_sga "4 II 6.7" "special case" AlgebraicGeometry.Scheme.PresheafOfModules
add_to_sga "4 II 6.7" "AB5, small constant ring" CategoryTheory.Sheaf.ab5ofSize
add_to_sga "4 II 6.7" "special case" CategoryTheory.Sheaf.instIsGrothendieckAbelian
add_to_sga "4 II 6.7" "special case" PresheafOfModules.instAbelian
add_to_sga "4 II 6.7" "special case" PresheafOfModules.instIsGrothendieckAbelian
add_to_sga "4 II 6.7" "special case" TopCat.Sheaf.instAbelian
add_to_sga "4 II 6.8" "special case" CategoryTheory.Sheaf.freeYoneda
add_to_sga "4 II 6.9" "Remark 6.9, special case" AddCommGrpCat.enoughInjectives
add_to_sga "4 II 6.9" CategoryTheory.AB4Star
add_to_sga "4 II 6.9" CategoryTheory.AB4StarOfSize
add_to_sga "4 II 6.9" "Remark 6.9, special case" CommGrpCat.enoughInjectives
add_to_sga "4 II 6.9" "Remark 6.9, special case" ModuleCat.enoughInjectives
add_to_sga "4 II 6.9" "Remark 6.9, special case" instEnoughInjectivesModuleCatInt
add_to_sga "4 II 6.9" "Remark 6.9, special case" instEnoughInjectivesModuleCatOfSmall
add_to_sga "4 III 1.1" CategoryTheory.Functor.IsContinuous
add_to_sga "4 III 1.3" "clause 1), special case"
  CategoryTheory.Adjunction.sheafPushforwardContinuous
add_to_sga "4 III 1.3" "clause 5)"
  CategoryTheory.Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
add_to_sga "4 III 1.3" "more general"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
add_to_sga "4 III 1.4" "Upper square"
  CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeUliftYonedaUliftYonedaMap
add_to_sga "4 III 1.4" "Upper square"
  CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeYonedaYonedaMap
add_to_sga "4 III 1.6" CategoryTheory.CoverPreserving.of_isContinuous
add_to_sga "4 III 1.6" "i ⇔ ii" CategoryTheory.Functor.isContinuous_iff_coverPreserving
add_to_sga "4 III 1.6" "partial" CategoryTheory.Functor.isContinuous_of_coverPreserving
add_to_sga "4 III 1.6" "iii ⇒ i, partial"
  CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
add_to_sga "4 III 1.7" "special case" TopCat.Sheaf.instIsLeftAdjointPullback
add_to_sga "4 III 1.7" "(2), special case" instHasColimitsCommAlgCat
add_to_sga "4 III 1.9.1" Opens.grothendieckTopology
add_to_sga "4 III 1.9.1" "partial" TopCat.Presheaf.coveringOfPresieve.iSup_eq_of_mem_grothendieck
add_to_sga "4 III 1.9.1" "partial" TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover
add_to_sga "4 III 1.9.1" "partial" TopCat.Presheaf.presieveOfCovering.mem_grothendieckTopology
add_to_sga "4 III 1.9.1" TopCat.Sheaf.pullback
add_to_sga "4 III 1.9.1" "partial" TopCat.Sheaf.pullbackIso
add_to_sga "4 III 1.9.1" TopCat.Sheaf.pushforward
add_to_sga "4 III 1.9.1" TopologicalSpace.Opens
add_to_sga "4 III 1.9.1" TopologicalSpace.Opens.map
add_to_sga "4 III 1.9.1" "object formula of f^{-1}" TopologicalSpace.Opens.map_coe
add_to_sga "4 III 1.9.1" "object formula of f^{-1}" TopologicalSpace.Opens.mem_map
add_to_sga "4 III 1.9.1" "continuity of f^{-1}" instIsContinuousOpensCarrierMapGrothendieckTopology
add_to_sga "4 III 1.9.2" "partial" IsOpen.isOpenMap_inclusion
add_to_sga "4 III 1.9.2" "partial" IsOpen.isOpenMap_subtype_val
add_to_sga "4 III 1.9.2" "more general" TopologicalSpace.Opens.sheafRestrict
add_to_sga "4 III 1.9.2" "more general" Topology.IsOpenEmbedding.functor
add_to_sga "4 III 1.11" CategoryTheory.Functor.IsContinuous
add_to_sga "4 III 1.11" CategoryTheory.Functor.sheafPushforwardContinuousCompSheafToPresheafIso
add_to_sga "4 III 2.2" "Forward implication"
  CategoryTheory.RanIsSheafOfIsCocontinuous.isLimitMultifork
add_to_sga "4 III 2.2" "Forward implication" CategoryTheory.ran_isSheaf_of_isCocontinuous
add_to_sga "4 III 2.3" "clause 2, special case"
  CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility
add_to_sga "4 III 2.3" "clause 3, special case" CategoryTheory.Functor.sheafAdjunctionCocontinuous
add_to_sga "4 III 2.3" CategoryTheory.Functor.sheafPushforwardCocontinuous
add_to_sga "4 III 2.5" "(ii) ⇒ (i)" CategoryTheory.Adjunction.isContinuous_of_isCocontinuous
add_to_sga "4 III 2.5" "(ii) ⇒ (i)" CategoryTheory.instIsContinuousRightAdjointOfIsCocontinuous
add_to_sga "4 III 2.6" "more general" CategoryTheory.Adjunction.Triple.fullyFaithfulEquiv
add_to_sga "4 III 2.6" CategoryTheory.Functor.sheafAdjunctionCocontinuous
add_to_sga "4 III 2.6" "partial"
  CategoryTheory.Functor.sheafPullbackConstruction.instIsRightAdjointSheafSheafPushforwardContinuousOfHasWeakSheafify
add_to_sga "4 III 2.6" CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
add_to_sga "4 III 2.7" "more general" CategoryTheory.Functor.sheafAdjunctionCocontinuous
add_to_sga "4 III 2.7" "more general" IsOpenMap.adjunction
add_to_sga "4 III 2.7" "(i^{-1})^s ≅ Φ_s" Topology.IsOpenEmbedding.sheafPullbackIso
add_to_sga "4 III 3.1" CategoryTheory.Functor.inducedTopology
add_to_sga "4 III 3.1" "partial" CategoryTheory.Functor.instIsContinuousInducedTopology
add_to_sga "4 III 3.1" "more general" CategoryTheory.Functor.le_inducedTopology_iff
add_to_sga "4 III 3.2" CategoryTheory.Functor.mem_inducedTopology_iff
add_to_sga "4 III 4.1" "i) ⇒ ii)" CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom
add_to_sga "4 III 4.1" "more general" CategoryTheory.Functor.sheafInducedTopologyEquivOfIsCoverDense
add_to_sga "4 III 4.1" "special case" CategoryTheory.coherentTopology.equivalence
add_to_sga "4 III 4.1" "special case" CategoryTheory.coherentTopology.equivalence'
add_to_sga "4 III 4.1.1" CategoryTheory.Comma
add_to_sga "4 III 4.1.1" "second step"
  CategoryTheory.Functor.IsCoverDense.functorPullback_pushforward_covering
add_to_sga "4 III 4.1.1" "more general" CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom
add_to_sga "4 III 4.1.1" "partial" CategoryTheory.Functor.IsCoverDense.sheafHom_restrict_eq
add_to_sga "4 III 4.1.1" "more general" CategoryTheory.Functor.IsDenseSubsite.instIsCocontinuous
add_to_sga "4 III 4.1.1" "First step of 4.1.1"
  CategoryTheory.Functor.whiskerLeft_obj_map_bijective_of_isCoverDense
add_to_sga "4 III 4.4" "more general" CategoryTheory.Functor.IsDenseSubsite.instIsCocontinuous
add_to_sga "4 III 4.4" "more general" CategoryTheory.Functor.instIsCocontinuousRestrictedTopology
add_to_sga "4 III 4.4" "special case" CategoryTheory.Functor.sheafAdjunctionCocontinuous
add_to_sga "4 III 5.1" "special case" CategoryTheory.GrothendieckTopology.over
add_to_sga "4 III 5.1" "special case" CategoryTheory.Sieve.overEquiv
add_to_sga "4 III 5.3" CategoryTheory.Sheaf.over
add_to_sga "4 III 5.3" "special case" TopologicalSpace.Opens.sheafRestrict
add_to_sga "4 III 5.5" "Clause 1"
  CategoryTheory.CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow
add_to_sga "4 III 5.5" CategoryTheory.OverPresheafAux.toOverYonedaCompRestrictedYoneda
add_to_sga "4 III 5.5" CategoryTheory.presheafToSheaf
add_to_sga "4 III 5.5" CategoryTheory.sheafToPresheaf
