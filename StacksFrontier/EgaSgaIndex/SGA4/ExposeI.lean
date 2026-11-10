module  -- shake: keep-all

import Mathlib.Algebra.Category.AlgCat.FilteredColimits
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.MonCat.Adjunctions
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Indization
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Generator.Abelian
import Mathlib.CategoryTheory.Generator.Indization
import Mathlib.CategoryTheory.Groupoid.Subgroupoid
import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.CategoryTheory.Limits.Elements
import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits
import Mathlib.CategoryTheory.Limits.Indization.Products
import Mathlib.CategoryTheory.Limits.Preserves.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
import Mathlib.CategoryTheory.Monoidal.Cartesian.ShrinkYoneda
import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Presentable.SharplyLT.Basic
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.Order.Birkhoff
import Mathlib.Order.Ideal
import Mathlib.Order.KonigLemma
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.SetTheory.ZFC.Class
import Mathlib.Topology.Sheaves.Limits
import Std.Data.Iterators.Lemmas.Equivalence.HetT
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 4, Exposé I: references registered by name

The `add_to_sga` registrations of `StacksFrontier.EgaSgaIndex.SGA4` for Exposé I
of SGA 4, in the order of that file. See its module docstring.
-/

add_to_sga "4 I 1.0" Small
add_to_sga "4 I 1.0" Std.Internal.Small
add_to_sga "4 I 1.1" CategoryTheory.LocallySmall
add_to_sga "4 I 1.1.1" CategoryTheory.Cat.Hom.instCategory
add_to_sga "4 I 1.1.1" CategoryTheory.Cat.exp
add_to_sga "4 I 1.1.1" CategoryTheory.Functor
add_to_sga "4 I 1.1.1" "b), special case" CategoryTheory.instLocallySmallFunctor
add_to_sga "4 I 1.1.1" "a)" CategoryTheory.instSmallFunctorOfLocallySmall
add_to_sga "4 I 1.2" "more general" CategoryTheory.Functor
add_to_sga "4 I 1.3" CategoryTheory.Category.opposite
add_to_sga "4 I 1.3" "partial" CategoryTheory.CategoryStruct.opposite
add_to_sga "4 I 1.3" "(a), special case" CategoryTheory.Functor.hom
add_to_sga "4 I 1.3" CategoryTheory.shrinkYoneda
add_to_sga "4 I 1.3" "special case" CategoryTheory.shrinkYonedaGrp
add_to_sga "4 I 1.3" "special case" CategoryTheory.shrinkYonedaGrpObjObjEquiv
add_to_sga "4 I 1.3" "special case" CategoryTheory.shrinkYonedaMon
add_to_sga "4 I 1.3" "special case" CategoryTheory.shrinkYonedaMonObjObjEquiv
add_to_sga "4 I 1.3" "chosen bijection φ(y,x)" CategoryTheory.shrinkYonedaObjObjEquiv
add_to_sga "4 I 1.3" "partial" CategoryTheory.shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
add_to_sga "4 I 1.3" "special case" CategoryTheory.uliftYoneda_obj_map
add_to_sga "4 I 1.3" "(a), special case" CategoryTheory.yoneda
add_to_sga "4 I 1.3" "(b)" Shrink
add_to_sga "4 I 1.3.1" CategoryTheory.yoneda
add_to_sga "4 I 1.3.2" "more general" CategoryTheory.Functor.FullyFaithful.whiskeringRight
add_to_sga "4 I 1.3.2" CategoryTheory.Functor.whiskeringRight
add_to_sga "4 I 1.3.2" "partial" CategoryTheory.shrinkCoyonedaUliftFunctorIso
add_to_sga "4 I 1.3.2" "partial" CategoryTheory.uliftYonedaIsoShrinkYoneda
add_to_sga "4 I 1.3.3" CategoryTheory.yoneda
add_to_sga "4 I 1.4" CategoryTheory.ULiftYoneda.fullyFaithful
add_to_sga "4 I 1.4" "faithfulness"
  CategoryTheory.ULiftYoneda.instFaithfulFunctorOppositeTypeUliftYoneda
add_to_sga "4 I 1.4" CategoryTheory.Yoneda.fullyFaithful
add_to_sga "4 I 1.4" "faithfulness" CategoryTheory.Yoneda.yoneda_faithful
add_to_sga "4 I 1.4" "fullness" CategoryTheory.Yoneda.yoneda_full
add_to_sga "4 I 1.4" "naturality in X" CategoryTheory.map_yonedaEquiv
add_to_sga "4 I 1.4" "naturality in X" CategoryTheory.map_yonedaEquiv'
add_to_sga "4 I 1.4" CategoryTheory.shrinkYonedaEquiv_shrinkYoneda_map
add_to_sga "4 I 1.4" "bijection" CategoryTheory.uliftYonedaEquiv
add_to_sga "4 I 1.4" CategoryTheory.uliftYonedaEquiv_uliftYoneda_map
add_to_sga "4 I 1.4" "bijection Hom(h(X)" CategoryTheory.yonedaEquiv
add_to_sga "4 I 1.4" "naturality in X" CategoryTheory.yonedaEquiv_naturality
add_to_sga "4 I 1.4" "naturality in X" CategoryTheory.yonedaEquiv_symm_naturality_left
add_to_sga "4 I 1.4" CategoryTheory.yonedaEquiv_yoneda_map
add_to_sga "4 I 1.4" CategoryTheory.yonedaLemma
add_to_sga "4 I 1.4" "partial" CategoryTheory.yonedaOpCompYonedaObj
add_to_sga "4 I 1.4.1" CategoryTheory.Functor.IsRepresentable
add_to_sga "4 I 1.4.1" "witnessing data" CategoryTheory.Functor.RepresentableBy
add_to_sga "4 I 1.4.1" "more general" CategoryTheory.Functor.essImage
add_to_sga "4 I 1.4.1" CategoryTheory.yoneda
add_to_sga "4 I 1.4.2" "more general" CategoryTheory.Functor.corepresentableByUliftFunctorEquiv
add_to_sga "4 I 1.4.2" "partial" CategoryTheory.Functor.instIsCorepresentableCompUliftFunctor
add_to_sga "4 I 1.4.2" "partial" CategoryTheory.Functor.instIsRepresentableCompOppositeUliftFunctor
add_to_sga "4 I 1.4.2" "more general" CategoryTheory.Functor.isCorepresentable_comp_uliftFunctor_iff
add_to_sga "4 I 1.4.2" CategoryTheory.Functor.isRepresentable_comp_uliftFunctor_iff
add_to_sga "4 I 1.4.2" "more general" CategoryTheory.Functor.representableByUliftFunctorEquiv
add_to_sga "4 I 2.1" "partial" CategoryTheory.Limits.Cone
add_to_sga "4 I 2.1" CategoryTheory.Limits.IsLimit
add_to_sga "4 I 2.1" "partial" CategoryTheory.Limits.IsLimit.OfNatIso.limitCone
add_to_sga "4 I 2.1" CategoryTheory.Limits.IsLimit.ofRepresentableBy
add_to_sga "4 I 2.1" CategoryTheory.Limits.IsLimit.representableBy
add_to_sga "4 I 2.1" CategoryTheory.Limits.limit
add_to_sga "4 I 2.1" "partial" CategoryTheory.Limits.limit.cone
add_to_sga "4 I 2.1" "partial" CategoryTheory.Limits.limit.isLimit
add_to_sga "4 I 2.1" "partial" CategoryTheory.Limits.limit.isoLimitCone
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.HasCoequalizer
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.HasCoequalizers
add_to_sga "4 I 2.1.1" "special case" CategoryTheory.Limits.HasCokernel
add_to_sga "4 I 2.1.1" "special case" CategoryTheory.Limits.HasCokernels
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.HasCoproduct
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.HasCoproducts
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.HasCoproductsOfShape
add_to_sga "4 I 2.1.1" "special case" CategoryTheory.Limits.HasFiniteCoproducts
add_to_sga "4 I 2.1.1" "special case" CategoryTheory.Limits.HasKernel
add_to_sga "4 I 2.1.1" "special case" CategoryTheory.Limits.HasKernels
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.HasProduct
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.HasProducts
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.HasProductsOfShape
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.coequalizer
add_to_sga "4 I 2.1.1" "special case" CategoryTheory.Limits.cokernel
add_to_sga "4 I 2.1.1" "special case" CategoryTheory.Limits.coprod
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.equalizer
add_to_sga "4 I 2.1.1" "special case" CategoryTheory.Limits.kernel
add_to_sga "4 I 2.1.1" "special case" CategoryTheory.Limits.kernelIsKernel
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.productIsProduct
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.pullback
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.pushout
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.pushout.cocone
add_to_sga "4 I 2.1.1" CategoryTheory.Limits.sigmaObj
add_to_sga "4 I 2.1.1" "more general" CategoryTheory.Limits.wideCoequalizer
add_to_sga "4 I 2.2" CategoryTheory.Limits.HasLimit
add_to_sga "4 I 2.2.1" "special case" CategoryTheory.Limits.HasLimits
add_to_sga "4 I 2.2.1" CategoryTheory.Limits.HasLimitsOfShape
add_to_sga "4 I 2.2.1" CategoryTheory.Limits.HasLimitsOfSize
add_to_sga "4 I 2.3" CategoryTheory.Limits.HasEqualizers
add_to_sga "4 I 2.3" CategoryTheory.Limits.HasLimits
add_to_sga "4 I 2.3" CategoryTheory.Limits.HasLimitsOfSize
add_to_sga "4 I 2.3" CategoryTheory.Limits.HasProducts
add_to_sga "4 I 2.3" CategoryTheory.Limits.HasPullbacks
add_to_sga "4 I 2.3" "iii⇒ii: kernels of pairs"
  CategoryTheory.Limits.hasEqualizers_of_hasPullbacks_and_binary_products
add_to_sga "4 I 2.3" "special case"
  CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products
add_to_sga "4 I 2.3" "special case"
  CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks
add_to_sga "4 I 2.3" "special case" CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits
add_to_sga "4 I 2.3" "ii⇒i, diagramwise" CategoryTheory.Limits.hasLimit_of_equalizer_and_product
add_to_sga "4 I 2.3" "ii⇒iii: fiber products"
  CategoryTheory.Limits.hasPullbacks_of_hasBinaryProducts_of_hasEqualizers
add_to_sga "4 I 2.3" "ii⇒i" CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products
add_to_sga "4 I 2.3.1" CategoryTheory.Limits.HasColimit
add_to_sga "4 I 2.3.1" CategoryTheory.Limits.HasColimits
add_to_sga "4 I 2.3.1" CategoryTheory.Limits.HasColimitsOfSize
add_to_sga "4 I 2.3.1" CategoryTheory.Limits.HasFiniteColimits
add_to_sga "4 I 2.3.1" CategoryTheory.Limits.HasFiniteLimits
add_to_sga "4 I 2.3.1" "(iii)⇒(ii)"
  CategoryTheory.Limits.hasCoequalizers_of_hasPushouts_and_binary_coproducts
add_to_sga "4 I 2.3.1" "more general" CategoryTheory.Limits.hasColimit_of_coequalizer_and_coproduct
add_to_sga "4 I 2.3.1" "(ii)⇒(i)"
  CategoryTheory.Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
add_to_sga "4 I 2.3.1" "more general"
  CategoryTheory.Limits.hasFiniteColimits_of_hasInitial_and_pushouts
add_to_sga "4 I 2.3.1" "(i)⇒(ii)" CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits
add_to_sga "4 I 2.3.1" "(ii)⇒(i)"
  CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products
add_to_sga "4 I 2.3.1" "(i)⇒(ii)" CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits
add_to_sga "4 I 2.3.1" "(ii)⇒(iii)"
  CategoryTheory.Limits.hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers
add_to_sga "4 I 2.3.1" "(ii)⇒(i)"
  CategoryTheory.Limits.has_colimits_of_hasCoequalizers_and_coproducts
add_to_sga "4 I 2.3.2" Ab
add_to_sga "4 I 2.3.2" "more general" AddCommGrpCat.hasColimit
add_to_sga "4 I 2.3.2" "more general" AddCommGrpCat.hasColimitsOfShape
add_to_sga "4 I 2.3.2" "more general" AddCommGrpCat.hasLimitsOfShape
add_to_sga "4 I 2.3.2" "more general" AddCommGrpCat.hasLimitsOfSize
add_to_sga "4 I 2.3.2" AddCommGrpCat.instCategory
add_to_sga "4 I 2.3.2" "more general" CategoryTheory.Limits.Types.hasColimit
add_to_sga "4 I 2.3.2" "more general" CategoryTheory.Limits.Types.hasColimitsOfShape
add_to_sga "4 I 2.3.2" "more general" CategoryTheory.Limits.Types.hasColimitsOfSize
add_to_sga "4 I 2.3.2" "more general" CategoryTheory.Limits.Types.hasLimit
add_to_sga "4 I 2.3.2" "more general" CategoryTheory.Limits.Types.hasLimitsOfShape
add_to_sga "4 I 2.3.2" "more general" CategoryTheory.Limits.Types.hasLimitsOfSize
add_to_sga "4 I 2.3.2" "more general" CategoryTheory.Types.instIsLocallyPresentableType
add_to_sga "4 I 2.3.2" CategoryTheory.types
add_to_sga "4 I 2.3.2" CommGrpCat
add_to_sga "4 I 2.3.2" CommGrpCat.hasLimits
add_to_sga "4 I 2.3.2" "more general" CommGrpCat.hasLimitsOfShape
add_to_sga "4 I 2.3.2" "special case" instHasFilteredColimitsAddCommGrpCat
add_to_sga "4 I 2.3.3" "partial" CategoryTheory.Functor.instSmallColimitType
add_to_sga "4 I 2.4.1" CategoryTheory.ExactFunctor
add_to_sga "4 I 2.4.1" CategoryTheory.LeftExactFunctor
add_to_sga "4 I 2.4.1" CategoryTheory.Limits.PreservesFiniteColimits
add_to_sga "4 I 2.4.1" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 I 2.4.1" CategoryTheory.RightExactFunctor
add_to_sga "4 I 2.4.1" CategoryTheory.exactFunctor
add_to_sga "4 I 2.4.1" CategoryTheory.leftExactFunctor
add_to_sga "4 I 2.4.1" CategoryTheory.rightExactFunctor
add_to_sga "4 I 2.4.2" CategoryTheory.Limits.HasTerminal
add_to_sga "4 I 2.4.2" CategoryTheory.Limits.IsTerminal
add_to_sga "4 I 2.4.2" "more general" CategoryTheory.Limits.isLimitEquivIsTerminalOfIsEmpty
add_to_sga "4 I 2.4.2" "sufficiency"
  CategoryTheory.Limits.preservesFiniteLimits_of_preservesTerminal_and_pullbacks
add_to_sga "4 I 2.4.2" "necessity"
  CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits
add_to_sga "4 I 2.4.2" "more general" CategoryTheory.ObjectProperty.limitsOfShape_isEmpty_iff
add_to_sga "4 I 2.5" CategoryTheory.IsUniversalColimit
add_to_sga "4 I 2.5.0" CategoryTheory.Functor.curry
add_to_sga "4 I 2.5.0" "partial" CategoryTheory.Functor.curry_obj_uncurry_obj
add_to_sga "4 I 2.5.0" CategoryTheory.Functor.currying
add_to_sga "4 I 2.5.0" CategoryTheory.Functor.uncurry
add_to_sga "4 I 2.5.0" "partial" CategoryTheory.Functor.uncurry_obj_curry_obj
add_to_sga "4 I 2.5.0" "special case" CategoryTheory.Limits.Fan.IsLimit.prod
add_to_sga "4 I 2.5.0" "special case"
  CategoryTheory.Limits.colimitCurrySwapCompColimIsoColimitCurryCompColim
add_to_sga "4 I 2.5.0" "partial"
  CategoryTheory.Limits.colimitCurrySwapCompColimIsoColimitCurryCompColim_ι_ι_hom
add_to_sga "4 I 2.5.0" "special case" CategoryTheory.Limits.colimitFlipCompColimIsoColimitCompColim
add_to_sga "4 I 2.5.0" "special case" CategoryTheory.Limits.colimitIsoColimitCurryCompColim
add_to_sga "4 I 2.5.0" "partial" CategoryTheory.Limits.instHasColimitProd
add_to_sga "4 I 2.5.0" "partial" CategoryTheory.Limits.instHasLimitProd
add_to_sga "4 I 2.5.0" "special case"
  CategoryTheory.Limits.isColimitCoconeOfHasColimitCurryCompColim
add_to_sga "4 I 2.5.0" CategoryTheory.Limits.lim
add_to_sga "4 I 2.5.0" "special case"
  CategoryTheory.Limits.limitCurrySwapCompLimIsoLimitCurryCompLim
add_to_sga "4 I 2.5.0" "special case" CategoryTheory.Limits.limitIsoLimitCurryCompLim
add_to_sga "4 I 2.5.0" "special case" CategoryTheory.Limits.piPiIso
add_to_sga "4 I 2.5.0" "special case" CategoryTheory.Limits.sigmaSigmaIso
add_to_sga "4 I 2.5.0" "special case"
  CategoryTheory.isFiltered_of_nonempty_limit_colimit_to_colimit_limit
add_to_sga "4 I 2.7" CategoryTheory.IsCofiltered
add_to_sga "4 I 2.7" CategoryTheory.IsConnected
add_to_sga "4 I 2.7" CategoryTheory.IsFiltered
add_to_sga "4 I 2.7" "Nonempty" CategoryTheory.IsFiltered.isConnected
add_to_sga "4 I 2.7" "partial" CategoryTheory.IsFilteredOrEmpty.isPreconnected
add_to_sga "4 I 2.7" CategoryTheory.Zigzag
add_to_sga "4 I 2.7" "partial" CategoryTheory.exists_zigzag'
add_to_sga "4 I 2.7" "partial" CategoryTheory.isCofiltered_of_isFiltered_op
add_to_sga "4 I 2.7" CategoryTheory.isCofiltered_op_iff_isFiltered
add_to_sga "4 I 2.7" "partial" CategoryTheory.isCofiltered_op_of_isFiltered
add_to_sga "4 I 2.7" "partial" CategoryTheory.isConnected_of_zigzag
add_to_sga "4 I 2.7" "partial" CategoryTheory.isFiltered_of_isCofiltered_op
add_to_sga "4 I 2.7" CategoryTheory.isFiltered_op_iff_isCofiltered
add_to_sga "4 I 2.7" "partial" CategoryTheory.isFiltered_op_of_isCofiltered
add_to_sga "4 I 2.7" "partial" CategoryTheory.isPreconnected_of_zigzag
add_to_sga "4 I 2.7" "partial" CategoryTheory.isPreconnected_zigzag
add_to_sga "4 I 2.7" "partial" CategoryTheory.zigzag_isConnected
add_to_sga "4 I 2.7" "partial" CategoryTheory.zigzag_isPreconnected
add_to_sga "4 I 2.7.1" "special case" CategoryTheory.IsFiltered.of_hasFiniteColimits
add_to_sga "4 I 2.8" "more general" CategoryTheory.Limits.filtered_colim_preservesFiniteLimits
add_to_sga "4 I 2.8" "more general"
  CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types
add_to_sga "4 I 2.8.1" "more general" CategoryTheory.Functor.eqvGen_colimitTypeRel_iff_of_isFiltered
add_to_sga "4 I 2.8.1" "more general" CategoryTheory.Functor.ιColimitType_eq_iff_of_isFiltered'
add_to_sga "4 I 2.8.1" "2: kernel identification"
  CategoryTheory.Limits.Concrete.colimit_rep_eq_iff_exists
add_to_sga "4 I 2.8.1" "2: kernel identification" CategoryTheory.Limits.IsColimit.eq_iff
add_to_sga "4 I 2.8.1" "more general" CategoryTheory.Limits.IsColimit.eq_iff'
add_to_sga "4 I 2.8.1" CategoryTheory.Limits.Types.FilteredColimit.Rel
add_to_sga "4 I 2.8.1" "2: kernel identification"
  CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff
add_to_sga "4 I 2.8.1" "2: kernel identification"
  CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff_aux
add_to_sga "4 I 2.8.1" "2: kernel identification"
  CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff
add_to_sga "4 I 2.8.1" "more general" CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
add_to_sga "4 I 2.8.1" "more general"
  CategoryTheory.Limits.Types.FilteredColimit.jointly_surjective_of_isColimit₂
add_to_sga "4 I 2.8.1" "more general"
  CategoryTheory.Limits.Types.FilteredColimit.rel_eq_eqvGen_colimitTypeRel
add_to_sga "4 I 2.8.1" "more general" CategoryTheory.Limits.Types.FilteredColimit.rel_equiv
add_to_sga "4 I 2.8.1" "2: kernel identification" CategoryTheory.Limits.colimit_eq_iff
add_to_sga "4 I 2.9" Ab
add_to_sga "4 I 2.9" "more general" CategoryTheory.Limits.filtered_colim_preservesFiniteLimits
run_cmd Lean.Elab.Command.elabCommand (← `(command| add_to_sga "4 I 2.9" "more general"
  $(Lean.mkIdent <| .str `CategoryTheory.Limits
    ("instPreservesFiniteLimitsFunctorColimOfPreservesColimitsOfShapeOf" ++
      "HasFiniteLimitsOfReflectsIsomorphismsForget"))))
add_to_sga "4 I 2.9" CategoryTheory.forget
add_to_sga "4 I 2.9" ModuleCat
add_to_sga "4 I 2.9" RingCat
add_to_sga "4 I 2.9" "special case" instPreservesFilteredColimitsAlgCatForgetAlgHomCarrier
add_to_sga "4 I 2.10" "special case" CategoryTheory.Limits.filtered_colim_preservesFiniteLimits
add_to_sga "4 I 2.10" "special case" instAB5AddCommGrpCat
add_to_sga "4 I 2.10" "special case" instPreservesFiniteLimitsFunctorAddCommGrpCatColim
add_to_sga "4 I 2.11" CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint
add_to_sga "4 I 2.11" CategoryTheory.Limits.PreservesColimit
add_to_sga "4 I 2.11" CategoryTheory.Limits.PreservesColimits
add_to_sga "4 I 2.11" CategoryTheory.Limits.PreservesLimit
add_to_sga "4 I 2.11" CategoryTheory.Limits.PreservesLimits
add_to_sga "4 I 2.11" CategoryTheory.ObjectProperty.preservesColimit
add_to_sga "4 I 2.11" CategoryTheory.ObjectProperty.preservesLimit
add_to_sga "4 I 3.1" CategoryTheory.Limits.HasColimits
add_to_sga "4 I 3.1" CategoryTheory.Limits.HasColimitsOfSize
add_to_sga "4 I 3.1" CategoryTheory.Limits.HasLimits
add_to_sga "4 I 3.1" CategoryTheory.Limits.HasLimitsOfSize
add_to_sga "4 I 3.1" CategoryTheory.Limits.PreservesColimits
add_to_sga "4 I 3.1" CategoryTheory.Limits.PreservesLimits
add_to_sga "4 I 3.1" "partial" CategoryTheory.Limits.evaluation_preservesColimit
add_to_sga "4 I 3.1" "partial" CategoryTheory.Limits.evaluation_preservesColimitsOfShape
add_to_sga "4 I 3.1" "special case" CategoryTheory.Limits.instHasFilteredColimitsOfSizeFunctor
add_to_sga "4 I 3.1" "special case"
  CategoryTheory.Limits.instPreservesFiniteColimitsFunctorObjEvaluationOfHasFiniteColimits
add_to_sga "4 I 3.1" "special case"
  CategoryTheory.Limits.instPreservesFiniteLimitsFunctorObjEvaluationOfHasFiniteLimits
add_to_sga "4 I 3.1" "partial" CategoryTheory.Limits.pointwiseIsColimit
add_to_sga "4 I 3.1" CategoryTheory.evaluation
add_to_sga "4 I 3.1" "special case" TopCat.instHasColimitsOfSizePresheafOfHasColimits
add_to_sga "4 I 3.1" "special case" TopCat.instHasLimitsOfShapePresheaf
add_to_sga "4 I 3.1" "special case" TopCat.instHasLimitsPresheaf
add_to_sga "4 I 3.3" CategoryTheory.Balanced
add_to_sga "4 I 3.3" "more general" CategoryTheory.GrothendieckTopology.preservesLimitsOfSize_yoneda
add_to_sga "4 I 3.3" CategoryTheory.IsUniversalColimit
add_to_sga "4 I 3.3" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 I 3.3" CategoryTheory.Limits.PreservesLimit
add_to_sga "4 I 3.3" CategoryTheory.Limits.PreservesLimits
add_to_sga "4 I 3.3" "Fourth clause for sets"
  CategoryTheory.Limits.filtered_colim_preservesFiniteLimits
add_to_sga "4 I 3.3" "special case"
  CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types
run_cmd Lean.Elab.Command.elabCommand (← `(command| add_to_sga "4 I 3.3" "Fourth clause for sets"
  $(Lean.mkIdent <| .str `CategoryTheory.Limits
    ("instPreservesFiniteLimitsFunctorColimOfPreservesColimitsOfShapeOf" ++
      "HasFiniteLimitsOfReflectsIsomorphismsForget"))))
add_to_sga "4 I 3.3" CategoryTheory.MorphismProperty.HasFactorization
add_to_sga "4 I 3.3" CategoryTheory.coyonedaFunctor_preservesLimits
add_to_sga "4 I 3.3" CategoryTheory.yonedaFunctor_preservesLimits
add_to_sga "4 I 3.3" "more general" instPreservesLimitsOfShapeSheafTypeYoneda
add_to_sga "4 I 3.4" CategoryTheory.Functor.Elements.coconeπOpCompShrinkYonedaFlip
add_to_sga "4 I 3.4" CategoryTheory.Functor.Elements.isColimitCoconeπOpCompShrinkYonedaFlip
add_to_sga "4 I 3.4" CategoryTheory.Presheaf.coconeOfRepresentable
add_to_sga "4 I 3.4" CategoryTheory.Presheaf.colimitOfRepresentable
add_to_sga "4 I 3.4" CategoryTheory.Presheaf.isColimitTautologicalCocone
add_to_sga "4 I 3.4" CategoryTheory.Presheaf.isColimitTautologicalCocone'
add_to_sga "4 I 3.4.0" "more general" CategoryTheory.CostructuredArrow
add_to_sga "4 I 4.1" CategoryTheory.Sieve.mk
add_to_sga "4 I 4.2" CategoryTheory.Sieve.functorInclusion
add_to_sga "4 I 4.2" "partial" CategoryTheory.Sieve.functorInclusion_is_mono
add_to_sga "4 I 4.2" CategoryTheory.Sieve.shrinkFunctor
add_to_sga "4 I 4.2" CategoryTheory.Sieve.sieveOfSubfunctor
add_to_sga "4 I 4.2" "left-inverse identity" CategoryTheory.Sieve.sieveOfSubfunctor_functorInclusion
add_to_sga "4 I 4.2" "partial" CategoryTheory.Sieve.uliftFunctorInclusion_is_mono
add_to_sga "4 I 4.2" CategoryTheory.Subfunctor.sieveOfSection
add_to_sga "4 I 4.3" CategoryTheory.Presheaf.imageSieve
add_to_sga "4 I 4.3" CategoryTheory.Presieve.category
add_to_sga "4 I 4.3" CategoryTheory.Presieve.diagram
add_to_sga "4 I 4.3" "bijection Hom(R" CategoryTheory.Presieve.shrinkFunctorHomEquiv
add_to_sga "4 I 4.3" CategoryTheory.Sieve.functor
add_to_sga "4 I 4.3" CategoryTheory.Sieve.functorInclusion
add_to_sga "4 I 4.3" "sieve-to-subobject" CategoryTheory.Sieve.functorInclusion_is_mono
add_to_sga "4 I 4.3" CategoryTheory.Sieve.shrinkFunctor
add_to_sga "4 I 4.3" CategoryTheory.Sieve.sieveOfSubfunctor
add_to_sga "4 I 4.3" "partial" CategoryTheory.Sieve.uliftFunctorInclusion_is_mono
add_to_sga "4 I 4.3" CategoryTheory.Subfunctor.sieveOfSection
add_to_sga "4 I 4.3.1" CategoryTheory.Sieve.pullback_arrows
add_to_sga "4 I 4.3.2" CategoryTheory.Sieve.inf
add_to_sga "4 I 4.3.2" CategoryTheory.Sieve.instCompleteLattice
add_to_sga "4 I 4.3.2" "two-member family" CategoryTheory.Sieve.inter
add_to_sga "4 I 4.3.2" "two-member family" CategoryTheory.Sieve.inter_apply
add_to_sga "4 I 4.3.2" CategoryTheory.Sieve.sInf_apply
add_to_sga "4 I 4.3.2" CategoryTheory.Sieve.sSup_apply
add_to_sga "4 I 4.3.2" CategoryTheory.Sieve.sup
add_to_sga "4 I 4.3.2" "two-member family" CategoryTheory.Sieve.union
add_to_sga "4 I 4.3.2" "two-member family" CategoryTheory.Sieve.union_apply
add_to_sga "4 I 4.3.3" "special case" CategoryTheory.Presheaf.imageSieve
add_to_sga "4 I 4.3.3" "one presheaf morphism" CategoryTheory.Presheaf.imageSieve_apply
add_to_sga "4 I 4.3.3" "special case" CategoryTheory.Presheaf.imageSieve_eq_sieveOfSection
add_to_sga "4 I 4.3.3" "special case" CategoryTheory.Sieve.coverByImage
add_to_sga "4 I 4.3.3" CategoryTheory.Sieve.generateFamily
add_to_sga "4 I 4.3.3" "representable domains" CategoryTheory.Sieve.generateFamily_eq
add_to_sga "4 I 4.3.3" "one generating arrow" CategoryTheory.Sieve.generateSingleton
add_to_sga "4 I 4.3.3" "special case" CategoryTheory.Sieve.generate_apply
add_to_sga "4 I 4.3.3" "representable domains" CategoryTheory.Sieve.mem_ofArrows_iff
add_to_sga "4 I 4.3.3" "partial" CategoryTheory.Sieve.ofArrows.exists
add_to_sga "4 I 4.3.3" "partial" CategoryTheory.Sieve.ofArrows.fac
add_to_sga "4 I 4.3.3" "two generating arrows" CategoryTheory.Sieve.ofTwoArrows
add_to_sga "4 I 4.3.3" "partial" CategoryTheory.Sieve.sup
add_to_sga "4 I 4.3.3" "partial" CategoryTheory.Sieve.union
add_to_sga "4 I 5.0" "more general" CategoryTheory.Bicategory.precomp
add_to_sga "4 I 5.0" "special case"
  CategoryTheory.instPreservesFiniteLimitsFunctorObjWhiskeringLeftOfHasFiniteLimits
add_to_sga "4 I 5.0" "more general" CategoryTheory.whiskeringLeft_preservesColimitsOfShape
add_to_sga "4 I 5.2" "more general" CategoryTheory.Limits.instHasFiniteLimitsFunctor
add_to_sga "4 I 5.2" "finite products" CategoryTheory.Limits.instHasFiniteProductsFunctor
add_to_sga "4 I 5.4" "more general" CategoryTheory.Adjunction.leftAdjoint_preservesColimits
add_to_sga "4 I 5.4" "more general" CategoryTheory.Adjunction.rightAdjoint_preservesLimits
add_to_sga "4 I 5.4" "more general"
  CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint
add_to_sga "4 I 5.4" "more general"
  CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint
add_to_sga "4 I 5.4" "more general"
  CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint
add_to_sga "4 I 5.4" "more general" CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint
add_to_sga "4 I 5.4" "Clause 3"
  CategoryTheory.Presheaf.instIsIsoFunctorLeftKanExtensionUnitOppositeTypeUliftYoneda
add_to_sga "4 I 5.4" "Clause 3"
  CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeYonedaYonedaMap
open CategoryTheory in
add_to_sga "4 I 5.4" "Clause 3"
  Presheaf.instUniqueHomLeftExtensionOppositeOpObjFunctorTypeUliftYonedaMkUliftYonedaMap
add_to_sga "4 I 5.4" "Clause 3"
  CategoryTheory.Presheaf.instUniqueHomLeftExtensionOppositeOpObjFunctorTypeYonedaMkYonedaMap
add_to_sga "4 I 5.4" "Clause 3" CategoryTheory.Presheaf.isExtensionAlongULiftYoneda
add_to_sga "4 I 5.4" "more general" CategoryTheory.Presheaf.isLeftKanExtension_along_uliftYoneda_iff
add_to_sga "4 I 5.4" "more general" CategoryTheory.Presheaf.preservesColimitsOfSize_leftKanExtension
add_to_sga "4 I 5.4" "more general"
  CategoryTheory.Presheaf.preservesColimitsOfSize_of_isLeftKanExtension
add_to_sga "4 I 5.6" "iv⇒v" CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful
add_to_sga "4 I 5.6" "v⇒iv" CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit
add_to_sga "4 I 5.6" "ii⇒iii" CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful
add_to_sga "4 I 5.6" "i⇒iii"
  CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso_hom_app
add_to_sga "4 I 5.7" "Remark 5.7 a)" CategoryTheory.Adjunction.Triple.fullyFaithfulEquiv
add_to_sga "4 I 5.7" "Remark 5.7 a)" CategoryTheory.Adjunction.Triple.isIso_unit_iff_isIso_counit
add_to_sga "4 I 5.7" "Remark 5.7 a)" CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful
add_to_sga "4 I 5.7" "Remark 5.7 a)" CategoryTheory.Adjunction.fullyFaithfulLOfCompIsoId
add_to_sga "4 I 5.7" "Remark 5.7 a)" CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit
add_to_sga "4 I 5.7" "Remark 5.7 a)" CategoryTheory.Adjunction.fullyFaithfulROfCompIsoId
add_to_sga "4 I 5.7" "Remark 5.7 a)" CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit
add_to_sga "4 I 5.7" "Remark 5.7 a)" CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful
add_to_sga "4 I 5.7" "Remark 5.7 a)" CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful
add_to_sga "4 I 5.7" "more general"
  CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtension.isIso_hom
add_to_sga "4 I 5.7" "more general"
  CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso_hom_app
add_to_sga "4 I 5.7" "more general"
  CategoryTheory.Functor.RightExtension.IsPointwiseRightKanExtension.isIso_hom
add_to_sga "4 I 5.8.2" "special case" AddCommGrpCat.adj
add_to_sga "4 I 5.8.2" "special case" AddCommGrpCat.free
add_to_sga "4 I 5.8.2" "special case" AddMonCat.adj
add_to_sga "4 I 5.8.2" "special case" AddMonCat.free
add_to_sga "4 I 5.8.2" "special case" AlgCat.free
add_to_sga "4 I 5.8.2" "partial" FreeAbelianGroup
add_to_sga "4 I 5.8.2" "partial" FreeGroup
add_to_sga "4 I 5.8.2" "special case" GrpCat.adj
add_to_sga "4 I 5.8.2" "Groups, special case" GrpCat.free
add_to_sga "4 I 5.8.2" "A-modules: Lib^ ⊣ esj^" PresheafOfModules.freeAdjunction
add_to_sga "4 I 5.8.3" "special case" CategoryTheory.Limits.Types.hasColimit
add_to_sga "4 I 5.8.3" "special case" instHasColimitsCommAlgCat
add_to_sga "4 I 5.8.3" "special case" instPreservesFiniteLimitsFunctorAddCommGrpCatColim
add_to_sga "4 I 5.10" CategoryTheory.CostructuredArrow
add_to_sga "4 I 5.10" CategoryTheory.CostructuredArrow.map
add_to_sga "4 I 5.12" "special case" CategoryTheory.Over.iteratedSliceEquiv
add_to_sga "4 I 5.14" "special case"
  CategoryTheory.Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isIso_hom_app
add_to_sga "4 I 6.1" "singleton family" CategoryTheory.Functor.Faithful
add_to_sga "4 I 6.1" "singleton family" CategoryTheory.Functor.ReflectsIsomorphisms
add_to_sga "4 I 6.1" CategoryTheory.JointlyFaithful
add_to_sga "4 I 6.1.1" CategoryTheory.Functor.pi'
add_to_sga "4 I 6.1.1" "partial" CategoryTheory.Functor.pi'CompEval
add_to_sga "4 I 6.1.1" "partial" CategoryTheory.Functor.pi'_eval
add_to_sga "4 I 6.1.1" "two-member family" CategoryTheory.Functor.prod'
add_to_sga "4 I 6.2" "(ii), special case"
  CategoryTheory.ConcreteCategory.epi_iff_surjective_of_preservesPushout
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback
add_to_sga "4 I 6.2" "(ii), special case"
  CategoryTheory.ConcreteCategory.mono_iff_injective_of_preservesPullback
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.ConcreteCategory.surjective_of_epi_of_preservesPushout
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.Functor.reflectsEpimorphisms_of_faithful
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.Functor.reflectsMonomorphisms_of_faithful
add_to_sga "4 I 6.2" "(iii), single functor"
  CategoryTheory.HasSubobjectClassifier.reflectsIsomorphisms
add_to_sga "4 I 6.2" "(iii), special case"
  CategoryTheory.HasSubobjectClassifier.reflectsIsomorphismsOp
add_to_sga "4 I 6.2" "(i), special case" CategoryTheory.IsCodetector.isCoseparator
add_to_sga "4 I 6.2" "more general" CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms
add_to_sga "4 I 6.2" "more general" CategoryTheory.JointlyFaithful.of_jointly_reflects_isIso_of_mono
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.JointlyReflectIsomorphisms.epi
add_to_sga "4 I 6.2" CategoryTheory.JointlyReflectIsomorphisms.jointlyFaithful
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectEpimorphisms
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectMonomorphisms
add_to_sga "4 I 6.2" "(v)" CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectsColimit
add_to_sga "4 I 6.2" "(v)" CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectsLimit
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.JointlyReflectIsomorphisms.mono
add_to_sga "4 I 6.2" "(v), special case"
  CategoryTheory.Limits.reflectsColimit_of_reflectsIsomorphisms
add_to_sga "4 I 6.2" "(v), special case" CategoryTheory.Limits.reflectsLimit_of_reflectsIsomorphisms
add_to_sga "4 I 6.2" "(i), special case"
  CategoryTheory.MorphismProperty.faithful_overPullback_of_isomorphisms_descendAlong
add_to_sga "4 I 6.2" "(ii), special case"
  CategoryTheory.MorphismProperty.functorCategory_epimorphisms
add_to_sga "4 I 6.2" "(ii), special case"
  CategoryTheory.MorphismProperty.functorCategory_monomorphisms
add_to_sga "4 I 6.2" "(ii), special case" CategoryTheory.Under.mono_iff_mono_right
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.preserves_epi_of_preservesColimit
add_to_sga "4 I 6.2" "(ii)" CategoryTheory.preserves_mono_of_preservesLimit
add_to_sga "4 I 6.2" "(iii), single functor"
  CategoryTheory.reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms
add_to_sga "4 I 6.3" "b), special case" CategoryTheory.IsCodetector.isCoseparator
add_to_sga "4 I 6.3" "b), special case" CategoryTheory.IsDetector.isSeparator
add_to_sga "4 I 6.3" "c) implies a)"
  CategoryTheory.JointlyFaithful.of_jointly_reflects_isIso_of_mono
add_to_sga "4 I 6.3" "b) implies a)" CategoryTheory.JointlyReflectIsomorphisms.jointlyFaithful
add_to_sga "4 I 6.3" "b), special case" CategoryTheory.ObjectProperty.IsDetecting.isSeparating
add_to_sga "4 I 6.3" "b), special case" CategoryTheory.isSeparator_detector
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.counit_epi_of_R_faithful
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.faithful_L_of_mono_unit_app
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.faithful_R_of_epi_counit_app
add_to_sga "4 I 6.4" "more general" CategoryTheory.Adjunction.fullyFaithfulLOfCompIsoId
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit
add_to_sga "4 I 6.4" "more general" CategoryTheory.Adjunction.fullyFaithfulROfCompIsoId
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.instIsIsoAppUnitOfFullOfFaithful
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful
add_to_sga "4 I 6.4" "partial" CategoryTheory.Adjunction.unit_mono_of_L_faithful
add_to_sga "4 I 6.5.1" "for a groupoid" CategoryTheory.Groupoid.isThin_iff
add_to_sga "4 I 6.5.1" CategoryTheory.IsGroupoid
add_to_sga "4 I 6.5.1" "for a groupoid" CategoryTheory.Subgroupoid.isThin_iff
add_to_sga "4 I 6.5.1" CategoryTheory.discreteCategory
add_to_sga "4 I 6.5.2" CategoryTheory.Functor.Faithful
add_to_sga "4 I 6.5.2" CategoryTheory.Functor.ReflectsIsomorphisms
add_to_sga "4 I 7.1" "special case" CategoryTheory.IsDetector
add_to_sga "4 I 7.1" CategoryTheory.ObjectProperty.IsDetecting
add_to_sga "4 I 7.1.3" CategoryTheory.Presheaf.restrictedULiftYoneda
add_to_sga "4 I 7.1.3" "C = E" CategoryTheory.yoneda
add_to_sga "4 I 7.2" "(i), c) ⇒ b)"
  CategoryTheory.Functor.IsDense.of_fullyFaithful_restrictedULiftYoneda
add_to_sga "4 I 7.2" "(i), b) ⇔ c)"
  CategoryTheory.Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda
add_to_sga "4 I 7.4" "special case" CategoryTheory.Subobject.eq_of_isDetecting
add_to_sga "4 I 7.9" "special case" CategoryTheory.isCoseparator_op_iff
add_to_sga "4 I 7.9" "special case" CategoryTheory.isSeparator_op_iff
add_to_sga "4 I 7.11" CategoryTheory.isInjective
add_to_sga "4 I 7.12" "special case" CategoryTheory.Abelian.has_injective_coseparator
add_to_sga "4 I 7.13" "abelian groups" AddCommGrpCat.enoughInjectives
add_to_sga "4 I 7.13" CategoryTheory.AB5
add_to_sga "4 I 7.13" CategoryTheory.AB5OfSize
add_to_sga "4 I 7.13" "special case" CommGrpCat.enoughInjectives
add_to_sga "4 I 7.13" "modules over a ring" ModuleCat.enoughInjectives
add_to_sga "4 I 7.13" "special case" SheafOfModules.free
add_to_sga "4 I 7.13" "special case" SheafOfModules.freeFunctor
add_to_sga "4 I 7.13" "special case" SheafOfModules.freeHomEquiv
add_to_sga "4 I 7.13" "special case" instEnoughInjectivesModuleCatInt
add_to_sga "4 I 7.13" "special case" instEnoughInjectivesModuleCatOfSmall
add_to_sga "4 I 8.1.1" CategoryTheory.Functor.Final
add_to_sga "4 I 8.1.1" "special case" CategoryTheory.Functor.Final.colimIso
add_to_sga "4 I 8.1.1" "special case" CategoryTheory.Functor.Final.colimitIso
add_to_sga "4 I 8.1.1" "special case" CategoryTheory.Functor.Final.colimit_pre_isIso
add_to_sga "4 I 8.1.1" "special case" CategoryTheory.Functor.final_iff_isIso_colimit_pre
add_to_sga "4 I 8.1.1" CategoryTheory.Limits.colimit.pre
add_to_sga "4 I 8.1.2" "necessity" CategoryTheory.Functor.Final.colimit_pre_isIso
add_to_sga "4 I 8.1.2" "necessity" CategoryTheory.Functor.Initial.limit_pre_isIso
add_to_sga "4 I 8.1.2.2" CategoryTheory.Functor.final_comp
add_to_sga "4 I 8.1.2.2" "special case" CategoryTheory.Functor.final_comp_equivalence
add_to_sga "4 I 8.1.2.2" "special case" CategoryTheory.Functor.final_equivalence_comp
add_to_sga "4 I 8.1.2.2" "special case" CategoryTheory.Functor.final_iff_comp_equivalence
add_to_sga "4 I 8.1.2.2" "special case" CategoryTheory.Functor.final_iff_comp_final_full_faithful
add_to_sga "4 I 8.1.2.2" "special case" CategoryTheory.Functor.final_iff_equivalence_comp
add_to_sga "4 I 8.1.2.2" "more general" CategoryTheory.Functor.final_iff_final_comp
add_to_sga "4 I 8.1.3" "more general" CategoryTheory.Functor.final_iff_of_isFiltered
add_to_sga "4 I 8.1.3" "b)" CategoryTheory.Functor.final_of_exists_of_isFiltered
add_to_sga "4 I 8.1.3" CategoryTheory.IsFiltered.of_final
add_to_sga "4 I 8.1.3" "c)"
  CategoryTheory.IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful
add_to_sga "4 I 8.1.3" "b)" CategoryTheory.IsFilteredOrEmpty.of_final
add_to_sga "4 I 8.1.4" IsCofinal
add_to_sga "4 I 8.1.4" "more general" IsCofinalFor
add_to_sga "4 I 8.1.4" Order.Cofinal
add_to_sga "4 I 8.1.5" Preorder.smallCategory
add_to_sga "4 I 8.1.5" "partial" Preorder.subsingleton_hom
add_to_sga "4 I 8.1.5" "more general" preordToCat
add_to_sga "4 I 8.1.6" "more general" CategoryTheory.IsCardinalFiltered.exists_cardinal_directed
add_to_sga "4 I 8.1.6" CategoryTheory.IsFiltered.exists_directed
add_to_sga "4 I 8.1.7" "special case" CategoryTheory.IsFiltered.exists_directed
add_to_sga "4 I 8.1.7" "necessity: I is filtered" CategoryTheory.IsFiltered.of_final
add_to_sga "4 I 8.1.7" "special case" CategoryTheory.Limits.IsFiltered.sequentialFunctor_final
add_to_sga "4 I 8.1.8" CategoryTheory.finallySmall_iff_exists_small_weakly_terminal_set
add_to_sga "4 I 8.1.8" "partial" CategoryTheory.finallySmall_of_small_weakly_terminal_set
add_to_sga "4 I 8.2.1" CategoryTheory.Functor
add_to_sga "4 I 8.2.1" CategoryTheory.Functor.map
add_to_sga "4 I 8.2.1" CategoryTheory.Functor.obj
add_to_sga "4 I 8.2.1" CategoryTheory.yoneda
add_to_sga "4 I 8.2.2" CategoryTheory.Limits.IndObjectPresentation
add_to_sga "4 I 8.2.2" CategoryTheory.Limits.IsIndObject
add_to_sga "4 I 8.2.2" "more general" CategoryTheory.ObjectProperty.ind
add_to_sga "4 I 8.2.2" "special case" CategoryTheory.ObjectProperty.of_essentiallySmall_index
add_to_sga "4 I 8.2.3" "more general" CategoryTheory.Functor.Final.colimIso
add_to_sga "4 I 8.2.3" "more general" CategoryTheory.Functor.Final.colimitIso
add_to_sga "4 I 8.2.3" "more general" CategoryTheory.Functor.Final.colimit_pre_isIso
add_to_sga "4 I 8.2.3" CategoryTheory.Functor.comp
add_to_sga "4 I 8.2.3" "special case" CategoryTheory.Functor.final_iff_isIso_colimit_pre
add_to_sga "4 I 8.2.3" "more general" CategoryTheory.Limits.ColimitPresentation.reindex
add_to_sga "4 I 8.2.3" CategoryTheory.Limits.colimit.pre
add_to_sga "4 I 8.2.3" "more general" CategoryTheory.ObjectProperty.ColimitOfShape.reindex
add_to_sga "4 I 8.2.4" CategoryTheory.Ind
add_to_sga "4 I 8.2.4" "partial" CategoryTheory.Ind.equivalence
add_to_sga "4 I 8.2.4" CategoryTheory.Ind.inclusion
add_to_sga "4 I 8.2.4" "partial" CategoryTheory.Ind.inclusion.fullyFaithful
add_to_sga "4 I 8.2.4" "partial" CategoryTheory.Ind.isIndObject_inclusion_obj
add_to_sga "4 I 8.2.4" "partial" CategoryTheory.Limits.IsIndObject
add_to_sga "4 I 8.2.4" "special case" CategoryTheory.instCategoryInd
add_to_sga "4 I 8.2.4" "Faithfulness of L"
  CategoryTheory.instFaithfulIndFunctorOppositeTypeInclusion
add_to_sga "4 I 8.2.4" "partial" CategoryTheory.instFullIndFunctorOppositeTypeInclusion
add_to_sga "4 I 8.2.5" "First step of 8.2.5" CategoryTheory.Limits.colimitYonedaHomIsoLimit
add_to_sga "4 I 8.2.5" "First step of 8.2.5" CategoryTheory.Limits.colimitYonedaHomIsoLimitRightOp
add_to_sga "4 I 8.2.5" CategoryTheory.instCategoryInd
add_to_sga "4 I 8.2.5" CategoryTheory.instLocallySmallFullSubcategoryFunctorOppositeTypeIsIndObject
add_to_sga "4 I 8.2.6" CategoryTheory.Ind.lim
add_to_sga "4 I 8.2.6" "partial" CategoryTheory.Ind.limCompInclusion
add_to_sga "4 I 8.2.7" CategoryTheory.Ind
add_to_sga "4 I 8.2.7" CategoryTheory.Ind.equivalence
add_to_sga "4 I 8.2.7" CategoryTheory.ObjectProperty.isoClosure
add_to_sga "4 I 8.3.1" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 I 8.3.1" "special case" CategoryTheory.Limits.isIndObject_iff_preservesFiniteLimits
add_to_sga "4 I 8.3.1" CategoryTheory.instPreservesFiniteColimitsIndYoneda
add_to_sga "4 I 8.3.1" CategoryTheory.leftExactFunctor
add_to_sga "4 I 8.3.2" "partial"
  CategoryTheory.CategoryOfElements.costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso
add_to_sga "4 I 8.3.2" CategoryTheory.CategoryOfElements.π
add_to_sga "4 I 8.3.2" CategoryTheory.CostructuredArrow.proj
add_to_sga "4 I 8.3.2" CategoryTheory.Functor.Elements
add_to_sga "4 I 8.3.2" CategoryTheory.Functor.Elements.coconeπOpCompShrinkYonedaFlip
add_to_sga "4 I 8.3.2" CategoryTheory.Functor.Elements.isColimitCoconeπOpCompShrinkYonedaFlip
add_to_sga "4 I 8.3.2" CategoryTheory.Presheaf.coconeOfRepresentable
add_to_sga "4 I 8.3.2" CategoryTheory.Presheaf.colimitOfRepresentable
add_to_sga "4 I 8.3.2" CategoryTheory.Presheaf.functorToRepresentables
add_to_sga "4 I 8.3.2" CategoryTheory.Presheaf.isColimitTautologicalCocone
add_to_sga "4 I 8.3.2" CategoryTheory.Presheaf.isColimitTautologicalCocone'
add_to_sga "4 I 8.3.2" "more general" CategoryTheory.Pseudofunctor.Grothendieck.forget
add_to_sga "4 I 8.3.2" CategoryTheory.Functor.Elements.instCategory
add_to_sga "4 I 8.3.2" "partial" CategoryTheory.yonedaEquiv
add_to_sga "4 I 8.3.2.3" "more general" CategoryTheory.Functor.Elements.instCreatesLimitπ
add_to_sga "4 I 8.3.2.3" "more general"
  CategoryTheory.Functor.Elements.instHasLimitsOfShape
add_to_sga "4 I 8.3.2.3" "filteredness of C/F" CategoryTheory.Functor.isCofiltered_elements
add_to_sga "4 I 8.3.2.3" "filteredness consequence"
  CategoryTheory.Limits.isFiltered_costructuredArrow_yoneda_iff_nonempty_preservesFiniteLimits
add_to_sga "4 I 8.3.2.3" "filteredness consequence"
  CategoryTheory.Limits.isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits
add_to_sga "4 I 8.3.2.3" "filteredness consequence" CategoryTheory.coflat_of_preservesFiniteColimits
add_to_sga "4 I 8.3.2.3" "filteredness of C/F" CategoryTheory.flat_of_preservesFiniteLimits
add_to_sga "4 I 8.3.2.3" "filteredness consequence"
  CategoryTheory.preservesFiniteColimits_iff_coflat
add_to_sga "4 I 8.3.2.3" "filteredness of C/F" CategoryTheory.preservesFiniteLimits_iff_flat
add_to_sga "4 I 8.3.3" "(i) ⇒ (ii), (i) ⇒ (iii)" CategoryTheory.Limits.IsIndObject.finallySmall
add_to_sga "4 I 8.3.3" "partial" CategoryTheory.Limits.IsIndObject.isFiltered
add_to_sga "4 I 8.3.3" CategoryTheory.Limits.isIndObject_iff
add_to_sga "4 I 8.3.3" "partial" CategoryTheory.Limits.isIndObject_iff_preservesFiniteLimits
add_to_sga "4 I 8.3.3" "(ii) ⇒ (i)" CategoryTheory.Limits.isIndObject_of_isFiltered_of_finallySmall
add_to_sga "4 I 8.3.4" "special case" CategoryTheory.Ind.leftExactFunctorEquivalence
add_to_sga "4 I 8.3.4" CategoryTheory.Limits.IndObjectPresentation
add_to_sga "4 I 8.3.4" CategoryTheory.Limits.IsIndObject
add_to_sga "4 I 8.3.4" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 I 8.3.4" "special case" CategoryTheory.Limits.isIndObject_iff_preservesFiniteLimits
add_to_sga "4 I 8.3.4" CategoryTheory.leftExactFunctor
add_to_sga "4 I 8.4" "partial" CategoryTheory.Cat.chosenTerminalIsTerminal
add_to_sga "4 I 8.4" CategoryTheory.Functor.const
add_to_sga "4 I 8.4" CategoryTheory.Ind.yoneda
add_to_sga "4 I 8.4" "full faithfulness of c" CategoryTheory.Ind.yoneda.fullyFaithful
add_to_sga "4 I 8.4" CategoryTheory.Ind.yonedaCompInclusion
add_to_sga "4 I 8.4" "more general" CategoryTheory.IsFiltered.of_hasTerminal
add_to_sga "4 I 8.4" "more general" CategoryTheory.IsFiltered.of_isTerminal
add_to_sga "4 I 8.4" "faithfulness of c" CategoryTheory.instFaithfulIndYoneda
add_to_sga "4 I 8.4" "fullness of c" CategoryTheory.instFullIndYoneda
add_to_sga "4 I 8.4.3" "more general"
  CategoryTheory.Functor.IsEventuallyConstantFrom.isColimitOfIsIso
add_to_sga "4 I 8.4.3" CategoryTheory.Functor.const
add_to_sga "4 I 8.4.4" "more general" CategoryTheory.Functor.essImage
add_to_sga "4 I 8.5.1" CategoryTheory.Limits.isIndObject_colimit
add_to_sga "4 I 8.5.1"
  CategoryTheory.instCreatesColimitsOfShapeIndFunctorOppositeTypeInclusionOfIsFiltered
add_to_sga "4 I 8.5.1" "special case" CategoryTheory.instHasColimitsIndOfHasFiniteColimits
add_to_sga "4 I 8.5.1" CategoryTheory.instHasFilteredColimitsInd
add_to_sga "4 I 8.5.1"
  CategoryTheory.instIsClosedUnderColimitsOfShapeFunctorOppositeTypeIsIndObjectOfIsFiltered
add_to_sga "4 I 8.5.2" CategoryTheory.Limits.isIndObject_colimit
add_to_sga "4 I 8.5.2"
  CategoryTheory.instIsClosedUnderColimitsOfShapeFunctorOppositeTypeIsIndObjectOfIsFiltered
add_to_sga "4 I 8.5.3" "partial" CategoryTheory.Ind.colimitPresentationCompYoneda
add_to_sga "4 I 8.5.4" "partial" CategoryTheory.Functor.curry
add_to_sga "4 I 8.5.4" "partial" CategoryTheory.Functor.curryObj
add_to_sga "4 I 8.5.4" "partial" CategoryTheory.Functor.currying
add_to_sga "4 I 8.5.4" "Canonical functor Hom(I" CategoryTheory.Ind.lim
add_to_sga "4 I 8.5.4" "more general" CategoryTheory.instIsFilteredForall
add_to_sga "4 I 8.5.4" CategoryTheory.instIsFilteredProd
add_to_sga "4 I 8.5.4" "more general" CategoryTheory.isCardinalFiltered_pi
add_to_sga "4 I 8.5.4" "more general" CategoryTheory.isCardinalFiltered_prod
open CategoryTheory in
add_to_sga "4 I 8.6.2" "f_! extends f"
  Presheaf.instIsLeftKanExtensionFunctorOppositeTypeLanOpHomCompULiftYonedaIsoULiftYonedaCompLan
add_to_sga "4 I 8.6.2" "partial"
  CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeUliftYonedaUliftYonedaMap
add_to_sga "4 I 8.6.2" "partial"
  CategoryTheory.Presheaf.instIsLeftKanExtensionOppositeObjFunctorTypeYonedaYonedaMap
add_to_sga "4 I 8.7.1.7" "more general" CategoryTheory.Adjunction.leftAdjoint_preservesColimits
add_to_sga "4 I 8.7.1.7" "more general" CategoryTheory.Functor.essImage
add_to_sga "4 I 8.7.1.7" "more general"
  CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint
add_to_sga "4 I 8.7.1.7" "more general"
  CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint
add_to_sga "4 I 8.7.2" "partial" CategoryTheory.Limits.PreservesFilteredColimits
add_to_sga "4 I 8.7.2" "partial" CategoryTheory.Limits.PreservesFilteredColimitsOfSize
add_to_sga "4 I 8.7.3" "first clause" CategoryTheory.instHasFilteredColimitsInd
add_to_sga "4 I 8.7.4" "partial" CategoryTheory.Equivalence.fullyFaithfulToEssImage
add_to_sga "4 I 8.7.4" "partial" CategoryTheory.Functor.toEssImageCompι
add_to_sga "4 I 8.7.5" "more general" CategoryTheory.ObjectProperty.FullSubcategory
add_to_sga "4 I 8.7.5" "more general" CategoryTheory.ObjectProperty.FullSubcategory.category
open CategoryTheory.IsCardinalAccessibleCategory in
add_to_sga "4 I 8.7.5.2" "partial"
  instIsCardinalFilteredCostructuredArrowFullSubcategoryIsCardinalPresentableι
open CategoryTheory.IsFinitelyAccessibleCategory in
add_to_sga "4 I 8.7.5.2" "Filteredness clause"
  instIsFilteredCostructuredArrowFullSubcategoryIsFinitelyPresentableι
add_to_sga "4 I 8.7.5.2" "special case" CategoryTheory.Limits.isIndObject_iff
add_to_sga "4 I 8.7.5.2" "partial"
  CategoryTheory.ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCardinalClosure_ι
add_to_sga "4 I 8.7.5.2" "partial"
  CategoryTheory.ObjectProperty.isFiltered_costructuredArrow_colimitsCardinalClosure_ι
add_to_sga "4 I 8.7.6" CategoryTheory.IsFinitelyPresentable
add_to_sga "4 I 8.7.6" CategoryTheory.ObjectProperty.isFinitelyPresentable
add_to_sga "4 I 8.7.6" "more general" CategoryTheory.isCardinalPresentable
add_to_sga "4 I 8.7.8" CategoryTheory.Idempotents.FunctorExtension₁.obj
add_to_sga "4 I 8.7.8" CategoryTheory.Idempotents.Karoubi
add_to_sga "4 I 8.7.8" CategoryTheory.Idempotents.Karoubi.Hom
add_to_sga "4 I 8.7.8" CategoryTheory.Idempotents.Karoubi.instCategory
add_to_sga "4 I 8.7.8" "partial" CategoryTheory.Idempotents.Karoubi.retract
add_to_sga "4 I 8.7.8" "full faithfulness of φ" CategoryTheory.Idempotents.fullyFaithfulToKaroubi
add_to_sga "4 I 8.7.8" CategoryTheory.Idempotents.functorExtension
add_to_sga "4 I 8.7.8" CategoryTheory.Idempotents.functorExtension₁
add_to_sga "4 I 8.7.8" "partial"
  CategoryTheory.Idempotents.functorExtension₁CompWhiskeringLeftToKaroubiIso
add_to_sga "4 I 8.7.8" CategoryTheory.Idempotents.functorExtension₂
add_to_sga "4 I 8.7.8" "partial"
  CategoryTheory.Idempotents.functorExtension₂CompWhiskeringLeftToKaroubiIso
add_to_sga "4 I 8.7.8" "partial" CategoryTheory.Idempotents.instFaithfulKaroubiToKaroubi
add_to_sga "4 I 8.7.8" "partial" CategoryTheory.Idempotents.instFullKaroubiToKaroubi
add_to_sga "4 I 8.7.8" "special case"
  CategoryTheory.Idempotents.instIsEquivalenceFunctorKaroubiObjWhiskeringLeftToKaroubi
add_to_sga "4 I 8.7.8" "Karoubi C is Karoubian"
  CategoryTheory.Idempotents.instIsIdempotentCompleteKaroubi
add_to_sga "4 I 8.7.8"
  CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent
add_to_sga "4 I 8.7.8" "partial, special case" CategoryTheory.Idempotents.karoubiUniversal₁
add_to_sga "4 I 8.7.8" CategoryTheory.Idempotents.toKaroubi
add_to_sga "4 I 8.7.8" "partial" CategoryTheory.Idempotents.whiskeringLeftObjToKaroubiFullyFaithful
add_to_sga "4 I 8.7.8" CategoryTheory.IsIdempotentComplete
add_to_sga "4 I 8.7.9" "b) (i) ⇒ (ii)" CategoryTheory.instHasColimitsIndOfHasFiniteColimits
add_to_sga "4 I 8.8.1" "partial" CategoryTheory.Limits.functorCategoryHasColimit
add_to_sga "4 I 8.8.1" "partial" CategoryTheory.Limits.instHasFilteredColimitsOfSizeFunctor
add_to_sga "4 I 8.8.1" "partial" CategoryTheory.Limits.isIndObject_colimit
add_to_sga "4 I 8.8.1" "partial" CategoryTheory.Limits.pointwiseIsColimit
add_to_sga "4 I 8.8.1" "partial"
  CategoryTheory.instCreatesColimitsOfShapeIndFunctorOppositeTypeInclusionOfIsFiltered
add_to_sga "4 I 8.8.1" "partial" CategoryTheory.instHasFilteredColimitsInd
add_to_sga "4 I 8.8.1" "partial"
  CategoryTheory.instIsClosedUnderColimitsOfShapeFunctorOppositeTypeIsIndObjectOfIsFiltered
add_to_sga "4 I 8.8.3" "more general" CategoryTheory.CostructuredArrow
add_to_sga "4 I 8.8.4" CategoryTheory.IsFiltered
add_to_sga "4 I 8.8.4" CategoryTheory.Limits.HasFiniteColimits
add_to_sga "4 I 8.8.4" CategoryTheory.Limits.PreservesFiniteColimits
add_to_sga "4 I 8.8.4" "partial" CategoryTheory.Limits.functorCategoryHasColimit
add_to_sga "4 I 8.8.4" "partial" CategoryTheory.Limits.functorCategoryHasColimitsOfShape
add_to_sga "4 I 8.8.4" "partial" CategoryTheory.Limits.instHasFiniteColimitsFunctor
add_to_sga "4 I 8.8.4" "special case" CategoryTheory.Limits.instHasFiniteCoproductsFunctor
add_to_sga "4 I 8.8.4" "partial"
  CategoryTheory.Limits.instPreservesFiniteColimitsFunctorObjEvaluationOfHasFiniteColimits
add_to_sga "4 I 8.8.4" "partial" CategoryTheory.Limits.pointwiseIsColimit
add_to_sga "4 I 8.8.7" Order.Ideal
add_to_sga "4 I 8.8.7" "Injectivity of L₀" OrderEmbedding.supIrredLowerSet
add_to_sga "4 I 8.9.1" "special case" CategoryTheory.Limits.instAB5IndOfHasFiniteLimits
add_to_sga "4 I 8.9.1" "special case"
  CategoryTheory.Limits.instHasExactColimitsOfShapeIndOfHasFiniteLimits
add_to_sga "4 I 8.9.1" "8.9.1(c)"
  CategoryTheory.Limits.isIndObject_limit_of_discrete_of_hasLimitsOfShape
add_to_sga "4 I 8.9.1" "partial"
  CategoryTheory.instCreatesFiniteLimitsIndFunctorOppositeTypeInclusionOfHasFiniteLimits
add_to_sga "4 I 8.9.1" "partial"
  CategoryTheory.instCreatesLimitsOfShapeIndFunctorOppositeTypeDiscreteInclusionOfHasLimitsOfShape
add_to_sga "4 I 8.9.1" "partial"
  CategoryTheory.instCreatesLimitsOfSizeIndFunctorOppositeTypeInclusionOfHasLimits
add_to_sga "4 I 8.9.1" "8.9.1(c)" CategoryTheory.instHasFiniteLimitsInd
add_to_sga "4 I 8.9.1" "8.9.1(c)" CategoryTheory.instHasLimitsInd
add_to_sga "4 I 8.9.1" "8.9.1(c)" CategoryTheory.instHasLimitsOfShapeDiscreteInd
add_to_sga "4 I 8.9.1" "8.9.1(c), special case"
  CategoryTheory.instHasLimitsOfShapeWalkingParallelPairInd
open CategoryTheory in
add_to_sga "4 I 8.9.1" "8.9.1(c)"
  instIsClosedUnderLimitsOfShapeFunctorOppositeTypeIsIndObjectDiscreteOfHasLimitsOfShape
add_to_sga "4 I 8.9.1" "8.9.1(a), the functor c" CategoryTheory.instPreservesLimitsIndYoneda
add_to_sga "4 I 8.9.1" "d), special case"
  CategoryTheory.instPreservesLimitsOfShapeFunctorIndLimOfFinCategoryOfHasLimitsOfShape
add_to_sga "4 I 8.9.2" "partial"
  CategoryTheory.instCreatesFiniteLimitsIndFunctorOppositeTypeInclusionOfHasFiniteLimits
add_to_sga "4 I 8.9.2" "partial" CategoryTheory.instHasColimitsIndOfHasFiniteColimits
add_to_sga "4 I 8.9.2" "partial" CategoryTheory.instHasFiniteLimitsInd
add_to_sga "4 I 8.9.2" "special case"
  CategoryTheory.instPreservesColimitsOfShapeFunctorIndLimOfFinCategoryOfHasColimitsOfShape
add_to_sga "4 I 8.9.2" "special case"
  CategoryTheory.instPreservesLimitsOfShapeFunctorIndLimOfFinCategoryOfHasLimitsOfShape
add_to_sga "4 I 8.9.3" "partial" CategoryTheory.Limits.isIndObject_limit_of_discrete
add_to_sga "4 I 8.9.3" "partial"
  CategoryTheory.Limits.isIndObject_limit_of_discrete_of_hasLimitsOfShape
add_to_sga "4 I 8.9.3" "partial" CategoryTheory.Limits.isIndObject_pi
add_to_sga "4 I 8.9.3" "special case" CategoryTheory.instHasFiniteLimitsInd
add_to_sga "4 I 8.9.3" "special case" CategoryTheory.instHasLimitsInd
add_to_sga "4 I 8.9.3" "special case" CategoryTheory.instHasLimitsOfShapeDiscreteInd
open CategoryTheory in
add_to_sga "4 I 8.9.3" "special case"
  instIsClosedUnderLimitsOfShapeFunctorOppositeTypeIsIndObjectDiscreteOfHasLimitsOfShape
add_to_sga "4 I 8.9.3" "partial" CategoryTheory.instIsFilteredForall
add_to_sga "4 I 8.9.3" "special case" CategoryTheory.instIsFilteredProd
add_to_sga "4 I 8.9.3" "more general" CategoryTheory.isCardinalFiltered_pi
add_to_sga "4 I 8.9.3" "partial" CategoryTheory.isCardinalFiltered_prod
add_to_sga "4 I 8.9.3" CategoryTheory.pi
add_to_sga "4 I 8.9.4" "(a)" CategoryTheory.Limits.isIndObject_limit_of_discrete
add_to_sga "4 I 8.9.4" "special case"
  CategoryTheory.instPreservesColimitsOfShapeFunctorIndLimOfFinCategoryOfHasColimitsOfShape
add_to_sga "4 I 8.9.4" "special case"
  CategoryTheory.instPreservesLimitsOfShapeFunctorIndLimOfFinCategoryOfHasLimitsOfShape
add_to_sga "4 I 8.9.5" CategoryTheory.instHasColimitsIndOfHasFiniteColimits
add_to_sga "4 I 8.9.5" "Clause b), special case"
  CategoryTheory.instHasColimitsOfShapeDiscreteIndOfFinite
add_to_sga "4 I 8.9.5" CategoryTheory.instHasCoproductsIndOfHasFiniteCoproducts
add_to_sga "4 I 8.9.5" "Clause a)" CategoryTheory.instPreservesFiniteColimitsIndYoneda
add_to_sga "4 I 8.9.6" "Positive clause" CategoryTheory.Limits.isIndObject_colimit
add_to_sga "4 I 8.9.6" "Positive clause"
  CategoryTheory.instCreatesColimitsOfShapeIndFunctorOppositeTypeInclusionOfIsFiltered
add_to_sga "4 I 8.9.6" "Positive clause"
  CategoryTheory.instIsClosedUnderColimitsOfShapeFunctorOppositeTypeIsIndObjectOfIsFiltered
add_to_sga "4 I 8.9.6" "Clause" CategoryTheory.instPreservesFiniteColimitsIndYoneda
add_to_sga "4 I 8.9.9" "special case" CategoryTheory.instAbelianInd
add_to_sga "4 I 8.9.9" "c" CategoryTheory.instHasFiniteBiproductsInd
add_to_sga "4 I 8.9.9" "d" CategoryTheory.instHasFiniteLimitsInd
add_to_sga "4 I 8.9.9" "c" CategoryTheory.instPreadditiveInd
add_to_sga "4 I 8.9.10" "b), special case" CategoryTheory.instHasFiniteLimitsInd
add_to_sga "4 I 8.9.10" "b), special case" CategoryTheory.instHasLimitsInd
add_to_sga "4 I 8.9.10" CategoryTheory.instHasLimitsOfShapeDiscreteInd
add_to_sga "4 I 8.9.11" "partial" CategoryTheory.Ind.isSeparating_range_yoneda
add_to_sga "4 I 8.9.11" "partial" CategoryTheory.Ind.isSeparator_range_yoneda
add_to_sga "4 I 8.10" CategoryTheory.Ind.inclusion.fullyFaithful
add_to_sga "4 I 8.10" CategoryTheory.Ind.yoneda.fullyFaithful
add_to_sga "4 I 8.10" "Faithfulness clause of L"
  CategoryTheory.instFaithfulIndFunctorOppositeTypeInclusion
add_to_sga "4 I 8.10" "Fullness clause of L" CategoryTheory.instFullIndFunctorOppositeTypeInclusion
add_to_sga "4 I 8.10" "Fullness clause of c" CategoryTheory.instFullIndYoneda
add_to_sga "4 I 8.10.10" CategoryTheory.CategoryOfElements.structuredArrowEquivalence
add_to_sga "4 I 8.10.10" CategoryTheory.CategoryOfElements.π
add_to_sga "4 I 8.10.10" CategoryTheory.Functor.Elements
add_to_sga "4 I 8.10.10" CategoryTheory.Functor.Elements.isColimitCoconeπOpCompShrinkYonedaFlip
add_to_sga "4 I 8.10.10" "more general" CategoryTheory.StructuredArrow
add_to_sga "4 I 8.10.10" "more general" CategoryTheory.StructuredArrow.proj
add_to_sga "4 I 8.10.10" CategoryTheory.Functor.Elements.instCategory
add_to_sga "4 I 8.11.6" "special case" CategoryTheory.Adjunction.representableBy
add_to_sga "4 I 8.11.6" "special case" CategoryTheory.Functor.leftAdjointObjIsDefined_of_adjunction
add_to_sga "4 I 8.12.6" CategoryTheory.Limits.IsIndObject
add_to_sga "4 I 8.12.6" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 I 8.12.6" "special case" IsArtinian
add_to_sga "4 I 8.12.6" WellFounded
add_to_sga "4 I 8.12.8" CategoryTheory.Functor.IsRightAdjoint
add_to_sga "4 I 8.12.8" "necessity"
  CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint
add_to_sga "4 I 8.12.8" "necessity" CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint
add_to_sga "4 I 8.12.8" CategoryTheory.Limits.PreservesLimits
add_to_sga "4 I 8.12.8" "sufficiency"
  CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating
add_to_sga "4 I 8.12.9" "partial" CategoryTheory.Sheaf.instHasLimitsOfShape
add_to_sga "4 I 8.12.9" "partial" TopCat.instHasLimitsOfShapeSheaf
add_to_sga "4 I 8.12.9" "partial" TopCat.instHasLimitsOfSizeSheafOfHasLimits
add_to_sga "4 I 8.13.1" CategoryTheory.Limits.HasFilteredColimits
add_to_sga "4 I 8.13.1" CategoryTheory.Limits.HasFilteredColimitsOfSize
add_to_sga "4 I 8.13.3" "more general"
  CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
add_to_sga "4 I 8.13.3" "more general"
  CategoryTheory.Functor.isFinitelyAccessible_iff_preservesFilteredColimits
add_to_sga "4 I 9.0" Cardinal
add_to_sga "4 I 9.0" CategoryTheory.LargeCategory
add_to_sga "4 I 9.0" CategoryTheory.Limits.HasFilteredColimits
add_to_sga "4 I 9.0" CategoryTheory.Limits.HasFilteredColimitsOfSize
add_to_sga "4 I 9.0" CategoryTheory.LocallySmall
add_to_sga "4 I 9.0" CategoryTheory.SmallCategory
add_to_sga "4 I 9.1" "partial" CategoryTheory.IsFiltered
add_to_sga "4 I 9.1" "Clause of 9.1 b)" CategoryTheory.Limits.HasColimitsOfShape
add_to_sga "4 I 9.1" "9.1 a), special case" PartOrdEmb.isCardinalFiltered
add_to_sga "4 I 9.2" "partial" CategoryTheory.Functor.IsAccessible
add_to_sga "4 I 9.2" "Π-accessible functor" CategoryTheory.Functor.IsCardinalAccessible
add_to_sga "4 I 9.2" "special case" CategoryTheory.Functor.IsFinitelyAccessible
add_to_sga "4 I 9.2.1" "special case"
  CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
add_to_sga "4 I 9.2.1" "special case"
  CategoryTheory.Functor.instIsCardinalAccessibleOfPreservesColimitsOfSize
add_to_sga "4 I 9.2.1" "partial" CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint
add_to_sga "4 I 9.2.1" "partial" CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint
add_to_sga "4 I 9.2.1" "special case"
  CategoryTheory.Functor.isFinitelyAccessible_iff_preservesFilteredColimits
add_to_sga "4 I 9.3" CategoryTheory.Functor.hom
add_to_sga "4 I 9.3" CategoryTheory.coyoneda
add_to_sga "4 I 9.6" "(ii), special case" CategoryTheory.Functor.isCardinalAccessible_of_isLimit
add_to_sga "4 I 9.6" "(ii)" CategoryTheory.Limits.instHasFiniteLimitsFunctor
add_to_sga "4 I 9.7" "special case" CategoryTheory.Functor.isCardinalAccessible_of_isLimit
add_to_sga "4 I 9.8" "special case" CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone
add_to_sga "4 I 9.8" "partial" CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone.injective
add_to_sga "4 I 9.8" "partial"
  CategoryTheory.Functor.Accessible.Limits.isColimitMapCocone.surjective
add_to_sga "4 I 9.8" "special case" CategoryTheory.Functor.isCardinalAccessible_of_isLimit
add_to_sga "4 I 9.8" CategoryTheory.Limits.colimitLimitToLimitColimit
add_to_sga "4 I 9.8" CategoryTheory.Limits.colimitLimitToLimitColimitCone
add_to_sga "4 I 9.8" "special case" CategoryTheory.Limits.colimitLimitToLimitColimitCone_iso
add_to_sga "4 I 9.8" "partial" CategoryTheory.Limits.colimitLimitToLimitColimit_surjective
add_to_sga "4 I 9.11" "more general"
  CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
add_to_sga "4 I 9.11" "more general"
  CategoryTheory.Functor.isFinitelyAccessible_iff_preservesFilteredColimits
add_to_sga "4 I 9.12" CategoryTheory.EssentiallySmall
add_to_sga "4 I 9.13.1" "special case" Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT
add_to_sga "4 I 9.20" "(g)" CategoryTheory.Functor.leftKanExtension
add_to_sga "4 I 9.20.1" "more general" CategoryTheory.Sheaf
add_to_sga "4 I 9.21" CategoryTheory.EssentiallySmall
add_to_sga "4 I 9.21" "The hypothesis that p" CategoryTheory.Functor.IsFibered
add_to_sga "4 I 9.21.10" "special case" CategoryTheory.Limits.functorCategoryHasColimit
add_to_sga "4 I 9.21.10" CategoryTheory.Limits.pointwiseCocone
add_to_sga "4 I 9.21.10" "special case" CategoryTheory.Limits.pointwiseIsColimit
add_to_sga "4 I 9.21.15" "special case"
  Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.isColimit
add_to_sga "4 I 9.21.16" "(a), case φ = id"
  Cardinal.SharplyLT.exists_isCardinalFiltered_set_of_exists_cofinal
add_to_sga "4 I 9.25" "more general"
  CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
add_to_sga "4 I 9.25" "more general"
  CategoryTheory.Functor.isFinitelyAccessible_iff_preservesFilteredColimits
add_to_sga "4 I 10.1" CategoryTheory.IsPullback
add_to_sga "4 I 10.1" CategoryTheory.IsPushout
add_to_sga "4 I 10.1" CategoryTheory.Square.IsPushout
add_to_sga "4 I 10.1" "partial" CategoryTheory.Square.IsPushout.op
add_to_sga "4 I 10.3" CategoryTheory.EffectiveEpi
add_to_sga "4 I 10.3" CategoryTheory.EffectiveEpiFamily
add_to_sga "4 I 10.3" "partial" CategoryTheory.EffectiveEpiFamily.hom_ext
add_to_sga "4 I 10.3" CategoryTheory.EffectiveEpiFamilyStruct
add_to_sga "4 I 10.3" CategoryTheory.EffectiveEpiStruct
add_to_sga "4 I 10.3" "singleton family"
  CategoryTheory.EffectiveEpiStruct.isColimitCoforkOfIsPullback
add_to_sga "4 I 10.3" CategoryTheory.Epi
add_to_sga "4 I 10.3" CategoryTheory.MorphismProperty.epimorphisms
add_to_sga "4 I 10.3" CategoryTheory.MorphismProperty.universally
add_to_sga "4 I 10.3" "partial" CategoryTheory.MorphismProperty.universally_le
add_to_sga "4 I 10.3" "partial" CategoryTheory.effectiveEpiFamilyStructSingletonOfEffectiveEpi
add_to_sga "4 I 10.3" "partial" CategoryTheory.effectiveEpiStructOfEffectiveEpiFamilySingleton
add_to_sga "4 I 10.3" CategoryTheory.effectiveEpi_iff_effectiveEpiFamily
add_to_sga "4 I 10.3" "singleton case" CategoryTheory.effectiveEpi_of_kernelPair
add_to_sga "4 I 10.3" CategoryTheory.epi_iff_forall_injective
add_to_sga "4 I 10.3" "partial" CategoryTheory.epi_of_effectiveEpi
add_to_sga "4 I 10.3" "partial" CategoryTheory.instEffectiveEpiFamily
add_to_sga "4 I 10.3" "partial" CategoryTheory.instEffectiveEpiOfEffectiveEpiFamily
add_to_sga "4 I 10.3" "singleton case" CategoryTheory.isColimitCoforkOfEffectiveEpi
add_to_sga "4 I 10.4" CategoryTheory.EffectiveEpi
add_to_sga "4 I 10.4" CategoryTheory.EffectiveEpiFamily
add_to_sga "4 I 10.4" CategoryTheory.EffectiveEpiFamilyStruct
add_to_sga "4 I 10.4" CategoryTheory.MorphismProperty.monomorphisms
add_to_sga "4 I 10.4" CategoryTheory.op_epi_iff
add_to_sga "4 I 10.4" "partial" CategoryTheory.op_epi_of_mono
add_to_sga "4 I 10.4" CategoryTheory.op_mono_iff
add_to_sga "4 I 10.4" "partial" CategoryTheory.op_mono_of_epi
add_to_sga "4 I 10.4" CategoryTheory.unop_epi_iff
add_to_sga "4 I 10.4" "partial" CategoryTheory.unop_epi_of_mono
add_to_sga "4 I 10.4" CategoryTheory.unop_mono_iff
add_to_sga "4 I 10.4" "partial" CategoryTheory.unop_mono_of_epi
add_to_sga "4 I 10.6" CategoryTheory.IsSplitEpi
add_to_sga "4 I 10.6" CategoryTheory.Limits.HasCoequalizer
add_to_sga "4 I 10.6" CategoryTheory.Limits.coequalizer
add_to_sga "4 I 10.6" CategoryTheory.Limits.equalizer
add_to_sga "4 I 10.6" CategoryTheory.Retract
add_to_sga "4 I 10.6" IsIdempotentElem
add_to_sga "4 I 10.7" CategoryTheory.Limits.HasPullbacksAlong
add_to_sga "4 I 10.7" "more general" CategoryTheory.MorphismProperty.HasPullbacksAlong
add_to_sga "4 I 10.7" "more general" CategoryTheory.Presieve.HasPullbacks
add_to_sga "4 I 10.8" "Strict quotient" CategoryTheory.EffectiveEpi
add_to_sga "4 I 10.8" CategoryTheory.Subobject.representative
add_to_sga "4 I 10.8" CategoryTheory.Subobject.representativeIso
add_to_sga "4 I 10.9" CategoryTheory.EquivalenceRelation
add_to_sga "4 I 10.9" CategoryTheory.IsKernelPair
add_to_sga "4 I 10.9" "special case" CategoryTheory.IsKernelPair.equivalenceRelation
add_to_sga "4 I 10.9" "partial" CategoryTheory.IsKernelPair.isReflexivePair
add_to_sga "4 I 10.9" CategoryTheory.Limits.pullback
add_to_sga "4 I 10.9" CategoryTheory.Limits.pullback.fst
add_to_sga "4 I 10.9" CategoryTheory.Limits.pullback.snd
add_to_sga "4 I 10.10" CategoryTheory.EffectiveEquivalenceRelation
add_to_sga "4 I 10.10" "partial" CategoryTheory.EffectiveEquivalenceRelation.isCoequalizer
add_to_sga "4 I 10.10" CategoryTheory.IsEffectiveEquivalenceRelation
add_to_sga "4 I 10.10" CategoryTheory.IsUniversallyEffectiveEquivalenceRelation
add_to_sga "4 I 10.10" CategoryTheory.UniversallyEffectiveEquivalenceRelation
add_to_sga "4 I 10.11" CategoryTheory.Subobject
add_to_sga "4 I 10.11" CategoryTheory.Subobject.mk
add_to_sga "4 I App.Definition1" ZFSet.IsTransitive
add_to_sga "4 I App.Definition2" "special case" Cardinal.IsInaccessible
add_to_sga "4 I App.Definition2" "special case" Cardinal.IsRegular
add_to_sga "4 I App.Definition2" "special case" Cardinal.IsStrongLimit
add_to_sga "4 I App.Definition2" Cardinal.IsStrongPrelimit
add_to_sga "4 I App.Lemma3" exists_seq_forall_proj_of_forall_finite
add_to_sga "4 I App.Lemma3" "more general" nonempty_sections_of_finite_cofiltered_system
add_to_sga "4 I App.Lemma3" "more general" nonempty_sections_of_finite_cofiltered_system.init
add_to_sga "4 I App.Lemma3" "more general" nonempty_sections_of_finite_inverse_system
add_to_sga "4 I App.Proposition12" "more general" Class.mem_asymm
add_to_sga "4 I App.Proposition12" "more general" Class.mem_irrefl
add_to_sga "4 I App.Proposition12" "more general" PSet.mem_asymm
add_to_sga "4 I App.Proposition12" "more general" PSet.mem_irrefl
add_to_sga "4 I App.Proposition12" "more general" ZFSet.mem_asymm
add_to_sga "4 I App.Proposition12" "more general" ZFSet.mem_irrefl
add_to_sga "4 I App.Proposition12" "more general" ZFSet.regularity
