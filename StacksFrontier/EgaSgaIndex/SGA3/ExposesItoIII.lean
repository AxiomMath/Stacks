module  -- shake: keep-all

import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.MonCat.Adjunctions
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.Algebra.Module.Congruence.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Notation.Prod
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Over.OverClass
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Functor.FunctorHom
import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Generator.Presheaf
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Subfunctor.Equalizer
import Mathlib.CategoryTheory.Subfunctor.OfSection
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Submonoid.Centralizer
import Mathlib.GroupTheory.Subsemigroup.Centralizer
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Extension.Basic
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Topology.Sheaves.Abelian
import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 3 references registered by name: Exposés I to III

The `add_to_sga` registrations of SGA 3, Exposés I, II and III, re-exported by
`StacksFrontier.EgaSgaIndex.SGA3`.
-/

add_to_sga "3 I 1.1" CategoryTheory.Functor
add_to_sga "3 I 1.1" CategoryTheory.Functor.IsRepresentable
add_to_sga "3 I 1.1" CategoryTheory.Functor.RepresentableBy
add_to_sga "3 I 1.1" CategoryTheory.Functor.essImage
add_to_sga "3 I 1.1" CategoryTheory.Functor.hom
add_to_sga "3 I 1.1" "injectivity of Hom(X"
  CategoryTheory.GrothendieckTopology.instFaithfulSheafTypeUliftYoneda
add_to_sga "3 I 1.1" "injectivity of Hom(X"
  CategoryTheory.GrothendieckTopology.instFaithfulSheafTypeYoneda
add_to_sga "3 I 1.1" "surjectivity of Hom(X"
  CategoryTheory.GrothendieckTopology.instFullSheafTypeYoneda
add_to_sga "3 I 1.1" "special case" CategoryTheory.GrothendieckTopology.yonedaEquiv
add_to_sga "3 I 1.1" "special case" CategoryTheory.Ind.yoneda.fullyFaithful
add_to_sga "3 I 1.1" "more general" CategoryTheory.Presheaf.freeYonedaHomEquiv
add_to_sga "3 I 1.1" CategoryTheory.ULiftYoneda.fullyFaithful
add_to_sga "3 I 1.1" CategoryTheory.Yoneda.fullyFaithful
add_to_sga "3 I 1.1" "partial" CategoryTheory.Yoneda.yoneda_faithful
add_to_sga "3 I 1.1" "partial" CategoryTheory.Yoneda.yoneda_full
add_to_sga "3 I 1.1" CategoryTheory.fullyFaithfulShrinkYoneda
add_to_sga "3 I 1.1" "faithfulness" CategoryTheory.instFaithfulFunctorOppositeTypeShrinkYoneda
add_to_sga "3 I 1.1" CategoryTheory.yoneda
add_to_sga "3 I 1.1" CategoryTheory.yonedaEquiv
add_to_sga "3 I 1.1" CategoryTheory.yonedaLemma
add_to_sga "3 I 1.1.1" "surjectivity of Hom_D(X" CategoryTheory.ObjectProperty.full_ι
add_to_sga "3 I 1.1.1" "Hom_D(X" CategoryTheory.Yoneda.fullyFaithful
add_to_sga "3 I 1.1.1" "partial" CategoryTheory.Yoneda.yoneda_full
add_to_sga "3 I 1.1.1" "more general" CategoryTheory.yonedaEquiv
add_to_sga "3 I 1.2" "partial, special case"
  CategoryTheory.Functor.Monoidal.RepresentableBy.tensorObj
add_to_sga "3 I 1.2" "more general" CategoryTheory.Functor.isTerminalConst
add_to_sga "3 I 1.2" CategoryTheory.Functor.sections
add_to_sga "3 I 1.2" "more general" CategoryTheory.IsPullback.of_is_product
add_to_sga "3 I 1.2" "more general" CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation
add_to_sga "3 I 1.2" "more general" CategoryTheory.Limits.functorCategoryHasColimit
add_to_sga "3 I 1.2" "special case"
  CategoryTheory.Limits.instPreservesFiniteColimitsFunctorObjEvaluationOfHasFiniteColimits
add_to_sga "3 I 1.2" "more general" CategoryTheory.Limits.pointwiseIsColimit
add_to_sga "3 I 1.2" "partial" CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono
add_to_sga "3 I 1.2" "more general" CategoryTheory.Limits.pullback.isIso_diagonal_iff
add_to_sga "3 I 1.2" "more general" CategoryTheory.MorphismProperty.diagonal_isomorphisms
add_to_sga "3 I 1.2" "more general" CategoryTheory.MorphismProperty.functorCategory_epimorphisms
add_to_sga "3 I 1.2" "more general" CategoryTheory.MorphismProperty.functorCategory_monomorphisms
add_to_sga "3 I 1.2" "more general" CategoryTheory.NatTrans.epi_iff_epi_app
add_to_sga "3 I 1.2" "more general" CategoryTheory.NatTrans.epi_iff_epi_app'
add_to_sga "3 I 1.2" "partial" CategoryTheory.NatTrans.epi_of_epi_app
add_to_sga "3 I 1.2" "more general" CategoryTheory.NatTrans.mono_iff_mono_app
add_to_sga "3 I 1.2" "more general" CategoryTheory.NatTrans.mono_iff_mono_app'
add_to_sga "3 I 1.2" "partial" CategoryTheory.NatTrans.mono_of_mono_app
add_to_sga "3 I 1.2" "special case" CategoryTheory.Sheaf.isTerminalTerminal
add_to_sga "3 I 1.2" CategoryTheory.Sheaf.terminal
add_to_sga "3 I 1.2" "special case" CategoryTheory.Sieve.equalizer_apply
add_to_sga "3 I 1.2" CategoryTheory.Subfunctor
add_to_sga "3 I 1.2" CategoryTheory.Subfunctor.equalizer
add_to_sga "3 I 1.2" CategoryTheory.Subfunctor.equalizer.fork
add_to_sga "3 I 1.2" "more general" CategoryTheory.Subfunctor.equalizer.forkIsLimit
add_to_sga "3 I 1.2" CategoryTheory.Subfunctor.equalizer.ι
add_to_sga "3 I 1.2" "more general" CategoryTheory.Subfunctor.equalizer_obj
add_to_sga "3 I 1.2" "more general" CategoryTheory.Subfunctor.mem_equalizer_iff
add_to_sga "3 I 1.2" CategoryTheory.Subfunctor.mk
add_to_sga "3 I 1.2" "more general" CategoryTheory.constantPresheafAdj
add_to_sga "3 I 1.2" CategoryTheory.coyonedaFunctor_preservesLimits
add_to_sga "3 I 1.2" "each Hom(S" CategoryTheory.coyonedaPreservesLimitsOfShape
add_to_sga "3 I 1.2" "each Hom(S" CategoryTheory.coyoneda_preservesLimit
add_to_sga "3 I 1.2" "each Hom(S" CategoryTheory.coyoneda_preservesLimits
add_to_sga "3 I 1.2" "partial" CategoryTheory.instEpiAppOfFunctor
add_to_sga "3 I 1.2" "partial" CategoryTheory.instMonoAppOfFunctor
add_to_sga "3 I 1.2" "partial"
  CategoryTheory.instPreservesColimitFunctorOppositeTypeObjCoyonedaOpYoneda
add_to_sga "3 I 1.2" "more general"
  CategoryTheory.instPreservesLimitsOfSizeFunctorOppositeTypeShrinkYoneda
add_to_sga "3 I 1.2" "more general" CategoryTheory.mono_iff_isPullback
add_to_sga "3 I 1.2" "more general" CategoryTheory.uliftYonedaFunctor_preservesLimits
add_to_sga "3 I 1.2" CategoryTheory.yonedaFunctor_preservesLimits
add_to_sga "3 I 1.2" "more general" instPreservesLimitsOfShapeSheafTypeYoneda
add_to_sga "3 I 1.2" "more general" limitConeOfTerminalAndPullbacks
add_to_sga "3 I 1.2" "more general" prodIsoPullback
add_to_sga "3 I 1.3" "more general" CategoryTheory.CostructuredArrow.mkIdTerminal
add_to_sga "3 I 1.3" "partial" CategoryTheory.Over.equivalenceOfIsTerminal
add_to_sga "3 I 1.3" CategoryTheory.Over.homMk
add_to_sga "3 I 1.3" "partial" CategoryTheory.Over.instHasTerminal
add_to_sga "3 I 1.3" CategoryTheory.Over.iteratedSliceBackward
add_to_sga "3 I 1.3" "partial" CategoryTheory.Over.iteratedSliceEquiv
add_to_sga "3 I 1.3" CategoryTheory.Over.iteratedSliceForward
add_to_sga "3 I 1.3" CategoryTheory.Over.mk
add_to_sga "3 I 1.3" "partial" CategoryTheory.Over.over_hasTerminal
add_to_sga "3 I 1.3" CategoryTheory.OverClass.asOver
add_to_sga "3 I 1.3" CategoryTheory.OverClass.asOverHom
add_to_sga "3 I 1.3" CategoryTheory.SplitEpi
add_to_sga "3 I 1.3" "partial" CategoryTheory.equivToOverUnit
add_to_sga "3 I 1.3" CategoryTheory.instCategoryOver
add_to_sga "3 I 1.6" CategoryTheory.Over.forget
add_to_sga "3 I 1.6" "special case" CategoryTheory.Over.forgetAdjStar
add_to_sga "3 I 1.6" "partial" CategoryTheory.Over.forget_map
add_to_sga "3 I 1.6" "object clause of i_S" CategoryTheory.Over.forget_obj
add_to_sga "3 I 1.6" "partial" CategoryTheory.Over.instIsLeftAdjointForget
add_to_sga "3 I 1.6" "partial" CategoryTheory.Over.instIsRightAdjointPullback
add_to_sga "3 I 1.6" "p_S is a right adjoint" CategoryTheory.Over.instIsRightAdjointStar
add_to_sga "3 I 1.6" "i_{T/S}" CategoryTheory.Over.iteratedSliceBackward_forget
add_to_sga "3 I 1.6" CategoryTheory.Over.iteratedSliceBackward_forget_forget
add_to_sga "3 I 1.6" CategoryTheory.Over.iteratedSliceForward_forget
add_to_sga "3 I 1.6" CategoryTheory.Over.mapForget_eq
add_to_sga "3 I 1.6" "partial" CategoryTheory.Over.pullbackIsRightAdjoint
add_to_sga "3 I 1.6" "more general" CategoryTheory.Sheaf.over
add_to_sga "3 I 1.6" "partial" CategoryTheory.forgetAdjToOver
add_to_sga "3 I 1.6" "partial" CategoryTheory.forgetAdjToOver.homEquiv_symm
add_to_sga "3 I 1.6.1" "Hom(h_S, F) ≃ F(S)" CategoryTheory.yonedaEquiv
add_to_sga "3 I 1.7" CategoryTheory.Functor.functorHom
add_to_sga "3 I 1.7" CategoryTheory.Functor.functorHomEquiv
add_to_sga "3 I 1.7" "Bijection Hom(E" CategoryTheory.FunctorToTypes.functorHomEquiv
add_to_sga "3 I 1.7" "more general" CategoryTheory.MonoidalClosed.internalHom
add_to_sga "3 I 1.7" CategoryTheory.presheafHom
add_to_sga "3 I 1.7" "special case" CategoryTheory.presheafHomSectionsEquiv
add_to_sga "3 I 1.7" CategoryTheory.sheafHom
add_to_sga "3 I 1.7" CategoryTheory.sheafHom'
add_to_sga "3 I 1.7.0" CategoryTheory.Functor.Elements.coconeπOpCompShrinkYonedaFlip
add_to_sga "3 I 1.7.0" "component φ_E(S)"
  CategoryTheory.Functor.Elements.coconeπOpCompShrinkYonedaObj
add_to_sga "3 I 1.7.0" CategoryTheory.Functor.Elements.isColimitCoconeπOpCompShrinkYonedaFlip
add_to_sga "3 I 1.7.0" "bijectivity of φ_E(S)"
  CategoryTheory.Functor.Elements.isColimitCoconeπOpCompShrinkYonedaObj
add_to_sga "3 I 1.7.0" "arrow condition" CategoryTheory.OverPresheafAux.MakesOverArrow
add_to_sga "3 I 1.7.0" "hom-sets of C_/E" CategoryTheory.OverPresheafAux.OverArrows
add_to_sga "3 I 1.7.0" CategoryTheory.Presheaf.coconeOfRepresentable
add_to_sga "3 I 1.7.0" CategoryTheory.Presheaf.colimitOfRepresentable
add_to_sga "3 I 1.7.0" "The diagram (V" CategoryTheory.Presheaf.functorToRepresentables
add_to_sga "3 I 1.7.0" CategoryTheory.Presheaf.isColimitTautologicalCocone
add_to_sga "3 I 1.7.0" CategoryTheory.Presheaf.isColimitTautologicalCocone'
add_to_sga "3 I 1.7.0" "partial" CategoryTheory.yonedaEquiv
add_to_sga "3 I 1.7.1" CategoryTheory.Functor.Elements.coconeπOpCompShrinkYonedaFlip
add_to_sga "3 I 1.7.1" CategoryTheory.Functor.Elements.coconeπOpCompShrinkYonedaObj
add_to_sga "3 I 1.7.1" "more general"
  CategoryTheory.Functor.Elements.isColimitCoconeπOpCompShrinkYonedaFlip
add_to_sga "3 I 1.7.1" "partial"
  CategoryTheory.Functor.Elements.isColimitCoconeπOpCompShrinkYonedaObj
add_to_sga "3 I 1.7.1" "more general"
  CategoryTheory.Functor.Elements.shrinkYonedaCompWhiskeringLeftObjπCompColimIso
add_to_sga "3 I 1.7.1" CategoryTheory.MonoidalClosed.curry
add_to_sga "3 I 1.7.1" "more general" CategoryTheory.MonoidalClosed.ihomCurryIso
add_to_sga "3 I 1.7.1" CategoryTheory.MonoidalClosed.uncurry
add_to_sga "3 I 1.7.1" "(a)" CategoryTheory.ParametrizedAdjunction.preservesLimit_flip_obj
add_to_sga "3 I 1.7.1" "(a)" CategoryTheory.ParametrizedAdjunction.preservesLimitsOfShape_flip_obj
add_to_sga "3 I 1.7.1" CategoryTheory.Presheaf.coconeOfRepresentable
add_to_sga "3 I 1.7.1" "more general" CategoryTheory.Presheaf.colimitOfRepresentable
add_to_sga "3 I 1.7.1" CategoryTheory.Presheaf.functorToRepresentables
add_to_sga "3 I 1.7.1" CategoryTheory.Presheaf.isColimitTautologicalCocone
add_to_sga "3 I 1.7.1" "more general" CategoryTheory.Presheaf.isColimitTautologicalCocone'
add_to_sga "3 I 1.7.1" CategoryTheory.denseAtYoneda
add_to_sga "3 I 1.7.2" CategoryTheory.Aut
add_to_sga "3 I 1.7.2" CategoryTheory.End
add_to_sga "3 I 1.7.2" "more general" CategoryTheory.Functor.functorHomEquiv
add_to_sga "3 I 1.7.2" CategoryTheory.Iso
add_to_sga "3 I 1.7.2" CategoryTheory.presheafHom
add_to_sga "3 I 1.7.2" "more general" CategoryTheory.presheafHomSectionsEquiv
add_to_sga "3 I 1.7.2" "more general" CategoryTheory.sheafHomSectionsEquiv
add_to_sga "3 I 1.7.3" "partial" CategoryTheory.internalizeHom
add_to_sga "3 I 1.8" "more general" AlgebraicGeometry.instCoproductsOfShapeDisjointSchemeOfSmall
add_to_sga "3 I 1.8" "more general" AlgebraicGeometry.isEmpty_pullback_sigmaι_of_ne
add_to_sga "3 I 1.8" CategoryTheory.Limits.BinaryCoproductDisjoint
add_to_sga "3 I 1.8" CategoryTheory.Limits.CoproductDisjoint
add_to_sga "3 I 1.8" CategoryTheory.Limits.sigmaConst
add_to_sga "3 I 1.8" "more general" CategoryTheory.Limits.sigmaConstObjCompIso
add_to_sga "3 I 1.8" "more general" CategoryTheory.Limits.sigmaObj
add_to_sga "3 I 2.1.1" CategoryTheory.Functor
add_to_sga "3 I 2.1.1" "more general" CategoryTheory.Functor.addGrpObjObj
add_to_sga "3 I 2.1.1" "more general" CategoryTheory.Functor.grpObjObj
add_to_sga "3 I 2.1.1" "more general" CategoryTheory.Grp.instCartesianMonoidalCategory
add_to_sga "3 I 2.1.1" "more general" CategoryTheory.Grp.instCategory
add_to_sga "3 I 2.1.1" "more general" CategoryTheory.GrpObj
add_to_sga "3 I 2.1.1" "partial" CategoryTheory.Sheaf.isTerminalTerminal
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.AddGrpObj.ofRepresentableBy
add_to_sga "3 I 2.1.2" "partial"
  CategoryTheory.AddGrpObj.ofRepresentableBy_yonedaAddGrpObjRepresentableBy
add_to_sga "3 I 2.1.2" CategoryTheory.Grp
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.Grp.instCartesianMonoidalCategory
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.Grp.instCategory
add_to_sga "3 I 2.1.2" CategoryTheory.GrpObj
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.GrpObj.ofInvertible
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.GrpObj.ofRepresentableBy
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.essImage_yonedaAddGrp
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.essImage_yonedaGrp
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.yonedaAddGrpFullyFaithful
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.yonedaAddGrpObj
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.yonedaAddGrpObjIsoOfRepresentableBy
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.yonedaGrp
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.yonedaGrpFullyFaithful
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.yonedaGrpObj
add_to_sga "3 I 2.1.2" "partial" CategoryTheory.yonedaGrpObjIsoOfRepresentableBy
add_to_sga "3 I 2.2" "additive group case"
  CategoryTheory.AddGrpObj.ofRepresentableBy_yonedaAddGrpObjRepresentableBy
add_to_sga "3 I 2.2" CategoryTheory.GrpObj
add_to_sga "3 I 2.2" "group species" CategoryTheory.GrpObj.ofRepresentableBy
add_to_sga "3 I 2.2" "group case"
  CategoryTheory.GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy
add_to_sga "3 I 2.2" "group structure on Hom(F" CategoryTheory.Hom.group
add_to_sga "3 I 2.2" CategoryTheory.MonObj
add_to_sga "3 I 2.2" "monoid case"
  CategoryTheory.MonObj.ofRepresentableBy_yonedaMonObjRepresentableBy
add_to_sga "3 I 2.2" "partial"
  CategoryTheory.instPreservesLimitsOfSizeFunctorOppositeTypeShrinkYoneda
add_to_sga "3 I 2.2" "partial" CategoryTheory.yonedaAddGrpObj
add_to_sga "3 I 2.2" "partial" CategoryTheory.yonedaFunctor_preservesLimits
add_to_sga "3 I 2.2" "partial" CategoryTheory.yonedaGrpObj
add_to_sga "3 I 2.3.1" "special case" Action.mk
add_to_sga "3 I 2.3.1" "partial" Action.ρAut
add_to_sga "3 I 2.3.1" "partial" CategoryTheory.Hom.mulAction
add_to_sga "3 I 2.3.1" "partial" CategoryTheory.PreGaloisCategory.IsNaturalSMul
add_to_sga "3 I 2.3.1" "partial" CategoryTheory.PreGaloisCategory.toAut
add_to_sga "3 I 2.3.1" "special case" MulAction
add_to_sga "3 I 2.3.1" "partial" MulAction.toEndHom
add_to_sga "3 I 2.3.1" "Final clause" MulAction.toPerm
add_to_sga "3 I 2.3.1" "partial" MulAction.toPermHom
add_to_sga "3 I 2.3.2" "special case" FixedPoints.subgroup
add_to_sga "3 I 2.3.2" "special case" MulAction.fixedPoints
add_to_sga "3 I 2.3.2" "special case" fixedPointsSubAddOfNormal
add_to_sga "3 I 2.3.3" "special case" AddSubgroup.centralizer
add_to_sga "3 I 2.3.3" "special case" AddSubgroup.mem_normalizer_iff_addConj_image_eq
add_to_sga "3 I 2.3.3" "special case" AddSubgroup.mem_normalizer_iff_conj_image_eq
add_to_sga "3 I 2.3.3" "special case" AddSubgroup.mem_normalizer_iff_map_addConj_eq
add_to_sga "3 I 2.3.3" "special case" AddSubgroup.normalizer
add_to_sga "3 I 2.3.3" "special case" ConjAct.stabilizer_eq_centralizer
add_to_sga "3 I 2.3.3" "special case" Subgroup.centralizer
add_to_sga "3 I 2.3.3" "special case" Subgroup.centralizer_eq_comap_stabilizer
add_to_sga "3 I 2.3.3" "special case" Subgroup.conjAct_pointwise_smul_iff
add_to_sga "3 I 2.3.3" "special case" Subgroup.mem_normalizer_iff_conj_image_eq
add_to_sga "3 I 2.3.3" "special case" Subgroup.mem_normalizer_iff_map_conj_eq
add_to_sga "3 I 2.3.3" "special case" Subgroup.normalizer
add_to_sga "3 I 2.3.3.1" "special case" AddAction.stabilizer_finset_singleton
add_to_sga "3 I 2.3.3.1" "special case" AddAction.stabilizer_singleton
add_to_sga "3 I 2.3.3.1" "more general" CategoryTheory.Sheaf.ΓNatIsoSectionsFunctor
add_to_sga "3 I 2.3.3.1" "more general" CategoryTheory.Sheaf.ΓNatIsoSheafSections
add_to_sga "3 I 2.3.3.1" "more general" CategoryTheory.Sheaf.ΓObjEquivSections
add_to_sga "3 I 2.3.3.1" CategoryTheory.Subfunctor.ofSection
add_to_sga "3 I 2.3.3.1" "special case" MulAction.stabilizer_finset_singleton
add_to_sga "3 I 2.3.3.1" "special case" MulAction.stabilizer_singleton
add_to_sga "3 I 2.3.5" "(a), special case" Action.ρAut
add_to_sga "3 I 2.3.5" "Int for ordinary groups" AddAut.addConj
add_to_sga "3 I 2.3.5" "Int for ordinary groups" AddAut.conj
add_to_sga "3 I 2.3.5" "special case" AddSubgroup.centralizer
add_to_sga "3 I 2.3.5" "partial" CategoryTheory.GrpObj.conj
add_to_sga "3 I 2.3.5" "partial" ConjAct.instSMul
add_to_sga "3 I 2.3.5" "(a), special case" DistribMulAction.toAddAut
add_to_sga "3 I 2.3.5" "Int, special case" MulAut.conj
add_to_sga "3 I 2.3.5" "(a), special case" MulDistribMulAction
add_to_sga "3 I 2.3.5" "(a), special case" MulDistribMulAction.toMulAut
add_to_sga "3 I 2.3.5" "(b)" SemidirectProduct
add_to_sga "3 I 2.3.5" "(b) for ordinary groups" SemidirectProduct.instGroup
add_to_sga "3 I 2.3.5" "(b)" SemidirectProduct.instMul
add_to_sga "3 I 2.3.5" "partial" Set.centralizer
add_to_sga "3 I 2.3.5" "special case" Subgroup.centralizer
add_to_sga "3 I 2.3.5" "special case" Subgroup.normalizer
add_to_sga "3 I 2.3.6" "partial" AddCommGroup.center_eq_top
add_to_sga "3 I 2.3.6" "partial" AddGroup.addCommGroupOfCenterEqTop
add_to_sga "3 I 2.3.6" "special case" AddSubgroup.Normal
add_to_sga "3 I 2.3.6" "special case" AddSubgroup.center
add_to_sga "3 I 2.3.6" "partial" AddSubgroup.center_eq_top
add_to_sga "3 I 2.3.6" "special case" AddSubgroup.center_eq_top_iff
add_to_sga "3 I 2.3.6" "special case" AddSubgroup.centralizer_eq_top_iff_subset
add_to_sga "3 I 2.3.6" "Centr(G) = Centr_G(G)" AddSubgroup.centralizer_univ
add_to_sga "3 I 2.3.6" "special case" AddSubgroup.normalizer_eq_top_iff
add_to_sga "3 I 2.3.6" "special case" CommGroup
add_to_sga "3 I 2.3.6" "partial" CommGroup.center_eq_top
add_to_sga "3 I 2.3.6" "partial" Group.commGroupOfCenterEqTop
add_to_sga "3 I 2.3.6" "special case" Subgroup.Normal
add_to_sga "3 I 2.3.6" "special case" Subgroup.center
add_to_sga "3 I 2.3.6" "partial" Subgroup.center_eq_top
add_to_sga "3 I 2.3.6" "special case" Subgroup.center_eq_top_iff
add_to_sga "3 I 2.3.6" "special case" Subgroup.centralizer_eq_top_iff_subset
add_to_sga "3 I 2.3.6" "Centr(G) = Centr_G(G)" Subgroup.centralizer_univ
add_to_sga "3 I 2.3.6" "special case" Subgroup.mem_center_iff
add_to_sga "3 I 2.3.6" "partial" Subgroup.normalizer_eq_top
add_to_sga "3 I 2.3.6" "special case" Subgroup.normalizer_eq_top_iff
add_to_sga "3 I 2.3.6" "special case" Submonoid.centralizer_eq_top_iff_subset
add_to_sga "3 I 2.3.6" "special case" Subsemigroup.centralizer_eq_top_iff_subset
add_to_sga "3 I 2.3.6" "Centr(G) = Centr_G(G)" Subsemigroup.centralizer_univ
add_to_sga "3 I 2.3.6.1" "partial" AddMonoidHom.normal_ker
add_to_sga "3 I 2.3.6.1" "special case" MonoidHom.ker
add_to_sga "3 I 2.3.6.1" "partial" MonoidHom.normal_ker
add_to_sga "3 I 2.3.6.2" "special case" FaithfulSMul
add_to_sga "3 I 2.3.6.2" "special case" FaithfulVAdd
add_to_sga "3 I 2.3.6.2" "special case" faithfulSMul_iff
add_to_sga "3 I 2.3.6.2" "special case" faithfulVAdd_iff
add_to_sga "3 I 2.3.7" "more general" CategoryTheory.RegularMono.ofIsSplitMono
add_to_sga "3 I 2.3.7" "special case" GroupExtension.Splitting.conjAct
add_to_sga "3 I 2.3.7" "special case"
  GroupExtension.Splitting.semidirectProductToGroupExtensionEquiv
add_to_sga "3 I 2.3.7" "special case" SemidirectProduct
add_to_sga "3 I 2.3.7" "special case" SemidirectProduct.instGroup
add_to_sga "3 I 2.3.8" "special case" GroupExtension.Splitting.semidirectProductMulEquiv
add_to_sga "3 I 2.3.8" "special case"
  GroupExtension.Splitting.semidirectProductToGroupExtensionEquiv
add_to_sga "3 I 3.1" PresheafOfModules.instAddCommGroupHom
add_to_sga "3 I 3.1" PresheafOfModules.instPreadditive
add_to_sga "3 I 3.1.1" "special case" LinearMap.quotKerEquivRange
add_to_sga "3 I 3.1.1" "ordinary modules" ModuleCat.abelian
add_to_sga "3 I 3.1.1" "special case" ModuleCat.coprodIsoDirectSum
add_to_sga "3 I 3.1.1" "special case" ModuleCon.quotientKerEquivOfSurjective
add_to_sga "3 I 3.1.1" "abelianity of O-Mod" PresheafOfModules.instAbelian
add_to_sga "3 I 3.1.1" "special case" PresheafOfModules.instIsGrothendieckAbelian
add_to_sga "3 I 3.1.1" "special case" TopCat.instAbelianPresheaf
add_to_sga "3 I 3.1.2" "special case" AddCommGrpCat.enoughInjectives
add_to_sga "3 I 3.1.2" "special case" CommGrpCat.enoughInjectives
add_to_sga "3 I 3.1.2" "special case" ModuleCat.enoughInjectives
add_to_sga "3 I 3.1.2" "special case" instEnoughInjectivesModuleCatInt
add_to_sga "3 I 3.1.2" "special case" instEnoughInjectivesModuleCatOfSmall
add_to_sga "3 I 3.1.3" "more general" CategoryTheory.Functor.const
add_to_sga "3 I 3.2" "special case" Action.instAbelian
add_to_sga "3 I 3.2" "special case" DistribMulAction
add_to_sga "3 I 3.2" DistribMulAction.toLinearEquiv
add_to_sga "3 I 3.2" "special case" Rep.Hom
add_to_sga "3 I 3.2" "special case" Rep.instAddCommGroupHom
add_to_sga "3 I 3.2" "partial" Rep.instPreadditive
add_to_sga "3 I 3.2" "special case" Representation
add_to_sga "3 I 3.2" "special case" Representation.IntertwiningMap
add_to_sga "3 I 3.2" Representation.ofDistribMulAction
add_to_sga "3 I 3.2.1" CategoryTheory.AddGrpObj.ofRepresentableBy
add_to_sga "3 I 3.2.1" CategoryTheory.CommGrpObj.ofRepresentableBy
add_to_sga "3 I 3.2.1" CategoryTheory.GrpObj.ofRepresentableBy
add_to_sga "3 I 3.2.1" "special case" MonoidAlgebra
add_to_sga "3 I 3.2.1" "special case" Rep.equivalenceModuleMonoidAlgebra
add_to_sga "3 I 3.2.1" "special case" Rep.instAbelian
add_to_sga "3 I 3.2.1" "special case"
  Rep.instIsEquivalenceModuleCatMonoidAlgebraOfModuleMonoidAlgebra
add_to_sga "3 I 3.2.1" "special case"
  Rep.instIsEquivalenceModuleCatMonoidAlgebraToModuleMonoidAlgebra
add_to_sga "3 I 3.2.1" "special case" TopCat.instAbelianPresheaf
add_to_sga "3 I 3.2.1" "special case" instAB5ModuleCat
add_to_sga "3 I 3.2.1" "special case" instEnoughInjectivesModuleCatInt
add_to_sga "3 I 3.2.1" "special case" instEnoughInjectivesModuleCatOfSmall
add_to_sga "3 I 4.2" "base Spec ℤ" AlgebraicGeometry.AffineScheme.equivCommRingCat
add_to_sga "3 I 4.2" "base Spec ℤ"
  AlgebraicGeometry.AffineScheme.instIsEquivalenceOppositeCommRingCatOpRightOpΓ
add_to_sga "3 I 4.2" "base Spec ℤ"
  AlgebraicGeometry.AffineScheme.instIsEquivalenceOppositeCommRingCatRightOpΓ
add_to_sga "3 I 4.2" "base Spec ℤ" AlgebraicGeometry.AffineScheme.ΓIsEquiv
add_to_sga "3 I 4.2" AlgebraicGeometry.IsAffineHom
add_to_sga "3 I 4.2" "base Spec ℤ" AlgebraicGeometry.Spec
add_to_sga "3 I 4.2" "affine base" AlgebraicGeometry.algSpec
add_to_sga "3 I 4.2" "partial"
  AlgebraicGeometry.instBialgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfMonObjOverSchemeSpecAsOverOfIsAffine
add_to_sga "3 I 4.2" "partial" AlgebraicGeometry.instCommGrpObjSpecAsOverSpec
add_to_sga "3 I 4.2" "affine base, partial"
  AlgebraicGeometry.instHopfAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfGrpObjOverSchemeSpecAsOverOfIsAffine
add_to_sga "3 I 4.2" "partial"
  AlgebraicGeometry.instIsIsoSchemeAppUnitOppositeCommRingCatAdjunctionOfIsAffine
add_to_sga "3 I 4.2" "partial" AlgebraicGeometry.instMonObjSpecAsOverSpec
add_to_sga "3 I 4.2" AlgebraicGeometry.isAffineHom_iff
add_to_sga "3 I 4.2" "partial" AlgebraicGeometry.mul_spec_asOver_spec_left
add_to_sga "3 I 4.2" "partial" AlgebraicGeometry.one_spec_asOver_spec_left
add_to_sga "3 I 4.2" "affine base" AlgebraicGeometry.specOverSpec
add_to_sga "3 I 4.2" "special case" instHopfAlgebraCarrierUnopCommAlgCatOfGrpObjOpposite
add_to_sga "3 I 4.3.1" "partial" AlgebraicGeometry.Scheme.Γ
add_to_sga "3 I 4.3.2" AddMonoidAlgebra
add_to_sga "3 I 4.3.2" "special case" AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_of
add_to_sga "3 I 4.3.2" "special case" AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one
add_to_sga "3 I 4.3.2" "special case" AddMonoidAlgebra.isGroupLikeElem_of
add_to_sga "3 I 4.3.2" LaurentPolynomial
add_to_sga "3 I 4.3.2" "special case" LaurentPolynomial.instBialgebra
add_to_sga "3 I 4.3.2" "special case" MonoidAlgebra.isGroupLikeElem_iff_mem_range_of
add_to_sga "3 I 4.3.2" "special case" MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one
add_to_sga "3 I 4.3.2" "special case" MonoidAlgebra.isGroupLikeElem_of
add_to_sga "3 I 4.3.2" "special case" MonoidAlgebra.isGroupLikeElem_single_one
add_to_sga "3 I 4.3.3" "special case" AlgebraicGeometry.AffineSpace.SpecIso
add_to_sga "3 I 4.3.3" "special case" AlgebraicGeometry.AffineSpace.instIsAffine
add_to_sga "3 I 4.3.3" "special case" AlgebraicGeometry.AffineSpace.isoOfIsAffine
add_to_sga "3 I 4.3.3" AlgebraicGeometry.Scheme.Γ
add_to_sga "3 I 4.4.1" "partial" AddChar.instAddCommGroup
add_to_sga "3 I 4.4.1" "partial" AddChar.instCommGroup
add_to_sga "3 I 4.4.1" "partial" AlgebraicGeometry.Spec.homEquiv
add_to_sga "3 I 4.4.1" "partial" AlgebraicGeometry.Spec.mapMulEquiv
add_to_sga "3 I 4.4.1" MonoidAlgebra
add_to_sga "3 I 4.4.1" "partial" MonoidAlgebra.lift
add_to_sga "3 I 4.4.1" "partial" MonoidHom.instCommGroup
add_to_sga "3 I 4.4.1" "partial" MulChar.commGroup
add_to_sga "3 I 4.4.2" "special case" AddMonoidAlgebra.instBialgebra
add_to_sga "3 I 4.4.2" "Reverse implication" AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_of
add_to_sga "3 I 4.4.2" "Reverse implication"
  AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one
add_to_sga "3 I 4.4.2" "special case" AddMonoidAlgebra.isGroupLikeElem_of
add_to_sga "3 I 4.4.2" "special case" AddMonoidAlgebra.isGroupLikeElem_single_one
add_to_sga "3 I 4.4.2" "Reverse implication" MonoidAlgebra.isGroupLikeElem_iff_mem_range_of
add_to_sga "3 I 4.4.2" "Reverse implication" MonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one
add_to_sga "3 I 4.4.2" "special case" MonoidAlgebra.isGroupLikeElem_of
add_to_sga "3 I 4.5" "special case" Matrix.GeneralLinearGroup.toLin
add_to_sga "3 I 4.5" "special case" Matrix.GeneralLinearGroup.toLin'
add_to_sga "3 I 4.6.1" AlgebraicGeometry.Scheme.Modules.pullback
add_to_sga "3 I 4.6.1" "special case" AlgebraicGeometry.Scheme.Modules.restrictFunctor
add_to_sga "3 I 4.6.4" "more general" AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
add_to_sga "3 I 4.6.4" "more general" SheafOfModules.PullbackConstruction.adjunction
add_to_sga "3 I 4.6.5" "special case" IsBaseChange.linearMapLeftRight
add_to_sga "3 I 4.6.5" "Affine finite-free case" IsBaseChange.linearMapRight
add_to_sga "3 I 4.6.5" "Affine finite-free case" IsBaseChange.linearMapRightBaseChangeEquiv
add_to_sga "3 I 4.6.5" "special case" Module.FinitePresentation.isBaseChange_map
add_to_sga "3 I 4.6.5" "special case" Module.FinitePresentation.linearEquivMap
add_to_sga "3 I 4.6.5" "special case" Module.isBaseChange_map_of_finite_free
add_to_sga "3 I 4.7.1" "special case" Action.Hom
add_to_sga "3 I 4.7.1" "special case" DistribMulActionHom
add_to_sga "3 I 4.7.1" "special case" Representation
add_to_sga "3 I 4.7.1" "special case" Representation.IntertwiningMap
add_to_sga "3 I 4.7.1.0" "partial" Representation.dual
add_to_sga "3 I 4.7.1.1" AlgebraicGeometry.Scheme.Modules
add_to_sga "3 I 4.7.1.1" "partial" AlgebraicGeometry.Scheme.Modules.instAbelian
add_to_sga "3 I 4.7.1.1" "more general" PresheafOfModules.instAbelian
add_to_sga "3 I 4.7.3" "partial" AddMonoidAlgebra.instBialgebra
add_to_sga "3 I 4.7.3" "partial" DirectSum.decomposeTensorEquiv
add_to_sga "3 I 4.7.3" "special case" DirectSum.tensorDecomposition
add_to_sga "3 I 4.7.3" "partial" MonoidAlgebra.instBialgebra
add_to_sga "3 I 4.7.3" "special case" TensorProduct.directSum
add_to_sga "3 I 4.7.3" "special case" TensorProduct.directSumLeft
add_to_sga "3 I 4.7.3" "special case" TensorProduct.directSumRight
add_to_sga "3 I 5.1" "special case" ContinuousCohomology.d₀kerIso
add_to_sga "3 I 5.1" "special case" ContinuousCohomology.zeroIso
add_to_sga "3 I 5.1" "H^n(G, special case" groupCohomology
add_to_sga "3 I 5.1" "H^0(G, special case" groupCohomology.H0
add_to_sga "3 I 5.1" "H^0(G,F)=Γ(F^G)" groupCohomology.H0Iso
add_to_sga "3 I 5.1" "H^0(G, special case" groupCohomology.H0IsoOfIsTrivial
add_to_sga "3 I 5.1" "standard complex C*(G,F)" groupCohomology.cochainsFunctor
add_to_sga "3 I 5.1" "C^n(G,F)=Hom(G^n,F), n≥0" groupCohomology.cochainsFunctor_obj_X_carrier
add_to_sga "3 I 5.1" "special case" groupCohomology.cochainsFunctor_obj_d
add_to_sga "3 I 5.1" "special case" groupCohomology.cochainsIso₀
add_to_sga "3 I 5.1" "C^1(G,F)=Hom(G,F)" groupCohomology.cochainsIso₁
add_to_sga "3 I 5.1" "boundary formula for n=0" groupCohomology.comp_d₀₁_eq
add_to_sga "3 I 5.1" "boundary formula for n=1" groupCohomology.comp_d₁₂_eq
add_to_sga "3 I 5.1" "boundary formula for n=2" groupCohomology.comp_d₂₃_eq
add_to_sga "3 I 5.1" "boundary formula for n=0" groupCohomology.dArrowIso₀₁
add_to_sga "3 I 5.1" "boundary formula for n=0" groupCohomology.d₀₁
add_to_sga "3 I 5.1" "special case" groupCohomology.d₀₁_comp_d₁₂
add_to_sga "3 I 5.1" "special case" groupCohomology.d₀₁_comp_d₁₂_assoc
add_to_sga "3 I 5.1" "boundary formula for n=1" groupCohomology.d₁₂
add_to_sga "3 I 5.1" "boundary formula for n=2" groupCohomology.d₂₃
add_to_sga "3 I 5.1" "boundary formula for n=0" groupCohomology.eq_d₀₁_comp_inv
add_to_sga "3 I 5.1" "boundary formula for n=1" groupCohomology.eq_d₁₂_comp_inv
add_to_sga "3 I 5.1" "boundary formula for n=1" groupCohomology.eq_d₁₂_comp_inv_assoc
add_to_sga "3 I 5.1" "H^n(G, special case" groupCohomology.functor
add_to_sga "3 I 5.1" "partial" groupCohomology.inhomogeneousCochains
add_to_sga "3 I 5.1" "∂∘∂=0 in all degrees" groupCohomology.inhomogeneousCochains.d_comp_d
add_to_sga "3 I 5.1" "special case" groupCohomology.inhomogeneousCochains.d_def
add_to_sga "3 I 5.1" "special case" inhomogeneousCochains.d
add_to_sga "3 I 5.1" "special case" inhomogeneousCochains.d_hom_apply
add_to_sga "3 I 5.1.1" "special case" groupCohomology.cochainsFunctor_obj_d
add_to_sga "3 I 5.1.1" "special case" groupCohomology.comp_d₁₂_eq
add_to_sga "3 I 5.1.1" "special case" groupCohomology.d₁₂
add_to_sga "3 I 5.1.1" "special case" groupCohomology.eq_d₁₂_comp_inv
add_to_sga "3 I 5.1.1" "special case" groupCohomology.inhomogeneousCochains.d_def
add_to_sga "3 I 5.1.1" "special case" inhomogeneousCochains.d
add_to_sga "3 I 5.1.1" "special case" inhomogeneousCochains.d_hom_apply
add_to_sga "3 I 5.2" "special case" PresheafOfModules.instAbelian
add_to_sga "3 I 5.2" "special case" TopCat.instAbelianPresheaf
add_to_sga "3 I 5.2" "Abelian groups" instEnoughInjectivesModuleCatInt
add_to_sga "3 I 5.2" "special case" instEnoughInjectivesModuleCatOfSmall
add_to_sga "3 I 5.2.0" "special case" ContRepresentation.coind
add_to_sga "3 I 5.2.0" "partial" ContRepresentation.coindV
add_to_sga "3 I 5.2.0" "special case" ContRepresentation.coind_toMonoidHom_apply_apply_coe
add_to_sga "3 I 5.2.0" "special case" Rep.coind
add_to_sga "3 I 5.2.0" "special case" Rep.coind'
add_to_sga "3 I 5.2.0" "Functor E, special case" Rep.coindFunctor
add_to_sga "3 I 5.2.0" "special case" Representation.coind
add_to_sga "3 I 5.2.0" "G-O-module E(P) = Hom(G" Representation.coind'
add_to_sga "3 I 5.2.0" "partial" Representation.coindMap
add_to_sga "3 I 5.2.0" "partial" Representation.coindV
add_to_sga "3 I 5.2.0" "(h), special case" Representation.coind_apply
add_to_sga "3 I 5.2.0.2" "(i)" Rep.resCoindAdjunction
add_to_sga "3 I 5.2.1" "special case" CategoryTheory.DeltaFunctor.isUniversal_of_isZero_injective
add_to_sga "3 I 5.2.1" "special case" groupCohomology.mapShortComplex₁_exact
add_to_sga "3 I 5.2.1" "special case" groupCohomology.mapShortComplex₂_exact
add_to_sga "3 I 5.2.1" "special case" groupCohomology.mapShortComplex₃_exact
add_to_sga "3 I 5.2.1" "special case" groupCohomology.map_cochainsFunctor_eval_shortExact
add_to_sga "3 I 5.2.1" "special case" groupCohomology.map_cochainsFunctor_shortExact
add_to_sga "3 I 5.3" "H^0(G, special case" Rep.FiniteCyclicGroup.groupCohomologyIso₀
add_to_sga "3 I 5.3" "special case" Rep.invariantsFunctor
add_to_sga "3 I 5.3" "special case" Representation.invariants
add_to_sga "3 I 5.3" "Hⁿ(G, special case" groupCohomology
add_to_sga "3 I 5.3" "H⁰(G, special case" groupCohomology.H0Iso
add_to_sga "3 I 5.3" "(f), special case" groupCohomology.d₀₁
add_to_sga "3 I 5.3" "Coalgebra formula for ∂" groupCohomology.inhomogeneousCochains
add_to_sga "3 I 5.3.1.1" CategoryTheory.Adjunction
add_to_sga "3 I 5.3.1.1" "more general" CategoryTheory.Adjunction.mapInjectivePresentation
add_to_sga "3 I 5.3.1.1" CategoryTheory.DeltaFunctor.Effaceable
add_to_sga "3 I 5.3.1.1" CategoryTheory.DeltaFunctor.Effacement
add_to_sga "3 I 5.3.1.1" CategoryTheory.Functor.PreservesInjectiveObjects
add_to_sga "3 I 5.3.1.1" "more general"
  CategoryTheory.IsGrothendieckAbelian.monoMapFactorizationDataRlp
add_to_sga "3 I 5.3.1.1" "partial" Module.Flat.iff_lTensor_injectiveₛ
add_to_sga "3 I 5.3.1.1" "partial" Module.Flat.iff_lTensor_preserves_injective_linearMap
add_to_sga "3 I 5.3.1.1" "partial" Module.Flat.iff_lTensor_preserves_injective_linearMapₛ
add_to_sga "3 I 5.3.1.1" "partial" Module.Flat.iff_rTensor_injectiveₛ
add_to_sga "3 I 5.3.1.1" "partial" Module.Flat.iff_rTensor_preserves_injective_linearMap
add_to_sga "3 I 5.3.1.1" "partial" Module.Flat.iff_rTensor_preserves_injective_linearMapₛ
add_to_sga "3 I 5.3.1.1" ModuleCat.enoughInjectives
add_to_sga "3 I 5.3.1.1" "special case" Rep.resCoindAdjunction
add_to_sga "3 I 5.3.1.1" "5.3.1.1(i), special case" Rep.resIndAdjunction
add_to_sga "3 I 6.2" "(i), special case" DistribMulAction.toLinearEquiv
add_to_sga "3 I 6.2" "(i), special case" DistribMulAction.toLinearEquiv_symm_apply
add_to_sga "3 I 6.3" "special case" Action.HomSubtype
add_to_sga "3 I 6.3" "special case" AddActionHomClass
add_to_sga "3 I 6.3" "partial" CategoryTheory.IsModHom.mulActionHom
add_to_sga "3 I 6.3" "special case" DistribMulActionHomClass
add_to_sga "3 I 6.3" "special case" DistribMulActionSemiHomClass
add_to_sga "3 I 6.3" "special case" LinearMap.intertwiningMap_of_isIntertwiningMap
add_to_sga "3 I 6.3" "special case" MulActionHom
add_to_sga "3 I 6.3" "special case" MulActionHom.mk
add_to_sga "3 I 6.3" "special case" MulActionHomClass
add_to_sga "3 I 6.3" "special case" MulActionSemiHomClass
add_to_sga "3 I 6.3" "special case" Representation.IntertwiningMap
add_to_sga "3 I 6.4" PresheafOfModules.restrictₛₗ
add_to_sga "3 I 6.5.4" "more general" CategoryTheory.Adjunction.homEquiv_apply
add_to_sga "3 I 6.5.4" "more general" CategoryTheory.Adjunction.homEquiv_unit
add_to_sga "3 I 6.8.5" "affine case" Algebra.Extension.tensorCotangentOfFlat
add_to_sga "3 II 1.1" "partial" CategoryTheory.Functor.functorHomEquiv
add_to_sga "3 II 1.3" "partial" CategoryTheory.Hom.addGroup
add_to_sga "3 II 1.3" "partial" CategoryTheory.Hom.commGroup
add_to_sga "3 II 1.3" "partial" CategoryTheory.Hom.mulAction
add_to_sga "3 II 2.1" "special case" DualNumber
add_to_sga "3 II 2.1" "special case" QuadraticAlgebra.instCommRing
add_to_sga "3 II 2.1" "special case" TrivSqZeroExt
add_to_sga "3 II 2.1" "special case" TrivSqZeroExt.algebra'
add_to_sga "3 II 2.1" "special case" TrivSqZeroExt.algebraBase
add_to_sga "3 II 2.1" "special case" TrivSqZeroExt.fstHom
add_to_sga "3 II 2.1" "special case" TrivSqZeroExt.instAlgebra
add_to_sga "3 II 3.9.0.1" AddMonoidHom.coe_mker
add_to_sga "3 II 3.9.0.1" "Clause (a), special case" AddMonoidHom.comap_bot
add_to_sga "3 II 3.9.0.1" IsUnital
add_to_sga "3 II 3.9.0.1" "(a), special case" MonoidHom.coe_ker
add_to_sga "3 II 3.9.0.1" MonoidHom.coe_mker
add_to_sga "3 II 3.9.0.1" "(a), special case" MonoidHom.ker
add_to_sga "3 II 3.9.0.1" MonoidHom.mker
add_to_sga "3 II 3.9.0.1" MulOneClass
add_to_sga "3 II 3.10" "special case" EckmannHilton.addCommMonoid
add_to_sga "3 II 3.10" "special case" EckmannHilton.commGroup
add_to_sga "3 II 3.10" "special case" EckmannHilton.commMonoid
add_to_sga "3 II 3.10" "partial" EckmannHilton.mul
add_to_sga "3 II 3.10" "partial" EckmannHilton.mul_comm
add_to_sga "3 II 3.10" "partial" EckmannHilton.one
add_to_sga "3 II 3.10" "partial" MulHom
add_to_sga "3 II 3.10" Prod.instMul
add_to_sga "3 II 3.14" "partial" DualNumber
add_to_sga "3 II 4.1.2" "special case" MulActionHom.End.equivMulOpposite
add_to_sga "3 II 4.1.2" "special case" MulActionHom.End.mulOppositeEquiv
add_to_sga "3 II 4.2.0" "more general" CategoryTheory.Functor.mapAddGrp
add_to_sga "3 II 4.2.0" "more general" CategoryTheory.Functor.mapGrp
add_to_sga "3 II 4.2.0" "partial" CategoryTheory.Hom.commGroup
add_to_sga "3 II 4.2.0" "partial" CategoryTheory.Hom.group
add_to_sga "3 II 4.2.0.2" "special case" AddCommGrpCat.instAddCommGroupHom
add_to_sga "3 II 4.2.0.2" "special case" MonoidHom.instCommGroup
add_to_sga "3 II 4.2.B" "Clause b), special case" groupCohomology.cocycles₁
add_to_sga "3 II 4.2.B" "Clause b), special case" groupCohomology.mem_cocycles₁_iff
add_to_sga "3 II 4.3.2" "(3)" PresheafOfModules.restrictₛₗ
add_to_sga "3 II 4.3.4" "special case" DualNumber.fst_eq_zero_iff_eps_dvd
add_to_sga "3 II 4.5.1" DualNumber
add_to_sga "3 II 4.5.1" DualNumber.eps
add_to_sga "3 II 4.5.1" "more general" TrivSqZeroExt
add_to_sga "3 II 4.7.1" "special case" DualNumber
add_to_sga "3 II 4.7.1" "partial" DualNumber.eps
add_to_sga "3 II 4.7.1" "partial" DualNumber.eps_mul_eps
add_to_sga "3 II 4.7.1" "partial" DualNumber.eps_pow_two
add_to_sga "3 II 4.11.4" "(c), special case"
  AlgebraicGeometry.instIsClosedImmersionLeftSchemeOneOverSpecOf
add_to_sga "3 II 5.1.1" Module.Dual
add_to_sga "3 II 5.3.0" "partial, special case" LieAlgebra.center
add_to_sga "3 II 5.3.0" "special case" LieModule.maxTrivSubmodule
add_to_sga "3 II 5.3.0" "special case" LieSubalgebra.mem_normalizer_iff
add_to_sga "3 II 5.3.0" "special case" LieSubalgebra.mem_normalizer_iff'
add_to_sga "3 II 5.3.0" "partial" LieSubalgebra.normalizer
add_to_sga "3 II 5.3.0" "special case" LieSubmodule.mem_normalizer
add_to_sga "3 II 5.3.0" "special case" LieSubmodule.normalizer
add_to_sga "3 II 5.3.0" "special case" NonUnitalSubalgebra.coe_centralizer
add_to_sga "3 II 5.3.0" "partial, special case" Subalgebra.centralizer
add_to_sga "3 II 5.3.0" "special case" Subalgebra.coe_centralizer
add_to_sga "3 II 6.2" "partial" AddCommMonCat.free
add_to_sga "3 II 6.2" "Affine case" DualNumber.lift
add_to_sga "3 II 6.5" "Membership condition" mem_nilradical
add_to_sga "3 II 6.5" "Pointwise value Nil(S)" nilradical
add_to_sga "3 III 0.1.3" "more general" CategoryTheory.Adjunction.mapGrp
add_to_sga "3 III 0.1.4" AlgebraicGeometry.Scheme.Modules.pullback
add_to_sga "3 III 0.1.4" "special case" Ideal.map
add_to_sga "3 III 0.1.7" "special case" Algebra.Extension.CotangentSpace.map
add_to_sga "3 III 0.1.7" "special case" Algebra.Extension.infinitesimal
add_to_sga "3 III 0.1.7" "(1), special case" Algebra.Extension.toInfinitesimal
add_to_sga "3 III 0.1.7" "special case" AlgebraicGeometry.AffineScheme.equivCommRingCat
add_to_sga "3 III 0.1.7" "partial" AlgebraicGeometry.IsAffine.of_isPullback
add_to_sga "3 III 0.1.7" "(a)" AlgebraicGeometry.ext_of_isAffine
add_to_sga "3 III 0.1.7" "(a), special case"
  AlgebraicGeometry.instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfOverSpecOfIsAffine
add_to_sga "3 III 0.1.7" "(a), special case"
  AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom
add_to_sga "3 III 0.1.7" "(a), special case"
  AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1
add_to_sga "3 III 0.1.7" "(a), special case" AlgebraicGeometry.instIsOverHomSchemeIsoSpecSpec
add_to_sga "3 III 0.1.7" "0.1.7(b), special case" KaehlerDifferential.map
add_to_sga "3 III 0.1.7" "Square-zero criterion" TrivSqZeroExt.algHom_ext
add_to_sga "3 III 0.1.7" "Square-zero criterion" TrivSqZeroExt.lift
add_to_sga "3 III 0.6" "partial" AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth
add_to_sga "3 III 0.6" "special case" Module.Dual
add_to_sga "3 III 0.6" "special case" Module.FinitePresentation.isBaseChange_map
add_to_sga "3 III 0.12" "special case" KaehlerDifferential.isBaseChange
add_to_sga "3 III 0.13" "partial" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "3 III 0.13" "partial" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "3 III 0.13" "special case"
  AlgebraicGeometry.Scheme.instIsStableUnderBaseChangeFpqcPrecoverage
add_to_sga "3 III 0.13" "special case" CommRingCat.instIsStableUnderCobaseChangeFlat
add_to_sga "3 III 0.13" "special case" Module.Flat.isBaseChange
add_to_sga "3 III 0.13" "special case" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_sga "3 III 0.13" "special case" RingHom.Flat.isStableUnderBaseChange
add_to_sga "3 III 0.13" "special case" RingHom.finitePresentation_isStableUnderBaseChange
add_to_sga "3 III 0.14" "special case"
  Algebra.FormallySmooth.instFinitePresentationKaehlerDifferentialOfEssFiniteType
add_to_sga "3 III 0.14" "partial" Ideal.tensorCotangentEquiv
add_to_sga "3 III 0.17" "partial" AlgebraicGeometry.IsAffine.of_isPullback
add_to_sga "3 III 0.17" "special case" AlgebraicGeometry.instIsAffineFiberOfIsAffineHom
add_to_sga "3 III 0.17" "partial" AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom
add_to_sga "3 III 0.17" "partial" AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1
add_to_sga "3 III 0.17" "partial" AlgebraicGeometry.isAffine_of_isAffineHom
add_to_sga "3 III 1.1" "H^n(G, special case" groupCohomology
add_to_sga "3 III 1.1" "special case" groupCohomology.cochainsFunctor
add_to_sga "3 III 1.1" "special case" groupCohomology.cochainsFunctor_obj_X_carrier
add_to_sga "3 III 1.1" "special case" groupCohomology.cochainsIso₁
add_to_sga "3 III 1.1" "special case" groupCohomology.cochainsIso₂
add_to_sga "3 III 1.1" "special case" groupCohomology.cochainsIso₃
add_to_sga "3 III 1.1" "H^n(G, special case" groupCohomology.functor
add_to_sga "3 III 1.1" "special case" groupCohomology.inhomogeneousCochains
add_to_sga "3 III 1.2.1" "special case" GroupExtension.Splitting.conjAct
add_to_sga "3 III 1.2.1" "special case" GroupExtension.conjAct
add_to_sga "3 III 1.2.1.2" "(E), special case" AddGroupExtension.Splitting
add_to_sga "3 III 1.2.1.2" "more general" CategoryTheory.SplitEpi
add_to_sga "3 III 1.2.1.2" "(E), special case" GroupExtension.Splitting
add_to_sga "3 III 1.2.1.2" "(E)" GroupExtension.Splitting.semidirectProductToGroupExtensionEquiv
add_to_sga "3 III 1.2.1.2" "partial" SemidirectProduct.inr_splitting
add_to_sga "3 III 1.3.1" "special case" AffineEquiv.constVAdd
add_to_sga "3 III 1.3.1" "special case" ContinuousAffineEquiv.constVAdd
add_to_sga "3 III 1.3.1" "partial" MulAut
add_to_sga "3 III 1.3.1" "special case" MulDistribMulAction.toMulAut
add_to_sga "3 III 2.5" "(a), special case" Algebra.FormallySmooth.exists_lift
add_to_sga "3 III 2.5" "partial" AlgebraicGeometry.Scheme.Hom.finitePresentation_appTop
add_to_sga "3 III 2.5" "partial" AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth
add_to_sga "3 III 4.1" AddTorsor
add_to_sga "3 III 4.1" CategoryTheory.Limits.pushout
add_to_sga "3 III 4.5" "partial" CategoryTheory.Sheaf.H'
add_to_sga "3 III 4.5.0" "special case" Ideal.Cotangent
add_to_sga "3 III 4.5.0" "special case" Ideal.Cotangent.smul_eq_zero_of_mem
add_to_sga "3 III 4.6.6" "more general" IsLocalization.flat
add_to_sga "3 III 4.6.6" "more general" Localization.flat
add_to_sga "3 III 4.6.6" "more general" RingHom.Flat.holdsForLocalizationAway
add_to_sga "3 III 4.6.6" "more general" TrivSqZeroExt
add_to_sga "3 III 4.6.6" "more general" TrivSqZeroExt.kerIdeal
add_to_sga "3 III 4.6.6" "more general" TrivSqZeroExt.kerIdeal_sq
add_to_sga "3 III 4.8" "(iii), special case" KaehlerDifferential.cotangentComplexBaseChange
add_to_sga "3 III 4.8" "(iii), special case" KaehlerDifferential.isBaseChange
add_to_sga "3 III 4.8.0" "special case" Ideal.tensorCotangentHom_surjective
add_to_sga "3 III 4.13" "partial" Ideal.Cotangent
add_to_sga "3 III 4.13" "partial" Ideal.tensorCotangentHom_injective_of_flat
add_to_sga "3 III 4.22" "special case" dualTensorHomEquiv
add_to_sga "3 III 4.22" "special case" dualTensorHomEquivOfBasis
add_to_sga "3 III 4.22" "affine base, T = S₀" dualTensorHom_bijective
add_to_sga "3 III 4.35" "more general" CategoryTheory.AddGrpObj.ofIso
add_to_sga "3 III 4.35" "more general" CategoryTheory.GrpObj.ofIso
add_to_sga "3 III 4.35" "more general" CategoryTheory.GrpObj.ofIso_mul
add_to_sga "3 III 4.35" "more general" CategoryTheory.ShortComplex.ShortExact.δ
add_to_sga "3 III 4.38" DualNumber
add_to_sga "3 III 4.38" LieDerivation
add_to_sga "3 III 4.38" LieDerivation.ad
