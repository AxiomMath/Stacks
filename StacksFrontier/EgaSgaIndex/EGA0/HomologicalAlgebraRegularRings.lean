module  -- shake: keep-all

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
import Mathlib.Algebra.Colimit.Ring
import Mathlib.Algebra.Exact.Sequence
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Groupoid.Subgroupoid
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Cartesian.Ring
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.RepresentedBy
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.FieldTheory.CardinalEmb
import Mathlib.ModelTheory.Basic
import Mathlib.Order.NonemptyFiniteChains
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Extension.Basic
import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalProperties.InjectiveDimension
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Sheaves.Flasque
import StacksCore.Algebra.Homology.HomologicalBicomplex
import StacksCore.Algebra.Homology.SpectralSequence.EdgeStep
import StacksCore.CategoryTheory.Filtration.GradedExact
import StacksCore.FieldTheory.PurelyInseparable.Basic
import StacksCore.Topology.Noetherian.ConstructiblePreimage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA 0, §§8–17: references registered by name

Declarations realizing numbered items of EGA 0, §8 (representable functors), §9 (constructible
sets), §10 (flat modules), §11 (homological algebra), §12 (cohomology of sheaves), §13
(projective limits in homological algebra), §14 (combinatorial dimension of a topological
space), §15 (regular sequences), §16 (dimension and depth of Noetherian local rings) and §17
(regular rings), from the EGA/SGA concept index, that are not tagged where they are declared:
Mathlib and core declarations without an `add_to_stacks` pointer in this library, and (with
`--draft-only`) those of `StacksCore/`.
Part of the EGA 0 index, split by section.
-/

add_to_ega "0 8.1.1" CategoryTheory.yoneda
add_to_ega "0 8.1.2" CategoryTheory.yoneda
add_to_ega "0 8.1.3" CategoryTheory.MorphismProperty.naturalityProperty
add_to_ega "0 8.1.3" CategoryTheory.NatTrans.mk
add_to_ega "0 8.1.3" "special case" CategoryTheory.yoneda
add_to_ega "0 8.1.3" CategoryTheory.yonedaEquiv
add_to_ega "0 8.1.4" CategoryTheory.coyonedaEquiv
add_to_ega "0 8.1.4" "special case" CategoryTheory.curriedCoyonedaLemma
add_to_ega "0 8.1.4" "small category" CategoryTheory.curriedYonedaLemma
add_to_ega "0 8.1.4" "β ∘ α = id" CategoryTheory.map_yonedaEquiv
add_to_ega "0 8.1.4" "β ∘ α = id" CategoryTheory.map_yonedaEquiv'
add_to_ega "0 8.1.4" "more general" CategoryTheory.uliftYonedaEquiv
add_to_ega "0 8.1.4" "partial" CategoryTheory.uliftYonedaEquiv_uliftYoneda_map
add_to_ega "0 8.1.4" CategoryTheory.yonedaEquiv
add_to_ega "0 8.1.4" "partial" CategoryTheory.yonedaEquiv_yoneda_map
add_to_ega "0 8.1.4" CategoryTheory.yonedaLemma
add_to_ega "0 8.1.5" "more general" CategoryTheory.Equivalence.fullyFaithfulToEssImage
add_to_ega "0 8.1.5" "partial" CategoryTheory.Functor.EssImageSubcategory
add_to_ega "0 8.1.5" CategoryTheory.Functor.FullyFaithful
add_to_ega "0 8.1.5" CategoryTheory.Functor.FullyFaithful.full
add_to_ega "0 8.1.5" "more general" CategoryTheory.Functor.FullyFaithful.isoEquiv
add_to_ega "0 8.1.5" CategoryTheory.Functor.FullyFaithful.map_surjective
add_to_ega "0 8.1.5" "partial" CategoryTheory.Functor.FullyFaithful.preimageIso
add_to_ega "0 8.1.5" "more general" CategoryTheory.Functor.asEquivalence
add_to_ega "0 8.1.5" "partial" CategoryTheory.Functor.inv
add_to_ega "0 8.1.5" "partial" CategoryTheory.Functor.preimageIso
add_to_ega "0 8.1.5" "partial" CategoryTheory.ObjectProperty.FullSubcategory
add_to_ega "0 8.1.5" CategoryTheory.ObjectProperty.FullSubcategory.category
add_to_ega "0 8.1.5" "partial"
  CategoryTheory.ObjectProperty.instIsEquivalenceFullSubcategoryIsoClosureιOfLE
add_to_ega "0 8.1.5" "more general" CategoryTheory.ObjectProperty.isEquivalence_ιOfLE_iff
add_to_ega "0 8.1.5" CategoryTheory.ObjectProperty.isoClosure
add_to_ega "0 8.1.5" "special case" CategoryTheory.Subgroupoid.full
add_to_ega "0 8.1.6" "more general" CategoryTheory.uliftYonedaEquiv_uliftYoneda_map
add_to_ega "0 8.1.6" "more general" CategoryTheory.yonedaEquiv
add_to_ega "0 8.1.6" CategoryTheory.yonedaEquiv_yoneda_map
add_to_ega "0 8.1.6" "special case" SSet.yonedaEquiv_map
add_to_ega "0 8.1.7" "more general" CategoryTheory.GrothendieckTopology.fullyFaithfulUliftYoneda
add_to_ega "0 8.1.7" "faithfulness"
  CategoryTheory.GrothendieckTopology.instFaithfulSheafTypeUliftYoneda
add_to_ega "0 8.1.7" "faithfulness" CategoryTheory.GrothendieckTopology.instFaithfulSheafTypeYoneda
add_to_ega "0 8.1.7" "fullness" CategoryTheory.GrothendieckTopology.instFullSheafTypeYoneda
add_to_ega "0 8.1.7" "more general" CategoryTheory.ULiftYoneda.fullyFaithful
add_to_ega "0 8.1.7" "faithfulness"
  CategoryTheory.ULiftYoneda.instFaithfulFunctorOppositeTypeUliftYoneda
add_to_ega "0 8.1.7" CategoryTheory.Yoneda.fullyFaithful
add_to_ega "0 8.1.7" "faithfulness" CategoryTheory.Yoneda.yoneda_faithful
add_to_ega "0 8.1.7" "fullness" CategoryTheory.Yoneda.yoneda_full
add_to_ega "0 8.1.7" "more general" CategoryTheory.fullyFaithfulShrinkYoneda
add_to_ega "0 8.1.7" CategoryTheory.yoneda
add_to_ega "0 8.1.8" CategoryTheory.Functor.IsRepresentable
add_to_ega "0 8.1.8" CategoryTheory.Functor.IsRepresentable.iff_exists_isRepresentedBy
add_to_ega "0 8.1.8" CategoryTheory.Functor.IsRepresentedBy
add_to_ega "0 8.1.8" CategoryTheory.Functor.IsRepresentedBy.iff_exists_representableBy
add_to_ega "0 8.1.8" CategoryTheory.Functor.IsRepresentedBy.iff_isIso_uliftYonedaEquiv
add_to_ega "0 8.1.8" "partial" CategoryTheory.Functor.IsRepresentedBy.of_isRepresentable
add_to_ega "0 8.1.8" CategoryTheory.Functor.IsRepresentedBy.representableBy
add_to_ega "0 8.1.8" "partial" CategoryTheory.Functor.IsRepresentedBy.representableBy_homEquiv_apply
add_to_ega "0 8.1.8" CategoryTheory.Functor.RepresentableBy
add_to_ega "0 8.1.8" "partial" CategoryTheory.Functor.RepresentableBy.ext
add_to_ega "0 8.1.8" "partial" CategoryTheory.Functor.RepresentableBy.ext_iff
add_to_ega "0 8.1.8" "partial" CategoryTheory.Functor.RepresentableBy.isRepresentedBy
add_to_ega "0 8.1.8" "partial" CategoryTheory.Functor.RepresentableBy.uniqueUpToIso
add_to_ega "0 8.1.8" "partial" CategoryTheory.Yoneda.ext
add_to_ega "0 8.1.8" "partial, special case" CategoryTheory.yonedaEquiv
add_to_ega "0 8.1.9" CategoryTheory.Functor.cones
add_to_ega "0 8.1.9" "partial" CategoryTheory.Limits.Cone
add_to_ega "0 8.1.9" CategoryTheory.Limits.IsLimit
add_to_ega "0 8.1.9" CategoryTheory.Limits.IsLimit.OfNatIso.limitCone
add_to_ega "0 8.1.9" CategoryTheory.Limits.IsLimit.liftConeMorphism
add_to_ega "0 8.1.9" "partial" CategoryTheory.Limits.IsLimit.ofRepresentableBy
add_to_ega "0 8.1.9" "partial" CategoryTheory.Limits.IsLimit.representableBy
add_to_ega "0 8.1.9" CategoryTheory.Limits.Types.Limit.mk
add_to_ega "0 8.1.9" CategoryTheory.Limits.limit
add_to_ega "0 8.1.9" "partial" CategoryTheory.Limits.limit.homIso'
add_to_ega "0 8.1.9" "partial" CategoryTheory.Limits.limit.homIso_hom
add_to_ega "0 8.1.9" "clause 2°" CategoryTheory.Limits.limit.hom_ext
add_to_ega "0 8.1.9" CategoryTheory.Limits.limit.lift
add_to_ega "0 8.1.9" "clause 1°" CategoryTheory.Limits.limit.w
add_to_ega "0 8.1.9" CategoryTheory.Limits.limit.π
add_to_ega "0 8.1.9" "partial" CategoryTheory.cones_obj_map
add_to_ega "0 8.1.9" "special case" InverseSystem
add_to_ega "0 8.1.10" "more general" CategoryTheory.Functor.const
add_to_ega "0 8.1.10" "partial" CategoryTheory.Limits.Concrete.instUniqueToTypeTerminal
add_to_ega "0 8.1.10" CategoryTheory.Limits.IsTerminal
add_to_ega "0 8.1.10" CategoryTheory.Limits.IsTerminal.uniqueUpToIso
add_to_ega "0 8.1.10" CategoryTheory.Limits.Types.constPUnitFunctor
add_to_ega "0 8.1.10" "partial" CategoryTheory.Limits.Types.instUniqueTerminalType
add_to_ega "0 8.1.10" CategoryTheory.Limits.Types.isTerminalEquivUnique
add_to_ega "0 8.1.10" "partial" CategoryTheory.Limits.Types.isTerminalPUnit
add_to_ega "0 8.1.10" "partial" CategoryTheory.Limits.isIso_of_isTerminal
add_to_ega "0 8.1.10" CategoryTheory.Limits.terminal
add_to_ega "0 8.1.10" "partial" CategoryTheory.Limits.terminalIsTerminal
add_to_ega "0 8.1.10" "special case" CategoryTheory.Limits.terminalIsoIsTerminal
add_to_ega "0 8.1.11" "partial" CategoryTheory.Functor.CorepresentableBy
add_to_ega "0 8.1.11" "partial" CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso
add_to_ega "0 8.1.11" CategoryTheory.Functor.IsCorepresentable
add_to_ega "0 8.1.11" CategoryTheory.Functor.hom
add_to_ega "0 8.1.11" "partial" CategoryTheory.Limits.IsColimit.corepresentableBy
add_to_ega "0 8.1.11" CategoryTheory.coyoneda
add_to_ega "0 8.1.11" CategoryTheory.shrinkCoyoneda
add_to_ega "0 8.2.1" "partial" CategoryTheory.FunctorToTypes.binaryProductIso
add_to_ega "0 8.2.1" "partial" CategoryTheory.FunctorToTypes.binaryProductLimit
add_to_ega "0 8.2.1" "partial" CategoryTheory.FunctorToTypes.binaryProductLimitCone
add_to_ega "0 8.2.1" CategoryTheory.FunctorToTypes.prod
add_to_ega "0 8.2.1" "more general" CategoryTheory.NatTrans.app_naturality
add_to_ega "0 8.2.1" "more general" CategoryTheory.NatTrans.app_naturality._to_dual_1
add_to_ega "0 8.2.1" "more general" CategoryTheory.NatTrans.naturality._to_dual_1
add_to_ega "0 8.2.1" "more general" CategoryTheory.NatTrans.naturality_assoc
add_to_ega "0 8.2.1" "more general" CategoryTheory.NatTrans.naturality_assoc._to_dual_1
add_to_ega "0 8.2.2" "special case" CategoryTheory.instIsAddMonHomComp
add_to_ega "0 8.2.2" "special case" CategoryTheory.instIsMonHomComp
add_to_ega "0 8.2.2" "special case" DistribMulActionHom.comp
add_to_ega "0 8.2.2" "special case" FirstOrder.Language.Hom.comp
add_to_ega "0 8.2.2" "special case" InfHom.comp
add_to_ega "0 8.2.2" "special case" MonoidHom.comp
add_to_ega "0 8.2.2" "special case" MulDistribMulActionHom.comp
add_to_ega "0 8.2.2" "special case" MulEquiv
add_to_ega "0 8.2.2" "special case" MulHom
add_to_ega "0 8.2.2" "special case" MulHom.comp
add_to_ega "0 8.2.2" "special case" MulSemiringActionHom.comp
add_to_ega "0 8.2.2" "special case" SupHom.comp
add_to_ega "0 8.2.3" CategoryTheory.AddGrpObj
add_to_ega "0 8.2.3" "Commutative C-rings" CategoryTheory.CommRingObj
add_to_ega "0 8.2.3" CategoryTheory.Grp
add_to_ega "0 8.2.3" CategoryTheory.GrpObj
add_to_ega "0 8.2.3" CategoryTheory.GrpObj.ofRepresentableBy
add_to_ega "0 8.2.3" CategoryTheory.Hom.commRing
add_to_ega "0 8.2.3" CategoryTheory.Hom.group
add_to_ega "0 8.2.3" CategoryTheory.Hom.ring
add_to_ega "0 8.2.3" CategoryTheory.RingObj
add_to_ega "0 8.2.3" CategoryTheory.RingObjCat
add_to_ega "0 8.2.3" CategoryTheory.yonedaAddGrpObj
add_to_ega "0 8.2.3" CategoryTheory.yonedaGrpObj
add_to_ega "0 8.2.3" CategoryTheory.yonedaRingObj
add_to_ega "0 8.2.5" CategoryTheory.Limits.BinaryFan.associator
add_to_ega "0 8.2.5" CategoryTheory.Limits.prod.associator
add_to_ega "0 8.2.6" "partial" inv_mul_cancel_right
add_to_ega "0 8.2.6" "partial" mul_inv_cancel_left
add_to_ega "0 9.1.1" "special case" AlgebraicGeometry.quasiCompact_iff_isSpectralMap
add_to_ega "0 9.1.1" IsRetrocompact
add_to_ega "0 9.1.1" IsRetrocompact_iff_isSpectralMap_subtypeVal
add_to_ega "0 9.1.2" "special case" IsCompact.isConstructible
add_to_ega "0 9.1.2" "partial" IsRetrocompact.isConstructible
add_to_ega "0 9.1.2" Topology.IsConstructible
add_to_ega "0 9.1.2" "partial" Topology.IsConstructible.biInter
add_to_ega "0 9.1.2" "partial" Topology.IsConstructible.compl
add_to_ega "0 9.1.2" "partial" Topology.IsConstructible.iInter
add_to_ega "0 9.1.2" "partial" Topology.IsConstructible.inter
add_to_ega "0 9.1.2" "partial" Topology.IsConstructible.of_compl
add_to_ega "0 9.1.2" "partial" Topology.IsConstructible.sInter
add_to_ega "0 9.1.2" "partial" Topology.IsConstructible.sUnion
add_to_ega "0 9.1.2" "partial" Topology.IsConstructible.union
add_to_ega "0 9.1.2" "partial" Topology.isConstructible_compl
add_to_ega "0 9.1.5" "special case" IsCompact.isConstructible
add_to_ega "0 9.1.5" "partial" IsRetrocompact.isConstructible
add_to_ega "0 9.1.6" "partial" IsCompact.isRetrocompact
add_to_ega "0 9.1.6" "partial" IsRetrocompact.isCompact
add_to_ega "0 9.1.10" "necessity" Topology.IsConstructible.isLocallyConstructible
add_to_ega "0 9.1.11" Topology.IsLocallyConstructible
add_to_ega "0 9.1.12" Topology.IsConstructible.isLocallyConstructible
add_to_ega "0 9.1.12" "more general"
  Topology.IsLocallyConstructible.iff_isConstructible_of_isOpenCover
add_to_ega "0 9.1.12" "more general" Topology.IsLocallyConstructible.inter_of_isOpen_isCompact
add_to_ega "0 9.1.12" Topology.IsLocallyConstructible.isConstructible
add_to_ega "0 9.1.12" "more general"
  Topology.IsLocallyConstructible.isConstructible_of_subset_of_isCompact
add_to_ega "0 9.2.1" "more general" Topology.IsConstructible.preimage
add_to_ega "0 9.2.1" "more general" isConstructibleSet_preimage
add_to_ega "0 10.1.2" "(b) ⇒ (a), special case" Module.free_of_maximalIdeal_rTensor_injective
add_to_ega "0 10.1.2" "special case" Module.free_quotSMulTop_iff_free
add_to_ega "0 10.1.3" "a ⇒ c" Module.Flat.of_free
add_to_ega "0 10.1.3" "(ii): c ⇒ b, c ⇒ b" Module.Flat.projective_of_finitePresentation
add_to_ega "0 10.1.3" "(ii)" Module.freeLocus_eq_univ
add_to_ega "0 10.1.3" "(ii)" Module.freeLocus_eq_univ_iff
add_to_ega "0 10.1.3" "(ii): c ⇒ a, c ⇒ a" Module.free_of_flat_of_finrank_eq
add_to_ega "0 10.1.3" "(ii): c ⇒ a, c ⇒ a" Module.free_of_flat_of_isLocalRing
add_to_ega "0 10.1.3" "(ii): d ⇒ a, d ⇒ a" Module.free_of_maximalIdeal_rTensor_injective
add_to_ega "0 10.2.2" "special case" Module.free_of_flat_of_finrank_eq
add_to_ega "0 10.2.2" "special case" Module.free_of_flat_of_isLocalRing
add_to_ega "0 10.2.3" AdicCompletion
add_to_ega "0 10.2.3" AdicCompletion.instAlgebra
add_to_ega "0 10.2.3" AdicCompletion.module
add_to_ega "0 10.2.3" AdicCompletion.subalgebra
add_to_ega "0 10.2.3" Ideal.adicTopology
add_to_ega "0 10.2.3" UniformSpace.Completion.algebra
add_to_ega "0 10.2.3" UniformSpace.Completion.algebra'
add_to_ega "0 10.2.8" "more general" Module.free_of_flat_of_finrank_eq
add_to_ega "0 10.2.8" "more general" Module.free_of_flat_of_isLocalRing
add_to_ega "0 10.3.1.1" FractionRing
add_to_ega "0 10.3.1.1" Ideal.map
add_to_ega "0 10.3.1.1" "B is a flat A'-module" IsLocalization.flat
add_to_ega "0 10.3.1.1" Localization
add_to_ega "0 10.3.1.1" Localization.AtPrime
add_to_ega "0 10.3.1.1" "B is a local ring" Localization.AtPrime.isLocalRing
add_to_ega "0 10.3.1.1" "B is a flat A-module" Localization.flat
add_to_ega "0 10.3.1.1" Polynomial
add_to_ega "0 10.3.1.1" "partial" Polynomial.residueFieldMapCAlgEquiv
add_to_ega "0 10.3.1.2" AdjoinRoot
add_to_ega "0 10.3.1.2" AdjoinRoot.powerBasis'
add_to_ega "0 10.3.1.2" AdjoinRoot.powerBasisAux'
add_to_ega "0 10.3.1.2" Ideal.IsMaximal
add_to_ega "0 10.3.1.2" IsAdjoinRootMonic.basis
add_to_ega "0 10.3.1.2" IsLocalRing
add_to_ega "0 10.3.1.2" IsLocalRing.ResidueField
add_to_ega "0 10.3.1.2" IsNoetherianRing
add_to_ega "0 10.3.1.2" Module.Finite
add_to_ega "0 10.3.1.2" Module.Flat
add_to_ega "0 10.3.1.2" Module.Free
add_to_ega "0 10.3.1.2" Polynomial.Monic
add_to_ega "0 10.3.1.2" "partial" Polynomial.Monic.finite_adjoinRoot
add_to_ega "0 10.3.1.2" "partial" Polynomial.Monic.finite_quotient
add_to_ega "0 10.3.1.2" "B is a free A-module" Polynomial.Monic.free_adjoinRoot
add_to_ega "0 10.3.1.2" "B is a free A-module" Polynomial.Monic.free_quotient
add_to_ega "0 10.3.1.3" Ideal.map
add_to_ega "0 10.3.1.3" IsLocalHom
add_to_ega "0 10.3.1.3" IsLocalRing
add_to_ega "0 10.3.1.3" IsLocalRing.ResidueField
add_to_ega "0 10.3.1.3" IsLocalRing.maximalIdeal
add_to_ega "0 10.3.1.3" IsNoetherianRing
add_to_ega "0 10.3.1.3" Module.Flat
add_to_ega "0 10.3.1.3" Ring.DirectLimit
add_to_ega "0 10.3.1.4" AdjoinRoot
add_to_ega "0 10.3.1.4" "algebraic successor" AdjoinRoot.isLocalHom_of_monic_of_degree_pos
add_to_ega "0 10.3.1.4" "1°" Field.Emb.Cardinal.filtration_succ
add_to_ega "0 10.3.1.4" "3°: the tower exhausts K" Field.Emb.Cardinal.iSup_adjoin_eq_top
add_to_ega "0 10.3.1.4" Field.Emb.Cardinal.leastExt
add_to_ega "0 10.3.1.4" "special case" IsPurelyInseparable.exists_tower
add_to_ega "0 10.3.1.4" Localization.AtPrime
add_to_ega "0 10.3.1.4" Ring.DirectLimit
add_to_ega "0 11.1.1" "more general" CategoryTheory.CohomologicalSpectralSequence
add_to_ega "0 11.1.1" "(a), special case" CategoryTheory.CohomologicalSpectralSequenceFin
add_to_ega "0 11.1.1" CategoryTheory.E₂CohomologicalSpectralSequence
add_to_ega "0 11.1.1" "(a), special case" CategoryTheory.E₂CohomologicalSpectralSequenceNat
add_to_ega "0 11.1.1" "partial" CategoryTheory.FilteredObject.gr
add_to_ega "0 11.1.1" "more general" CategoryTheory.SpectralSequence
add_to_ega "0 11.1.1" "(a)" HomologicalComplex
add_to_ega "0 11.1.2" "partial" CategoryTheory.SpectralSequence.Hom
add_to_ega "0 11.1.2" "partial" CategoryTheory.SpectralSequence.instCategory
add_to_ega "0 11.1.2" "more general" CategoryTheory.SpectralSequence.isIso_hom_of_GE
add_to_ega "0 11.1.3" CategoryTheory.Filtration.IsExhaustive
add_to_ega "0 11.1.4" CategoryTheory.AB5
add_to_ega "0 11.1.4" CategoryTheory.AB5OfSize
add_to_ega "0 11.1.4" CategoryTheory.HasExactColimitsOfShape
add_to_ega "0 11.1.4" CategoryTheory.Limits.HasFilteredColimits
add_to_ega "0 11.1.4" CategoryTheory.Limits.HasFilteredColimitsOfSize
add_to_ega "0 11.2.1" CategoryTheory.Functor.mapHomologicalComplex
add_to_ega "0 11.2.1" "special case" CategoryTheory.ShortComplex.abCyclesIso
add_to_ega "0 11.2.1" "partial" CategoryTheory.ShortComplex.cycles
add_to_ega "0 11.2.1" "partial" CategoryTheory.ShortComplex.cyclesIsKernel
add_to_ega "0 11.2.1" "partial" CategoryTheory.ShortComplex.cyclesIsoKernel
add_to_ega "0 11.2.1" CategoryTheory.ShortComplex.homology
add_to_ega "0 11.2.1" "special case" CategoryTheory.ShortComplex.moduleCatCyclesIso
add_to_ega "0 11.2.1" ChainComplex
add_to_ega "0 11.2.1" ChainComplex.cochainComplexEquivalence
add_to_ega "0 11.2.1" "Zⁿ of the Hom complex" CochainComplex.HomComplex.Cocycle
add_to_ega "0 11.2.1" "Zⁿ of the Hom complex" CochainComplex.HomComplex.Cocycle.isKernel
add_to_ega "0 11.2.1" "special case" CochainComplex.HomComplex.CohomologyClass
add_to_ega "0 11.2.1" "Bⁿ of the Hom complex" CochainComplex.HomComplex.coboundaries
add_to_ega "0 11.2.1" "Zⁿ of the Hom complex" CochainComplex.HomComplex.cocycle
add_to_ega "0 11.2.1" "special case" CochainComplex.HomComplex.homologyAddEquiv
add_to_ega "0 11.2.1" CochainComplex.of
add_to_ega "0 11.2.1" "special case" CochainComplex.plus
add_to_ega "0 11.2.1" ComplexShape.down
add_to_ega "0 11.2.1" ComplexShape.up
add_to_ega "0 11.2.1" "more general" HomologicalComplex
add_to_ega "0 11.2.1" HomologicalComplex.cycles
add_to_ega "0 11.2.1" HomologicalComplex.cyclesFunctor
add_to_ega "0 11.2.1" "partial" HomologicalComplex.cyclesIsKernel
add_to_ega "0 11.2.1" HomologicalComplex.gradedHomologyFunctor
add_to_ega "0 11.2.1" "partial" HomologicalComplex.iCycles
add_to_ega "0 11.2.1" "more general" HomologicalComplex₂
add_to_ega "0 11.2.1" "partial" HomologicalComplex₂.DoubleComplex
add_to_ega "0 11.2.3" "abutment clause" Homotopy.homologyMap_eq
add_to_ega "0 11.2.4" "special case" instPreservesHomologyFunctorAddCommGrpCatColim
add_to_ega "0 11.3.1" CategoryTheory.Limits.HasCoproducts
add_to_ega "0 11.3.1" "special case" CochainComplex.mapBifunctor
add_to_ega "0 11.3.1" "special case" HomologicalComplex.HasMapBifunctor
add_to_ega "0 11.3.1" "Operator d′" HomologicalComplex.homologyMap
add_to_ega "0 11.3.1" "special case" HomologicalComplex.mapBifunctor.d_eq
add_to_ega "0 11.3.1" HomologicalComplex₂
add_to_ega "0 11.3.1" HomologicalComplex₂.DoubleComplex
add_to_ega "0 11.3.1" "more general" HomologicalComplex₂.HasTotal
add_to_ega "0 11.3.1" "more general" HomologicalComplex₂.d_comm
add_to_ega "0 11.3.1" "partial" HomologicalComplex₂.d₂
add_to_ega "0 11.3.1" "partial" HomologicalComplex₂.d₂_eq'
add_to_ega "0 11.3.1" HomologicalComplex₂.total
add_to_ega "0 11.3.1" "partial" HomologicalComplex₂.totalFunctor
add_to_ega "0 11.3.1" "partial" HomologicalComplex₂.total_d
add_to_ega "0 11.3.1" "partial" HomologicalComplex₂.ι_D₁
add_to_ega "0 11.3.1" "partial" HomologicalComplex₂.ι_D₂
add_to_ega "0 11.3.5" HomologicalComplex.homologyFunctor
add_to_ega "0 11.3.5" HomologicalComplex₂.flip
add_to_ega "0 11.3.5" HomologicalComplex₂.flipFunctor
add_to_ega "0 11.3.5" HomologicalComplex₂.total
add_to_ega "0 11.3.5" HomologicalComplex₂.totalFunctor
add_to_ega "0 11.4.1" CategoryTheory.InjectiveResolution
add_to_ega "0 11.4.1" CategoryTheory.ProjectiveResolution
add_to_ega "0 11.4.2" "special case" CategoryTheory.InjectiveResolution
add_to_ega "0 11.4.2" "special case" CategoryTheory.InjectiveResolution.descHomotopy
add_to_ega "0 11.4.2" "special case" CategoryTheory.InjectiveResolution.instHasInjectiveResolution
add_to_ega "0 11.4.2" "special case" CategoryTheory.InjectiveResolution.instHasInjectiveResolutions
add_to_ega "0 11.4.3" CategoryTheory.Functor.mapHomologicalComplex
add_to_ega "0 11.4.6" "more general" CochainComplex.mapBifunctor
add_to_ega "0 11.4.6" "more general" HomologicalComplex.mapBifunctor
add_to_ega "0 11.5.2.2" "special case" CategoryTheory.InjectiveResolution.homotopyEquiv_hom_ι
add_to_ega "0 11.5.2.4" "special case" CategoryTheory.InjectiveResolution.isoRightDerivedObj
add_to_ega "0 11.6.1" "special case" CategoryTheory.ProjectiveResolution
add_to_ega "0 11.6.1" "special case" CategoryTheory.ProjectiveResolution.instHasProjectiveResolution
add_to_ega "0 11.6.1" "special case"
  CategoryTheory.ProjectiveResolution.instHasProjectiveResolutions
add_to_ega "0 11.6.1" "special case" CategoryTheory.ProjectiveResolution.iso
add_to_ega "0 11.6.1" "special case" CategoryTheory.ProjectiveResolution.of
add_to_ega "0 11.6.1" "special case" CategoryTheory.projectiveResolutions
add_to_ega "0 11.6.1" ChainComplex
add_to_ega "0 11.6.1" ComplexShape.down
add_to_ega "0 11.6.1" "more general" HomologicalComplex
add_to_ega "0 11.6.1" "more general" HomologicalComplex₂
add_to_ega "0 11.6.2" "partial" CategoryTheory.Functor.leftDerived
add_to_ega "0 11.7.1" "more general" HomologicalComplex.instAbelian
add_to_ega "0 11.7.1" HomologicalComplex₂
add_to_ega "0 11.8.1" "more general" AlgebraicTopology.AlternatingFaceMapComplex.obj
add_to_ega "0 11.8.1" "more general" AlgebraicTopology.SSet.singularChainComplexFunctor
add_to_ega "0 11.8.1" "more general" AlgebraicTopology.alternatingFaceMapComplex
add_to_ega "0 11.8.1" "more general" SSet.chainComplex
add_to_ega "0 11.8.1" "more general" SSet.chainComplexFunctor
add_to_ega "0 11.8.2" "partial" TensorProduct.quotientTensorQuotientEquiv
add_to_ega "0 11.8.4" "more general" CategoryTheory.Functor
add_to_ega "0 11.9.1" "special case"
  CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
add_to_ega "0 11.10.2" "special case" Module.sum_neg_one_pow_finrank_eq_zero_of_exact
add_to_ega "0 11.10.2" "special case" Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six
add_to_ega "0 12.1.3" "affine schemes" AlgebraicGeometry.AffineScheme.Γ
add_to_ega "0 12.1.3" "locally ringed spaces" AlgebraicGeometry.LocallyRingedSpace.Γ
add_to_ega "0 12.1.3" "special case" AlgebraicGeometry.Scheme.Hom.app
add_to_ega "0 12.1.3" "scheme morphisms" AlgebraicGeometry.Scheme.Hom.appTop
add_to_ega "0 12.1.7" "partial" TopCat.Presheaf.IsFlasque.pushforward_isFlasque
add_to_ega "0 12.1.7" "partial" TopCat.Sheaf.IsFlasque.pushforward_isFlasque
add_to_ega "0 12.2.1" "partial" AlgebraicGeometry.Scheme.Modules.instAdditivePushforward
add_to_ega "0 12.2.1" "special case" AlgebraicGeometry.Scheme.Modules.pushforward
add_to_ega "0 12.2.1" CategoryTheory.HasInjectiveResolution
add_to_ega "0 12.2.1" CategoryTheory.HasInjectiveResolutions
add_to_ega "0 12.2.1" CategoryTheory.InjectiveResolution
add_to_ega "0 12.3.1" "partial" CategoryTheory.Abelian.extFunctor
add_to_ega "0 12.3.2" CategoryTheory.ShortComplex.ShortExact
add_to_ega "0 12.4.1" "special case" AlgebraicGeometry.Scheme.Modules.instIsGrothendieckAbelian
add_to_ega "0 12.4.1" CategoryTheory.AB5
add_to_ega "0 12.4.1" "special case" instAB5ModuleCat
add_to_ega "0 13.1.1" CategoryTheory.Limits.HasProducts
add_to_ega "0 13.1.1" "special case" CategoryTheory.Subobject.completeSemilatticeInf
add_to_ega "0 13.1.1" CategoryTheory.Subobject.sInf
add_to_ega "0 13.1.2" CategoryTheory.Functor.IsMittagLeffler
add_to_ega "0 13.1.2" "special case" CategoryTheory.Functor.IsMittagLeffler.eq_image_eventualRange
add_to_ega "0 13.1.2" "special case" CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp
add_to_ega "0 13.1.2" "Systems of sets" CategoryTheory.Functor.isMittagLeffler_of_surjective
add_to_ega "0 13.1.2" CategoryTheory.IsArtinianObject
add_to_ega "0 13.1.2" CategoryTheory.isArtinianObject
add_to_ega "0 13.1.2" IsArtinian
add_to_ega "0 13.1.2" "partial" IsArtinian.set_has_minimal
add_to_ega "0 13.1.2" "special case" IsArtinianRing
add_to_ega "0 13.1.2" "Modules" set_has_minimal_iff_artinian
add_to_ega "0 13.2.3" ComplexShape.up
add_to_ega "0 13.5.1" "more general" CategoryTheory.FilteredObject.subQuotShortComplex
add_to_ega "0 13.6.4" CategoryTheory.FilteredObject.gr
add_to_ega "0 13.6.6" "special case" Ideal.Filtration
add_to_ega "0 13.6.6" "special case" IsModuleFiltration
add_to_ega "0 13.6.6" "partial" Module
add_to_ega "0 13.6.6" "partial" ModuleCat.mkOfSMul
add_to_ega "0 14.1.1" LTSeries
add_to_ega "0 14.1.1" PartialOrder.NonemptyFiniteChains
add_to_ega "0 14.1.1" "partial" TopologicalSpace.IrreducibleCloseds
add_to_ega "0 14.1.1" TopologicalSpace.IrreducibleCloseds.instPartialOrder
add_to_ega "0 14.1.4" topologicalKrullDim_subspace_le
add_to_ega "0 14.1.9" "necessity, special case" TopologicalSpace.NoetherianSpace.discrete
add_to_ega "0 14.1.9" "necessity, special case" TopologicalSpace.NoetherianSpace.finite
add_to_ega "0 14.1.9" "sufficiency" topologicalKrullDim_zero_of_discreteTopology
add_to_ega "0 14.1.12" "partial" AlgebraicGeometry.genericPoint_eq_bot_of_affine
add_to_ega "0 14.1.12" "partial" IsDiscreteValuationRing.ringKrullDim_eq_one
add_to_ega "0 14.1.12" "partial" IsLocalRing.isClosed_singleton_closedPoint
add_to_ega "0 14.1.12" PrimeSpectrum.comap
add_to_ega "0 14.1.12" RingHom.prod
add_to_ega "0 14.1.12" "partial" continuous_of_discreteTopology
add_to_ega "0 14.1.12" "dim(X) ≤ 0" topologicalKrullDim_zero_of_discreteTopology
add_to_ega "0 14.2.6" "(i), special case"
  AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
add_to_ega "0 14.2.6" "(i), special case"
  TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
add_to_ega "0 15.1.1" "partial" PolynomialModule
add_to_ega "0 15.1.1" "partial" PolynomialModule.polynomialTensorProductLEquivPolynomialModule
add_to_ega "0 15.1.4" "special case" IsRegular
add_to_ega "0 15.1.4" "special case" IsRightRegular
add_to_ega "0 15.1.4" IsSMulRegular
add_to_ega "0 15.1.13" "special case" Module.Flat.isSMulRegular_of_isRegular
add_to_ega "0 15.1.13" "special case" RingTheory.Sequence.IsRegular.of_faithfullyFlat
add_to_ega "0 15.1.13" "special case"
  RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange
add_to_ega "0 15.1.13" RingTheory.Sequence.IsWeaklyRegular.isWeaklyRegular_lTensor
add_to_ega "0 15.1.13" RingTheory.Sequence.IsWeaklyRegular.isWeaklyRegular_rTensor
add_to_ega "0 15.1.13" "special case" RingTheory.Sequence.IsWeaklyRegular.of_flat
add_to_ega "0 15.1.13" "special case" RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
add_to_ega "0 15.1.14" "special case" IsSMulRegular.of_flat
add_to_ega "0 15.1.14" "forward implication, n=1" IsSMulRegular.of_flat_of_isBaseChange
add_to_ega "0 15.1.14" "special case" Module.Flat.isSMulRegular_of_isRegular
add_to_ega "0 15.1.14" "special case" RingTheory.Sequence.IsRegular.of_faithfullyFlat
add_to_ega "0 15.1.14" "special case"
  RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange
add_to_ega "0 15.1.14" "more general" RingTheory.Sequence.IsWeaklyRegular.isWeaklyRegular_lTensor
add_to_ega "0 15.1.14" "more general" RingTheory.Sequence.IsWeaklyRegular.isWeaklyRegular_rTensor
add_to_ega "0 15.1.14" "forward implication, M=A" RingTheory.Sequence.IsWeaklyRegular.of_flat
add_to_ega "0 15.1.14" RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
add_to_ega "0 15.1.14" "special case" RingTheory.Sequence.IsWeaklyRegular.of_isLocalization
add_to_ega "0 15.1.20" "special case" IsSMulRegular.pow
add_to_ega "0 15.1.21" "a)⇒b)" IsSMulRegular.of_flat
add_to_ega "0 15.1.21" "a)⇒b)" Module.Flat.isSMulRegular_of_isRegular
add_to_ega "0 15.1.21" "a)⇒b)" RingTheory.Sequence.IsRegular.of_faithfullyFlat
add_to_ega "0 15.1.21" "a)⇒b)" RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange
add_to_ega "0 15.1.21" "a)⇒b)" RingTheory.Sequence.IsWeaklyRegular.of_flat
add_to_ega "0 15.1.21" "a)⇒b)" RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
add_to_ega "0 15.2.1" "special case" AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
add_to_ega "0 15.2.1" "partial" MvPolynomial.IsHomogeneous
add_to_ega "0 15.2.1" "partial" MvPolynomial.homogeneousSubmodule
add_to_ega "0 15.2.5" "special case" IsSMulRegular.of_flat
add_to_ega "0 15.2.5" "special case" IsSMulRegular.of_flat_of_isBaseChange
add_to_ega "0 15.2.5" "special case" RingTheory.Sequence.IsRegular.of_faithfullyFlat
add_to_ega "0 15.2.5" "special case" RingTheory.Sequence.IsRegular.of_faithfullyFlat_of_isBaseChange
add_to_ega "0 15.2.5" "special case" RingTheory.Sequence.IsWeaklyRegular.of_flat
add_to_ega "0 15.2.5" "special case" RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
add_to_ega "0 15.2.5" "special case" RingTheory.Sequence.IsWeaklyRegular.of_isLocalization
add_to_ega "0 16.1.1" "Upper bound" IsArtinianRing.instKrullDimLEOfNatNat
add_to_ega "0 16.1.1" "partial" IsDiscreteValuationRing.not_krullDimLE_zero
add_to_ega "0 16.1.1" "local Dedekind domains" IsDiscreteValuationRing.ringKrullDim_eq_one
add_to_ega "0 16.1.1" "partial" IsPrincipalIdealRing.krullDimLE_one
add_to_ega "0 16.1.1" "special case" IsPrincipalIdealRing.ringKrullDim_eq_one
add_to_ega "0 16.1.1" "example k[T]" MvPolynomial.ringKrullDim_of_isNoetherianRing
add_to_ega "0 16.1.1" Order.krullDim
add_to_ega "0 16.1.1" "more general" Order.krullDim_nonneg
add_to_ega "0 16.1.1" "more general" Order.krullDim_nonneg_iff
add_to_ega "0 16.1.1" "example k[T]" Polynomial.ringKrullDim_of_isNoetherianRing
add_to_ega "0 16.1.1" "more general" PrimeSpectrum.pointsEquivIrreducibleCloseds
add_to_ega "0 16.1.1" "partial" Ring.DimensionLEOne.principal_ideal_ring
add_to_ega "0 16.1.1" "partial" isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
add_to_ega "0 16.1.1" "more general" ringKrullDim_eq_bot_iff_subsingleton
add_to_ega "0 16.1.1" "partial" ringKrullDim_eq_zero_of_field
add_to_ega "0 16.1.1" "partial" ringKrullDim_eq_zero_of_isField
add_to_ega "0 16.1.1" "more general" ringKrullDim_nonneg_of_nontrivial
add_to_ega "0 16.1.1" "more general" zero_le_ringKrullDim_iff_nontrivial
add_to_ega "0 16.1.2" "partial" Ideal.isPrime_map_quotientMk_of_isPrime
add_to_ega "0 16.1.2" ringKrullDim_quotient_le
add_to_ega "0 16.1.2" "special case" ringKrullDim_quotient_succ_le_of_nonZeroDivisor
add_to_ega "0 16.1.3" Ideal.height
add_to_ega "0 16.1.3" Ideal.height_eq_inf_minimalPrimes
add_to_ega "0 16.1.3" "S = A \\ p for a prime p" Ideal.height_le_ringKrullDim_of_isPrime
add_to_ega "0 16.1.3" "S = A \\ p for a prime p" Ideal.height_le_ringKrullDim_of_ne_top
add_to_ega "0 16.1.3" "special case" Ideal.sup_isMaximal_height_eq_ringKrullDim
add_to_ega "0 16.1.3" "Local rings" IsLocalRing.maximalIdeal_height_eq_ringKrullDim
add_to_ega "0 16.1.3" "special case" IsLocalization.AtPrime.orderIsoOfPrime
add_to_ega "0 16.1.3" "more general" IsLocalization.orderIsoOfPrime
add_to_ega "0 16.1.3" "dim(A) ≤ sup_m dim(A_m)" Ring.krullDimLE_of_isLocalization_maximal
add_to_ega "0 16.1.5" "special case" Ring.DimensionLEOne.integralClosure
add_to_ega "0 16.1.5" "special case" Ring.DimensionLEOne.isIntegralClosure
add_to_ega "0 16.1.5" "special case" Ring.DimensionLEOne.of_isIntegral
add_to_ega "0 16.1.7" "Supp(M) ⊆ V(Ann(M))" Module.annihilator_le_of_mem_support
add_to_ega "0 16.1.7" "partial" Module.mem_support_iff_of_finite
add_to_ega "0 16.1.7" "partial" Module.supportDim_eq_ringKrullDim_quotient_annihilator
add_to_ega "0 16.1.7" "partial" Module.supportDim_le_ringKrullDim
add_to_ega "0 16.1.7" "special case" Module.supportDim_quotient_eq_ringKrullDim
add_to_ega "0 16.1.7" "special case" Module.supportDim_self_eq_ringKrullDim
add_to_ega "0 16.1.7" Module.support_eq_zeroLocus
add_to_ega "0 16.1.7" "(16.1.7.4) for M = A" Ring.krullDimLE_of_isLocalization_maximal
add_to_ega "0 16.1.10" "special case" IsArtinianRing.tfae
add_to_ega "0 16.1.10" "special case" support_of_supportDim_eq_zero
add_to_ega "0 16.2.1" Ideal.stableFiltration
add_to_ega "0 16.2.3" "M = R" ringKrullDim_le_ringKrullDim_quotient_add_card
add_to_ega "0 16.2.3.1" "more general" LinearMap.ker
add_to_ega "0 16.2.3.1" "clause (ii)"
  Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson
add_to_ega "0 16.2.3.1" "clause (ii)"
  Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
add_to_ega "0 16.2.3.1" "clause (ii)" Module.supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson
add_to_ega "0 16.2.3.1" "clause (ii)" Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
add_to_ega "0 16.2.5" "partial" Ideal.exists_spanRank_eq_and_height_eq
add_to_ega "0 16.2.5" "special case" IsArtinianRing.instKrullDimLEOfNatNat
add_to_ega "0 16.2.5" "special case" instFiniteRingKrullDimOfIsLocalRing
add_to_ega "0 16.2.5" "special case" isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
add_to_ega "0 16.2.5" "lower bound" ringKrullDim_le_ringKrullDim_quotient_add_card
add_to_ega "0 16.2.5" "lower bound" ringKrullDim_le_ringKrullDim_quotient_add_encard
add_to_ega "0 16.2.5" "special case" ringKrullDim_le_spanFinrank_maximalIdeal
add_to_ega "0 16.2.6" ringKrullDim_le_spanFinrank_maximalIdeal
add_to_ega "0 16.3.1" "a ⇒ b" Ideal.exists_finset_card_eq_height_of_isNoetherianRing
add_to_ega "0 16.3.1" "b ⇒ a" Ideal.height_le_card_of_mem_minimalPrimes_span
add_to_ega "0 16.3.1" "b ⇒ a" Ideal.height_le_card_of_mem_minimalPrimes_span_finset
add_to_ega "0 16.3.1" "more general" Ideal.height_le_iff_exists_minimalPrimes
add_to_ega "0 16.3.1" "b ⇒ a with n = 1" Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
add_to_ega "0 16.3.1" "b ⇒ a with a = p" Ideal.height_le_spanFinrank
add_to_ega "0 16.3.1" "b ⇒ a with a = p" Ideal.height_le_spanRank
add_to_ega "0 16.3.1" "b ⇒ a" Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes
add_to_ega "0 16.3.1" "b ⇒ a" Ideal.height_le_spanRank_toENat_of_mem_minimal_primes
add_to_ega "0 16.3.1" Ideal.minimalPrimes
add_to_ega "0 16.3.1" Ideal.minimalPrimes.equivIrreducibleComponents
add_to_ega "0 16.3.1" Ideal.span
add_to_ega "0 16.3.1" "special case" IsLocalRing.maximalIdeal_height_eq_ringKrullDim
add_to_ega "0 16.3.1" Localization.AtPrime
add_to_ega "0 16.3.1" "a = 0" PrimeSpectrum.vanishingIdeal_irreducibleComponents
add_to_ega "0 16.3.1" "a = 0" PrimeSpectrum.vanishingIdeal_mem_minimalPrimes
add_to_ega "0 16.3.1" PrimeSpectrum.zeroLocus
add_to_ega "0 16.3.1" "a = 0" PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents
add_to_ega "0 16.3.1" "a = 0" PrimeSpectrum.zeroLocus_minimalPrimes
add_to_ega "0 16.3.1" irreducibleComponents
add_to_ega "0 16.3.1" "a = 0" minimalPrimes.equivIrreducibleComponents
add_to_ega "0 16.3.2" "more general" Ideal.height_le_iff_exists_minimalPrimes
add_to_ega "0 16.3.2" "sufficiency" Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
add_to_ega "0 16.3.2" "special case"
  Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing
add_to_ega "0 16.3.2" "more general" Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes
add_to_ega "0 16.3.2" "more general" Ideal.height_le_spanRank_toENat_of_mem_minimal_primes
add_to_ega "0 16.3.2" "more general" Ideal.map_height_le_one_of_mem_minimalPrimes
add_to_ega "0 16.3.4" "special case" Module.supportDim_add_length_eq_supportDim_of_isRegular
add_to_ega "0 16.3.4" "special case" Module.supportDim_le_supportDim_quotSMulTop_succ
add_to_ega "0 16.3.4" "more general"
  Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson
add_to_ega "0 16.3.4" "special case"
  Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson
add_to_ega "0 16.3.4" "sufficiency, local case"
  Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
add_to_ega "0 16.3.4" "special case" Module.supportDim_quotSMulTop_succ_eq_supportDim
add_to_ega "0 16.3.4" "special case" Module.supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson
add_to_ega "0 16.3.4" "sufficiency" Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
add_to_ega "0 16.3.4" "special case" ringKrullDim_le_ringKrullDim_quotSMulTop_succ
add_to_ega "0 16.3.4" "special case" ringKrullDim_le_ringKrullDim_quotient_add_card
add_to_ega "0 16.3.4" "special case" ringKrullDim_le_ringKrullDim_quotient_add_encard
add_to_ega "0 16.3.4" "special case" ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
add_to_ega "0 16.3.4" "special case" ringKrullDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson
add_to_ega "0 16.3.4" "special case"
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
add_to_ega "0 16.3.7" "Local ring; k = 1" Module.supportDim_le_supportDim_quotSMulTop_succ
add_to_ega "0 16.3.7" "special case"
  Module.supportDim_le_supportDim_quotSMulTop_succ_of_mem_jacobson
add_to_ega "0 16.3.7" "Local ring; M = A; k = 1" ringKrullDim_le_ringKrullDim_quotSMulTop_succ
add_to_ega "0 16.3.7" "M = A" ringKrullDim_le_ringKrullDim_quotient_add_card
add_to_ega "0 16.3.7" "M = A" ringKrullDim_le_ringKrullDim_quotient_add_encard
add_to_ega "0 16.3.7" "M = A" ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
add_to_ega "0 16.3.7" "M = A"
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
add_to_ega "0 16.3.8" "partial" Ideal.exists_spanRank_eq_and_height_eq
add_to_ega "0 16.4.4" "Vanishing of Ext^i(k" ModuleCat.exists_isRegular_of_exists_subsingleton_ext
add_to_ega "0 16.4.4" "Ext^i(k" ModuleCat.exists_isRegular_tfae
add_to_ega "0 16.4.4" "Ext^i(k" ModuleCat.subsingleton_ext_of_exists_isRegular
add_to_ega "0 16.4.6.4" TrivSqZeroExt
add_to_ega "0 16.4.6.4" "J is the nilradical of A" TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst
add_to_ega "0 16.4.6.4" "partial" TrivSqZeroExt.isNilpotent_inr
add_to_ega "0 16.4.6.4" TrivSqZeroExt.kerIdeal
add_to_ega "0 16.5.9" "dim(M/(x_1" Module.supportDim_add_length_eq_supportDim_of_isRegular
add_to_ega "0 16.5.9" "special case" ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
add_to_ega "0 17.1.1" "(b) ⇔ (c)" IsRegularLocalRing.iff_finrank_cotangentSpace
add_to_ega "0 17.1.2" IsRegularLocalRing
add_to_ega "0 17.1.2" "partial" IsRegularLocalRing.iff_finrank_cotangentSpace
add_to_ega "0 17.1.4" "special case" IsDiscreteValuationRing.TFAE
add_to_ega "0 17.1.4" "(ii)" IsDiscreteValuationRing.ringKrullDim_eq_one
add_to_ega "0 17.1.4" "(ii), special case" IsLocalRing.finrank_CotangentSpace_eq_one_iff
add_to_ega "0 17.1.4" "(i), (ii)"
  IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing
add_to_ega "0 17.1.4" "(iii), special case" PowerSeries.maximalIdeal_eq_span_X
add_to_ega "0 17.1.4" "(i)" ringKrullDim_eq_zero_of_field
add_to_ega "0 17.2.1" "necessity at bound zero" CategoryTheory.Abelian.Ext.eq_zero_of_injective
add_to_ega "0 17.2.1" "necessity at bound zero" CategoryTheory.Abelian.Ext.eq_zero_of_projective
add_to_ega "0 17.2.1" "finite-bound inheritance" CategoryTheory.Retract.hasInjectiveDimensionLT
add_to_ega "0 17.2.1" "finite-bound inheritance" CategoryTheory.Retract.hasProjectiveDimensionLT
add_to_ega "0 17.2.1" "more general" CategoryTheory.Retract.injectiveDimension_le
add_to_ega "0 17.2.1" "dimension inequality" CategoryTheory.Retract.projectiveDimension_le
add_to_ega "0 17.2.1" "special case"
  CategoryTheory.ShortComplex.ShortExact.hasInjectiveDimensionLT_X₃_iff
add_to_ega "0 17.2.1" "partial" CategoryTheory.hasInjectiveDimensionLT_of_enoughProjectives
add_to_ega "0 17.2.1" "partial" CategoryTheory.hasProjectiveDimensionLT_of_enoughInjectives
add_to_ega "0 17.2.1" CategoryTheory.injectiveDimension
add_to_ega "0 17.2.1" "bound n = 0" CategoryTheory.injective_iff_hasInjectiveDimensionLT_one
add_to_ega "0 17.2.1" "necessity at bound zero"
  CategoryTheory.instHasInjectiveDimensionLTOfNatNatOfInjective
add_to_ega "0 17.2.1" "necessity at bound zero"
  CategoryTheory.instHasProjectiveDimensionLTOfNatNatOfProjective
add_to_ega "0 17.2.1" "special case" CategoryTheory.instInjectiveOfHasInjectiveDimensionLTOfNatNat
add_to_ega "0 17.2.1" "special case" CategoryTheory.instProjectiveOfHasProjectiveDimensionLTOfNatNat
add_to_ega "0 17.2.1" CategoryTheory.projectiveDimension
add_to_ega "0 17.2.1" "bound n = 0" CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
add_to_ega "0 17.2.1" "bound n = 0" CategoryTheory.projective_iff_hasProjectiveDimensionLT_one
add_to_ega "0 17.2.1" "special case" Module.Projective.directSum_iff
add_to_ega "0 17.2.1" "free ambient module" Module.Projective.iff_split
add_to_ega "0 17.2.1" "special case" Module.Projective.of_split
add_to_ega "0 17.2.1" "special case" ModuleCat.hasInjectiveDimensionLE_of_quotients
add_to_ega "0 17.2.1" "special case" ModuleCat.hasInjectiveDimensionLT_iff_quotients
add_to_ega "0 17.2.1" "special case" ModuleCat.hasInjectiveDimensionLT_of_quotients
add_to_ega "0 17.2.1" "special case" ModuleCat.hasProjectiveDimensionLT_of_forall_finite
add_to_ega "0 17.2.1" "n = 0" isZero_Ext_succ_of_projective
add_to_ega "0 17.2.2" "(ii), special case"
  CategoryTheory.Functor.isZero_leftDerived_obj_projective_succ
add_to_ega "0 17.2.2" "(ii), special case"
  CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ
add_to_ega "0 17.2.2" "more general" CategoryTheory.injective_iff_hasInjectiveDimensionLT_one
add_to_ega "0 17.2.2" "(i)" CategoryTheory.instHasInjectiveDimensionLTOfNatNatOfInjective
add_to_ega "0 17.2.2" "(i)" CategoryTheory.instHasProjectiveDimensionLTOfNatNatOfProjective
add_to_ega "0 17.2.2" "(i)" CategoryTheory.instInjectiveOfHasInjectiveDimensionLTOfNatNat
add_to_ega "0 17.2.2" "(i)" CategoryTheory.instProjectiveOfHasProjectiveDimensionLTOfNatNat
add_to_ega "0 17.2.2" "(ii), special case" CategoryTheory.isZero_Tor'_succ_of_projective
add_to_ega "0 17.2.2" "(i), special case" CategoryTheory.projectiveDimension_eq_zero_iff
add_to_ega "0 17.2.2" "more general" CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero
add_to_ega "0 17.2.2" "more general" CategoryTheory.projective_iff_hasProjectiveDimensionLT_one
add_to_ega "0 17.2.2" "more general" Module.free_of_flat_of_isLocalRing
add_to_ega "0 17.2.2" "(i)" ModuleCat.projectiveDimension_eq_zero_of_projective
add_to_ega "0 17.2.5" "partial" Module.injective_of_localization_maximal
add_to_ega "0 17.2.5" "partial" Module.injective_of_localization_maximal'
add_to_ega "0 17.2.5" "partial" Module.projective_of_localization_maximal
add_to_ega "0 17.2.5" "partial" Module.projective_of_localization_maximal'
add_to_ega "0 17.2.5" "partial" ModuleCat.hasInjectiveDimensionLE_iff_forall_maximalSpectrum
add_to_ega "0 17.2.5" "partial" ModuleCat.hasInjectiveDimensionLE_iff_forall_primeSpectrum
add_to_ega "0 17.2.5" "partial" ModuleCat.hasProjectiveDimensionLE_iff_forall_maximalSpectrum
add_to_ega "0 17.2.5" "partial" ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum
add_to_ega "0 17.2.5" ModuleCat.injectiveDimension_eq_iSup_localizedModule_maximal
add_to_ega "0 17.2.5" ModuleCat.injectiveDimension_eq_iSup_localizedModule_prime
add_to_ega "0 17.2.5" "partial"
  ModuleCat.injectiveDimension_le_injectiveDimension_of_isLocalizedModule
add_to_ega "0 17.2.5" "partial"
  ModuleCat.instPreservesInjectiveObjectsLocalizationLocalizedModuleFunctorOfIsNoetherianRing
add_to_ega "0 17.2.5" "partial" ModuleCat.localizedModule_hasInjectiveDimensionLE
add_to_ega "0 17.2.5" "partial" ModuleCat.localizedModule_hasProjectiveDimensionLE
add_to_ega "0 17.2.5" ModuleCat.projectiveDimension_eq_iSup_localizedModule_maximal
add_to_ega "0 17.2.5" ModuleCat.projectiveDimension_eq_iSup_localizedModule_prime
add_to_ega "0 17.2.5" "partial"
  ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule
add_to_ega "0 17.2.5" "partial" instProjectiveLocalizationLocalizedModule
add_to_ega "0 17.2.7" ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
add_to_ega "0 17.2.7" "more general"
  ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular
add_to_ega "0 17.2.7" "special case" ModuleCat.projectiveDimension_quotient_eq_length
add_to_ega "0 17.2.8" "(c) ⇒ (b)" CategoryTheory.hasInjectiveDimensionLT_of_enoughProjectives
add_to_ega "0 17.2.8" "(c) ⇒ (a)" CategoryTheory.hasProjectiveDimensionLT_of_enoughInjectives
add_to_ega "0 17.2.8" "special case" ModuleCat.hasProjectiveDimensionLT_of_forall_finite
add_to_ega "0 17.2.14" "partial" ModuleCat.hasInjectiveDimensionLE_iff_forall_primeSpectrum
add_to_ega "0 17.2.14" "partial" ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum
add_to_ega "0 17.2.14" "partial" ModuleCat.injectiveDimension_eq_iSup_localizedModule_prime
add_to_ega "0 17.2.14" "partial" ModuleCat.projectiveDimension_eq_iSup_localizedModule_prime
add_to_ega "0 17.3.1.2" "special case" Ideal.IsMaximal.mem_associatedPrimes_of_isFractionRing
add_to_ega "0 17.3.3" "partial" Algebra.Extension.Cotangent.map
add_to_ega "0 17.3.3" "partial" Ideal.mapCotangent
add_to_ega "0 17.3.6" "For a local ring" IsRegularLocalRing.of_isRegularRing_of_isLocalRing
add_to_ega "0 17.3.6" IsRegularRing
add_to_ega "0 17.3.7" MvPolynomial.isRegularRing_of_isRegularRing
add_to_ega "0 17.3.7" "n = 1" Polynomial.isRegularRing_of_isRegularRing
add_to_ega "0 17.3.8.1" AdicCompletion
