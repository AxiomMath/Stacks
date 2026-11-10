module  -- shake: keep-all

import Mathlib.Algebra.Category.Ring.EqualizerPushout
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.Torsor.Defs
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Yoneda
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.LocalEpi
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Plus
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
import Mathlib.CategoryTheory.Sites.Sieves.Presieve
import Mathlib.CategoryTheory.Sites.Sieves.Shrink
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Subfunctor.Sieves
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subterminal
import Mathlib.CategoryTheory.Types.Epimorphisms
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Quot
import Mathlib.Order.Setoid.Basic
import Mathlib.Data.Subtype
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.GroupTheory.Congruence.Defs
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Coequalizer
import Mathlib.Logic.Relation
import Mathlib.Order.RelClasses
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.RelIso.Set
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Torsor
import Mathlib.Topology.Constructible
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import StacksCore.CategoryTheory.Presheaf
import StacksCore.RingTheory.PiTensorProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 3 references registered by name: Exposés IV and IX

The `add_to_sga` registrations of SGA 3, Exposés IV and IX (IX sorts after IV in the generator's
order), re-exported by `StacksFrontier.EgaSgaIndex.SGA3`.
-/

add_to_sga "3 IV 1.1" CategoryTheory.Epi
add_to_sga "3 IV 1.1" CategoryTheory.MorphismProperty.epimorphisms
add_to_sga "3 IV 1.1" "more general" CategoryTheory.MorphismProperty.universally
add_to_sga "3 IV 1.1" CategoryTheory.epi_iff_forall_injective
add_to_sga "3 IV 1.2" CategoryTheory.Limits.Cofork.IsColimit.epi
add_to_sga "3 IV 1.2" CategoryTheory.Limits.Cofork.IsColimit.hom_ext
add_to_sga "3 IV 1.2" "more general" CategoryTheory.Limits.IsColimit
add_to_sga "3 IV 1.2" "more general" CategoryTheory.Limits.IsLimit
add_to_sga "3 IV 1.2" CategoryTheory.Limits.coequalizer.cofork
add_to_sga "3 IV 1.2" "(2), special case" CategoryTheory.Limits.coequalizer.hom_ext
add_to_sga "3 IV 1.2" "(2), special case" CategoryTheory.Limits.coequalizer.hom_ext_iff
add_to_sga "3 IV 1.2" "(2), special case" CategoryTheory.Limits.coequalizer.π_epi
add_to_sga "3 IV 1.2" CategoryTheory.Limits.coequalizerIsCoequalizer
add_to_sga "3 IV 1.2" CategoryTheory.Limits.epi_of_isColimit_cofork
add_to_sga "3 IV 1.2" "more general" CategoryTheory.Limits.epi_of_isColimit_parallelFamily
add_to_sga "3 IV 1.2" CategoryTheory.Limits.equalizer.fork
add_to_sga "3 IV 1.2" "(2), special case" CategoryTheory.Limits.map_π_epi
add_to_sga "3 IV 1.2" "(2), special case"
  CategoryTheory.Limits.splitEpiOfIdempotentOfIsColimitCofork
add_to_sga "3 IV 1.2" "more general" CategoryTheory.Limits.wideCoequalizer.π_epi
add_to_sga "3 IV 1.2" CategoryTheory.RegularEpi.epi
add_to_sga "3 IV 1.2" "(2), special case"
  CategoryTheory.ShortComplex.exact_and_epi_g_iff_g_is_cokernel
add_to_sga "3 IV 1.3" CategoryTheory.EffectiveEpi
add_to_sga "3 IV 1.3" "partial" CategoryTheory.EffectiveEpiFamily.hom_ext
add_to_sga "3 IV 1.3" CategoryTheory.EffectiveEpiStruct
add_to_sga "3 IV 1.3" "partial" CategoryTheory.epi_of_effectiveEpi
add_to_sga "3 IV 1.3" "partial" CategoryTheory.strongEpi_of_effectiveEpi
add_to_sga "3 IV 1.4" CategoryTheory.MorphismProperty.IsMultiplicative.instEpimorphisms
add_to_sga "3 IV 1.4" CategoryTheory.epi_comp'
add_to_sga "3 IV 1.4" CategoryTheory.epi_comp_iff_of_epi
add_to_sga "3 IV 1.4" "(a), special case" CategoryTheory.epi_comp_iff_of_isIso
add_to_sga "3 IV 1.4" CategoryTheory.epi_of_epi
add_to_sga "3 IV 1.4" CategoryTheory.epi_of_epi_fac
add_to_sga "3 IV 1.6" "Epimorphism clause" CategoryTheory.Over.epi_homMk
add_to_sga "3 IV 1.11" "partial"
  CategoryTheory.ObjectProperty.instIsStableUnderBaseChangeEpiModSerre
add_to_sga "3 IV 1.11" "partial" CategoryTheory.Types.instIsStableUnderBaseChangeEpimorphismsType
add_to_sga "3 IV 1.12" "more general" CategoryTheory.IsSplitEpi.EffectiveEpi
add_to_sga "3 IV 1.12" CategoryTheory.IsSplitEpi.epi
add_to_sga "3 IV 1.12" CategoryTheory.SplitEpi.epi
add_to_sga "3 IV 1.12" "more general"
  CategoryTheory.effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi
add_to_sga "3 IV 1.12" "more general"
  CategoryTheory.effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi'
add_to_sga "3 IV 1.12" "more general" CategoryTheory.instEffectiveEpiFamilyCompOfIsSplitEpi
add_to_sga "3 IV 1.13" "more general" CategoryTheory.EffectiveEpiFamily
add_to_sga "3 IV 1.13" "more general" CategoryTheory.EffectiveEpiFamilyStruct
add_to_sga "3 IV 1.14" "special case" AlgebraicGeometry.Flat.isIso_of_surjective_of_mono
add_to_sga "3 IV 1.14" CategoryTheory.IsKernelPair.id_of_mono
add_to_sga "3 IV 1.14" "partial" CategoryTheory.IsKernelPair.isIso_of_mono
add_to_sga "3 IV 1.14" "partial" CategoryTheory.IsPullback.isIso_fst_of_mono
add_to_sga "3 IV 1.14" "more general" CategoryTheory.Limits.PullbackCone.fst_eq_snd_of_mono_eq
add_to_sga "3 IV 1.14" "partial" CategoryTheory.Limits.PullbackCone.isIso_fst_of_mono_of_isLimit
add_to_sga "3 IV 1.14" CategoryTheory.Limits.coequalizer.isoTargetOfSelf
add_to_sga "3 IV 1.14" CategoryTheory.Limits.coequalizer.π_of_eq
add_to_sga "3 IV 1.14" CategoryTheory.Limits.coequalizer.π_of_self
add_to_sga "3 IV 1.14" "partial" CategoryTheory.Limits.fst_eq_snd_of_mono_eq
add_to_sga "3 IV 1.14" CategoryTheory.Limits.isIso_colimit_cocone_parallelPair_of_eq
add_to_sga "3 IV 1.14" CategoryTheory.Limits.isIso_colimit_cocone_parallelPair_of_self
add_to_sga "3 IV 1.14" "partial" CategoryTheory.Limits.isIso_fst_of_mono
add_to_sga "3 IV 1.14" "partial" CategoryTheory.Limits.isIso_snd_of_mono
add_to_sga "3 IV 1.14" "more general" CategoryTheory.Limits.pullback_snd_iso_of_left_factors_mono
add_to_sga "3 IV 1.14" "more general" CategoryTheory.Limits.pullback_snd_iso_of_right_factors_mono
add_to_sga "3 IV 1.14" "special case" CategoryTheory.MorphismProperty.diagonal_isomorphisms
add_to_sga "3 IV 1.14" "more general" CategoryTheory.isIso_of_mono_of_strongEpi
add_to_sga "3 IV 1.14" "more general" CategoryTheory.isIso_of_regularEpi_of_mono
add_to_sga "3 IV 1.14" "partial" CategoryTheory.mono_iff_isIso_snd
add_to_sga "3 IV 2.1" "more general" CategoryTheory.Pseudofunctor.toDescentData
add_to_sga "3 IV 2.2" "more general" CategoryTheory.MorphismProperty.HasPullbacks
add_to_sga "3 IV 2.2" "more general" CategoryTheory.Pseudofunctor.bijective_toDescentData_map_iff
add_to_sga "3 IV 2.5" "converse" CategoryTheory.IsKernelPair.cancel_right_of_mono
add_to_sga "3 IV 2.5" "converse" CategoryTheory.IsKernelPair.comp_of_mono
add_to_sga "3 IV 2.5" "partial" CategoryTheory.IsKernelPair.id_of_mono
add_to_sga "3 IV 2.5" "partial" CategoryTheory.IsKernelPair.isIso_of_mono
add_to_sga "3 IV 2.5" "partial" CategoryTheory.IsKernelPair.mono_of_isIso_fst
add_to_sga "3 IV 2.5" "special case" CategoryTheory.IsSubterminal.isIso_diag
add_to_sga "3 IV 2.5" "special case" CategoryTheory.IsSubterminal.isoDiag
add_to_sga "3 IV 2.5" "partial" CategoryTheory.Limits.isIso_fst_of_mono
add_to_sga "3 IV 2.5" "partial" CategoryTheory.Limits.isIso_snd_of_mono
add_to_sga "3 IV 2.5" CategoryTheory.Limits.pullback.diagonal
add_to_sga "3 IV 2.5" "partial" CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono
add_to_sga "3 IV 2.5" CategoryTheory.Limits.pullback.isIso_diagonal_iff
add_to_sga "3 IV 2.5" "cartesian square 2.5.1" CategoryTheory.Limits.pullbackDiagonalMapIso
add_to_sga "3 IV 2.5" "special case" CategoryTheory.MorphismProperty.diagonal_isomorphisms
add_to_sga "3 IV 2.5" "special case" CategoryTheory.isSubterminal_of_isIso_diag
add_to_sga "3 IV 2.5" "more general" CategoryTheory.mono_iff_isPullback
add_to_sga "3 IV 2.6" CategoryTheory.yoneda
add_to_sga "3 IV 3.1.1" CategoryTheory.EquivalenceRelation
add_to_sga "3 IV 3.1.1" "first projection p₁" TypeCat.p₁OfRel
add_to_sga "3 IV 3.1.1" "second projection p₂" TypeCat.p₂OfRel
add_to_sga "3 IV 3.1.2" CategoryTheory.Limits.Cofork
add_to_sga "3 IV 3.1.2" CategoryTheory.Limits.coequalizer
add_to_sga "3 IV 3.1.2" "the quotient map p" CategoryTheory.Limits.coequalizer.condition
add_to_sga "3 IV 3.1.2" "partial" Con.hom_ext
add_to_sga "3 IV 3.1.2" "partial" Con.hom_ext_iff
add_to_sga "3 IV 3.1.2" "partial" Con.lift_unique
add_to_sga "3 IV 3.1.2" "special case" Function.Coequalizer
add_to_sga "3 IV 3.1.2" "special case" Function.Coequalizer.mk
add_to_sga "3 IV 3.1.2" "special case" MulAction.orbitRel.Quotient
add_to_sga "3 IV 3.1.2" "partial" Quot.sound
add_to_sga "3 IV 3.1.2" "special case" Quotient
add_to_sga "3 IV 3.1.2" "partial" Quotient.lift
add_to_sga "3 IV 3.1.2" "partial" Quotient.liftOn
add_to_sga "3 IV 3.1.2" "Quotient map p" Quotient.mk
add_to_sga "3 IV 3.1.2" "Quotient map p" Quotient.mk'
add_to_sga "3 IV 3.1.2" "partial" Quotient.sound
add_to_sga "3 IV 3.1.2" "special case" QuotientAddGroup.leftRel
add_to_sga "3 IV 3.1.2" "special case" QuotientGroup.instHasQuotientSubgroup
add_to_sga "3 IV 3.1.2" "special case" QuotientGroup.leftRel
add_to_sga "3 IV 3.1.2" "partial" RingQuot.lift_unique
add_to_sga "3 IV 3.1.2" "partial" RingQuot.ringQuot_ext
add_to_sga "3 IV 3.1.2" "partial" Setoid.lift_unique
add_to_sga "3 IV 3.1.4" "uniqueness of v" Con.lift_unique
add_to_sga "3 IV 3.1.4" "special case" Quotient.map
add_to_sga "3 IV 3.1.4" "uniqueness of v" Setoid.lift_unique
add_to_sga "3 IV 3.1.6" "more general" CategoryTheory.Limits.coequalizer.desc
add_to_sga "3 IV 3.1.6" "more general" CategoryTheory.Subobject.pullback
add_to_sga "3 IV 3.1.6" "monoids, special case" Con.comapQuotientEquivOfSurj_mk
add_to_sga "3 IV 3.1.6" "partial" Equivalence.comap
add_to_sga "3 IV 3.1.6" "partial" Function.instIsEquivOnFun
add_to_sga "3 IV 3.1.6" "special case" InvImage
add_to_sga "3 IV 3.1.6" "partial" InvImage.equivalence
add_to_sga "3 IV 3.1.6" "partial" IsEquiv.comap
add_to_sga "3 IV 3.1.6" "partial" Order.Preimage.instIsEquiv
add_to_sga "3 IV 3.1.6" "special case" Quotient.map
add_to_sga "3 IV 3.1.6" "types, special case" Quotient.map'_mk
add_to_sga "3 IV 3.1.6" "partial" RelHom.preimage
add_to_sga "3 IV 3.1.6" "special case" Setoid.comap
add_to_sga "3 IV 3.1.6" "special case" Subtype.instSetoid_mathlib
add_to_sga "3 IV 3.1.6" "special case" continuous_quot_map
add_to_sga "3 IV 3.1.6" "special case" preimage_equivalence
add_to_sga "3 IV 3.2.1" "special case" Action.Hom
add_to_sga "3 IV 3.2.1" "special case" Action.mk
add_to_sga "3 IV 3.2.1" "special case" AddAction.orbitRel
add_to_sga "3 IV 3.2.1" "special case" AddAction.orbitRel.Quotient
add_to_sga "3 IV 3.2.1" "(i), special case" IsCancelSMul
add_to_sga "3 IV 3.2.1" "special case" MulAction
add_to_sga "3 IV 3.2.1" "special case" MulAction.orbitRel
add_to_sga "3 IV 3.2.1" "special case" MulAction.orbitRel.Quotient
add_to_sga "3 IV 3.2.1" "special case" QuotientGroup.instHasQuotientSubgroup
add_to_sga "3 IV 3.2.1" "special case" QuotientGroup.leftRel
add_to_sga "3 IV 3.2.1" "special case" QuotientGroup.rightRel
add_to_sga "3 IV 3.2.1" "(i), special case" isCancelSMul_iff_eq_one_of_smul_eq
add_to_sga "3 IV 3.2.2" "special case" SubAddAction.orbitRel_of_subAdd
add_to_sga "3 IV 3.2.2" "(iii)" SubAddAction.vadd'
add_to_sga "3 IV 3.2.2" "special case" SubMulAction.orbitRel_of_subMul
add_to_sga "3 IV 3.2.2" "special case" Subrepresentation.toRepresentation
add_to_sga "3 IV 3.2.3" Quotient.map
add_to_sga "3 IV 3.2.3" "partial" QuotientAddGroup.map_mk
add_to_sga "3 IV 3.2.3" "special case" QuotientGroup.map
add_to_sga "3 IV 3.2.3" "partial" Setoid.lift_unique
add_to_sga "3 IV 3.3.1" CategoryTheory.IsKernelPair
add_to_sga "3 IV 3.3.1" CategoryTheory.IsKernelPair.equivalenceRelation
add_to_sga "3 IV 3.3.1" CategoryTheory.Limits.pullback
add_to_sga "3 IV 3.3.2" "(i), special case" CategoryTheory.EffectiveEquivalenceRelation
add_to_sga "3 IV 3.3.2" "C-equivalence relation" CategoryTheory.EquivalenceRelation
add_to_sga "3 IV 3.3.2" CategoryTheory.Functor.IsRepresentable
add_to_sga "3 IV 3.3.2" CategoryTheory.Functor.reprX
add_to_sga "3 IV 3.3.2" "effectiveness predicate" CategoryTheory.IsEffectiveEquivalenceRelation
add_to_sga "3 IV 3.3.2" "(iii)" CategoryTheory.IsKernelPair
add_to_sga "3 IV 3.3.2" CategoryTheory.Limits.coequalizer
add_to_sga "3 IV 3.3.2.1" "more general" CategoryTheory.IsKernelPair.toCoequalizer
add_to_sga "3 IV 3.3.2.1" "more general" CategoryTheory.IsKernelPair.toCoequalizer'
add_to_sga "3 IV 3.3.2.1" "more general" CategoryTheory.RegularEpi.effectiveEpi
add_to_sga "3 IV 3.3.2.1" CategoryTheory.effectiveEpi_of_kernelPair
add_to_sga "3 IV 3.3.2.1" "more general" CategoryTheory.instEffectiveEpiOfIsRegularEpi
add_to_sga "3 IV 3.3.2.1" CategoryTheory.instIsRegularEpiπ_1
add_to_sga "3 IV 3.3.2.1" "Second assertion" CategoryTheory.isColimitCoforkOfEffectiveEpi
add_to_sga "3 IV 3.3.2.1" "partial" Equivalence.quot_mk_eq_iff
add_to_sga "3 IV 3.3.2.1" "partial" Setoid.ker_mk_eq
add_to_sga "3 IV 3.3.3" CategoryTheory.IsUniversallyEffectiveEquivalenceRelation
add_to_sga "3 IV 3.3.3" CategoryTheory.UniversallyEffectiveEquivalenceRelation
add_to_sga "3 IV 3.3.3.2" "more general" AlgebraicGeometry.AffineSpace.homOverEquiv
add_to_sga "3 IV 3.3.3.2" "injectivity of Hom_S(X" AlgebraicGeometry.AffineSpace.hom_ext
add_to_sga "3 IV 3.3.4" "(i) ⇒ (ii)" CategoryTheory.IsKernelPair.comp_of_mono
add_to_sga "3 IV 3.3.4" "(ii) ⇒ (i)" Con.kerLift_injective
add_to_sga "3 IV 3.3.4" "(i) ⇒ (ii)" Con.ker_eq_lift_of_injective
add_to_sga "3 IV 3.3.4" "(ii) ⇒ (i)" Setoid.kerLift_injective
add_to_sga "3 IV 3.3.5" "partial" CategoryTheory.IsUniversallyEffectiveEquivalenceRelation
add_to_sga "3 IV 3.3.5" "partial" CategoryTheory.UniversallyEffectiveEquivalenceRelation
add_to_sga "3 IV 3.4" AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_sga "3 IV 3.4" "Affine case" CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat
add_to_sga "3 IV 3.4.1" "(a)" CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst
add_to_sga "3 IV 3.4.1" CategoryTheory.MorphismProperty.IsStableUnderComposition
add_to_sga "3 IV 3.4.3" "special case" CategoryTheory.IsUniversallyEffectiveEquivalenceRelation
add_to_sga "3 IV 3.4.3" "special case" CategoryTheory.UniversallyEffectiveEquivalenceRelation
add_to_sga "3 IV 3.4.6" "special case" Setoid.prodQuotientEquiv
add_to_sga "3 IV 3.4.7" "special case" MonoidHom.eq_iff
add_to_sga "3 IV 3.4.7" "special case" QuotientGroup.con_ker_eq_conKer
add_to_sga "3 IV 3.4.7.1" "special case" AddCon.quotientKerEquivOfSurjective
add_to_sga "3 IV 3.4.7.1" "special case" Con.quotientKerEquivOfSurjective
add_to_sga "3 IV 3.4.7.1" "special case" QuotientAddGroup.quotientKerEquivOfSurjective
add_to_sga "3 IV 3.4.7.1" "special case" QuotientGroup.quotientKerEquivOfSurjective
add_to_sga "3 IV 4.1.1" "partial" CategoryTheory.Sieve.functor
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.generateFamily
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.generateSingleton
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.generate_apply
add_to_sga "3 IV 4.1.1" "more general" CategoryTheory.Sieve.inf
add_to_sga "3 IV 4.1.1" "partial" CategoryTheory.Sieve.instCompleteLattice
add_to_sga "3 IV 4.1.1" "partial" CategoryTheory.Sieve.inter
add_to_sga "3 IV 4.1.1" "partial" CategoryTheory.Sieve.inter_apply
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.mem_ofArrows_iff
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.mem_ofObjects_iff
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.ofArrows_eq_ofObjects
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.ofObjects
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.ofTwoArrows
add_to_sga "3 IV 4.1.1" "more general" CategoryTheory.Sieve.sInf_apply
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.sieveOfSubfunctor
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.sieveOfSubfunctor_apply
add_to_sga "3 IV 4.1.1" "partial" CategoryTheory.Sieve.sieveOfSubfunctor_functorInclusion
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.sieveOfUliftSubfunctor
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.sieveOfUliftSubfunctor_apply
add_to_sga "3 IV 4.1.1" "partial" CategoryTheory.Sieve.sieveOfUliftSubfunctor_uliftFunctorInclusion
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.sup
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.union
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve.union_apply
add_to_sga "3 IV 4.1.1" "more general" CategoryTheory.Subfunctor
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Subfunctor.sieveOfSection
add_to_sga "3 IV 4.1.1" "more general" CategoryTheory.instPartialOrderSubfunctor
add_to_sga "3 IV 4.1.2" "singleton families" CategoryTheory.Subfunctor.image_obj
add_to_sga "3 IV 4.1.4.0" "τ₁σ = τ₂σ" CategoryTheory.Equalizer.Presieve.w
add_to_sga "3 IV 4.1.4.0" "The map τ₁ to ∏_{i" CategoryTheory.Presheaf.firstMap
add_to_sga "3 IV 4.1.4.0" "partial" CategoryTheory.Presheaf.firstObj
add_to_sga "3 IV 4.1.4.0" "special case" CategoryTheory.Sieve.exists_eq_ofArrows
add_to_sga "3 IV 4.1.4.0" "special case" CategoryTheory.Sieve.generate_sieve
add_to_sga "3 IV 4.1.4.0" "special case" CategoryTheory.Sieve.ofArrows_category
add_to_sga "3 IV 4.1.4.0" "the map τ1" TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
add_to_sga "3 IV 4.1.4.0" "the identity τ1σ = τ2σ" TopCat.Presheaf.SheafConditionEqualizerProducts.w
add_to_sga "3 IV 4.1.4.0" "the identity τ1σ = τ2σ"
  TopCat.Presheaf.SheafConditionEqualizerProducts.w_apply
add_to_sga "3 IV 4.1.6" "more general" CategoryTheory.ObjectProperty.FullSubcategory.category
add_to_sga "3 IV 4.1.7" CategoryTheory.Sieve.functor
add_to_sga "3 IV 4.1.7" "partial" CategoryTheory.Sieve.ofArrows_category
add_to_sga "3 IV 4.1.7" CategoryTheory.Sieve.shrinkFunctor
add_to_sga "3 IV 4.1.7" CategoryTheory.Sieve.sieveOfSubfunctor
add_to_sga "3 IV 4.1.7" "partial" CategoryTheory.Sieve.sieveOfSubfunctor_functorInclusion
add_to_sga "3 IV 4.1.7" CategoryTheory.Sieve.sieveOfUliftSubfunctor
add_to_sga "3 IV 4.1.7" "partial" CategoryTheory.Sieve.sieveOfUliftSubfunctor_uliftFunctorInclusion
add_to_sga "3 IV 4.1.7" CategoryTheory.Subfunctor.sieveOfSection
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.Cover
add_to_sga "3 IV 4.2.1" "more general" CategoryTheory.GrothendieckTopology.arrow_trans
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.covering_of_eq_top
add_to_sga "3 IV 4.2.1" "T′5 with F representable"
  CategoryTheory.GrothendieckTopology.intersection_covering_iff
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.mk
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.pullback_stable'
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.sieves
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.superset_covering
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.top_mem
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.top_mem'
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.transitive
add_to_sga "3 IV 4.2.1" CategoryTheory.GrothendieckTopology.transitive'
add_to_sga "3 IV 4.2.2" "partial" CategoryTheory.GrothendieckTopology.instCompleteLattice
add_to_sga "3 IV 4.2.2" CategoryTheory.GrothendieckTopology.instInfSet
add_to_sga "3 IV 4.2.2" CategoryTheory.GrothendieckTopology.instLEGrothendieckTopology
add_to_sga "3 IV 4.2.2" CategoryTheory.GrothendieckTopology.instPartialOrder
add_to_sga "3 IV 4.2.2" CategoryTheory.GrothendieckTopology.isGLB_sInf
add_to_sga "3 IV 4.2.2" CategoryTheory.GrothendieckTopology.le_def
add_to_sga "3 IV 4.2.2" "partial" CategoryTheory.GrothendieckTopology.mem_sInf
add_to_sga "3 IV 4.2.2" CategoryTheory.Precoverage.toGrothendieck
add_to_sga "3 IV 4.2.3" "special case" CategoryTheory.Coverage.Saturate.transitive
add_to_sga "3 IV 4.2.3" "special case" CategoryTheory.Coverage.mem_toGrothendieck_sieves_of_superset
add_to_sga "3 IV 4.2.3" "special case" CategoryTheory.Coverage.saturate_of_superset
add_to_sga "3 IV 4.2.3" "(C 4), special case"
  CategoryTheory.GrothendieckTopology.instHasIsosToPrecoverage
add_to_sga "3 IV 4.2.3" "special case"
  CategoryTheory.GrothendieckTopology.instIsStableUnderBaseChangeToPrecoverage
add_to_sga "3 IV 4.2.3" "special case" CategoryTheory.GrothendieckTopology.mem_toCoverage_iff
add_to_sga "3 IV 4.2.3" "special case" CategoryTheory.GrothendieckTopology.superset_covering
add_to_sga "3 IV 4.2.3" "special case" CategoryTheory.GrothendieckTopology.transitive
add_to_sga "3 IV 4.2.3" "special case" CategoryTheory.GrothendieckTopology.transitive'
add_to_sga "3 IV 4.2.3" "more general" CategoryTheory.Presheaf.isLocallySurjective_of_iso
add_to_sga "3 IV 4.2.5" "partial" CategoryTheory.Precoverage
add_to_sga "3 IV 4.2.5" CategoryTheory.Precoverage.HasIsos
add_to_sga "3 IV 4.2.5" "P1" CategoryTheory.Precoverage.IsStableUnderBaseChange
add_to_sga "3 IV 4.2.5" CategoryTheory.Precoverage.IsStableUnderComposition
add_to_sga "3 IV 4.2.5" CategoryTheory.Precoverage.toPretopology
add_to_sga "3 IV 4.2.5" CategoryTheory.Pretopology
add_to_sga "3 IV 4.2.6" "J_R(S) ⊆ J(S)" CategoryTheory.Coverage.Saturate.of
add_to_sga "3 IV 4.2.6" "J_R(S) ⊆ J(S)" CategoryTheory.Precoverage.Saturate.of
add_to_sga "3 IV 4.2.6" "J_R(S) ⊆ J(S)" CategoryTheory.Precoverage.generate_mem_toGrothendieck
add_to_sga "3 IV 4.2.8" "(iii) ⇒ (i)" CategoryTheory.Coverage.mem_toGrothendieck_sieves_of_superset
add_to_sga "3 IV 4.2.8" "(ii) ⇒ (i), special case" CategoryTheory.Coverage.saturate_of_superset
add_to_sga "3 IV 4.2.8" "(ii) ⇒ (i)" CategoryTheory.GrothendieckTopology.superset_covering
add_to_sga "3 IV 4.2.8" "special case" CategoryTheory.Pretopology.mem_toGrothendieck
add_to_sga "3 IV 4.3.1" CategoryTheory.Functor
add_to_sga "3 IV 4.3.1" CategoryTheory.Presheaf.IsSeparated
add_to_sga "3 IV 4.3.1" "special case" CategoryTheory.Presheaf.IsSheaf'
add_to_sga "3 IV 4.3.1" CategoryTheory.Presieve.IsSeparatedFor
add_to_sga "3 IV 4.3.1" "more general" CategoryTheory.Presieve.IsSeparatedFor.of_mono
add_to_sga "3 IV 4.3.1" CategoryTheory.Presieve.IsSheaf
add_to_sga "3 IV 4.3.1" "partial" CategoryTheory.Presieve.IsSheafFor
add_to_sga "3 IV 4.3.1" CategoryTheory.Presieve.YonedaSheafCondition
add_to_sga "3 IV 4.3.1" "more general" CategoryTheory.Sheaf
add_to_sga "3 IV 4.3.1" CategoryTheory.Sieve.functor
add_to_sga "3 IV 4.3.1" CategoryTheory.Sieve.functorInclusion
add_to_sga "3 IV 4.3.1" CategoryTheory.Subfunctor.isSeparated
add_to_sga "3 IV 4.3.1" "partial" CategoryTheory.sheafToPresheaf
add_to_sga "3 IV 4.3.1" "partial" CategoryTheory.yonedaEquiv
add_to_sga "3 IV 4.3.1" "special case" TopCat.Presheaf.IsSheaf
add_to_sga "3 IV 4.3.2" "partial, special case" CategoryTheory.Subfunctor.to_sheafify_lift_unique
add_to_sga "3 IV 4.3.4" "more general" CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff
add_to_sga "3 IV 4.3.4" "Sheaf clause" CategoryTheory.Presheaf.IsSheaf.isSheafFor
add_to_sga "3 IV 4.3.4" "Sheaf clause, necessity" CategoryTheory.Presieve.IsSheaf.isSheafFor
add_to_sga "3 IV 4.3.4" "Sheaf clause, necessity"
  CategoryTheory.Presieve.IsSheaf.isSheafFor_of_mem_precoverage
add_to_sga "3 IV 4.3.4" "more general" CategoryTheory.Presieve.isSheaf_coverage
add_to_sga "3 IV 4.3.5" "special case" CategoryTheory.Presheaf.isSheaf_iff_isSheaf'
add_to_sga "3 IV 4.3.5" "partial" CategoryTheory.Presieve.IsSheaf.isSheafFor
add_to_sga "3 IV 4.3.5" "necessity" TopCat.Presheaf.IsSheaf.section_ext
add_to_sga "3 IV 4.3.5" "special case" TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types
add_to_sga "3 IV 4.3.6" "more general"
  CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
add_to_sga "3 IV 4.3.6" "maximality"
  CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
add_to_sga "3 IV 4.3.6" CategoryTheory.Sheaf.canonicalTopology
add_to_sga "3 IV 4.3.6" "partial" CategoryTheory.Sheaf.isSheaf_of_isRepresentable
add_to_sga "3 IV 4.3.6" "partial" CategoryTheory.Sheaf.isSheaf_yoneda_obj
add_to_sga "3 IV 4.3.6" "more general" CategoryTheory.Sheaf.le_finestTopology
add_to_sga "3 IV 4.3.6" "more general" CategoryTheory.Sheaf.sheaf_for_finestTopology
add_to_sga "3 IV 4.3.8" "more general" CategoryTheory.GrothendieckTopology.Cover
add_to_sga "3 IV 4.3.9" "partial" CategoryTheory.GrothendieckTopology.Cover.instOrderTop
add_to_sga "3 IV 4.3.9" "partial" CategoryTheory.GrothendieckTopology.Cover.instSemilatticeInf
add_to_sga "3 IV 4.3.9" "partial" CategoryTheory.GrothendieckTopology.top_mem
add_to_sga "3 IV 4.3.9" "restriction map Hom(R" CategoryTheory.Meq.refine
add_to_sga "3 IV 4.3.9" "partial" CategoryTheory.Presieve.isAmalgamation_restrict
add_to_sga "3 IV 4.3.10" "more general" CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists
add_to_sga "3 IV 4.3.10" "more general" CategoryTheory.GrothendieckTopology.Plus.exists_rep
add_to_sga "3 IV 4.3.10" CategoryTheory.Presheaf.isLocallyInjective_toPlus
add_to_sga "3 IV 4.3.10.0" "more general" CategoryTheory.GrothendieckTopology.Plus.mk
add_to_sga "3 IV 4.3.10.0" "more general" CategoryTheory.GrothendieckTopology.plusFunctor
add_to_sga "3 IV 4.3.10.0" "more general" CategoryTheory.GrothendieckTopology.plusObj
add_to_sga "3 IV 4.3.10.0" "more general" CategoryTheory.GrothendieckTopology.toPlus
add_to_sga "3 IV 4.3.11" "(iv)" CategoryTheory.GrothendieckTopology.Plus.exists_of_sep
add_to_sga "3 IV 4.3.11" "(iv), special case"
  CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus
add_to_sga "3 IV 4.3.11" "more general" CategoryTheory.GrothendieckTopology.isIso_toPlus_of_isSheaf
add_to_sga "3 IV 4.3.11" "partial" CategoryTheory.GrothendieckTopology.plus_hom_ext
add_to_sga "3 IV 4.3.11" "(iii)" CategoryTheory.GrothendieckTopology.toPlus_plusLift
add_to_sga "3 IV 4.3.11" CategoryTheory.Presheaf.isLocallySurjective_toPlus
add_to_sga "3 IV 4.3.12" "R is separated" CategoryTheory.Presieve.IsSeparatedFor.of_mono
add_to_sga "3 IV 4.3.12" "R is separated" CategoryTheory.Subfunctor.isSeparated
add_to_sga "3 IV 4.3.13" "more general" CategoryTheory.sheafToPresheaf
add_to_sga "3 IV 4.3.14" CategoryTheory.GrothendieckTopology.sheafification
add_to_sga "3 IV 4.3.14" CategoryTheory.plusPlusSheaf
add_to_sga "3 IV 4.3.14" CategoryTheory.sheafToPresheaf
add_to_sga "3 IV 4.3.14" "partial" CategoryTheory.sheafToPresheaf_isRightAdjoint
add_to_sga "3 IV 4.3.15" CategoryTheory.presheafToSheaf
add_to_sga "3 IV 4.3.15" CategoryTheory.sheafify
add_to_sga "3 IV 4.3.16" "more general"
  CategoryTheory.GrothendieckTopology.preservesFiniteLimits_plusFunctor
add_to_sga "3 IV 4.3.16" "more general"
  CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification
add_to_sga "3 IV 4.3.16" "more general" CategoryTheory.preservesFiniteLimits_presheafToSheaf
add_to_sga "3 IV 4.3.17" CategoryTheory.Functor
add_to_sga "3 IV 4.3.17" CategoryTheory.Functor.const
add_to_sga "3 IV 4.3.17" CategoryTheory.Limits.Types.limNatIsoSectionsFunctor
add_to_sga "3 IV 4.3.17" "partial" CategoryTheory.Limits.Types.limitEquivSections
add_to_sga "3 IV 4.3.17" "special case" CategoryTheory.Limits.limYoneda
add_to_sga "3 IV 4.3.17" CategoryTheory.Limits.whiskeringLimYonedaIsoCones
add_to_sga "3 IV 4.3.17" CategoryTheory.Presieve.category
add_to_sga "3 IV 4.3.17" "more general" CategoryTheory.Sheaf.isLimitConeΓ
add_to_sga "3 IV 4.3.17" "special case" CategoryTheory.Sheaf.over
add_to_sga "3 IV 4.3.17" "more general" CategoryTheory.Sheaf.ΓNatIsoLim
add_to_sga "3 IV 4.3.17" "special case" CategoryTheory.SimplicialObject.const
add_to_sga "3 IV 4.3.18" "partial" CategoryTheory.Equalizer.Sieve.equalizer_sheaf_condition
add_to_sga "3 IV 4.3.18" CategoryTheory.Presheaf.IsSeparated
add_to_sga "3 IV 4.3.18" CategoryTheory.Presheaf.IsSheaf'
add_to_sga "3 IV 4.3.18" "partial" CategoryTheory.Presheaf.isLimit_iff_isSheafFor
add_to_sga "3 IV 4.3.18" CategoryTheory.Presheaf.isSeparated_iff_subsingleton
add_to_sga "3 IV 4.3.18" CategoryTheory.Presheaf.isSheaf_iff_isLimit
add_to_sga "3 IV 4.3.18" CategoryTheory.Presheaf.isSheaf_iff_multiequalizer
add_to_sga "3 IV 4.3.18" CategoryTheory.Presheaf.isSheaf_iff_multifork
add_to_sga "3 IV 4.3.18" "partial" CategoryTheory.Presheaf.subsingleton_iff_isSeparatedFor
add_to_sga "3 IV 4.3.18" "partial" CategoryTheory.Presieve.IsSeparatedFor
add_to_sga "3 IV 4.3.18" CategoryTheory.Presieve.IsSheaf
add_to_sga "3 IV 4.3.18" "partial" CategoryTheory.Presieve.IsSheafFor
add_to_sga "3 IV 4.3.18" CategoryTheory.Sheaf
add_to_sga "3 IV 4.4.1" "more general"
  CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification
add_to_sga "3 IV 4.4.1" "more general" CategoryTheory.Sheaf.createsLimitsOfShape
add_to_sga "3 IV 4.4.1" "(ii)" CategoryTheory.Sheaf.hasFilteredColimitsOfSize
add_to_sga "3 IV 4.4.1" "(ii)" CategoryTheory.Sheaf.instHasColimitsOfShape
add_to_sga "3 IV 4.4.1" "(ii)" CategoryTheory.Sheaf.instHasColimitsOfSize
add_to_sga "3 IV 4.4.1" "(ii)" CategoryTheory.Sheaf.instHasFiniteColimits
add_to_sga "3 IV 4.4.1" "(i)" CategoryTheory.Sheaf.instHasFiniteLimits
add_to_sga "3 IV 4.4.1" "(i)" CategoryTheory.Sheaf.instHasLimitsOfShape
add_to_sga "3 IV 4.4.1" "(i)"
  CategoryTheory.Sheaf.instIsClosedUnderLimitsOfShapeFunctorOppositeIsSheaf
add_to_sga "3 IV 4.4.1" "more general" CategoryTheory.Sheaf.isColimitSheafifyCocone
add_to_sga "3 IV 4.4.1" "(i)" CategoryTheory.Sheaf.isSheaf_of_isLimit
add_to_sga "3 IV 4.4.1" "more general"
  CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
add_to_sga "3 IV 4.4.1" "more general" CategoryTheory.preservesFiniteLimits_presheafToSheaf
add_to_sga "3 IV 4.4.1" "more general" CategoryTheory.preservesLimitsOfShape_presheafToSheaf
add_to_sga "3 IV 4.4.1" "(i), special case" TopCat.instCreatesLimitsSheafPresheafForgetOfHasLimits
add_to_sga "3 IV 4.4.1" "(i), special case" TopCat.instHasLimitsOfShapeSheaf
add_to_sga "3 IV 4.4.1" "(i), special case" TopCat.instHasLimitsOfSizeSheafOfHasLimits
add_to_sga "3 IV 4.4.1" "(i), special case" TopCat.isSheaf_of_isLimit
add_to_sga "3 IV 4.4.1" "(i), special case" TopCat.limit_isSheaf
add_to_sga "3 IV 4.4.2" CategoryTheory.GrothendieckTopology.bot_covering
add_to_sga "3 IV 4.4.2" CategoryTheory.GrothendieckTopology.trivial
add_to_sga "3 IV 4.4.2" CategoryTheory.GrothendieckTopology.trivial_covering
add_to_sga "3 IV 4.4.2" CategoryTheory.GrothendieckTopology.trivial_eq_bot
add_to_sga "3 IV 4.4.2" "more general" CategoryTheory.Presheaf.isSheaf_bot
add_to_sga "3 IV 4.4.2" CategoryTheory.Presieve.isSheaf_bot
add_to_sga "3 IV 4.4.3" "(ii) ⇒ (i)" CategoryTheory.EffectiveEpiFamily.hom_ext
add_to_sga "3 IV 4.4.3" "special case" CategoryTheory.Sheaf.epi_of_isLocallySurjective
add_to_sga "3 IV 4.4.3" "special case" CategoryTheory.Sheaf.epi_of_isLocallySurjective'
add_to_sga "3 IV 4.4.3" "(iv), special case" CategoryTheory.Sheaf.image
add_to_sga "3 IV 4.4.3" "special case" CategoryTheory.Sheaf.isLocallySurjective_iff_epi
add_to_sga "3 IV 4.4.3" "(ii) ⇒ (i)" CategoryTheory.epi_of_effectiveEpi
add_to_sga "3 IV 4.4.4" "If X→Y is an epimorphism"
  CategoryTheory.Limits.PushoutCocone.inl_eq_inr_of_epi_eq
add_to_sga "3 IV 4.4.4" "If X→Y is an epimorphism" CategoryTheory.Limits.inl_eq_inr_of_epi_eq
add_to_sga "3 IV 4.4.4" "If X→Y is an epimorphism" CategoryTheory.epi_iff_inl_eq_inr
add_to_sga "3 IV 4.4.7" "partial" CategoryTheory.Sheaf.instIsLocallySurjectiveFunToImage
add_to_sga "3 IV 4.4.7" CategoryTheory.Sheaf.toImage
add_to_sga "3 IV 4.4.7" "factorization identity" CategoryTheory.Sheaf.toImage_ι
add_to_sga "3 IV 4.4.7" CategoryTheory.Subfunctor.toRangeSheafify
add_to_sga "3 IV 4.4.7" CategoryTheory.imageFactorization
add_to_sga "3 IV 4.4.7" CategoryTheory.imageMonoFactorization
add_to_sga "3 IV 4.4.7" "partial" CategoryTheory.instMonoSheafTypeImageι
open CategoryTheory.GrothendieckTopology in
add_to_sga "3 IV 4.4.8" "special case"
  ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map
open CategoryTheory.GrothendieckTopology in
add_to_sga "3 IV 4.4.8" "special case"
  ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map
open CategoryTheory.GrothendieckTopology in
add_to_sga "3 IV 4.4.8" "special case"
  ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map
open CategoryTheory.GrothendieckTopology in
add_to_sga "3 IV 4.4.8" "special case"
  ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
add_to_sga "3 IV 4.4.8" CategoryTheory.Presheaf.IsLocallySurjective
add_to_sga "3 IV 4.4.8" "more general" CategoryTheory.Presieve.IsSeparatedFor.of_mono
add_to_sga "3 IV 4.4.8" "(v)" CategoryTheory.Sheaf.epi_of_isLocallySurjective
add_to_sga "3 IV 4.4.8" "(v)" CategoryTheory.Sheaf.epi_of_isLocallySurjective'
add_to_sga "3 IV 4.4.8" "(v), special case" CategoryTheory.Sheaf.isLocallySurjective_iff_epi
add_to_sga "3 IV 4.4.8" "more general" CategoryTheory.Subfunctor.isSeparated
add_to_sga "3 IV 4.4.10" "special case" Subrel
add_to_sga "3 IV 4.5" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "3 IV 4.5" "(i) ⇒ (ii)"
  CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
add_to_sga "3 IV 4.5" "(ii) ⇒ (i)"
  CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
add_to_sga "3 IV 4.5" CategoryTheory.GrothendieckTopology.yoneda
add_to_sga "3 IV 4.5" CategoryTheory.GrothendieckTopology.yonedaCompSheafToPresheaf
add_to_sga "3 IV 4.5.1" "more general" CategoryTheory.GrothendieckTopology.fullyFaithfulUliftYoneda
add_to_sga "3 IV 4.5.1" "partial"
  CategoryTheory.GrothendieckTopology.instFaithfulSheafTypeUliftYoneda
add_to_sga "3 IV 4.5.1" "j is faithful"
  CategoryTheory.GrothendieckTopology.instFaithfulSheafTypeYoneda
add_to_sga "3 IV 4.5.1" "partial" CategoryTheory.GrothendieckTopology.instFullSheafTypeUliftYoneda
add_to_sga "3 IV 4.5.1" "j is full" CategoryTheory.GrothendieckTopology.instFullSheafTypeYoneda
add_to_sga "3 IV 4.5.1" CategoryTheory.GrothendieckTopology.mem_over_iff
add_to_sga "3 IV 4.5.1" CategoryTheory.GrothendieckTopology.over
add_to_sga "3 IV 4.5.1" "partial" CategoryTheory.GrothendieckTopology.overEquiv_symm_mem_over
add_to_sga "3 IV 4.5.1" CategoryTheory.GrothendieckTopology.preservesLimitsOfSize_yoneda
add_to_sga "3 IV 4.5.1" "more general" instPreservesLimitsOfShapeSheafTypeUliftYoneda
add_to_sga "3 IV 4.5.1" instPreservesLimitsOfShapeSheafTypeYoneda
add_to_sga "3 IV 4.5.5" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "3 IV 4.5.5" "partial"
  CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
add_to_sga "3 IV 4.5.5" CategoryTheory.GrothendieckTopology.yoneda
add_to_sga "3 IV 4.5.5" "special case" CategoryTheory.Sheaf.isSheaf_of_isRepresentable
add_to_sga "3 IV 4.5.5" "h_X is a sheaf" CategoryTheory.Sheaf.isSheaf_yoneda_obj
add_to_sga "3 IV 4.5.5" CategoryTheory.yoneda
add_to_sga "3 IV 4.5.6" "(i) ⇒ (ii)" CategoryTheory.Over.epi_homMk
add_to_sga "3 IV 4.5.7" "more general"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.isomorphisms
add_to_sga "3 IV 4.5.7" "more general" CategoryTheory.Sheaf.isIso_iff_of_coversTop
add_to_sga "3 IV 4.5.7" "(ii), partial" CategoryTheory.Sheaf.isIso_of_coversTop
add_to_sga "3 IV 4.5.8" "special case"
  AlgebraicGeometry.instIsZariskiLocalAtTargetMonomorphismsScheme
add_to_sga "3 IV 4.5.9" "(i)⇔(ii)"
  CategoryTheory.Presheaf.isLocallyInjective_iff_injective_of_separated
add_to_sga "3 IV 4.5.13" "special case" CategoryTheory.Presheaf.IsSheaf.hom
add_to_sga "3 IV 4.5.13" "special case" CategoryTheory.Presheaf.isSheaf_functorEnrichedHom
add_to_sga "3 IV 4.6" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "3 IV 4.6" CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
add_to_sga "3 IV 4.6" CategoryTheory.GrothendieckTopology.yoneda
add_to_sga "3 IV 4.6" "canonical topology" CategoryTheory.Sheaf.isSheaf_of_isRepresentable
add_to_sga "3 IV 4.6" "special case" CategoryTheory.Sheaf.isSheaf_yoneda_obj
add_to_sga "3 IV 4.6.1" "special case" Setoid.prod
add_to_sga "3 IV 4.6.3" "more general"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst
add_to_sga "3 IV 4.6.3" CategoryTheory.MorphismProperty.IsStableUnderComposition
add_to_sga "3 IV 4.6.4" "more general" CategoryTheory.GrothendieckTopology.instHasIsosToPrecoverage
add_to_sga "3 IV 4.6.15" CategoryTheory.yoneda
add_to_sga "3 IV 4.7" AlgebraicGeometry.Scheme
add_to_sga "3 IV 4.7" AlgebraicGeometry.Scheme.fpqcPrecoverage
add_to_sga "3 IV 4.7" AlgebraicGeometry.Scheme.fpqcTopology
add_to_sga "3 IV 4.7" "special case" AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology
add_to_sga "3 IV 4.7" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "3 IV 5.1.2" "special case" Equiv.smulConst
add_to_sga "3 IV 5.1.2" "special case" Homeomorph.smulConst
add_to_sga "3 IV 5.1.7.1" "special case" MonoidHom.div_mem_ker_iff
add_to_sga "3 IV 5.1.7.1" "special case" MonoidHom.eq_iff
add_to_sga "3 IV 5.1.7.1" "special case" QuotientAddGroup.con_ker_eq_addConKer
add_to_sga "3 IV 5.1.7.1" "special case" QuotientGroup.con_ker_eq_conKer
add_to_sga "3 IV 5.1.7.1" "special case" QuotientGroup.quotientKerEquivOfSurjective
add_to_sga "3 IV 5.2.2" AddAction.quotient
add_to_sga "3 IV 5.2.2" MulAction.quotient
add_to_sga "3 IV 5.2.2" MulActionHom.toQuotient
add_to_sga "3 IV 5.2.3" "special case" Con.group
add_to_sga "3 IV 5.2.3" "special case" QuotientGroup.congr
add_to_sga "3 IV 5.2.3" "special case" QuotientGroup.map
add_to_sga "3 IV 5.2.3" "special case" QuotientGroup.mk'
add_to_sga "3 IV 5.2.4" "partial" Con.group
add_to_sga "3 IV 5.2.4" "partial" QuotientGroup.instIsTopologicalGroup
add_to_sga "3 IV 5.2.4" "partial" QuotientGroup.map
add_to_sga "3 IV 5.2.4" "existence clause" QuotientGroup.mk'
add_to_sga "3 IV 5.2.5" "(ii) ⇒ (iii)" AddCon.kerLift_mk
add_to_sga "3 IV 5.2.5" "(i) ⇒ (iii), partial" AddCon.lift_coe
add_to_sga "3 IV 5.2.5" "(i) ⇒ (iii), partial" AddCon.lift_comp_mk'
add_to_sga "3 IV 5.2.5" "(i) ⇒ (iii), partial" AddCon.lift_mk'
add_to_sga "3 IV 5.2.5" "partial" AddCon.lift_unique
add_to_sga "3 IV 5.2.5" "(ii) ⇔ (iii), partial" AddMonoidHom.restrictHomKerEquiv
add_to_sga "3 IV 5.2.5" "partial" Con.hom_ext_iff
add_to_sga "3 IV 5.2.5" "(ii) ⇒ (iii)" Con.kerLift_mk
add_to_sga "3 IV 5.2.5" "(i) ⇒ (iii), partial" Con.lift_coe
add_to_sga "3 IV 5.2.5" "(i) ⇒ (iii), partial" Con.lift_comp_mk'
add_to_sga "3 IV 5.2.5" "(i) ⇒ (iii), partial" Con.lift_mk'
add_to_sga "3 IV 5.2.5" "partial" Con.lift_unique
add_to_sga "3 IV 5.2.5" "(ii) ⇔ (iii), partial" MonoidHom.domRestrictHomKerEquiv
add_to_sga "3 IV 5.2.5" "partial" MonoidHom.domRestrictHomKerEquiv_symm_coe_apply
add_to_sga "3 IV 5.2.5" "(ii) ⇒ (iii), partial" MonoidHom.restrictHomKerEquiv_apply_coe
add_to_sga "3 IV 5.2.5" "partial" MonoidHom.restrictHomKerEquiv_symm_coe_apply
add_to_sga "3 IV 5.2.5" "(ii) ⇒ (iii)" QuotientAddGroup.map_mk
add_to_sga "3 IV 5.2.5" QuotientGroup.lift
add_to_sga "3 IV 5.2.5" "partial" QuotientGroup.monoidHom_ext
add_to_sga "3 IV 5.2.5" "partial" QuotientGroup.monoidHom_ext_iff
add_to_sga "3 IV 5.2.6" "special case" Con.kerLift_injective
add_to_sga "3 IV 5.2.7" "special case" QuotientAddGroup.comapMk'OrderIso
add_to_sga "3 IV 5.2.7" "special case" QuotientGroup.comapMk'OrderIso
add_to_sga "3 IV 5.2.7" "K = K' ×_{G'} G" Subgroup.comap_map_eq_self
add_to_sga "3 IV 5.2.7" "special case" Subgroup.normal_comap_iff_of_surjective
add_to_sga "3 IV 5.2.8" "special case" Action.FintypeCat.quotientToEndHom
add_to_sga "3 IV 5.2.8" "partial" Action.FintypeCat.quotientToEndHom_mk
add_to_sga "3 IV 5.2.8" "partial" AddAction.quotient
add_to_sga "3 IV 5.2.8" "partial" AddAction.right_quotientAction
add_to_sga "3 IV 5.2.8" "partial" AddAction.right_quotientAction'
add_to_sga "3 IV 5.2.8" "partial" MulAction.quotient
add_to_sga "3 IV 5.2.8" "partial" MulAction.right_quotientAction
add_to_sga "3 IV 5.2.8" "partial" MulAction.right_quotientAction'
add_to_sga "3 IV 5.2.8" "special case" QuotientAddGroup.quotientInfEquivSumNormalQuotient
add_to_sga "3 IV 5.2.8" "special case" QuotientAddGroup.quotientInfEquivSumNormalizerQuotient
add_to_sga "3 IV 5.2.8" "special case" QuotientAddGroup.quotientKerEquivRange
add_to_sga "3 IV 5.2.8" "special case" QuotientGroup.quotientInfEquivProdNormalQuotient
add_to_sga "3 IV 5.2.8" "special case" QuotientGroup.quotientInfEquivProdNormalizerQuotient
add_to_sga "3 IV 5.2.8" "special case" QuotientGroup.quotientKerEquivOfSurjective
add_to_sga "3 IV 5.2.8" "special case" QuotientGroup.quotientKerEquivRange
add_to_sga "3 IV 5.2.9" "special case" QuotientAddGroup.quotientQuotientEquivQuotient
add_to_sga "3 IV 5.2.9" "special case" QuotientGroup.quotientQuotientEquivQuotient
add_to_sga "3 IV 5.3.1" "special case" QuotientAddGroup.comapMk'OrderIso
add_to_sga "3 IV 5.3.1" "special case" QuotientGroup.comapMk'OrderIso
add_to_sga "3 IV 5.3.1" "partial" QuotientGroup.map_normal
add_to_sga "3 IV 6.1" "partial" AlgebraicGeometry.Scheme.OpenCover
add_to_sga "3 IV 6.1" AlgebraicGeometry.Scheme.zariskiPrecoverage
add_to_sga "3 IV 6.1" AlgebraicGeometry.Scheme.zariskiPretopology
add_to_sga "3 IV 6.1" AlgebraicGeometry.Scheme.zariskiTopology
add_to_sga "3 IV 6.1" "generated topology" AlgebraicGeometry.Scheme.zariskiTopology_eq
add_to_sga "3 IV 6.1.1" "more general" AlgebraicGeometry.Scheme.instSubcanonicalFppfTopology
add_to_sga "3 IV 6.1.1" "more general" AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology
add_to_sga "3 IV 6.1.1" "more general" AlgebraicGeometry.Scheme.instSubcanonicalProetaleTopology
add_to_sga "3 IV 6.1.1" AlgebraicGeometry.Scheme.subcanonical_zariskiTopology
add_to_sga "3 IV 6.1.1" AlgebraicGeometry.preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology
add_to_sga "3 IV 6.2.3" "partial" CategoryTheory.Presieve.isSheafFor_of_factorsThru
add_to_sga "3 IV 6.2.3" "partial" CategoryTheory.Presieve.isSheafFor_subsieve_aux
add_to_sga "3 IV 6.3" "more general" AlgebraicGeometry.Scheme.OpenCover.finiteSubcover
add_to_sga "3 IV 6.3" AlgebraicGeometry.Scheme.fppfTopology
add_to_sga "3 IV 6.3" AlgebraicGeometry.Scheme.fpqcTopology
add_to_sga "3 IV 6.3" "more general" AlgebraicGeometry.Scheme.grothendieckTopology_monotone
add_to_sga "3 IV 6.3" "more general" AlgebraicGeometry.Scheme.propQCTopology
add_to_sga "3 IV 6.3" "(ét) ≥ (Zar)" AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology
add_to_sga "3 IV 6.3.1" "(iii)" AlgebraicGeometry.Scheme.instSubcanonicalFppfTopology
add_to_sga "3 IV 6.3.1" "more general" AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology
add_to_sga "3 IV 6.3.2" "partial" AlgebraicGeometry.Scheme.Hom.singleton_mem_fppfPrecoverage
add_to_sga "3 IV 6.4.3" IsRetrocompact
add_to_sga "3 IV 6.4.3" IsRetrocompact_iff_isSpectralMap_subtypeVal
add_to_sga "3 IV 6.6" "Diagram 6.6.1" AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage
add_to_sga "3 IV 6.6" "more general" AlgebraicGeometry.Scheme.grothendieckTopology
add_to_sga "3 IV 6.6" "Diagram 6.6.1" AlgebraicGeometry.Scheme.instSubcanonicalFppfTopology
add_to_sga "3 IV 6.6" "Diagram 6.6.1" AlgebraicGeometry.Scheme.zariskiTopology_le_etaleTopology
add_to_sga "3 IV 6.6" CategoryTheory.GrothendieckTopology.bot_covering
add_to_sga "3 IV 6.6" CategoryTheory.GrothendieckTopology.trivial
add_to_sga "3 IV 6.6" "coarsest topology" CategoryTheory.GrothendieckTopology.trivial_eq_bot
add_to_sga "3 IV 6.7" "Footnote 66" CategoryTheory.ObjectProperty.localEpi.of_epi
add_to_sga "3 IV 6.7" "partial" CategoryTheory.Presheaf.epi_of_isLocallySurjective_bot
add_to_sga "3 IV 6.7" "more general" CategoryTheory.Presheaf.isLocallySurjective_bot_iff_epi
add_to_sga "3 IV 6.7" "Footnote 66" CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi
add_to_sga "3 IV 6.7" "more general" CategoryTheory.Subfunctor.epi_iff_range_eq_top
add_to_sga "3 IV 6.7" "partial" CategoryTheory.Subfunctor.range_eq_top
add_to_sga "3 IX 2.1" "b, special case" AddMonoidAlgebra.finiteType_iff_group_fg
add_to_sga "3 IX 2.1" "special case"
  Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
add_to_sga "3 IX 2.1" "partial"
  AlgebraicGeometry.Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact
add_to_sga "3 IX 2.1" "partial"
  AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact
open AlgebraicGeometry in
add_to_sga "3 IX 2.1" "partial"
  instDescendsAlongSchemeLocallyOfFinitePresentationMinMorphismPropertySurjectiveFlatQuasiCompact
open AlgebraicGeometry in
add_to_sga "3 IX 2.1" "partial"
  instDescendsAlongSchemeLocallyOfFiniteTypeMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "3 IX 2.1" "partial"
  AlgebraicGeometry.instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_sga "3 IX 2.1" "special case" RingHom.FiniteType.codescendsAlong_faithfullyFlat
add_to_sga "3 IX 2.10" "partial" CategoryTheory.Limits.pullback
add_to_sga "3 IX 3.3" "special case" Algebra.FormallySmooth.comp_lift
add_to_sga "3 IX 3.3" "special case" Algebra.FormallySmooth.exists_lift
add_to_sga "3 IX 3.3" Algebra.FormallySmooth.lift
add_to_sga "3 IX 3.3" Algebra.FormallySmooth.liftOfSurjective
add_to_sga "3 IX 4.1" "Closed-equalizer step"
  AlgebraicGeometry.Scheme.instIsClosedImmersionιOfIsSeparated
add_to_sga "3 IX 4.1" "special case" AlgebraicGeometry.ext_of_fromSpecResidueField_eq
add_to_sga "3 IX 4.1" "special case" AlgebraicGeometry.ext_of_isDominant
add_to_sga "3 IX 4.1" "partial" AlgebraicGeometry.isClosedImmersion_equalizer_ι_left
add_to_sga "3 IX 5.4" "special case"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfLocallyOfFinitePresentationOfSurjectiveOfFlat
add_to_sga "3 IX 5.4" "partial"
  AlgebraicGeometry.Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat
add_to_sga "3 IX 5.4" CategoryTheory.IsSplitEpi
add_to_sga "3 IX 5.4" "partial" CategoryTheory.IsSplitEpi.EffectiveEpi
add_to_sga "3 IX 5.4" CategoryTheory.SplitEpi
add_to_sga "3 IX 5.4" IsPurelyInseparable
add_to_sga "3 IX 7.2" "more general" PiTensorProduct.productMap
add_to_sga "3 IX 7.2" "pure-tensor formula" PiTensorProduct.productMap_tmul
add_to_sga "3 IX 8.0" "more general" linearIndepOn_isGroupLikeElem
add_to_sga "3 IX 8.0" "more general" linearIndep_groupLikeVal
add_to_sga "3 IX 8.0" "special case" linearIndependent_monoidHom
