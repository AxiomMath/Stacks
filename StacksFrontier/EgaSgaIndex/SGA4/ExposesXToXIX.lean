module  -- shake: keep-all

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
import Mathlib.CategoryTheory.DinatTrans
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Functor.CurryingThree
import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PolynomialLaw.Basic
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.Topology.IsLocalHomeomorph
import StacksCore.RingTheory.NormTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 4, Exposés X to XIX: references registered by name

The `add_to_sga` registrations of `StacksFrontier.EgaSgaIndex.SGA4` for Exposés X to XIX
of SGA 4, in the order of that file. See its module docstring.
-/

add_to_sga "4 X 2.1" "partial" IsFormallyReal.instOfIsStrictOrderedRing
add_to_sga "4 X 2.2.1" AdicCompletion
add_to_sga "4 X 2.2.1" IsFractionRing
add_to_sga "4 X 2.3" AlgebraicGeometry.Scheme.functionField
add_to_sga "4 XI 2.1" "special case" Algebra.isOpen_smoothLocus
add_to_sga "4 XI 2.1" "partial" AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus
add_to_sga "4 XI 2.1" AlgebraicGeometry.Scheme.Hom.smoothLocus
add_to_sga "4 XI 4.0" IsLocalHomeomorph
add_to_sga "4 XI 4.0" "partial" Topology.IsOpenEmbedding.isLocalHomeomorph
add_to_sga "4 XI 4.0" isLocalHomeomorph_iff_isOpenEmbedding_restrict
add_to_sga "4 XII 3.5" CategoryTheory.PresheafOfGroups.H1
add_to_sga "4 XII 3.5" CategoryTheory.PresheafOfGroups.OneCocycle.IsCohomologous
add_to_sga "4 XII 4.3" "Parenthetical clause" AlgebraicGeometry.instIsClosedImmersionFstScheme
add_to_sga "4 XII 4.3" "special case" AlgebraicGeometry.instIsClosedImmersionMorphismRestrict
add_to_sga "4 XII 4.3" "Parenthetical clause" AlgebraicGeometry.instIsClosedImmersionSndScheme
add_to_sga "4 XII 5.6" IsClopen
add_to_sga "4 XII 5.6" TopologicalSpace.Clopens
add_to_sga "4 XII 6.13" "special case" HenselianLocalRing
add_to_sga "4 XII 6.13" "partial" Ideal.Cotangent
add_to_sga "4 XIII 1.5" "special case" Algebra.FormallyEtale.comp_bijective
add_to_sga "4 XIII 1.5" "special case" LinearMap.surjective_of_surjective_comp_mkQ
add_to_sga "4 XIV 1.11" "Final shrinking step"
  AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton
add_to_sga "4 XIV 4.3" AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen
add_to_sga "4 XIV 4.3" AlgebraicGeometry.Scheme.affineBasicOpen
add_to_sga "4 XIV 4.3" AlgebraicGeometry.Scheme.basicOpen
add_to_sga "4 XIX 7.3.0" "partial" instAlgebraAdjoinPthRoots
add_to_sga "4 XV 1.3" ConnectedSpace
add_to_sga "4 XVI 3.1" "more general" AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι
add_to_sga "4 XVII 0.3" "One variable with ε = +1" CategoryTheory.Functor.CommShift
add_to_sga "4 XVII 0.4" "special case" ChainComplex
add_to_sga "4 XVII 0.4" "special case" ChainComplex.of
add_to_sga "4 XVII 0.4" "more general" Finsupp.single
add_to_sga "4 XVII 0.4" "special case" HomologicalComplex
add_to_sga "4 XVII 0.4" "more general" Pi.basisFun
add_to_sga "4 XVII 0.4" "more general" Pi.basisFun_apply
add_to_sga "4 XVII 0.4" "more general" Pi.single
add_to_sga "4 XVII 0.5" CategoryTheory.Limits.IndObjectPresentation
add_to_sga "4 XVII 0.5" CategoryTheory.Limits.IsIndObject
add_to_sga "4 XVII 0.5" "more general" CategoryTheory.ObjectProperty.ind
add_to_sga "4 XVII 0.6" CategoryTheory.Ind
add_to_sga "4 XVII 0.6" CategoryTheory.Ind.lim
add_to_sga "4 XVII 0.6" CategoryTheory.Limits.IsIndObject
add_to_sga "4 XVII 0.7" AlgebraicGeometry.Scheme
add_to_sga "4 XVII 0.7" AlgebraicGeometry.Scheme.IsSeparated
add_to_sga "4 XVII 0.9" AlgebraicGeometry.instCartesianMonoidalCategoryOverScheme
add_to_sga "4 XVII 0.9" "n = 2" CategoryTheory.Limits.pullback
add_to_sga "4 XVII 0.10" "partial" AlgebraicGeometry.Scheme.Etale
add_to_sga "4 XVII 0.10" "partial" AlgebraicGeometry.Scheme.etalePrecoverage
add_to_sga "4 XVII 0.10" "étale pretopology on Sch" AlgebraicGeometry.Scheme.etalePretopology
add_to_sga "4 XVII 0.10" "partial" AlgebraicGeometry.Scheme.fppfPrecoverage
add_to_sga "4 XVII 0.10" "fppf topology on Sch" AlgebraicGeometry.Scheme.fppfTopology
add_to_sga "4 XVII 0.10" "partial" AlgebraicGeometry.Scheme.fpqcPrecoverage
add_to_sga "4 XVII 0.10" "fpqc topology on Sch" AlgebraicGeometry.Scheme.fpqcTopology
add_to_sga "4 XVII 0.10" AlgebraicGeometry.Scheme.overGrothendieckTopology
add_to_sga "4 XVII 0.10" "partial" AlgebraicGeometry.Scheme.smallEtalePretopology
add_to_sga "4 XVII 0.10" AlgebraicGeometry.Scheme.smallEtaleTopology
add_to_sga "4 XVII 0.10" AlgebraicGeometry.Scheme.smallGrothendieckTopology
add_to_sga "4 XVII 0.10" AlgebraicGeometry.Scheme.smallGrothendieckTopologyOfLE
add_to_sga "4 XVII 1.1.1" CochainComplex.mappingCone
add_to_sga "4 XVII 1.1.1" "partial" CochainComplex.mappingCone.d_fst_v
add_to_sga "4 XVII 1.1.1" "partial" CochainComplex.mappingCone.d_fst_v'
add_to_sga "4 XVII 1.1.1" "partial" CochainComplex.mappingCone.d_fst_v'_assoc
add_to_sga "4 XVII 1.1.1" "partial" CochainComplex.mappingCone.d_fst_v_assoc
add_to_sga "4 XVII 1.1.1" "partial" CochainComplex.mappingCone.d_snd_v_assoc
add_to_sga "4 XVII 1.1.1" "Forward clause" CochainComplex.trianglehOfDegreewiseSplit_distinguished
add_to_sga "4 XVII 1.1.1" HomotopyCategory.composableArrowsFunctor
add_to_sga "4 XVII 1.1.3" CategoryTheory.Functor.IsTriangulated
add_to_sga "4 XVII 1.1.4.2.1" "special case" CochainComplex.shiftFunctor_obj_X
add_to_sga "4 XVII 1.1.4.2.1" "special case" CochainComplex.shiftFunctor_obj_X'
add_to_sga "4 XVII 1.1.4.2.1" "special case" CochainComplex.shiftFunctor_obj_d
add_to_sga "4 XVII 1.1.4.2.1" "special case" CochainComplex.shiftFunctor_obj_d'
add_to_sga "4 XVII 1.1.4.2.1" "I = {1" HomologicalComplex₂.shiftFunctor₁
add_to_sga "4 XVII 1.1.4.7" "special case"
  CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso
add_to_sga "4 XVII 1.1.4.7" "special case" HomologicalComplex₂.shiftFunctor₁₂CommIso
add_to_sga "4 XVII 1.1.4.7" "special case" HomologicalComplex₂.totalShift₁Iso_hom_totalShift₂Iso_hom
add_to_sga "4 XVII 1.1.4.7" "special case"
  HomologicalComplex₂.totalShift₁Iso_hom_totalShift₂Iso_hom_assoc
add_to_sga "4 XVII 1.1.4.7" "special case" HomologicalComplex₂.totalShift₁Iso_trans_totalShift₂Iso
add_to_sga "4 XVII 1.1.6.2" "One input, special case" CategoryTheory.Functor.mapHomologicalComplex
add_to_sga "4 XVII 1.1.9" "more general" CategoryTheory.DinatTrans
add_to_sga "4 XVII 1.1.9" "more general" CategoryTheory.DinatTrans.mk
add_to_sga "4 XVII 1.1.9" "more general" CategoryTheory.Functor.currying₃
add_to_sga "4 XVII 1.1.9" "more general" CategoryTheory.Functor.curry₃
add_to_sga "4 XVII 1.1.10" CochainComplex.HomComplex
add_to_sga "4 XVII 1.1.10" CochainComplex.HomComplex.δ
add_to_sga "4 XVII 1.1.10" "(iii), composition map" CochainComplex.HomComplex.δ_ofHom_comp
add_to_sga "4 XVII 1.1.10" CochainComplex.HomComplex_d_hom_apply
add_to_sga "4 XVII 1.1.10" "more general" HomologicalComplex.tensorObj
add_to_sga "4 XVII 1.1.11" CategoryTheory.AdditiveFunctor
add_to_sga "4 XVII 1.1.11" CategoryTheory.Functor.Additive
add_to_sga "4 XVII 1.1.11" CategoryTheory.Preadditive
add_to_sga "4 XVII 1.1.11" CategoryTheory.additiveFunctor
add_to_sga "4 XVII 1.1.13" CochainComplex.truncGE
add_to_sga "4 XVII 1.1.13" CochainComplex.truncLE
add_to_sga "4 XVII 1.1.13" "clause" CochainComplex.truncLEXIso
add_to_sga "4 XVII 1.1.13" "clause" CochainComplex.truncLEXIsoCycles
add_to_sga "4 XVII 1.1.13" "more general" HomologicalComplex.truncGE
add_to_sga "4 XVII 1.1.13" "more general" HomologicalComplex.truncLE
add_to_sga "4 XVII 1.1.14" "(ii), special case" CochainComplex.instQuasiIsoAtIntιTruncLE
add_to_sga "4 XVII 1.1.14" "(ii), special case" CochainComplex.instQuasiIsoAtIntπTruncGE
add_to_sga "4 XVII 1.1.14" "more general" CochainComplex.quasiIsoAt_ιTruncLE
add_to_sga "4 XVII 1.1.14" "more general" CochainComplex.quasiIsoAt_πTruncGE
add_to_sga "4 XVII 1.1.14" CochainComplex.ιTruncLE
add_to_sga "4 XVII 1.1.14" CochainComplex.πTruncGE
add_to_sga "4 XVII 1.1.14" "more general" ComplexShape.Embedding.ιTruncLENatTrans
add_to_sga "4 XVII 1.1.14" "more general" HomologicalComplex.instQuasiIsoAtιTruncLEF
add_to_sga "4 XVII 1.1.14" "more general" HomologicalComplex.instQuasiIsoAtπTruncGEF
add_to_sga "4 XVII 1.1.14" "more general" HomologicalComplex.quasiIsoAt_ιTruncLE
add_to_sga "4 XVII 1.1.14" "more general" HomologicalComplex.quasiIsoAt_πTruncGE
add_to_sga "4 XVII 1.1.14" "more general" HomologicalComplex.ιTruncLE
add_to_sga "4 XVII 1.1.14" "more general" HomologicalComplex.πTruncGE
add_to_sga "4 XVII 1.1.15" "more general" CochainComplex.truncGE
add_to_sga "4 XVII 1.1.15" "partial" CochainComplex.truncGEXIsoOpcycles
add_to_sga "4 XVII 1.1.15" "more general" CochainComplex.truncLE
add_to_sga "4 XVII 1.1.15" "partial" CochainComplex.truncLEXIsoCycles
add_to_sga "4 XVII 1.1.15" "Vanishing clause" HomologicalComplex.instIsStrictlySupportedTruncGE
add_to_sga "4 XVII 1.1.15" "more general" HomologicalComplex.truncGE
add_to_sga "4 XVII 1.1.15" "more general" HomologicalComplex.truncLE
add_to_sga "4 XVII 1.1.16" "more general" HomologicalComplex.stupidTrunc
open CategoryTheory.Functor in
add_to_sga "4 XVII 1.2.3" "(i), special case"
  instIsRightDerivedFunctorPlusPlusRightDerivedFunctorPlusRightDerivedFunctorPlusUnitQuasiIso
add_to_sga "4 XVII 1.2.3" "(i), special case" CategoryTheory.Functor.rightDerivedFunctorPlus
open CategoryTheory.Functor in
add_to_sga "4 XVII 1.2.8" "special case"
  instIsRightDerivedFunctorPlusPlusRightDerivedFunctorPlusRightDerivedFunctorPlusUnitQuasiIso
add_to_sga "4 XVII 1.2.8" "(A), special case"
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
add_to_sga "4 XVII 2.2.3" "(ii)" CategoryTheory.IsTriangulated
add_to_sga "4 XVII 2.2.4" "partial" CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂
add_to_sga "4 XVII 2.2.4" "partial"
  CategoryTheory.Pretriangulated.preadditiveYoneda_map_distinguished
add_to_sga "4 XVII 2.2.6" "partial" AlgebraicGeometry.Scheme.Modules.instAbelian
add_to_sga "4 XVII 2.2.6" "partial" PresheafOfModules.instAbelian
add_to_sga "4 XVII 2.2.7" "special case" CochainComplex.of
add_to_sga "4 XVII 2.2.7" "special case" CochainComplex.shiftFunctor
add_to_sga "4 XVII 2.2.7" "partial" CochainComplex.shiftFunctor_obj_X'
add_to_sga "4 XVII 2.2.7" "partial" CochainComplex.shiftFunctor_obj_d
add_to_sga "4 XVII 2.2.7" "partial" CochainComplex.shiftFunctor_obj_d'
add_to_sga "4 XVII 2.2.7" "special case" HomologicalComplex
add_to_sga "4 XVII 2.2.7" "special case" HomologicalComplex.Hom
add_to_sga "4 XVII 2.2.7" "special case" HomologicalComplex.instAbelian
add_to_sga "4 XVII 2.2.7" "special case" HomologicalComplex.instCategory
add_to_sga "4 XVII 2.2.8" "special case" HomotopyCategory.quotient
add_to_sga "4 XVII 2.2.8" "special case" HomotopyCategory.quotient_map_eq_zero_iff
add_to_sga "4 XVII 2.2.8" "special case" instCategoryHomotopyCategory
add_to_sga "4 XVII 2.2.9" "(i), special case" HomotopyCategory.instIsTriangulatedIntUp
add_to_sga "4 XVII 2.2.9" "(i)" HomotopyCategory.instPretriangulatedIntUp
add_to_sga "4 XVII 2.2.10" "(A), special case" HomotopyCategory.instIsTriangulatedIntUpPlus
add_to_sga "4 XVII 2.2.10" "partial" HomotopyCategory.plus
open CategoryTheory.Pseudofunctor.CoGrothendieck in
add_to_sga "4 XVII 2.2.12" "partial"
  instIsEquivalenceαCategoryObjLocallyDiscreteOppositeCatMkOpFiberForgetInducedFunctor
add_to_sga "4 XVII 2.2.13.1" "special case" CategoryTheory.Equivalence.inverse_additive
add_to_sga "4 XVII 2.2.13.1" CategoryTheory.Functor.Additive
add_to_sga "4 XVII 2.2.13.1" CategoryTheory.Functor.IsTriangulated
add_to_sga "4 XVII 2.2.13.1" CategoryTheory.Limits.PreservesFiniteLimits
add_to_sga "4 XVII 2.4.0" "special case" CategoryTheory.Functor.essImageDistTriang
add_to_sga "4 XVII 2.4.0" "special case"
  CategoryTheory.Triangulated.Localization.instIsTriangulatedLocalization
add_to_sga "4 XVII 2.4.0" "special case"
  CategoryTheory.Triangulated.Localization.instIsTriangulatedLocalization'
add_to_sga "4 XVII 2.4.0" "Over a one-point base"
  CategoryTheory.Triangulated.Localization.instPretriangulatedLocalization
add_to_sga "4 XVII 2.4.0" "Over a one-point base"
  CategoryTheory.Triangulated.Localization.instPretriangulatedLocalization'
add_to_sga "4 XVII 2.4.0" "Over a one-point base"
  CategoryTheory.Triangulated.Localization.pretriangulated
add_to_sga "4 XVII 3.2.3" "(i): open-immersion half"
  AlgebraicGeometry.isOpenImmersion_isMultiplicative
add_to_sga "4 XVII 3.2.4" "(ii)" CategoryTheory.Limits.HasPullbacks
add_to_sga "4 XVII 3.2.4" "(iii)" CategoryTheory.MorphismProperty.HasFactorization
add_to_sga "4 XVII 3.2.4" "(i)" CategoryTheory.WideSubcategory
add_to_sga "4 XVII 3.2.4" "(i)" CategoryTheory.WideSubcategory.category
add_to_sga "4 XVII 3.2.6" CategoryTheory.IsCofiltered
add_to_sga "4 XVII 3.3.1" CategoryTheory.Pseudofunctor
add_to_sga "4 XVII 3.3.1" CategoryTheory.StrictlyUnitaryPseudofunctor
add_to_sga "4 XVII 3.3.3" CategoryTheory.CatCommSq
add_to_sga "4 XVII 3.3.3" "(i bis)" CategoryTheory.Pseudofunctor
add_to_sga "4 XVII 3.3.3" "special case" CategoryTheory.Pseudofunctor.isoMapOfCommSq
add_to_sga "4 XVII 4.1.1" "(ii)" LinearMap.lTensor_injective_of_exact_of_flat
add_to_sga "4 XVII 4.1.2" "more general"
  HomotopyCategory.Plus.instIsIsoAppOfInjectiveXIntAsHomologicalComplexUpHomotopicObjPlus
add_to_sga "4 XVII 4.1.6" "partial" HomologicalComplex.tensorObj
add_to_sga "4 XVII 4.1.6" "special case" PresheafOfModulesOfCommRing.Monoidal.tensorObj
add_to_sga "4 XVII 4.1.6" "special case" TensorProduct
add_to_sga "4 XVII 4.2.12" "(i)" CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mk
add_to_sga "4 XVII 5.5.2.2" PolynomialLaw
add_to_sga "4 XVII 5.5.2.2" "partial" PolynomialLaw.isCompat
add_to_sga "4 XVII 5.5.2.2" "partial" PolynomialLaw.isCompat_apply
add_to_sga "4 XVII 5.5.2.2" PolynomialLaw.mk
add_to_sga "4 XVII 5.5.3" AlgebraicTopology.AlternatingCofaceMapComplex.obj
add_to_sga "4 XVII 5.5.3" AlgebraicTopology.AlternatingCofaceMapComplex.objD
add_to_sga "4 XVII 5.5.3" AlgebraicTopology.alternatingCofaceMapComplex
add_to_sga "4 XVII 5.5.3" CategoryTheory.CosimplicialObject
add_to_sga "4 XVII 5.5.3" CochainComplex.IsStrictlyGE
add_to_sga "4 XVII 5.5.4.1" "more general" CategoryTheory.Adjunction.localization
add_to_sga "4 XVII 5.5.6.3" Module.Finite
add_to_sga "4 XVII 5.5.6.3" Module.Flat
add_to_sga "4 XVII 5.5.6.3" Module.Projective
add_to_sga "4 XVII 5.5.6.3" "A = ℤ" instPreservesHomologyFunctorAddCommGrpCatColim
add_to_sga "4 XVII 5.5.25.2" "partial" CochainComplex.mappingCone
add_to_sga "4 XVII 5.5.29" "partial" SheafOfModules.IsQuasicoherent
add_to_sga "4 XVII 5.5.29" "partial" SheafOfModules.isQuasicoherent
add_to_sga "4 XVII 6.2.1" "more general" CategoryTheory.Limits.biproduct.matrix
add_to_sga "4 XVII 6.2.8" CategoryTheory.Arrow.augmentedCechNerve
add_to_sga "4 XVII 6.2.8" CategoryTheory.SimplicialObject.augmentedCechNerve
add_to_sga "4 XVII 6.2.8" Fin
add_to_sga "4 XVII 6.2.8" SimplexCategory.mk
add_to_sga "4 XVII 6.3.1" "special case" IsBaseChange.det_endHom
add_to_sga "4 XVII 6.3.1" "special case" LinearMap.det_baseChange
add_to_sga "4 XVII 6.3.1" "special case" LinearMap.det_comp
add_to_sga "4 XVII 6.3.1" "special case" LinearMap.det_smul
add_to_sga "4 XVII 6.3.1" "special case" Matrix.GeneralLinearGroup.map_det
add_to_sga "4 XVII 6.3.1" "partial" exteriorPower.map_comp
add_to_sga "4 XVII 6.3.10" "more general" Algebra.norm
add_to_sga "4 XVII 6.3.15" "(iv), special case" Algebra.trace_algebraMap
add_to_sga "4 XVII 6.3.15" "Clause (v), special case" Algebra.trace_comp_trace
add_to_sga "4 XVII 6.3.15" "Clause (v), special case" Algebra.trace_comp_trace_of_basis
add_to_sga "4 XVII 6.3.15" "Clause (v), special case" Algebra.trace_trace
add_to_sga "4 XVII 6.3.15" "Clause (v), special case" Algebra.trace_trace_of_basis
add_to_sga "4 XVII 6.3.15" "(v)" trace_trace
add_to_sga "4 XVII 7.0.5" "more general" CategoryTheory.SimplicialObject.augmentedCechNerve
add_to_sga "4 XVII 7.0.5" "partial" CategoryTheory.SimplicialObject.cechNerve
add_to_sga "4 XVII 7.1.2" "partial" CategoryTheory.SimplicialObject.augmentedCechNerve
add_to_sga "4 XVII 7.1.2" "partial" CategoryTheory.SimplicialObject.cechNerve
add_to_sga "4 XVII 7.3.1" "more general" HomologicalComplex.truncLE
add_to_sga "4 XVII 7.3.1" "more general" HomologicalComplex.truncLE'
add_to_sga "4 XVII 7.3.3" CategoryTheory.ExactFunctor
add_to_sga "4 XVII 7.3.3" CategoryTheory.exactFunctor
add_to_sga "4 XVII 7.3.3" "more general" CochainComplex.mapBifunctor
add_to_sga "4 XVII 7.3.3" "more general" HomologicalComplex.mapBifunctor
add_to_sga "4 XVII 7.3.3" "more general" HomologicalComplex.mapBifunctorMap
add_to_sga "4 XVII 7.3.3" "special case" HomologicalComplex.quasiIso_map_of_preservesHomology
add_to_sga "4 XVII 7.3.3" "special case" HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory
add_to_sga "4 XVIII 1.4.7" "(x), special case" AddCommGrpCat.hom_add_apply
add_to_sga "4 XVIII 1.4.7" "b, special case" AddCommGrpCat.instAddHom
add_to_sga "4 XVIII 1.4.7" "(x), special case" AddHom.add_apply
add_to_sga "4 XVIII 1.4.7" "b, special case" AddHom.instAdd
add_to_sga "4 XVIII 1.4.7" "b, special case" AddMonoidHom.add
add_to_sga "4 XVIII 1.4.7" "(x), special case" AddMonoidHom.add_apply
add_to_sga "4 XVIII 1.4.7" "c" CategoryTheory.Monoidal.associator_hom_app
add_to_sga "4 XVIII 1.4.14" "partial" DerivedCategory.IsGE
add_to_sga "4 XVIII 1.4.14" "partial" DerivedCategory.IsLE
add_to_sga "4 XVIII 1.4.21" HomologicalComplex.single
add_to_sga "4 XVIII 1.4.24" "more general" CategoryTheory.Sheaf.freeYoneda
add_to_sga "4 XVIII 3.1.9" "more general"
  HomotopyCategory.Plus.instIsIsoAppOfInjectiveXIntAsHomologicalComplexUpHomotopicObjPlus
add_to_sga "4 XVIII 3.1.12.1" "partial" PresheafOfModules.restrictScalarsObj
add_to_sga "4 XVIII 3.1.15" CategoryTheory.Comma
add_to_sga "4 XVIII 3.2.6" "partial" Module.Dual
add_to_sga "4 XVIII 3.2.6" "special case" Module.injective_of_isSemisimpleRing
