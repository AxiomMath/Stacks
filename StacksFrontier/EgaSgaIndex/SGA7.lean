module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.CastCard
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Submersion
import Mathlib.GroupTheory.Divisible
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.Graded.External
import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.Defs
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.Isocrystal
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Irreducible
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Sober
import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# SGA 7 references registered by name

Declarations realizing numbered items of SGA 7, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_sga "7 I 0.0.1" AlgebraicGeometry.Spec
add_to_sga "7 I 0.0.5" Algebra.EssFiniteType
add_to_sga "7 I 0.0.5" RingHom.EssFiniteType
add_to_sga "7 I 0.3" AddSubgroup.inertia
add_to_sga "7 I 0.3" ExpChar
add_to_sga "7 I 0.3" Field.absoluteGaloisGroup
add_to_sga "7 I 0.3" "partial" Ideal.Quotient.map_ker_stabilizer_subtype
add_to_sga "7 I 0.3" "partial" Ideal.Quotient.stabilizerQuotientInertiaEquiv
add_to_sga "7 I 0.3" "partial" Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk
add_to_sga "7 I 0.3" "partial" IsFractionRing.ker_stabilizerHom
add_to_sga "7 I 0.3" "partial" IsFractionRing.stabilizerQuotientInertiaEquiv
add_to_sga "7 I 0.3" ValuationSubring.inertiaSubgroup
add_to_sga "7 I 0.5.2" "special case" Algebra.IsAlgebraic.isSeparable_of_perfectField
add_to_sga "7 I 0.5.3" AdjoinRoot
add_to_sga "7 I 0.5.3" PerfectClosure
add_to_sga "7 I 0.5.3" WittVector
add_to_sga "7 I 0.5.3" WittVector.instCommRing
add_to_sga "7 I 0.5.3" "partial" WittVector.isAdicCompleteIdealSpanP
add_to_sga "7 I 0.5.3" "partial" WittVector.isDiscreteValuationRing
add_to_sga "7 I 0.5.3" "partial" WittVector.quotientPEquiv
add_to_sga "7 I 1.3" "partial" Submodule.QuotientTorsion.torsion_eq_bot
add_to_sga "7 I 2.1" FiberBundle
add_to_sga "7 IX 1.0" LinearMap.IsAlt
add_to_sga "7 IX 1.0" LinearMap.IsPerfPair
add_to_sga "7 IX 1.0" LinearMap.Nondegenerate
add_to_sga "7 IX 1.1" "more general" CategoryTheory.CommGrpObj.ofRepresentableBy
add_to_sga "7 IX 1.1" "special case"
  CommAlgCat.instIsEquivalenceOppositeFiniteEtaleFintypeCatFiberOfIsSepClosed
add_to_sga "7 IX 1.1" Field.absoluteGaloisGroup
add_to_sga "7 IX 2.4" Representation.invariants
add_to_sga "7 IX 3.1" "partial" ExpChar.prime
add_to_sga "7 IX 3.1" "partial" ExpChar.zero
add_to_sga "7 IX 3.1.3" "parenthetical clause" AlgebraicGeometry.Flat.isIso_of_surjective_of_mono
add_to_sga "7 IX 3.1.3" "parenthetical clause" AlgebraicGeometry.IsOpenImmersion.isIso
add_to_sga "7 IX 3.1.3" "special case" AlgebraicGeometry.Scheme.Hom.isIso_iff_finrank_eq
add_to_sga "7 IX 3.1.3" "partial, special case"
  AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank
add_to_sga "7 IX 3.1.3" "special case" Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant
add_to_sga "7 IX 3.1.3" "special case" Module.free_of_flat_of_finrank_eq
add_to_sga "7 IX 3.1.3" "special case" Module.free_of_flat_of_isLocalRing
add_to_sga "7 IX 3.1.3" "partial, special case" Module.isLocallyConstant_rankAtStalk
add_to_sga "7 IX 3.1.3" "partial, special case" Module.rankAtStalk_eq_of_le_of_finite_of_flat
add_to_sga "7 IX 3.1.3" "special case" Module.rankAtStalk_le_one_iff_surjective
add_to_sga "7 IX 3.6" "partial" Ideal.exists_comap_galRestrict_eq
add_to_sga "7 IX 4.1" Rep.quotientToInvariants
add_to_sga "7 IX 4.1" Rep.quotientToInvariantsFunctor
add_to_sga "7 IX 4.1" "partial" Rep.toInvariants
add_to_sga "7 IX 4.1" "partial" Representation.invariants
add_to_sga "7 IX 4.1" Representation.quotientToInvariants
add_to_sga "7 IX 4.1" "partial" Representation.quotientToInvariants_lift
add_to_sga "7 IX 4.2" "Quotient clause of 4.2.1" Ideal.Quotient.stabilizerQuotientInertiaEquiv
add_to_sga "7 IX 4.2" "Quotient clause of 4.2.1" IsFractionRing.stabilizerQuotientInertiaEquiv
add_to_sga "7 IX 4.2" cyclotomicCharacter
add_to_sga "7 IX 4.2" "partial" cyclotomicCharacter.spec
add_to_sga "7 IX 4.3" FiniteField.frobeniusAlgEquiv
add_to_sga "7 IX 4.3.2" "special case" FiniteField.frobeniusAlgHom
add_to_sga "7 IX 4.3.2" "special case" LinearMap.frobenius
add_to_sga "7 IX 4.3.2" "special case" LinearMap.iterateFrobenius
add_to_sga "7 IX 4.3.2" "partial" RingHom.iterateFrobenius_comm
add_to_sga "7 IX 4.3.2" "partial" RingHom.map_iterateFrobenius
add_to_sga "7 IX 4.3.2" "partial" RingHom.map_iterate_frobenius
add_to_sga "7 IX 4.7.2" "special case" IsAddKleinFour.addEquiv'
add_to_sga "7 IX 4.7.2" "Order-four case (r = 2)" IsKleinFour.mulEquiv'
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one
add_to_sga "7 IX 4.7.3" "(u − 1) prime" IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one'
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.ramificationIdxIn_eq
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.ramificationIdx_eq
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one'
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff
add_to_sga "7 IX 4.7.3" "partial" IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff'
add_to_sga "7 IX 4.7.3" "partial" IsPrimitiveRoot.eq_neg_one_of_two_right
add_to_sga "7 IX 4.7.3" "partial" IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_ne_two
add_to_sga "7 IX 4.7.3" "partial" IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_ne_two'
add_to_sga "7 IX 4.7.3" "partial" IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_pow_ne_two
add_to_sga "7 IX 4.7.3" "u − 1 divides p" IsPrimitiveRoot.toInteger_sub_one_dvd_prime
add_to_sga "7 IX 4.7.3" "u − 1 divides p" IsPrimitiveRoot.toInteger_sub_one_dvd_prime'
add_to_sga "7 IX 4.7.3" "(u − 1) prime, p odd" IsPrimitiveRoot.zeta_sub_one_prime_of_ne_two
add_to_sga "7 IX 4.7.3" Subring.closure
add_to_sga "7 IX 4.7.3" TensorProduct
add_to_sga "7 IX 4.7.4" "more general" Commute.of_orderOf_dvd_two
add_to_sga "7 IX 4.7.4" "special case" IsKleinFour.isMulCommutative
add_to_sga "7 IX 4.7.4" "special case" addCommMonoidOfExponentTwo
add_to_sga "7 IX 4.7.4" "special case" add_comm_of_exponent_two
add_to_sga "7 IX 4.7.4" "special case" commMonoidOfExponentTwo
add_to_sga "7 IX 4.7.4" "special case" mul_comm_of_exponent_two
add_to_sga "7 IX 6.2.2" "more general" WeierstrassCurve.ofJNe0Or1728_j
add_to_sga "7 IX 9.4" Module.Dual
add_to_sga "7 IX 9.7" Ideal.ramificationIdx
add_to_sga "7 IX 9.7" Ideal.ramificationIdx'
add_to_sga "7 IX 10.3" "special case"
  Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
add_to_sga "7 IX 10.3" "special case"
  Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
add_to_sga "7 IX 11.0" "partial" AddCommGroup.primaryComponent
add_to_sga "7 IX 11.0" "partial" CommGroup.primaryComponent
add_to_sga "7 IX 11.1" ModN
add_to_sga "7 IX 11.1" Representation.invariants
add_to_sga "7 IX 11.3" TopRep.homogeneousCochains
add_to_sga "7 IX 11.3" continuousCohomology
add_to_sga "7 IX 11.8" IsSepClosed
add_to_sga "7 IX 12.3" irreducibleComponents
add_to_sga "7 IX 13.1" "special case" GroupLieAlgebra
add_to_sga "7 IX 13.5.4" "partial" ZMod.rootsOfUnityAddChar
add_to_sga "7 IX 14.2" "special case" ModN
add_to_sga "7 IX 14.3.5" "partial" IsAdicComplete
add_to_sga "7 VI 1.2" DualNumber
add_to_sga "7 VI 1.2" "more general" TrivSqZeroExt
add_to_sga "7 VI 1.7" "partial" Ideal.mapCotangent
add_to_sga "7 VI 1.7" "special case" IsLocalRing.CotangentSpace
add_to_sga "7 VI 1.7" "special case"
  IsLocalRing.instFiniteDimensionalResidueFieldCotangentSpaceOfIsNoetherianRing
add_to_sga "7 VI 1.15" "special case" DualNumber
add_to_sga "7 VI 1.15" "relation ε² = 0" DualNumber.eps_mul_eps
add_to_sga "7 VI 1.15" TrivSqZeroExt
add_to_sga "7 VI 1.1(a)" CategoryTheory.Grothendieck.Hom
add_to_sga "7 VI 1.1(a)" CategoryTheory.Grothendieck.comp
add_to_sga "7 VI 1.1(a)" "partial" CategoryTheory.Grothendieck.functor_comp_forget
add_to_sga "7 VI 1.1(a)" CategoryTheory.Grothendieck.instCategory
add_to_sga "7 VI 1.1(a)" "induced functor" CategoryTheory.Grothendieck.map
add_to_sga "7 VI 1.1(a)" "induced functor" CategoryTheory.NatTrans.mapElements
add_to_sga "7 VI 1.1(a)" "more general" CategoryTheory.Pseudofunctor.Grothendieck.category
add_to_sga "7 VI 1.1(a)" "more general" CategoryTheory.Pseudofunctor.Grothendieck.categoryStruct
add_to_sga "7 VI 1.1(a)" "partial" CategoryTheory.Functor.Elements.instCategory
add_to_sga "7 VI 1.3(c)" "dual numbers k[ε] = k[k]" DualNumber
add_to_sga "7 VI 1.3(c)" TrivSqZeroExt
add_to_sga "7 VI 3.6" "partial" CommRingCat.tensorProd
add_to_sga "7 VI 3.1(a)" CategoryTheory.Sheaf
add_to_sga "7 VI 3.1(a)" CategoryTheory.presheafToSheaf
add_to_sga "7 VI 3.1(a)" CategoryTheory.sheafToPresheaf
add_to_sga "7 VI 3.1(a)" "partial" CategoryTheory.sheafToPresheaf_isRightAdjoint
add_to_sga "7 VI 3.1(a)" "partial" PresheafOfModules.instIsLeftAdjointSheafOfModulesSheafification
add_to_sga "7 VI 3.1(b)" CategoryTheory.Sheaf.H'
add_to_sga "7 VI 3.1(b)" CategoryTheory.Sheaf.cohomologyPresheaf
add_to_sga "7 VI 3.1(b)" CategoryTheory.Sheaf.cohomologyPresheafFunctor
add_to_sga "7 VI 3.1(b)" "partial" CategoryTheory.cechComplexFunctor
add_to_sga "7 VI 4.7" AlgebraicGeometry.Scheme.Hom.ker
add_to_sga "7 VI 4.7" "partial" AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι
add_to_sga "7 VI 4.7" "special case" Ideal.Cotangent
add_to_sga "7 VI 4.7" Ideal.cotangentEquivIdeal
add_to_sga "7 VI 4.7" "special case" Ideal.cotangentIdeal
add_to_sga "7 VI 4.14" "special case" Algebra.SubmersivePresentation.basisCotangent
add_to_sga "7 VI 4.14" "special case" Algebra.SubmersivePresentation.basisCotangent_apply
add_to_sga "7 VI 4.14" "special case" Algebra.SubmersivePresentation.cotangentEquiv
add_to_sga "7 VI 4.14" "partial" MvPowerSeries
add_to_sga "7 VI 5.1" Ideal.Fiber
add_to_sga "7 VI 5.5" "Coherence of Ω_{X|S}" KaehlerDifferential.finite
add_to_sga "7 VI 5.8" AdicCompletion
add_to_sga "7 VI 5.8" "special case" AlgebraicGeometry.specTargetImageIdeal
add_to_sga "7 VI 5.8" "special case" Ideal.under
add_to_sga "7 VII 1.1" "special case" AddGroupExtension
add_to_sga "7 VII 1.1" "special case" GroupExtension
add_to_sga "7 VII 1.3.1.0" "Hom_pt(P, special case" OneHom
add_to_sga "7 VII 1.3.1.0" "Hom_pt(P, special case" Pointed.Hom
add_to_sga "7 VII 1.3.4" "Morphisms of EXT(P" AddGroupExtension.Equiv
add_to_sga "7 VII 1.3.4" "Objects of EXT(P" GroupExtension
add_to_sga "7 VII 1.3.8" "partial" AlgebraicGeometry.Flat.instFstScheme
add_to_sga "7 VII 1.3.8" "partial" AlgebraicGeometry.Flat.instMorphismRestrict
add_to_sga "7 VII 1.3.8" "partial" AlgebraicGeometry.Flat.instSndScheme
add_to_sga "7 VII 1.3.8" "partial" AlgebraicGeometry.QuasiSeparated
add_to_sga "7 VII 1.3.8" "special case" AlgebraicGeometry.Scheme.instSubcanonicalFppfTopology
add_to_sga "7 VII 1.3.8" "special case" AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology
add_to_sga "7 VII 1.3.8" "special case" AlgebraicGeometry.Scheme.instSubcanonicalProetaleTopology
add_to_sga "7 VII 1.3.8" "special case" AlgebraicGeometry.Scheme.subcanonical_zariskiTopology
add_to_sga "7 VII 1.3.8" "special case"
  AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_left
add_to_sga "7 VII 1.3.8" "special case"
  AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
add_to_sga "7 VII 1.3.8" CategoryTheory.GrothendieckTopology.Subcanonical
add_to_sga "7 VII 1.3.8" "more general"
  CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
add_to_sga "7 VII 1.3.8" CategoryTheory.GrothendieckTopology.yoneda
add_to_sga "7 VII 1.3.8" CategoryTheory.Sheaf.canonicalTopology
add_to_sga "7 VII 1.3.8" "canonical topology case" CategoryTheory.Sheaf.isSheaf_of_isRepresentable
add_to_sga "7 VII 1.3.8" "canonical topology case" CategoryTheory.Sheaf.isSheaf_yoneda_obj
add_to_sga "7 VII 1.3.8" "flatness clause" CommRingCat.instIsStableUnderCobaseChangeFlat
add_to_sga "7 VII 1.3.8" "flatness clause" Module.Flat.isBaseChange
add_to_sga "7 VII 1.3.8" "flatness clause" RingHom.Flat.isStableUnderBaseChange
add_to_sga "7 VII 1.4" "special case" FreeAbelianGroup
add_to_sga "7 VII 1.4" "special case" FreeAbelianGroup.of
add_to_sga "7 VII 1.4" "special case" SheafOfModules.free
add_to_sga "7 VII 1.4" "special case" SheafOfModules.freeFunctor
add_to_sga "7 VII 2.9" "more general" CategoryTheory.Limits.Pi.ι
add_to_sga "7 VII 3.1" ChainComplex
add_to_sga "7 VII 3.1" "more general" CochainComplex.truncGE
add_to_sga "7 VII 3.1" ComplexShape.down
add_to_sga "7 VII 3.1" "more general" HomologicalComplex
add_to_sga "7 VII 3.1.7" "special case" CategoryTheory.Abelian.Ext.addEquiv₀
add_to_sga "7 VII 3.1.7" "partial" CategoryTheory.Abelian.Ext.homEquiv₀
add_to_sga "7 VII 3.1.7" "special case" CategoryTheory.Abelian.Ext.linearEquiv₀
add_to_sga "7 VII 3.1.7" "Bijectivity of Hom(X" CategoryTheory.Abelian.Ext.mk₀_bijective
add_to_sga "7 VII 3.2" "special case" CategoryTheory.Abelian.Ext
add_to_sga "7 VII 3.2" "special case" CategoryTheory.Abelian.Ext.homAddEquiv
add_to_sga "7 VII 3.2" "special case" CategoryTheory.Abelian.Ext.homEquiv
add_to_sga "7 VII 3.2" "special case" CategoryTheory.ProjectiveResolution.cochainComplex
add_to_sga "7 VII 3.2" "c(X, special case"
  CategoryTheory.ShortComplex.ShortExact.extClass_naturality
add_to_sga "7 VII 3.2" ChainComplex.cochainComplexEquivalence
add_to_sga "7 VII 3.3.6" "partial" CategoryTheory.Abelian.Ext.covariantSequence_exact
add_to_sga "7 VII 3.3.6" "Exactness at Extⁿ⁺¹(L•"
  CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'
add_to_sga "7 VII 3.3.6" "Exactness at Extⁿ(L•,A)"
  CategoryTheory.Abelian.Ext.covariant_sequence_exact₂'
add_to_sga "7 VII 3.3.6" "Exactness at Extⁿ(L•,A″)"
  CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'
add_to_sga "7 VII 3.4" "special case" CategoryTheory.Abelian.Ext.precomp
add_to_sga "7 VII 3.4" "special case" CategoryTheory.Abelian.Ext.precompOfLinear
add_to_sga "7 VII 3.4" "special case" CategoryTheory.ShortComplex.ShortExact.extClass_naturality
add_to_sga "7 VII 3.4" "special case" Ext
add_to_sga "7 VII 3.4.9" "partial" CategoryTheory.Abelian.Ext.contravariantSequence
add_to_sga "7 VII 3.4.9" "partial" CategoryTheory.Abelian.Ext.contravariantSequence_exact
add_to_sga "7 VII 3.4.9" "partial" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'
add_to_sga "7 VII 3.4.9" "partial" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂'
add_to_sga "7 VII 3.5" "special case" Ab
add_to_sga "7 VII 3.5" "special case" CommGrpCat
add_to_sga "7 VII 3.5" "special case" Module.Flat.of_free
add_to_sga "7 VII 3.5" "special case" ModuleCat
add_to_sga "7 VII 3.5" "special case" ModuleCat.forget₂AddCommGroupIsEquivalence
add_to_sga "7 VII 3.5" "partial" ModuleCat.free
add_to_sga "7 VII 3.6" "3.6.2" HomologicalComplex.tensorHom
add_to_sga "7 VII 3.6" HomologicalComplex.tensorObj
add_to_sga "7 VII 3.6.7" "special case" groupHomology.H1Iso
add_to_sga "7 VII 3.6.7" "special case" groupHomology.H2Iso
add_to_sga "7 VII 3.6.7" "special case" groupHomology.isoShortComplexH2
add_to_sga "7 VII 3.6.7" "special case" groupHomology.shortComplexH2
add_to_sga "7 VII 3.7.5" CategoryTheory.Abelian.Ext.contravariantSequence
add_to_sga "7 VII 3.7.5" "special case" CategoryTheory.Abelian.Ext.contravariantSequence_exact
add_to_sga "7 VII 3.7.5" "partial" CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂
add_to_sga "7 VII 3.7.5" "Exactness at Ext^n(P"
  CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂'
add_to_sga "7 VII 3.7.5" CategoryTheory.Abelian.Ext.covariantSequence
add_to_sga "7 VII 3.7.5" "special case" CategoryTheory.Abelian.Ext.covariantSequence_exact
add_to_sga "7 VII 3.7.5" "partial" CategoryTheory.Abelian.Ext.covariant_sequence_exact₁
add_to_sga "7 VII 3.7.5" "Exactness at Ext^{n+1}(P"
  CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'
add_to_sga "7 VII 3.7.5" "partial" CategoryTheory.Abelian.Ext.covariant_sequence_exact₂
add_to_sga "7 VII 3.7.5" "Exactness at Ext^n(P"
  CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'
add_to_sga "7 VII 3.7.5" CategoryTheory.DeltaFunctor
add_to_sga "7 VII 3.7.6" "partial" Module.Flat.iff_lTensor_exact'
add_to_sga "7 VII 3.7.6" "partial" Module.Flat.iff_lTensor_preserves_shortComplex_exact
add_to_sga "7 VII 3.7.6" "partial" Module.Flat.iff_rTensor_exact
add_to_sga "7 VII 3.7.6" "partial" Module.Flat.iff_rTensor_preserves_shortComplex_exact
add_to_sga "7 VII 3.7.6" "partial" Module.Flat.lTensor_exact
add_to_sga "7 VII 3.7.6" "partial" Module.Flat.lTensor_shortComplex_exact
add_to_sga "7 VII 3.7.6" "partial" Module.Flat.rTensor_exact
add_to_sga "7 VII 3.7.6" "partial" Module.Flat.rTensor_shortComplex_exact
add_to_sga "7 VII 3.7.6" "partial" lTensor_exact
add_to_sga "7 VII 3.8.8" "partial" HomologicalComplex.tensorObj
add_to_sga "7 VIII 0.2" "partial" AlgebraicGeometry.Scheme.fppfPrecoverage
add_to_sga "7 VIII 0.2" "partial" AlgebraicGeometry.Scheme.fppfTopology
add_to_sga "7 VIII 1.6" "more general" CategoryTheory.ihom.ev
add_to_sga "7 VIII 1.6" "special case" Module.Dual.eval
add_to_sga "7 VIII 1.6" "special case" Module.Dual.eval_apply
add_to_sga "7 VIII 2.1" AddSubgroup.torsionBy
add_to_sga "7 VIII 2.1" "Notation P_n = P/nP" ModN
add_to_sga "7 VIII 2.1" "partial" ModN.mkQ
add_to_sga "7 VIII 2.2.7" "special case" AddCommGroup.divisibleByIntOfSMulTopEqTop
add_to_sga "7 VIII 2.2.7" "special case" AddCommGroup.smul_top_eq_top_of_divisibleBy_int
add_to_sga "7 VIII 2.3" ModN
add_to_sga "7 VIII 2.3.19" "more general" DerivedCategory.triangleOfSESδ
add_to_sga "7 VIII 4.1" "more general" AlgebraicGeometry.smooth_of_grpObj
add_to_sga "7 VIII 7.0" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_sga "7 VIII 7.0" AlgebraicGeometry.Scheme.residueField
add_to_sga "7 VIII 7.0" "more general" AlgebraicGeometry.Spec
add_to_sga "7 VIII 7.3.5" Ideal.ramificationIdx
add_to_sga "7 VIII 7.3.5" Ideal.ramificationIdx'
add_to_sga "7 VIII 7.3.5.3" "partial" Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff
add_to_sga "7 VIII 7.3.5.3" "partial" Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff
add_to_sga "7 VIII 7.3.5.3" "Étale case" Ideal.ramificationIdx'_eq_one
add_to_sga "7 VIII 7.3.5.3" "special case" Ideal.ramificationIdx'_eq_one_iff
add_to_sga "7 VIII 7.3.5.3" "partial" Ideal.ramificationIdx'_eq_one_of_map_localization
add_to_sga "7 VIII 7.3.5.3" "Étale case" Ideal.ramificationIdx_eq_one
add_to_sga "7 VIII 7.3.5.3" "special case" Ideal.ramificationIdx_eq_one_iff
add_to_sga "7 VIII 7.3.5.3" "Étale case" Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
add_to_sga "7 VIII 7.3.5.3" "partial" Ideal.ramificationIdx_eq_one_of_map_localization
add_to_sga "7 X 2.26" AdicCompletion
add_to_sga "7 XI 1.1" "special case" AlgebraicGeometry.AffineSpace.isoOfIsAffine
add_to_sga "7 XI 1.3" "partial" Algebra.Extension.exact_cotangentComplex_toKaehler
add_to_sga "7 XI 2.4" Finset.card
add_to_sga "7 XI 2.4" Int.fdiv
add_to_sga "7 XI 2.4" Int.floor
add_to_sga "7 XI 2.4" Set.ncard
add_to_sga "7 XII 1.1" QuadraticMap.polar
add_to_sga "7 XII 1.1" QuadraticMap.polarBilin
add_to_sga "7 XII 1.2" "special case" QuadraticForm.equivalent_of_isAlgClosed
add_to_sga "7 XII 1.3" CliffordAlgebra.ι
add_to_sga "7 XII 1.3.1" "more general" CliffordAlgebra.contractLeft
add_to_sga "7 XII 1.3.1" "degree-zero clause" CliffordAlgebra.contractLeft_one
add_to_sga "7 XII 1.3.1" "degree-one clause" CliffordAlgebra.contractLeft_ι
add_to_sga "7 XII 1.3.1" "more general" CliffordAlgebra.even
add_to_sga "7 XII 1.3.1" "uniqueness of [λ]" CliffordAlgebra.even.algHom_ext
add_to_sga "7 XII 1.3.1" "uniqueness of [λ]" CliffordAlgebra.even.algHom_ext_iff
add_to_sga "7 XII 1.3.1" "special case" CliffordAlgebra.evenEquivEvenNeg
add_to_sga "7 XII 1.3.1" "more general" CliffordAlgebra.evenOdd
add_to_sga "7 XII 1.3.1" "more general" CliffordAlgebra.evenOdd_isCompl
add_to_sga "7 XII 1.3.1" "special case" CliffordAlgebra.evenToNeg
add_to_sga "7 XII 1.3.1" "special case" CliffordAlgebra.evenToNeg_comp_evenToNeg
add_to_sga "7 XII 1.3.1" "more general" CliffordAlgebra.gradedAlgebra
add_to_sga "7 XII 1.3.1" "uniqueness of s" CliffordAlgebra.hom_ext
add_to_sga "7 XII 1.3.1" "uniqueness of s" CliffordAlgebra.hom_ext_iff
add_to_sga "7 XII 1.3.1" "special case" CliffordAlgebra.involute_eq_of_mem_even
add_to_sga "7 XII 1.9" "partial" CliffordAlgebra.ofProd
add_to_sga "7 XII 1.9" CliffordAlgebra.prodEquiv
add_to_sga "7 XII 1.9" "partial" CliffordAlgebra.toProd
add_to_sga "7 XII 1.9" GradedTensorProduct.instAlgebra
add_to_sga "7 XII 1.9" GradedTensorProduct.instMul
add_to_sga "7 XII 1.9" GradedTensorProduct.instRing
add_to_sga "7 XII 1.9" GradedTensorProduct.mulHom
add_to_sga "7 XII 1.9" "special case" GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
add_to_sga "7 XII 1.9" "special case" GradedTensorProduct.tmul_zero_coe_mul_coe_tmul
add_to_sga "7 XII 1.9" TensorProduct.gradedMul
add_to_sga "7 XII 1.9" "more general" TensorProduct.tmul_of_gradedMul_of_tmul
add_to_sga "7 XII 1.10" CliffordAlgebra.prodEquiv
add_to_sga "7 XII 2.6" "local algebra C⁺(X" CliffordAlgebra.even
add_to_sga "7 XIII 0.2" "more general" CategoryTheory.Sheaf
add_to_sga "7 XIII 0.2" Field.absoluteGaloisGroup
add_to_sga "7 XIII 0.2" "partial" Ideal.Quotient.map_ker_stabilizer_subtype
add_to_sga "7 XIII 0.2" "more general" IsLocalRing.closedPoint
add_to_sga "7 XIII 0.2" "partial" ValuationSubring.inertiaSubgroup
add_to_sga "7 XIII 1.4.2" "partial" CochainComplex.trianglehOfDegreewiseSplit_distinguished
add_to_sga "7 XIII 1.4.2" "partial"
  HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit
add_to_sga "7 XIV 1.1" FundamentalGroup
add_to_sga "7 XIV 1.1" "XIV 1.1.2, special case" IsCoveringMap.fundamentalGroupMulAction
add_to_sga "7 XIV 1.1.1" FundamentalGroup
add_to_sga "7 XIV 1.1.1" "more general" FundamentalGroup.mul_def
add_to_sga "7 XIV 1.1.1" "more general" HomotopyGroup
add_to_sga "7 XIV 1.1.1" HomotopyGroup.group
add_to_sga "7 XIV 1.1.1" "more general" Path.Homotopic.Quotient
add_to_sga "7 XIV 1.1.1" Path.Homotopic.Quotient.mk
add_to_sga "7 XIV 1.1.2" "special case" IsCoveringMap.fundamentalGroupMulAction
add_to_sga "7 XIV 1.1.2" "special case" IsLocalHomeomorph.monodromy_theorem
add_to_sga "7 XIV 1.1.4" "Identification of π₁(X" IsQuotientCoveringMap.fundamentalGroupEquiv
add_to_sga "7 XIV 1.1.6" "standard disc {z ∈ ℂ" Complex.UnitDisc
add_to_sga "7 XIV 1.1.7" "partial" Complex.exists_continuousOn_eqOn_exp_comp
add_to_sga "7 XIV 1.1.10" "partial" Complex.isPrimitiveRoot_exp
add_to_sga "7 XIV 1.1.10" "partial" Complex.mem_rootsOfUnity
add_to_sga "7 XIV 1.3.4" "partial" Manifold.IsSubmersionAtOfComplement
add_to_sga "7 XIV 1.3.4" Manifold.IsSubmersionOfComplement
add_to_sga "7 XIV 2.1" "partial" IsNoetherianRing
add_to_sga "7 XIV 2.6" "partial" AlgebraicGeometry.Scheme.Hom.normalization
add_to_sga "7 XIV 3.2.3" "partial" Circle.exp
add_to_sga "7 XIV 3.2.3" "partial" Circle.isAddQuotientCoveringMap_exp
add_to_sga "7 XIV 3.2.3" "Covering-map clause" Circle.isCoveringMap_exp
add_to_sga "7 XIV 4.5" "partial" CategoryTheory.Limits.pullback
add_to_sga "7 XIV 4.5" "partial" Complex.exists_continuousOn_eqOn_exp_comp
add_to_sga "7 XIV 4.5" "forward implication" LinearMap.aeval_self_charpoly
add_to_sga "7 XIV 4.5" "forward implication" LinearMap.exists_monic_and_aeval_eq_zero
add_to_sga "7 XIV 4.5" "forward implication"
  LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero
add_to_sga "7 XIV 4.18" Complex.UnitDisc
add_to_sga "7 XIV 4.18" "more general" Metric.ball
add_to_sga "7 XV 1.1.2" Ideal.comap
add_to_sga "7 XV 1.1.2" Ideal.under
add_to_sga "7 XVI 1.3" "special case" Algebra.SubmersivePresentation.basisKaehler
add_to_sga "7 XVI 1.3" "special case" Algebra.SubmersivePresentation.basisKaehlerOfIsCompl
add_to_sga "7 XVI 1.3" "special case" Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply
add_to_sga "7 XVI 1.3" "special case" Algebra.SubmersivePresentation.basisKaehler_apply
add_to_sga "7 XVI 1.6" Field.absoluteGaloisGroup
add_to_sga "7 XVI 2.3" "more general" Finset.sum_eq_sum_iff_single
add_to_sga "7 XVII 1.1" "special case" QuadraticForm.equivalent_of_isAlgClosed
add_to_sga "7 XVII 3.1" "partial" Ideal.Cotangent
add_to_sga "7 XVII 5.1" "partial" Algebra.Extension.exact_cotangentComplex_toKaehler
add_to_sga "7 XVII 5.4" Multiset.esymm
add_to_sga "7 XVII 5.4" MvPolynomial.esymm
add_to_sga "7 XVII 5.4" "partial" MvPowerSeries
add_to_sga "7 XVII 5.4" "b_0 = 1" MvPowerSeries.coeff_invOfUnit
add_to_sga "7 XVII 5.4" "b_0 = 1" MvPowerSeries.coeff_inv_aux
add_to_sga "7 XVII 5.4" "b_0 = 1" MvPowerSeries.constantCoeff_invOfUnit
add_to_sga "7 XVII 5.4" MvPowerSeries.homogeneousComponent
add_to_sga "7 XVII 5.4" MvPowerSeries.inv.aux
add_to_sga "7 XVII 5.4" MvPowerSeries.invOfUnit
add_to_sga "7 XVII 5.4" "partial" MvPowerSeries.invOfUnit_mul
add_to_sga "7 XVII 5.4" "partial" MvPowerSeries.isHomogeneous_homogeneousComponent
add_to_sga "7 XVII 5.4" "partial" MvPowerSeries.isWeightedHomogeneous_weightedHomogeneousComponent
add_to_sga "7 XVII 5.4" "partial" MvPowerSeries.mul_invOfUnit
add_to_sga "7 XVII 5.4" MvPowerSeries.weightedHomogeneousComponent
add_to_sga "7 XVII 5.4" "ambient ring A[[T]]" PowerSeries
add_to_sga "7 XVIII 3.2" genericPoint
add_to_sga "7 XVIII 3.2" genericPoints.ofComponent
add_to_sga "7 XVIII 5.1" AlgebraicGeometry.Scheme.Hom.fiber
add_to_sga "7 XVIII 5.1" "partial" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_sga "7 XVIII 5.1" AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_sga "7 XVIII 5.1" "partial" AlgebraicGeometry.Scheme.Hom.fiber_fac
add_to_sga "7 XVIII 5.1" AlgebraicGeometry.Scheme.Hom.fiberι
add_to_sga "7 XVIII 5.1" "k is a preimmersion" AlgebraicGeometry.instIsPreimmersionFiberι
add_to_sga "7 XVIII 5.6.8" IsAlgClosed
add_to_sga "7 XVIII 5.8.5" "special case" groupCohomology.instMonoModuleCatFH1InfRes
add_to_sga "7 XXI 1.0" "special case" coe_iterateFrobenius
add_to_sga "7 XXI 1.0" "special case" frobenius
add_to_sga "7 XXI 1.0" "special case" iterateFrobenius
add_to_sga "7 XXI 1.0" "special case" iterateFrobenius_eq_pow
add_to_sga "7 XXI 1.0" "special case" iterate_frobenius
add_to_sga "7 XXI 2.0" "partial" FiniteField.coe_frobeniusAlgEquivOfAlgebraic
add_to_sga "7 XXI 2.0" "2.0.2, special case" frobeniusEquiv
add_to_sga "7 XXI 5.0" "formula f(x) = x^{q'}" FiniteField.coe_frobeniusAlgEquivOfAlgebraic
add_to_sga "7 XXI 5.0" "formula f(x) = x^{q'}" FiniteField.coe_frobeniusAlgHom
add_to_sga "7 XXI 5.0" FiniteField.frobeniusAlgEquiv
add_to_sga "7 XXI 5.0" FiniteField.frobeniusAlgEquivOfAlgebraic
add_to_sga "7 XXI 5.0" "formula f(x) = x^{q'}" FiniteField.frobeniusAlgEquivOfAlgebraic_apply
add_to_sga "7 XXI 5.0" "formula f(x) = x^{q'}" FiniteField.frobeniusAlgEquiv_apply
add_to_sga "7 XXI 5.0" "partial" FiniteField.frobeniusAlgHom
add_to_sga "7 XXI 5.0" "formula f(x) = x^{q'}" FiniteField.frobeniusAlgHom_apply
add_to_sga "7 XXI 5.0" "partial" IsAlgebraic
add_to_sga "7 XXI 5.0" "more general" IsIntegral
add_to_sga "7 XXI 5.0" "more general" Localization
add_to_sga "7 XXI 5.3.1" "partial" ContRepresentation.invariants
add_to_sga "7 XXI 5.3.1" "partial" Rep.invariantsFunctor
add_to_sga "7 XXI 5.3.1" "partial" Representation.Coinvariants
add_to_sga "7 XXI 5.3.1" "partial" Representation.invariants
add_to_sga "7 XXI 5.3.1" "partial" TopRep.invariants
add_to_sga "7 XXI 5.3.1" "partial" TopRep.invariantsFunctor
add_to_sga "7 XXII 1.0" LinearMap
add_to_sga "7 XXII 1.0.6" IsNilpotent
add_to_sga "7 XXII 1.0.6" "special case" Module.End.isNilpotent_restrict_genEigenspace_top
add_to_sga "7 XXII 1.1" LinearMap.fixedSubmodule
add_to_sga "7 XXII 1.1" "partial" LinearMap.fixedSubmodule_eq_ker
add_to_sga "7 XXII 2.2" "partial" AlgebraicClosure
add_to_sga "7 XXII 2.2" CategoryTheory.Limits.pullback
add_to_sga "7 XXII 2.2.4" "more general" FiniteField.coe_frobeniusAlgEquivOfAlgebraic
add_to_sga "7 XXII 2.2.4" "partial" FiniteField.coe_frobeniusAlgHom
add_to_sga "7 XXII 2.2.4" FiniteField.frobeniusAlgEquivOfAlgebraic
add_to_sga "7 XXII 2.2.4" "more general" FiniteField.frobeniusAlgEquivOfAlgebraic_apply
add_to_sga "7 XXII 2.2.4" "more general" FiniteField.frobeniusAlgEquiv_apply
add_to_sga "7 XXII 2.2.4" "partial" FiniteField.frobeniusAlgHom
add_to_sga "7 XXII 2.2.4" "special case" frobenius
add_to_sga "7 XXII 2.2.4" "formula for φ_p" frobeniusEquiv_def
add_to_sga "7 XXII 3.0" "more general" AlgebraicGeometry.Scheme.Hom.residueDegree
add_to_sga "7 XXII 3.0" PowerSeries.map
add_to_sga "7 XXII 3.7" "Two-member covering" Cardinal.mk_union_add_mk_inter
add_to_sga "7 XXII 3.7" "Two-member covering" Finset.card_inter
add_to_sga "7 XXII 3.7" "Two-member covering" Finset.card_union
add_to_sga "7 XXII 3.7" "Two-member covering" Finset.cast_card_inter
add_to_sga "7 XXII 3.7" "Two-member covering" Finset.cast_card_union
add_to_sga "7 XXII 3.7" Finset.inclusion_exclusion_card_biUnion
add_to_sga "7 XXII 3.7" "more general" Finset.inclusion_exclusion_card_inf_compl
add_to_sga "7 XXII 3.7" "more general" Finset.inclusion_exclusion_sum_biUnion
add_to_sga "7 XXII 3.7" "more general" Finset.inclusion_exclusion_sum_inf_compl
add_to_sga "7 XXII 3.7" "more general" MeasureTheory.integral_biUnion_eq_sum_powerset
add_to_sga "7 XXII 3.7" "more general" MeasureTheory.measureReal_biUnion_eq_sum_powerset
add_to_sga "7 XXII 4.0" AddChar
add_to_sga "7 XXII 4.0" AddChar.FiniteField.primitiveChar
add_to_sga "7 XXII 4.0" AddChar.FiniteField.primitiveChar_to_Complex
add_to_sga "7 XXII 4.0" "special case" AddChar.primitiveZModChar
add_to_sga "7 XXII 4.0" "more general" AddChar.sum_mulShift
add_to_sga "7 XXII 4.0" "values lie in μ_p" AddChar.val_mem_rootsOfUnity
add_to_sga "7 XXII 4.0" "prime field q^ν = p" AddChar.zmodChar
add_to_sga "7 XXII 4.0" "V* as D₊(∏ X_i)" AlgebraicGeometry.Proj.basicOpen
add_to_sga "7 XXII 4.0" MvPolynomial.IsHomogeneous
add_to_sga "7 XXII 4.0" "X^w = ∏ X_i^{w_i}" MvPolynomial.monic_monomial_eq
add_to_sga "7 XXII 4.0" MvPolynomial.monomial
add_to_sga "7 XXII 4.0" "partial" MvPolynomial.monomial_eq
add_to_sga "7 XXII 4.0" "special case" ZMod.isPrimitive_stdAddChar
add_to_sga "7 XXII 4.0" "partial" gaussSum_one_left
add_to_sga "7 XXII 4.0" rootsOfUnity
add_to_sga "7 XXII 4.0" "special case" surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar
add_to_sga "7 XXII 4.1" AddChar.FiniteField.primitiveChar
add_to_sga "7 XXII 4.1" AddChar.FiniteField.primitiveChar_to_Complex
add_to_sga "7 XXII 4.1" "special case" AddChar.primitiveZModChar
add_to_sga "7 XXII 4.1" "prime field 𝔽_p" AddChar.zmodChar
add_to_sga "7 XXII 4.1" "more general" AlgebraicClosure
add_to_sga "7 XXII 4.1" IsPrimitiveRoot
add_to_sga "7 XXII 4.1" "special case" Padic.addValuation
add_to_sga "7 XXII 4.1" "special case" Padic.addValuationDef
add_to_sga "7 XXII 4.1" "partial" Padic.valuation_p
add_to_sga "7 XXII 4.1" PadicAlgCl
add_to_sga "7 XXII 4.1" "partial" PadicAlgCl.valuation_p
add_to_sga "7 XXII 4.1" "special case" ZMod.rootsOfUnityAddChar
add_to_sga "7 XXII 4.4" MvPowerSeries.map
add_to_sga "7 XXII 4.4" "p = 2" PadicInt.residueField
add_to_sga "7 XXII 4.4" "(4.4.1), special case" WittVector.FractionRing.frobenius
add_to_sga "7 XXII 4.5" "more general" ContinuousLinearMap.lsmul
add_to_sga "7 XXII 4.5" "more general" ContinuousLinearMap.mul
add_to_sga "7 XXII 4.5" "more general" ContinuousLinearMap.mulLeftRight
add_to_sga "7 XXII 4.5" "more general" ContinuousLinearMap.mulₗᵢ
add_to_sga "7 XXII 4.5" "partial" ContinuousMap.mulLeft
add_to_sga "7 XXII 4.5" "partial" LinearMap.mul
add_to_sga "7 XXII 4.5" "more general" NonUnitalAlgHom.Lmul
add_to_sga "7 XXII 4.5.8" "partial" MvPolynomial.eval₂
add_to_sga "7 XXII 4.5.8" "partial" MvPolynomial.eval₂Hom
add_to_sga "7 XXII 4.5.8" MvPowerSeries.rescale
add_to_sga "7 XXII 4.5.8" MvPowerSeries.rescaleAlgHom
add_to_sga "7 XXII 4.5.8" MvPowerSeries.rescaleMonoidHom
add_to_sga "7 XXII 4.5.8" PowerSeries.rescale
add_to_sga "7 XXII 4.5.8" PowerSeries.rescaleAlgHom
add_to_sga "7 XXII 4.6" Valued.integer
add_to_sga "7 XXII 6.2" "partial" FiniteField.frobeniusAlgHom
