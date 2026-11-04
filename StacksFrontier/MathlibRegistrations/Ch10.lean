module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.Integral
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Oka
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import StacksCore.Tactic.StacksAttribute

/-!
# Chapter 10 (Commutative Algebra) tags stated by Mathlib

This file registers, with `add_to_stacks`, Mathlib declarations that state Stacks tags of
Chapter 10. Each tag is covered by the listed declarations together; when several declarations
cover one tag, the comment string names the part each one states.

## Tags

* 00EU: the localization of a ring at a minimal prime is zero-dimensional; its maximal
  ideal consists of nilpotents, and it is a field when the ring is reduced.
* 00FO: a finite type algebra over a Noetherian ring (a field or ℤ) is Noetherian.
* 00FP: over a Noetherian ring, finite modules and finite type algebras are finitely
  presented, and submodules of finite modules are finite.
* 00GB: a finite type algebra over a Jacobson ring is Jacobson, closed points map to closed
  points, and the residue field extensions at maximal ideals are finite.
* 00GM: an element is integral iff it lies in a finite subalgebra.
* 00GR: a ring inside a field that is integral (or finite) over it is a field, and the
  extension is algebraic (finite algebraic).
* 00HD: the equivalent characterisations of flatness by injectivity of tensored maps.
* 00HN: zero elements, zero modules, exactness, injectivity, surjectivity and bijectivity are
  local properties, checked at primes or at maximal ideals.
* 00ID: the value group of a valuation ring is a totally ordered abelian group.
* 00IE: the value group, the valuation, and discrete valuation rings.
* 00IF: the basic properties of the valuation of a valuation ring.
* 00LU: the long exact sequence of `Ext(M, -)` attached to a short exact sequence.
* 00OL: the local ring of the fibre at q, (S ⊗_R κ(p))_q = S_q / p S_q.
* 00RZ: Ω_{S/R} is finite for R → S of finite type.
* 00T6: standard smooth algebras.
* 00TK: polynomial rings are formally smooth.
* 00TL: formal smoothness via a section of P/J² → S.
* 065P: the long exact sequence of `Ext(-, N)` attached to a short exact sequence.
* 00U3: étale algebras over a field are finite products of finite separable extensions.
* 0GWM: a finitely presented module free at a prime is free on a basic open around it.
* 0H92: formally étale ring maps are stable under base change.
* 09DZ: an element of a discrete valuation ring generates its maximal ideal iff it is
  irreducible (Mathlib's notion of uniformizer).
* 058R: a module is finite projective if and only if it is finitely presented and flat.
* 05KH: an ideal maximal among non-principal ideals is prime, and a ring whose prime ideals are
  principal is a principal ideal ring.
* 046W: every field has a perfect purely inseparable extension, unique up to unique
  isomorphism.
-/

add_to_stacks 065P "exactness of the Ext^n0 -> ... -> Ext^n1 window (whole sequence for 1+n0=n1)"
  CategoryTheory.Abelian.Ext.contravariantSequence_exact
add_to_stacks 065P "the long exact sequence (as composable arrows)"
  CategoryTheory.Abelian.Ext.contravariantSequence
add_to_stacks 065P "exactness at Ext^n(M,N)"
  CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂'
add_to_stacks 065P "exactness at Ext^n(M',N)"
  CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'
add_to_stacks 065P "exactness at Ext^(n+1)(M'',N)"
  CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃'
add_to_stacks 065P "leading 0: Hom(M'',N) -> Hom(M,N) injective"
  CategoryTheory.Abelian.Ext.precomp_mk₀_injective_of_epi
add_to_stacks 065P "Ext^0(M,N) = Hom(M,N)" CategoryTheory.Abelian.Ext.addEquiv₀
-- Stacks 030B, (1) ⇒ (2) and (1) ⇒ (3): a localization of an integrally closed domain at a
-- submonoid of nonzero divisors, such as `R \ 𝔭` for a prime `𝔭`, is integrally closed. That
-- this localization is a domain is `IsLocalization.isDomain_of_le_nonZeroDivisors`.
add_to_stacks 030B "(1) ⇒ (2) and (1) ⇒ (3)" isIntegrallyClosed_of_isLocalization
-- Stacks 030B, (3) ⇒ (1): a domain whose localizations at all maximal ideals are integrally
-- closed is integrally closed.
add_to_stacks 030B "(3) ⇒ (1)" IsIntegrallyClosed.of_isLocalization_maximal
-- Item (1) of Stacks 034P: `Associated x y` asks for a unit `u` with `x * u = y`, which in a
-- commutative ring is the Stacks condition `y = u⁻¹ x`; the relation is symmetric
-- (`Associated.comm`).
add_to_stacks 034P "(1) associates" Associated
-- Item (3) of Stacks 034P, for `x ≠ 0`: the ideal `(x)` is prime exactly when `x` is a prime
-- element in Mathlib's sense. Stacks also calls `0` prime in a domain, since `(0)` is then a
-- prime ideal, whereas Mathlib's `Prime` excludes `0`; that case is not covered.
add_to_stacks 034P "(3) prime element, for nonzero elements" Ideal.span_singleton_prime

add_to_stacks 00EU "localization at a minimal prime is zero-dimensional"
  Ring.KrullDimLE.of_isLocalization
add_to_stacks 00EU "maximal ideal consists of nilpotents"
  Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal
add_to_stacks 00EU "reduced case: the localization is a field" Ring.KrullDimLE.isField_of_isReduced

add_to_stacks 00FO "over any Noetherian base; fields and ℤ are Noetherian"
  Algebra.FiniteType.isNoetherianRing

add_to_stacks 00FP "(1) finite modules are finitely presented" Module.finitePresentation_of_finite
add_to_stacks 00FP "(2) submodules of finite modules are finite" Submodule.FG.of_le
add_to_stacks 00FP "(3) finite type algebras are finitely presented"
  Algebra.FinitePresentation.of_finiteType

add_to_stacks 00GB "(1) S is Jacobson" isJacobsonRing_of_finiteType
add_to_stacks 00GB "(2) closed points map to closed points (scheme form)"
  AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints
add_to_stacks 00GB "(3) residue field extension is finite (applied to R/m → S/m')"
  finite_of_finite_type_of_isJacobsonRing

add_to_stacks 00GM "integral implies contained in a finite subalgebra"
  Algebra.finite_adjoin_of_finite_of_isIntegral
add_to_stacks 00GM "contained in a finite subalgebra implies integral" IsIntegral.of_mem_of_fg

add_to_stacks 00GR "integral case: R is a field" isField_of_isIntegral_of_isField
add_to_stacks 00GR "integral case: K is algebraic over R" Algebra.IsIntegral.isAlgebraic
add_to_stacks 00GR "finite case: finite implies integral (so R is a field via \
  isField_of_isIntegral_of_isField)" Algebra.IsIntegral.of_finite
add_to_stacks 00GR "finite case: K is a finite algebraic extension" Algebra.IsAlgebraic.of_finite

add_to_stacks 07T7 "(1) Ann(m) = {f | fm = 0}" Ideal.torsionOf
add_to_stacks 07T7 "(2) Ann(M) = {f | fm = 0 for all m}" Module.annihilator

add_to_stacks 00HD "(1) flat iff - ⊗ M exact (links Mathlib's Flat to the Stacks \
  definition)" Module.Flat.iff_rTensor_exact
add_to_stacks 00HD "(1) <=> (2)" Module.Flat.iff_rTensor_preserves_injective_linearMap
add_to_stacks 00HD "(1) <=> (3)" Module.Flat.iff_rTensor_injective'
add_to_stacks 00HD "(1) <=> (4)" Module.Flat.iff_rTensor_injective

add_to_stacks 00HN "(1) (c) => (a)" Module.eq_zero_of_localization_maximal
add_to_stacks 00HN "(2) (c) => (a)" Module.subsingleton_of_localization_maximal
add_to_stacks 00HN "(2) (a) <=> (b)" Module.support_eq_empty_iff
add_to_stacks 00HN "(2) (a) => (b)" IsLocalizedModule.subsingleton_of_subsingleton
add_to_stacks 00HN "(3) (c) => (a)" exact_of_localized_maximal
add_to_stacks 00HN "(3) (c) => (a), IsLocalizedModule form" exact_of_isLocalized_maximal
add_to_stacks 00HN "(3) (a) => (b)" IsLocalizedModule.map_exact
add_to_stacks 00HN "(4) (c) => (a)" injective_of_localized_maximal
add_to_stacks 00HN "(4) (a) => (b)" LocalizedModule.map_injective
add_to_stacks 00HN "(5) (c) => (a)" surjective_of_localized_maximal
add_to_stacks 00HN "(5) (a) => (b)" LocalizedModule.map_surjective
add_to_stacks 00HN "(6) (c) => (a)" bijective_of_localized_maximal
add_to_stacks 00HN "(b) => (c), maximal ideals are prime" Ideal.IsMaximal.isPrime

add_to_stacks 00ID "Gamma (with 0 adjoined) = K / A^x" ValuationRing.ValueGroup
add_to_stacks 00ID "the relation >=: a/b in image of A" ValuationRing.instLEValueGroup
add_to_stacks 00ID "the ordering is total" ValuationRing.le_total
add_to_stacks 00ID "the relation is a total order" ValuationRing.linearOrder
add_to_stacks 00ID "abelian group law on Gamma" ValuationRing.commGroupWithZero
add_to_stacks 00ID "compatibility of the order with the group \
  law" ValuationRing.linearOrderedCommGroupWithZero
add_to_stacks 00ID "restriction to Gamma = units (nonzero part) is an ordered \
  group" Units.isOrderedMonoid

-- Stacks 02LZ: a module of finite length is a finite module.
add_to_stacks 02JL "(1): integrality can be checked on the localizations at elements generating \
  the unit ideal" RingHom.isIntegral_ofLocalizationSpan
add_to_stacks 02JL "(2): finiteness can be checked on the localizations at elements generating \
  the unit ideal" RingHom.finite_ofLocalizationSpan

add_to_stacks 02LZ "step 1: length ≠ ⊤ ↔ finite length" Module.length_ne_top_iff
add_to_stacks 02LZ "step 2: finite length → Noetherian (and Artinian)"
  isFiniteLength_iff_isNoetherian_isArtinian
add_to_stacks 02LZ "step 3: Noetherian → finite" Module.IsNoetherian.finite

add_to_stacks 00IE "(1) value group Gamma" ValuationRing.ValueGroup
add_to_stacks 00IE "(1) Gamma is a totally ordered abelian group (with \
  zero)" ValuationRing.linearOrderedCommGroupWithZero
add_to_stacks 00IE "(2) the valuation v : K^* -> Gamma" ValuationRing.valuation
add_to_stacks 00IE "(1),(2) value group and valuation of a valuation \
  subring" ValuationSubring.valuation
add_to_stacks 00IE "(3) discrete valuation ring" IsDiscreteValuationRing
add_to_stacks 00IE "(3) Gamma = Z => DVR" Valuation.valuationSubring_isDiscreteValuationRing
add_to_stacks 00IE "(3) DVR => valuation discrete" IsDiscreteValuationRing.isRankOneDiscrete
add_to_stacks 00IE "(3) discrete valuation has value group = \
  Z" Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt

add_to_stacks 00IF "(1) v(a) = 0 <=> a in A^*" ValuationSubring.valuation_eq_one_iff
add_to_stacks 00IF "(1) v(a) = 0 <=> a in A^* (integers of a \
  valuation)" Valuation.Integers.isUnit_iff_valuation_eq_one
add_to_stacks 00IF "(2) v(ab) = v(a) + v(b)" Valuation.map_mul
add_to_stacks 00IF "(3) v(a+b) >= min(v(a), v(b))" Valuation.map_add
add_to_stacks 00IF "v takes values in Gamma_{>=0} on A" ValuationSubring.valuation_le_one

add_to_stacks 00LU "exactness of Ext^n0 -> ... -> Ext^n1 window (whole long exact sequence for \
  n0+1=n1)" CategoryTheory.Abelian.Ext.covariantSequence_exact
add_to_stacks 00LU "the long exact sequence (as composable \
  arrows)" CategoryTheory.Abelian.Ext.covariantSequence
add_to_stacks 00LU "exactness at Ext^n(M,N)" CategoryTheory.Abelian.Ext.covariant_sequence_exact₂'
add_to_stacks 00LU "exactness at Ext^n(M,N'')" CategoryTheory.Abelian.Ext.covariant_sequence_exact₃'
add_to_stacks 00LU "exactness at \
  Ext^(n+1)(M,N')" CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'
add_to_stacks 00LU "leading 0: Hom(M,N') -> Hom(M,N) \
  injective" CategoryTheory.Abelian.Ext.postcomp_mk₀_injective_of_mono
add_to_stacks 00LU "Ext^0(M,N) = Hom(M,N)" CategoryTheory.Abelian.Ext.addEquiv₀

add_to_stacks 00OL "the fibre ring S ⊗_R κ(p) (written κ(p) ⊗_R S)" Ideal.Fiber
add_to_stacks 00OL "primes q of S lying over p = primes of the fibre ring (inverse: \
  comap along S -> κ(p) ⊗_R S)" PrimeSpectrum.primesOverOrderIsoFiber
add_to_stacks 00OL "(S ⊗_R κ(p))_q = S_q / p S_q, with q the prime of S under the fibre \
  prime" Ideal.Fiber.localizationAlgEquivQuotient
add_to_stacks 00OL "the localization at a prime is a local ring" Localization.AtPrime.isLocalRing

add_to_stacks 00RZ KaehlerDifferential.finite

add_to_stacks 00T6 "standard smooth presentation (with [Finite ι])" Algebra.SubmersivePresentation
add_to_stacks 00T6 "S is standard smooth over R" Algebra.IsStandardSmooth

add_to_stacks 00TK Algebra.instFormallySmoothMvPolynomial

add_to_stacks 00TL Algebra.FormallySmooth.iff_split_surjection

add_to_stacks 00U3 Algebra.Etale.iff_exists_algEquiv_prod

add_to_stacks 0GWM Module.FinitePresentation.exists_free_localizedModule_powers

add_to_stacks 0H92 Algebra.FormallyEtale.instTensorProduct

add_to_stacks 09DZ IsDiscreteValuationRing.irreducible_iff_uniformizer

add_to_stacks 07BL "the canonical surjection R[S] → S, [s] ↦ s: the generators of S indexed by S \
itself, whose map MvPolynomial S R → S is aeval id" Algebra.Generators.self

-- A module is finite projective if and only if it is finitely presented and flat.
add_to_stacks 058R "(⇒) finitely presented" Module.finitePresentation_of_projective
add_to_stacks 058R "(⇒) flat: projective modules are flat" Module.Flat.of_projective
add_to_stacks 058R
  "(⇐) projective; finiteness comes from `FinitePresentation` (instance)"
  Module.Flat.projective_of_finitePresentation

add_to_stacks 0DVB "the isomorphism Hom(M, N) ⊗ L ≃ Hom(M, N ⊗ L) for M finite projective"
  rTensorHomEquivHomRTensor
add_to_stacks 0DVB "it is the canonical map f ⊗ l ↦ (m ↦ f m ⊗ l)"
  rTensorHomEquivHomRTensor_toLinearMap

-- Ideals maximal among non-principal ideals are prime; if all primes are principal, so is every
-- ideal.
add_to_stacks 05KH
  "(1), for the Oka family `Submodule.IsPrincipal` (`Ideal.isOka_isPrincipal`)"
  Ideal.IsOka.isPrime_of_maximal_not
add_to_stacks 05KH "(2)" IsPrincipalIdealRing.of_prime

/- Stacks 034X is not registered here: Mathlib does not prove that a domain whose nonzero ideals
factor uniquely into primes (the Stacks definition 034W, condition (1)) is Dedekind. The tag is
proved in `StacksFrontier/RingTheory/DedekindDomain/TFAE.lean`. -/

add_to_stacks 034U "a principal ideal domain is a domain (`IsDomain`) that is a principal ideal \
  ring" IsPrincipalIdealRing

-- Every field has a perfect purely inseparable extension, unique up to unique isomorphism.
add_to_stacks 046W
  "existence: the perfect closure of `k` in an algebraic closure is purely inseparable"
  perfectClosure.isPurelyInseparable
add_to_stacks 046W
  "existence: it is perfect (given a perfect ambient field, e.g. `IsAlgClosed.perfectField`)"
  perfectClosure.perfectField
add_to_stacks 046W "uniqueness: a `k`-map into any perfect extension exists"
  IsPurelyInseparable.instNonemptyAlgHomOfPerfectField
add_to_stacks 046W "uniqueness: such a `k`-map is unique"
  instSubsingletonAlgHomOfIsPurelyInseparable
