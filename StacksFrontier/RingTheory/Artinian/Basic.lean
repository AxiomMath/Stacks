module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# A ring with discrete spectrum is the product of its localizations at its maximal ideals

A commutative semiring with finitely many maximal ideals and locally nilpotent Jacobson radical is
the product of its localizations at those maximal ideals, and every prime of it is maximal. That
hypothesis is a property of the space `Spec R`: it says exactly that `Spec R` is discrete, by
`PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical`. It holds for every
Artinian ring — equivalently, by Hopkins–Levitzki, every ring of finite length over itself — so for
such a ring the hypothesis below is supplied by instance search.

## Main results

* `MaximalSpectrum.algebraMap_pi_bijective`: for a commutative semiring `R` with discrete prime
  spectrum and any family `Rₘ` of localizations of `R` at its maximal ideals, the canonical map
  `R → ∀ 𝔪, Rₘ 𝔪` is bijective.

## Implementation notes

The hypothesis `DiscreteTopology (PrimeSpectrum R)` is 00JA's own, not a substitute for it:
`PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical` rewrites it as
`Finite {I : Ideal R | I.IsMaximal} ∧ sInf {I : Ideal R | I.IsMaximal} ≤ nilradical R`. Against
00JB it is a genuine weakening, `IsArtinianRing R` being discreteness together with Noetherianness
(`isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`), and the difference is not vacuous:
`TrivSqZeroExt k V` for an infinite-dimensional `k`-vector space `V` has a single prime, hence a
discrete spectrum, and is not Noetherian.

Only the product decomposition is stated. 00JA's second clause, that every prime is maximal,
follows from `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero` through
`Ring.krullDimLE_zero_iff`, and in the Artinian case is `IsArtinianRing.isPrime_iff_isMaximal`;
00JB's other two clauses, the finite-length criterion and Noetherianness, already carry that tag
upstream, on `isArtinianRing_iff_isFiniteLength` and on the instance deriving `IsNoetherianRing R`
from `IsArtinianRing R`, as the model case of the decomposition carries 00JA on
`MaximalSpectrum.toPiLocalizationEquiv`. The source's parenthetical "(finite)" is no part of the
statement, which never uses it; discreteness does give `Finite (MaximalSpectrum R)` by
`Finite.of_injective` along `MaximalSpectrum.toPrimeSpectrum_injective`, not by instance.

The factors are an arbitrary family, in the form `IsLocalization.AtPrime (Rₘ 𝔪) 𝔪` rather than the
model `Localization.AtPrime 𝔪` of `MaximalSpectrum.toPiLocalizationEquiv`, since a user's
localizations are rarely that model on the nose; the base is a commutative semiring, the generality
of that sibling and of `MaximalSpectrum.toPiLocalization_injective`. The conclusion is bijectivity
of the pinned map `algebraMap R (∀ 𝔪, Rₘ 𝔪)`, whose `𝔪`-th component is `algebraMap R (Rₘ 𝔪)`;
`AlgEquiv.ofBijective` turns it into the isomorphism the source asserts.

## References

* [StackProject 00JA](https://stacks.math.columbia.edu/tag/00JA)
* [StackProject 00JB](https://stacks.math.columbia.edu/tag/00JB)
-/

namespace MaximalSpectrum

@[expose] public section

/-- **Stacks 00JA and 00JB** (the product decomposition).
A commutative semiring with discrete prime spectrum — in particular an Artinian ring — is the
product of its localizations at its (finitely many) maximal ideals: for any family `Rₘ` of
localizations of `R` at the maximal ideals of `R`, the canonical map `R → ∀ 𝔪, Rₘ 𝔪` is
bijective. -/
@[stacks 00JA "The product decomposition, for an arbitrary family of localizations. Discreteness \
  of `Spec R` is the tag's own hypothesis, by \
  `PrimeSpectrum.discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical`.",
  stacks 00JB "The final assertion, under discreteness of `Spec R` in place of Artinian-ness",
  sga "3 VIIB 0.1.1" "partial"]
public theorem algebraMap_pi_bijective (R : Type*) [CommSemiring R]
    [DiscreteTopology (PrimeSpectrum R)]
    (Rₘ : MaximalSpectrum R → Type*) [∀ m, CommSemiring (Rₘ m)] [∀ m, Algebra R (Rₘ m)]
    [∀ m, IsLocalization.AtPrime (Rₘ m) m.asIdeal] :
    Function.Bijective (algebraMap R (∀ m, Rₘ m)) :=
  bijective_algebraMap_of_linearEquiv <| ((toPiLocalizationEquiv R).trans <|
    AlgEquiv.piCongrRight fun m ↦ Localization.algEquiv m.asIdeal.primeCompl (Rₘ m)).toLinearEquiv

end

end MaximalSpectrum

-- ===== merged from Sec53/Tag00JA =====

@[expose] public section

/-- A ring with finitely many maximal ideals whose Jacobson radical is contained in the
nilradical is isomorphic to the product of its localizations at its maximal ideals, and
every prime ideal of it is maximal. -/
@[stacks 00JA, ega "I 6.2.2" "affine, special case"]
theorem nonempty_ringEquiv_pi_localization_and_isMaximal (R : Type*) [CommRing R] [Finite
  (MaximalSpectrum R)]
    (h : Ring.jacobson R ≤ nilradical R) :
    Nonempty (R ≃+* (Π m : MaximalSpectrum R, Localization.AtPrime m.asIdeal)) ∧
    (∀ p : Ideal R, p.IsPrime → p.IsMaximal) := by
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  have hjac : Ring.jacobson R = ⨅ m : MaximalSpectrum R, m.asIdeal := by
    rw [Ring.jacobson_eq_sInf_isMaximal, sInf_eq_iInf, ← MaximalSpectrum.range_asIdeal,
      iInf_range]
  have hmax : ∀ p : Ideal R, p.IsPrime → p.IsMaximal := by
    intro p hp
    have hnil : nilradical R ≤ p := nilradical_le_prime p
    have hjp : Ring.jacobson R ≤ p := le_trans h hnil
    rw [hjac, ← Finset.inf_univ_eq_iInf] at hjp
    rw [Ideal.IsPrime.inf_le' hp] at hjp
    obtain ⟨m, -, hm⟩ := hjp
    have hmaxm := m.isMaximal
    have heq : m.asIdeal = p := hmaxm.eq_of_le hp.ne_top hm
    rw [← heq]
    exact hmaxm
  have hfin : Finite (PrimeSpectrum R) :=
    Finite.of_surjective MaximalSpectrum.toPrimeSpectrum
      fun q => ⟨⟨q.asIdeal, hmax q.asIdeal q.isPrime⟩, rfl⟩
  have : DiscreteTopology (PrimeSpectrum R) := by
    rw [PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero]
    exact ⟨hfin, Ring.krullDimLE_zero_iff.mpr hmax⟩
  exact ⟨⟨MaximalSpectrum.toPiLocalizationEquiv R⟩, hmax⟩

-- ===== merged from Sec53/Tag00J6 =====


-- Stacks tag 00J6: https://stacks.math.columbia.edu/tag/00J6


/-- A finite-dimensional algebra over a field is an Artinian ring. -/
@[stacks 00J6, ega "IV 2.5.8.8" "special case"]
theorem finite_dimensional_algebra_is_artinian
    (K : Type*) [Field K] (R : Type*) [Ring R] [Algebra K R]
    [FiniteDimensional K R] : IsArtinianRing R :=
  isArtinian_of_tower K inferInstance

-- ===== merged from Sec53/Tag00J8 and Sec53/Tag00J7 =====

/-! Mathlib states both of these tags, and carries them on its own declarations, so nothing is
recorded for them here. Stacks 00J8, that the Jacobson radical of an Artinian ring is
nilpotent, is `IsArtinianRing.isNilpotent_jacobson_bot`, stated for `Ideal.jacobson ⊥`, which
is `Ring.jacobson R` by `Ideal.jacobson_bot`. Stacks 00J7, that an Artinian ring has only
finitely many maximal ideals, is `IsArtinianRing.setOfPred_isMaximal_finite`. -/

/-!
# Artinian rings: finite length, Noetherianness, and the product of localizations

Proof of Stacks 00JB. A commutative ring `R` is Artinian precisely when it has finite length as a
module over itself, and an Artinian ring is Noetherian, has all of its primes maximal, has only
finitely many maximal ideals, and is the product of its localizations at them.

## Main results

* `Stacks.Artinian.ProductDecomposition.solution`: a commutative ring is Artinian if and only if it
  has finite length over itself, and an Artinian ring is Noetherian, has all its primes maximal,
  has finitely many maximal ideals, and is the product of its localizations at them.

## Implementation notes

Each of the four assertions is a theorem of Mathlib, so the proof is an assembly of citations
rather than an argument; what follows records which argument each citation stands for.

The source proves the equivalence by hand: finite length gives both chain conditions, and
conversely a local Artinian ring is filtered by the powers of its maximal ideal, each successive
quotient a finite-dimensional residue-field vector space. That equivalence is the Hopkins–Levitzki
theorem `isArtinianRing_iff_isFiniteLength`, whose proof runs the same filtration argument over
the Jacobson radical without the reduction to the local case, so it is cited rather than repeated.

The product decomposition, which the source deduces from Stacks 00J7, 00J8 and 00JA, is instead
obtained from the discreteness of the Zariski topology on the spectrum: an Artinian ring has
finitely many primes, all of them maximal, hence a finite discrete spectrum; and for a
commutative semiring with discrete spectrum the canonical map to the product of the
localizations at the maximal ideals is an isomorphism of algebras,
`MaximalSpectrum.toPiLocalizationEquiv`. Bijectivity of the canonical map is read off that
isomorphism, whose underlying function it is.

## References

* [StackProject 00JB](https://stacks.math.columbia.edu/tag/00JB)
-/

namespace Stacks.Artinian.ProductDecomposition

/-- A commutative ring is Artinian if and only if it has finite length as a module over itself,
and an Artinian ring is Noetherian, has all its prime ideals maximal, has finitely many maximal
ideals, and is the product of its localizations at them: the canonical map
`MaximalSpectrum.toPiLocalization R` is bijective. -/
public theorem solution
    (R : Type*) [CommRing R] :
    (IsArtinianRing R ↔ IsFiniteLength R R) ∧
      (IsArtinianRing R → IsNoetherianRing R ∧ (∀ p : Ideal R, p.IsPrime → p.IsMaximal) ∧
        Finite (MaximalSpectrum R) ∧
        Function.Bijective (MaximalSpectrum.toPiLocalization R)) :=
  ⟨isArtinianRing_iff_isFiniteLength R, fun _ ↦
    ⟨inferInstance, fun p ↦ (IsArtinianRing.isPrime_iff_isMaximal p).mp, inferInstance,
      (MaximalSpectrum.toPiLocalizationEquiv R).bijective⟩⟩

end Stacks.Artinian.ProductDecomposition

/-!
# Artinian rings: finite length, Noetherianness, and the product of localizations

A commutative ring is Artinian exactly when it has finite length as a module over itself. Such a
ring is severely constrained: it is Noetherian as well as Artinian, every one of its prime ideals
is maximal — so its spectrum is a finite discrete space — and it has only finitely many maximal
ideals, at which the canonical map to the product of the localizations is an isomorphism. Thus an
Artinian ring is a finite product of Artinian local rings, each of them one of its own local
rings.

## Main results

* `isArtinianRing_iff_isFiniteLength_and_isNoetherianRing_and_toPiLocalization_bijective`: the
  finite-length criterion for Artinian-ness, together with Noetherianness, maximality of the
  primes, and the product decomposition of an Artinian ring.

## Implementation notes

"Any such ring" of the source's second sentence is a ring satisfying either of the equivalent
conditions of the first, so the consequences are stated under `IsArtinianRing R`; against that
antecedent "both Artinian and Noetherian" contributes `IsNoetherianRing R`, the Artinian half
being the hypothesis and, through the first conjunct, a consequence of finite length.

The product decomposition is bijectivity of the canonical map
`MaximalSpectrum.toPiLocalization R : R →ₐ[R] ∀ 𝔪 : MaximalSpectrum R, Localization.AtPrime 𝔪`,
whose `𝔪`-th component is `algebraMap R (Localization.AtPrime 𝔪)`
(`MaximalSpectrum.toPiLocalization_apply_apply`), rather than the existence of some isomorphism
`R ≃+* ∀ 𝔪, R_𝔪`: the source says that `R` *is* the product of its localizations, which is an
assertion about that map, and `AlgEquiv.ofBijective` recovers the isomorphism from it. The
parenthetical "(finite)" of the source is stated, as `Finite (MaximalSpectrum R)`; it is not
implied by the rest, a product over an infinite index being a perfectly good target for the same
map. The concrete localizations `Localization.AtPrime 𝔪` are the ones the canonical map targets;
for an arbitrary family `Rₘ` of localizations, and under the weaker hypothesis that `Spec R` is
discrete, the same bijectivity is `MaximalSpectrum.algebraMap_pi_bijective`.

Three of the four clauses are known to Lean: the first conjunct is
`isArtinianRing_iff_isFiniteLength`, Noetherianness is the instance derived from
`IsArtinianRing R`, maximality of the primes is `IsArtinianRing.isPrime_iff_isMaximal`, and the
decomposition is `MaximalSpectrum.toPiLocalizationEquiv` once `Spec R` is seen to be discrete.

Faithfulness. (1) The only hypotheses are `CommRing R` and, for the consequences,
`IsArtinianRing R`; each of the four consequences fails for some non-Artinian commutative ring
(`ℤ` has the non-maximal prime `(0)`, infinitely many maximal ideals, and a canonical map to the
product of its localizations that is not surjective; a polynomial ring over a field in infinitely
many variables is not Noetherian), so the antecedent is used throughout. (2) The base is the
source's: `IsFiniteLength R R` is finite length of `R` over itself, and the product decomposition
is of `R`-algebras over that same `R`, no localized base intervening. (3) The canonical map the
source names is pinned, as `MaximalSpectrum.toPiLocalization R`, not merely asserted to exist.
(4) The instantiation is not degenerate: `R = ZMod 6` is Artinian of length `2` over itself, both
its primes are maximal, and the decomposition is `ZMod 6 ≃+* ZMod 2 × ZMod 3`, while `R = ℤ`
satisfies neither side of the equivalence.

## References

* [StackProject 00JB](https://stacks.math.columbia.edu/tag/00JB)
-/

/-- **Artinian rings have finite length, and decompose.** A commutative ring `R` is Artinian if
and only if it has finite length as a module over itself; and any Artinian ring `R` is also
Noetherian, has all of its prime ideals maximal, has only finitely many maximal ideals, and is
the product of its localizations at them, in the sense that the canonical `R`-algebra map
`R → ∀ 𝔪 : MaximalSpectrum R, Localization.AtPrime 𝔪` is bijective. -/
@[stacks 00JB "All four assertions: the finite-length criterion, Noetherianness, maximality of \
  the primes, and the product decomposition, the last as bijectivity of the canonical map.",
  ega "I 6.2.2" "affine, special case", sga "3 VIIB 0.1.1" "partial, special case"]
public theorem
    isArtinianRing_iff_isFiniteLength_and_isNoetherianRing_and_toPiLocalization_bijective
    (R : Type*) [CommRing R] :
    (IsArtinianRing R ↔ IsFiniteLength R R) ∧
      (IsArtinianRing R → IsNoetherianRing R ∧ (∀ p : Ideal R, p.IsPrime → p.IsMaximal) ∧
        Finite (MaximalSpectrum R) ∧
        Function.Bijective (MaximalSpectrum.toPiLocalization R)) :=
          by apply Stacks.Artinian.ProductDecomposition.solution

add_to_stacks 00J5 "the descending chain condition, as stabilization of monotone chains"
  monotone_stabilizes_iff_artinian
