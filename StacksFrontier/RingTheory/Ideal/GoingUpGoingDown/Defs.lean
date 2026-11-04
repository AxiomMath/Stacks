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

@[expose] public section

/-!
# Going up and going down for ring maps

Let `φ : R → S` be a ring map. This file records the two literal definitions
from the Stacks project tag 00HV.

* `RingHom.GoingUp φ`: given primes `p ⊆ p'` in `R` and a prime `q` of `S`
  lying over `p`, there is a prime `q'` of `S` with `q ⊆ q'` lying over `p'`.
* `RingHom.GoingDown φ`: given primes `p ⊆ p'` in `R` and a prime `q'` of `S`
  lying over `p'`, there is a prime `q` of `S` with `q ⊆ q'` lying over `p`.

Here a prime `q` of `S` "lies over" a prime `p` of `R` when `φ⁻¹(q) = p`, i.e.
`Ideal.comap φ q = p`.

Mathlib's `Algebra.HasGoingDown` records the going-down property phrased through
the algebra structure; we give the literal ring-map formulation matching the
Stacks statement.
-/


variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring map `φ : R → S` satisfies **going up** if for all primes
`p ⊆ p'` of `R` and every prime `q` of `S` lying over `p` (that is,
`Ideal.comap φ q = p`), there exists a prime `q'` of `S` with `q ⊆ q'`
lying over `p'`. -/
@[stacks 00HV "(1)"]
def RingHom.GoingUp (φ : R →+* S) : Prop :=
  ∀ (p p' : Ideal R), p.IsPrime → p'.IsPrime → p ≤ p' →
    ∀ (q : Ideal S), q.IsPrime → Ideal.comap φ q = p →
      ∃ q' : Ideal S, q'.IsPrime ∧ q ≤ q' ∧ Ideal.comap φ q' = p'

/-- A ring map `φ : R → S` satisfies **going down** if for all primes
`p ⊆ p'` of `R` and every prime `q'` of `S` lying over `p'` (that is,
`Ideal.comap φ q' = p'`), there exists a prime `q` of `S` with `q ⊆ q'`
lying over `p`. -/
@[stacks 00HV "(2)"]
def RingHom.GoingDown (φ : R →+* S) : Prop :=
  ∀ (p p' : Ideal R), p.IsPrime → p'.IsPrime → p ≤ p' →
    ∀ (q' : Ideal S), q'.IsPrime → Ideal.comap φ q' = p' →
      ∃ q : Ideal S, q.IsPrime ∧ q ≤ q' ∧ Ideal.comap φ q = p

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A prime `q` of `S` *lies over* a prime `p` of `R` along `φ` if `φ⁻¹(q) = p`,
i.e. the contraction (comap) of `q` along `φ` equals `p`. -/
def LiesOver_00oh (φ : R →+* S) (q : Ideal S) (p : Ideal R) : Prop :=
  q.comap φ = p

/-- **Going up** (Stacks 00HV / Definition 10.41.1).
A ring map `φ : R → S` *satisfies going up* if: given primes `p ⊆ p'` in `R` and a
prime `q` in `S` lying over `p`, there exists a prime `q'` of `S` such that `q ⊆ q'`
and `q'` lies over `p'`. -/
def GoingUp_00oh (φ : R →+* S) : Prop :=
  ∀ (p p' : Ideal R), p.IsPrime → p'.IsPrime → p ≤ p' →
    ∀ (q : Ideal S), q.IsPrime → LiesOver_00oh φ q p →
      ∃ (q' : Ideal S), q'.IsPrime ∧ q ≤ q' ∧ LiesOver_00oh φ q' p'

/-- **Going down** (Stacks 00HV / Definition 10.41.1).
A ring map `φ : R → S` *satisfies going down* if: given primes `p ⊆ p'` in `R` and a
prime `q'` in `S` lying over `p'`, there exists a prime `q` of `S` such that `q ⊆ q'`
and `q` lies over `p`. -/
def GoingDown_00oh (φ : R →+* S) : Prop :=
  ∀ (p p' : Ideal R), p.IsPrime → p'.IsPrime → p ≤ p' →
    ∀ (q' : Ideal S), q'.IsPrime → LiesOver_00oh φ q' p' →
      ∃ (q : Ideal S), q.IsPrime ∧ q ≤ q' ∧ LiesOver_00oh φ q p

open Order

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A prime ideal `q ⊆ S` *lies over* a prime ideal `p ⊆ R` under `φ` if the
contraction `φ⁻¹(q)` equals `p`. -/
def LiesOver (φ : R →+* S) (q : Ideal S) (p : Ideal R) : Prop :=
  Ideal.comap φ q = p

/-- The ring map `φ : R → S` *satisfies going up* if for all primes `p ⊆ p'` in `R`
and any prime `q` in `S` lying over `p`, there is a prime `q'` of `S` with `q ⊆ q'`
lying over `p'`. -/
def GoingUp (φ : R →+* S) : Prop :=
  ∀ (p p' : Ideal R), p.IsPrime → p'.IsPrime → p ≤ p' →
    ∀ (q : Ideal S), q.IsPrime → LiesOver φ q p →
      ∃ q' : Ideal S, q'.IsPrime ∧ q ≤ q' ∧ LiesOver φ q' p'

@[expose] public section

open PrimeSpectrum

/-- The ring map `φ : R → S` **satisfies going down** if for all primes `p ≤ p'`
of `R` and every prime `q'` of `S` lying over `p'` (meaning `comap φ q' = p'`),
there exists a prime `q` of `S` with `q ≤ q'` lying over `p` (meaning
`comap φ q = p`).

Here "lying over" is expressed via `PrimeSpectrum.comap`, the contraction map
`q ↦ φ⁻¹(q)`, and the order `≤` on `PrimeSpectrum` is inclusion of the underlying
prime ideals (`p ≤ p' ↔ p.asIdeal ≤ p'.asIdeal`). -/
def RingHom.SatisfiesGoingDown {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) : Prop :=
  ∀ (p p' : PrimeSpectrum R), p ≤ p' →
    ∀ (q' : PrimeSpectrum S), comap φ q' = p' →
      ∃ (q : PrimeSpectrum S), q ≤ q' ∧ comap φ q = p

section GoingDownSketch
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

end GoingDownSketch

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]



