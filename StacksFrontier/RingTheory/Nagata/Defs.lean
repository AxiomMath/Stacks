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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universally Japanese rings and Nagata rings: definitions

A domain is *N-1* when its integral closure in its fraction field is a finite module over it,
and *N-2*, or *Japanese*, when its integral closure in every finite extension of that fraction
field is: these are `IsN1` and `IsJapaneseRing` of Tag 032F, stated here. Two conditions on a
commutative ring that is not assumed to be a domain are built from the second one. A ring `R` is
*universally Japanese* when every domain of finite type over `R` is N-2, and a *Nagata ring* when
`R` is Noetherian and every quotient of `R` by a prime ideal is N-2. Both are conditions on `R`
alone, quantifying over the domains built from it.

## Main definitions

* N-1 and N-2 (Japanese): `IsN1`, `IsJapaneseRing`.
* Universally Japanese: `IsUniversallyJapaneseRing`, `IsUniversallyJapanese`.
* Nagata: `IsNagataRing`.
* Variant formulations of N-1: `IsN1_032m`.
* Variant formulations of N-2: `IsN2Aux`, `IsN2_032k`, `IsN2_032m`, `IsN2_032s`, `IsN2_032u`.

## Implementation notes

The objects quantified over range in `Type u`, the universe of `R`: the finite-type domain `S`
of `IsUniversallyJapaneseRing`, the prime quotient `R ⧸ p` of `IsNagataRing`, and the finite
extension `L` inside `IsJapaneseRing`. No generality is lost, because a domain of finite type
over `R` is a quotient of a polynomial ring over `R` in finitely many variables, hence
`R`-isomorphic to one in `Type u`, and N-2 is invariant under an isomorphism of `R`-algebras.
An independent universe `v` would instead be wrong on two counts: it does not occur in the
resulting type, so the notation hides it, and below `u` there may be no finite-type domain over
`R` in `Type v` at all, making the condition vacuous.

The field of fractions is taken to be `FractionRing R`, as in Mathlib's `IsIntegrallyClosed`;
phrasing the conditions over an arbitrary `K` with `[IsFractionRing R K]` gives an equivalent
notion, and that equivalence is a separate result rather than part of the definition. `IsN1`
drops the source's hypothesis that `R` be a domain, exactly as `IsIntegrallyClosed` does, and is
an `abbrev`: it *is* the `Module.Finite` predicate it names, so it needs no API and can be used
as an instance binder directly. `IsJapaneseRing` keeps `[IsDomain R]`, where it is load-bearing:
it is what makes `FractionRing R` a field, so that `FiniteDimensional (FractionRing R) L`
expresses "finite field extension of `K`" at all.

The variant formulations of N-1 and N-2 differ in how the fraction field is presented
(`FractionRing R`, or an arbitrary `K` with `[IsFractionRing R K]`), and in the universe the
test extension lives in.

## References

* [Grothendieck and Dieudonné, *Éléments de géométrie algébrique*][EGA], Chapter 0,
  Definition 23.1.1
* [Stacks Project, Tag 032R](https://stacks.math.columbia.edu/tag/032R)
* [Stacks Project, Tag 032F](https://stacks.math.columbia.edu/tag/032F)
* [Stacks Project, Tag 0351](https://stacks.math.columbia.edu/tag/0351)
-/

@[expose] public section

universe u

/-- A domain `R` is **N-1** if the integral closure of `R` in its field of fractions is a finite
`R`-module.

The field of fractions is `FractionRing R`; see the module docstring for the formulation with an
arbitrary field of fractions. As with `IsIntegrallyClosed`, `R` is not required to be a domain:
for a general commutative ring `FractionRing R` is the total ring of fractions, and the condition
reads the same. -/
@[stacks 032F "(1)"]
abbrev IsN1 (R : Type*) [CommRing R] : Prop :=
  Module.Finite R (integralClosure R (FractionRing R))

/-- A domain `R` is **N-2**, or **Japanese**, if for every finite field extension `L` of its
field of fractions `K = Frac(R)`, the integral closure of `R` in `L` is a finite `R`-module.

The extension is presented as a field `L` that is a `K`-algebra, finite dimensional over `K`,
whose `R`-algebra structure is the composite of `R → K` with `K → L`. -/
@[stacks 032F "(2)", ega "0 23.1.1" "def. of Japanese"]
class IsJapaneseRing (R : Type u) [CommRing R] [IsDomain R] : Prop where
  finite (L : Type u) [Field L] [Algebra (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Module.Finite R (integralClosure R L)

attribute [instance] IsJapaneseRing.finite

/-- A ring `R` is **universally Japanese** if for every finite-type ring map `R → S` with `S` a
domain, the domain `S` is N-2 (Japanese), i.e. satisfies `IsJapaneseRing`. -/
@[stacks 032R "(1)", ega "0 23.1.1", ega "IV 7.7.1"]
class IsUniversallyJapaneseRing (R : Type u) [CommRing R] : Prop where
  /-- Every domain of finite type over `R` is N-2. -/
  japanese (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S] :
    IsJapaneseRing S

attribute [instance] IsUniversallyJapaneseRing.japanese

/-- A ring `R` is a **Nagata ring** if `R` is Noetherian and for every prime ideal `p ⊆ R` the
quotient domain `R ⧸ p` is N-2 (Japanese), i.e. satisfies `IsJapaneseRing`. -/
@[stacks 032R "(2)"]
class IsNagataRing (R : Type u) [CommRing R] : Prop where
  isNoetherianRing : IsNoetherianRing R
  isJapaneseRing_quotient (p : Ideal R) [p.IsPrime] : IsJapaneseRing (R ⧸ p)

/-- A Nagata ring is Noetherian. -/
instance (R : Type u) [CommRing R] [IsNagataRing R] : IsNoetherianRing R :=
  IsNagataRing.isNoetherianRing

/-- A domain `R` is N-2 if for every finite field extension `L`
of its fraction field `K = Frac(R)`, the integral closure of `R` in `L` is module-finite
over `R`. The extension `L` is presented as a field which is a `Frac(R)`-algebra (hence an
`R`-algebra via the scalar tower `R → Frac(R) → L`) that is finite-dimensional over
`Frac(R)`. -/
@[ega "0 23.1.1"]
abbrev IsN2_032u (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L],
    Module.Finite R (integralClosure R L)

/-- A domain `R` is **N-2** (also called **Japanese**) if for
every finite field extension `L / K` of its field of fractions `K = Frac(R)`,
the integral closure of `R` in `L` is a finite `R`-module.

The finite field extension `L / K` is encoded by a field `L` equipped with an
algebra structure over `K = FractionRing R` that is finite dimensional; the
ambient `R`-algebra structure on `L` is required to factor through `K`. -/
@[ega "0 23.1.1"]
abbrev IsN2_032s (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L],
    Module.Finite R (integralClosure R L)

/-- A ring `R` is **universally Japanese** if for every finite
type ring map `R → S` with `S` a domain, the ring `S` is N-2 (Japanese). -/
@[ega "0 23.1.1", ega "IV 7.7.1"]
abbrev IsUniversallyJapanese (R : Type u) [CommRing R] : Prop :=
  ∀ (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S],
    IsN2_032s S

/-- A domain `R` is N-2 if for every finite field extension `L` of `FractionRing R`, with `L` in
the universe of `R`, the integral closure of `R` in `L` is a finite `R`-module. -/
abbrev IsN2Aux (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (FractionRing R) L]
    [Algebra R L] [IsScalarTower R (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L],
    Module.Finite R (integralClosure R L)

/-- A domain `R` is *N-2* (or *Japanese*) if for every finite field extension `L/K`
of its fraction field `K = Frac(R)`, the integral closure of `R` in `L` (taken via
the tower `R ⊂ K ⊂ L`) is a finite `R`-module. -/
@[ega "0 23.1.1"]
abbrev IsN2_032k (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  IsN2Aux R

/-- N-1: the integral closure of `R` in its fraction field `K` is a finite
`R`-module. -/
abbrev IsN1_032m (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Prop :=
  Module.Finite R (integralClosure R K)

/-- N-2 (Japanese): for every finite field extension `L / K`, the integral closure
of `R` in `L` is a finite `R`-module. Here `L` ranges over field extensions of `K`
that are finite-dimensional over `K`, equipped with the induced `R`-algebra
structure (`IsScalarTower R K L`). -/
@[ega "0 23.1.1"]
abbrev IsN2_032m (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra R L] [IsScalarTower R K L],
    Module.Finite R (integralClosure R L)
