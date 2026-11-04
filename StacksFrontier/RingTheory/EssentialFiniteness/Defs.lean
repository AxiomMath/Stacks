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
# Ring maps essentially of finite type and essentially of finite presentation

A ring map `f : R →+* S` is essentially of finite type (resp. essentially of finite presentation)
if `S`, as an `R`-algebra via `f`, is a localization of an `R`-algebra of finite type (resp. of
finite presentation).

## Main definitions

* `IsEssentiallyOfFiniteType R S f`: `S` is a localization of a finite type `R`-algebra.
* `IsEssentiallyOfFinitePresentation R S f`: `S` is a localization of a finitely presented
  `R`-algebra.
-/

@[expose] public section

/-- A ring map `f : R →+* S` is *essentially of finite type* if `S` is, as an
`R`-algebra (via `f`), the localization at some submonoid of an `R`-algebra `T`
of finite type. -/
@[stacks 00QM "(1)", ega "IV 1.3.8"]
def IsEssentiallyOfFiniteType.{u} (R S : Type u) [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.FiniteType R T)
    (M : Submonoid T) (_ : Algebra T S), IsScalarTower R T S ∧ IsLocalization M S

/-- A ring map `f : R →+* S` is *essentially of finite presentation* if `S` is,
as an `R`-algebra (via `f`), the localization at some submonoid of an
`R`-algebra `T` of finite presentation. -/
@[stacks 00QM "(2)"]
def IsEssentiallyOfFinitePresentation.{u} (R S : Type u) [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.FinitePresentation R T)
    (M : Submonoid T) (_ : Algebra T S), IsScalarTower R T S ∧ IsLocalization M S

