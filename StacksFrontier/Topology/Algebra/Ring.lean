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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Topological rings

A topological ring is a ring with a topology for which addition and multiplication are continuous,
and a homomorphism of topological rings is a continuous ring homomorphism.

## Main definitions

* `StacksTopologicalRing`: a topological ring, defined by continuity of addition and
  multiplication.
* `StacksTopologicalRingHom`: a ring homomorphism between topological rings whose underlying
  function is continuous.

## Main results

* `stacksTopologicalRingHom_iff_continuous`: a ring homomorphism is a homomorphism of topological
  rings exactly when it is continuous.
* `stacksTopologicalRing_iff_isTopologicalRing`: `StacksTopologicalRing` is equivalent to
  Mathlib's `IsTopologicalRing`.
-/

@[expose] public section

/-- **Stacks 0B22**.
A ring `R` equipped with a topology is a topological ring if addition
$(x, y) \mapsto x + y$ and multiplication $(x, y) \mapsto x \cdot y$ are continuous as maps
$R \times R \to R$. -/
@[stacks 0B22, ega "0 3.1.4"]
def StacksTopologicalRing (R : Type*) [Ring R] [TopologicalSpace R] : Prop :=
  Continuous (fun p : R × R => p.1 + p.2) ∧
  Continuous (fun p : R × R => p.1 * p.2)

/-- **Stacks 0B22**.
A bundled ring homomorphism `f : R →+* S` between topological rings is a homomorphism of
topological rings if its underlying function is continuous. -/
@[stacks 0B22, ega "0 20.3.1" "Hom. cont(A,B)", ega "0 3.1.4", sga "3 VIIB 0.1.3"]
def StacksTopologicalRingHom
    {R S : Type*} [Ring R] [Ring S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S]
    (f : R →+* S) : Prop :=
  Continuous (f : R → S)

/-- A ring homomorphism between topological rings is a homomorphism of topological rings exactly
when it is continuous. -/
theorem stacksTopologicalRingHom_iff_continuous
    {R S : Type*} [Ring R] [Ring S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S]
    (f : R →+* S) :
    StacksTopologicalRingHom f ↔ Continuous (f : R → S) := Iff.rfl

/-- For a (unital) ring `R`, the Stacks definition of a topological ring
(addition and multiplication continuous) is equivalent to Mathlib's
`IsTopologicalRing`; continuity of negation follows from `-x = (-1) * x`. -/
theorem stacksTopologicalRing_iff_isTopologicalRing
    (R : Type*) [Ring R] [TopologicalSpace R] :
    StacksTopologicalRing R ↔ IsTopologicalRing R := by
  refine ⟨fun ⟨hadd, hmul⟩ => ?_, fun _ => ⟨continuous_add, continuous_mul⟩⟩
  have : ContinuousAdd R := ⟨hadd⟩
  have : ContinuousMul R := ⟨hmul⟩
  have : IsTopologicalSemiring R := ⟨⟩
  have : ContinuousNeg R := ⟨by
    have hm : Continuous (fun x : R => (-1 : R) * x) :=
      hmul.comp (show Continuous (fun x : R => ((-1 : R), x)) by continuity)
    simpa using hm⟩
  exact ⟨⟩
