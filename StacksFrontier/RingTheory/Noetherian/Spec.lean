module

public import StacksCore.Tactic.StacksAttribute
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
# Noetherian rings and their spectra

Stability of the Noetherian condition under finite-type extension and localization
(Stacks 00FN), the Noetherianness of `Spec R` as a topological space (Stacks 00FQ) and the
finiteness of the set of minimal primes (Stacks 00FR) are all Mathlib's, so only the
`add_to_stacks` and `add_to_ega` pointers to those declarations are recorded here.

The theorem proved here is the base change of a Noetherian ring along a finite-type ring map
(Stacks 0CY6), which Mathlib has only as the composite of `Algebra.FiniteType.baseChange` with
the Hilbert basis theorem.
-/

@[expose] public section

-- The former @[stacks 00FN "(1)"] theorem is the Mathlib theorem.
add_to_stacks 00FN "(1)" Algebra.FiniteType.isNoetherianRing
add_to_sga "3 VIB 10.10" "more general" Algebra.FiniteType.isNoetherianRing
add_to_sga "5 V 5.1.4" "special case" Algebra.FiniteType.isNoetherianRing
add_to_ega "0 22.3.1" "Noetherianity of A" Algebra.FiniteType.isNoetherianRing
add_to_ega "0 23.2.5" "Noetherian clause" Algebra.FiniteType.isNoetherianRing
add_to_ega "II 2.1.5" "sufficiency" Algebra.FiniteType.isNoetherianRing
add_to_ega "IV 1.4.1" "more general" Algebra.FiniteType.isNoetherianRing
add_to_ega "IV 1.5.3" "affine case" Algebra.FiniteType.isNoetherianRing

-- The former @[stacks 00FN "(2)"] theorem is the Mathlib theorem.
add_to_stacks 00FN "(2)" IsLocalization.isNoetherianRing
add_to_ega "0 10.3.1.1" "B is Noetherian" IsLocalization.isNoetherianRing

-- The former @[stacks 00FQ] theorem was `inferInstance`, i.e. the Mathlib instance itself.
add_to_stacks 00FQ PrimeSpectrum.instNoetherianSpace
add_to_ega "I 1.1.6" PrimeSpectrum.instNoetherianSpace

-- The former @[stacks 00FR] theorems are Mathlib's. The affine form — `Spec R` has finitely
-- many irreducible components — is `PrimeSpectrum.instNoetherianSpace` above followed by
-- `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`, which already carries
-- `@[stacks 0052 "(2)"]`; the ring-theoretic form is the lemma named here.
add_to_stacks 00FR minimalPrimes.finite_of_isNoetherianRing
add_to_ega "0 1.1.1" "Minimal primes over (0)" minimalPrimes.finite_of_isNoetherianRing
add_to_ega "0 2.2.5" "affine case" minimalPrimes.finite_of_isNoetherianRing
add_to_ega "0 2.2.5" "ring-theoretic form"
  minimalPrimes.finite_of_isNoetherianRing

/-- If `R → R'` is of finite type and `S` is a Noetherian `R`-algebra, then
the base change `R' ⊗[R] S` is a Noetherian ring.

The proof transports the result along the commutativity isomorphism
`S ⊗[R] R' ≃ R' ⊗[R] S`, after observing that base change preserves
finite type and applying the Hilbert basis theorem. -/
@[stacks 0CY6,
  ega "I 6.3.8" "affine case",
  ega "IV 1.5.5" "affine case",
  ega "I 10.13.5" "(ii)",
  ega "I 6.6.7" "affine case",
  ega "II 2.1.5" "sufficiency",
  ega "IV 1.3.5" "affine schemes",
  ega "IV 6.7.1.1" "special case",
  sga "1 III 1.4" "partial",
  sga "5 V 5.1.4" "special case",
  sga "5 V 5.1.5" "special case",
  sga "6 X 7.15" "special case",
  sga "6 X 7.17" "special case"]
theorem noetherian_base_change_finite_type
    (R R' S : Type*) [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R R'] [Algebra R S]
    [Algebra.FiniteType R R'] [IsNoetherianRing S] :
    IsNoetherianRing (TensorProduct R R' S) :=
  have : Algebra.FiniteType S (TensorProduct R S R') := Algebra.FiniteType.baseChange S
  have : IsNoetherianRing (TensorProduct R S R') := Algebra.FiniteType.isNoetherianRing S _
  isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm R S R').toRingEquiv

add_to_ega "0 2.2.5" "affine case" TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
