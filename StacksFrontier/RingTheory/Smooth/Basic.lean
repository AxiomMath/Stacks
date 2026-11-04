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
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.Basic
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
import StacksCore.Tactic.StacksAttribute

/-!
# Smooth and formally smooth ring maps

Base change and composition of smooth, standard smooth and formally smooth ring maps, and the
characterization of smoothness as formal smoothness plus finite presentation, are all Mathlib's.
This file records their Stacks tags, and their EGA and SGA references, on the Mathlib
declarations. That a polynomial ring is formally smooth over its base (Stacks 10.138.4, tag
`00TK`) is Mathlib's instance as well.

## Conventions

* An ideal `I` of a commutative ring `A` is of *square zero* if `I ^ 2 = 0`, i.e.
  `x * y = 0` for all `x, y ∈ I`.
* An `R`-algebra `S` is *formally smooth* over `R` if for every commutative `R`-algebra `A`,
  every square-zero ideal `I ⊆ A` and every `R`-algebra map `g : S → A ⧸ I` there is an
  `R`-algebra map `f : S → A` with `π ∘ f = g`, where `π : A → A ⧸ I` is the projection.
  This is `Algebra.FormallySmooth R S` (Stacks 10.138.1, tag `00TI`).
-/

-- The former @[stacks 00T4] declaration is now the Mathlib theorem.
add_to_stacks 00T4 "smoothness is stable under base change" Algebra.Smooth.baseChange
add_to_sga "1 II 4.13" "affine ascent" Algebra.Smooth.baseChange
add_to_sga "3 VIB 10.1" "smoothness, special case" Algebra.Smooth.baseChange
add_to_sga "3 VIB 2.1.2" "special case" Algebra.Smooth.baseChange
add_to_sga "6 VIII 1.6" "special case" Algebra.Smooth.baseChange
add_to_sga "6 VIII 1.8" "affine case" Algebra.Smooth.baseChange
add_to_sga "6 X 7.13.3" "special case" Algebra.Smooth.baseChange
add_to_ega "0 19.3.5" "(iii), special case" Algebra.Smooth.baseChange
add_to_ega "0 19.4.2" "Necessity, special case" Algebra.Smooth.baseChange
add_to_ega "0 19.4.6" "special case" Algebra.Smooth.baseChange
add_to_ega "IV 17.3.3" "(iii), special case" Algebra.Smooth.baseChange
add_to_ega "IV 17.7.3" "(ii)" Algebra.Smooth.baseChange
add_to_ega "IV 6.8.2" "special case" Algebra.Smooth.baseChange
add_to_ega "IV 6.8.3" "(iii), special case" Algebra.Smooth.baseChange
add_to_sga "1 II 1.3" "(ii), affine case" Algebra.Smooth.baseChange

-- The former @[stacks 00T9] declaration is now the Mathlib theorem.
add_to_stacks 00T9 "standard smoothness is stable under composition"
  RingHom.IsStandardSmooth.comp
add_to_sga "1 II 1.3" "(iii), special case" RingHom.IsStandardSmooth.comp

-- The former @[stacks 00TD] declaration is now the Mathlib theorem.
add_to_stacks 00TD "smoothness is stable under composition" RingHom.Smooth.comp
add_to_sga "1 II 1.3" "(iii), special case" RingHom.Smooth.comp
add_to_ega "IV 17.3.3" "(ii), special case" RingHom.Smooth.comp
add_to_ega "IV 6.8.3" "special case" RingHom.Smooth.comp

-- The former @[stacks 00TJ] declaration is now the Mathlib instance.
add_to_stacks 00TJ "formal smoothness is stable under base change"
  Algebra.FormallySmooth.instTensorProduct
add_to_ega "0 19.3.5" "(iii), special case" Algebra.FormallySmooth.instTensorProduct
add_to_ega "0 19.4.2" "Necessity, special case" Algebra.FormallySmooth.instTensorProduct
add_to_ega "0 19.4.6" "special case" Algebra.FormallySmooth.instTensorProduct
add_to_ega "0 19.9.3" "discrete topology" Algebra.FormallySmooth.instTensorProduct

-- The former @[stacks 00TN] declaration is now the Mathlib theorem.
add_to_stacks 00TN "smooth = formally smooth + finite presentation" Algebra.smooth_iff
add_to_ega "IV 17.3.1" "smooth case, ring maps" Algebra.smooth_iff
add_to_ega "IV 17.3.2" "(ii), smooth case" Algebra.smooth_iff

-- The former @[stacks 031H] declaration is now the Mathlib theorem.
add_to_stacks 031H "formal smoothness is stable under composition" Algebra.FormallySmooth.comp
add_to_ega "0 19.3.5" "(ii), special case" Algebra.FormallySmooth.comp
add_to_ega "0 19.5.4.4" "partial" Algebra.FormallySmooth.comp
add_to_ega "IV 17.1.3" "(ii), special case" Algebra.FormallySmooth.comp
