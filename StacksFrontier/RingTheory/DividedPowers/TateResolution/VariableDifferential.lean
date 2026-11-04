module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential.OddExtensionUnique
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential.OddExtensionLeibniz
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential.EvenPolynomial
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.VariableDifferential.ExistsUnique

/-!
# Differentials on a one-variable extension

This file re-exports the construction, for a cycle `f` of degree `d - 1` in a divided-power
differential graded algebra `A`, of the unique differential on `A⟨T⟩` extending the one of `A` and
sending a new variable `T` of degree `d` to `f`. The parts are:

* `VariableDifferential.OddExtensionUnique`: the odd-variable differential, its uniqueness,
  and the sign rules for the grading-sign automorphism;
* `VariableDifferential.OddExtensionLeibniz`: its Leibniz rule, square-zero property and
  compatibility with divided powers;
* `VariableDifferential.EvenPolynomial`: the even-variable differential and the differential
  graded algebra structure on both extensions;
* `VariableDifferential.ExistsUnique`: divided-power compatibility and uniqueness for the even
  variable, and the existence and uniqueness theorems (Tag 09PM).
-/
