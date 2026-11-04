module

public import Mathlib.Data.ENat.BigOperators
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Tactic

@[expose] public section

open Ring

/-- The integer-valued order of vanishing along a `1`-dimensional Noetherian local domain `R`
with fraction field `K`, evaluated at a nonzero element `x : K`.

This is `Multiplicative.toAdd` applied to the (unzeroed) value of `Ring.ordFrac R x`, which is
nonzero because `x` is a unit of the field `K` and `Ring.ordFrac R` is a `MonoidWithZero`
homomorphism. -/
noncomputable def ordInt (R : Type*) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Nontrivial R]
    (x : K) (hx : x ≠ 0) : ℤ :=
  Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac R x)
    ((hx.isUnit.map (Ring.ordFrac R)).ne_zero))
