module

public import Mathlib.RingTheory.Ideal.Cotangent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular systems of parameters

A sequence `y 0, …, y (n - 1)` in the maximal ideal `𝔪` of a local ring `R` is a *regular system
of parameters* if its images in the cotangent space `𝔪 / 𝔪 ^ 2` form a basis over the residue
field, and *is part of* one if those images are linearly independent.

## Main definitions

* `IsRegularSystemOfParameters`: the cotangent images form a basis over the residue field.
* `IsPartOfRegularSystemOfParameters`: the cotangent images are linearly independent.
-/

@[expose] public section

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}

/-- A sequence `y 0, …, y (n - 1)` in the maximal ideal `𝔪` of a local ring `R` is a *regular
system of parameters* if the images of the `y i` in the cotangent space `𝔪 / 𝔪 ^ 2` form a
basis over the residue field, i.e. they are linearly independent and they span. -/
@[ega "0 17.1.6", sga "2 IV 5.3"]
def IsRegularSystemOfParameters (y : Fin n → maximalIdeal R) : Prop :=
  LinearIndependent (ResidueField R) (fun i => (maximalIdeal R).toCotangent (y i)) ∧
    Submodule.span (ResidueField R) (Set.range fun i => (maximalIdeal R).toCotangent (y i)) = ⊤

/-- A sequence `z 0, …, z (n - 1)` in the maximal ideal `𝔪` of a local ring `R` *is part of a
regular system of parameters* if the images of the `z i` in the cotangent space `𝔪 / 𝔪 ^ 2` are
linearly independent over the residue field. -/
@[sga "4 XIX 2.1"]
def IsPartOfRegularSystemOfParameters (z : Fin n → maximalIdeal R) : Prop :=
  LinearIndependent (ResidueField R) (fun i => (maximalIdeal R).toCotangent (z i))

/-- `IsPartOfRegularSystemOfParameters`, under the name used in the Stacks 07NM statements. -/
@[sga "4 XIX 2.1"]
abbrev FormsPartOfRegularSystemOfParameters {R : Type*} [CommRing R] [IsLocalRing R] {r : ℕ}
    (z : Fin r → maximalIdeal R) : Prop :=
  IsPartOfRegularSystemOfParameters z

/-! ### Basic API -/

/-- The cotangent images of a regular system of parameters are linearly independent over the
residue field. -/
theorem IsRegularSystemOfParameters.linearIndependent {y : Fin n → maximalIdeal R}
    (h : IsRegularSystemOfParameters y) :
    LinearIndependent (ResidueField R) (fun i => (maximalIdeal R).toCotangent (y i)) :=
  h.1

/-- The cotangent images of a regular system of parameters span the cotangent space over the
residue field. -/
theorem IsRegularSystemOfParameters.span_eq_top {y : Fin n → maximalIdeal R}
    (h : IsRegularSystemOfParameters y) :
    Submodule.span (ResidueField R) (Set.range fun i => (maximalIdeal R).toCotangent (y i)) = ⊤ :=
  h.2

/-- A regular system of parameters is in particular part of a regular system of
parameters. -/
theorem IsRegularSystemOfParameters.isPartOfRegularSystemOfParameters
    {y : Fin n → maximalIdeal R} (h : IsRegularSystemOfParameters y) :
    IsPartOfRegularSystemOfParameters y :=
  h.1
