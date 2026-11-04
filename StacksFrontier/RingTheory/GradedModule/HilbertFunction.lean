module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Order.Filter.AtTopBot.Defs
public import StacksFrontier.Algebra.Polynomial.Numerical

/-!
# Hilbert functions of graded modules

A graded module over a ring `A` is a module `M` together with a family of submodules
`piece : ℤ → Submodule A M` carrying a `DirectSum.Decomposition`, so that `M = ⨁_n M^n`. Such a
module is *locally finite* when each `M^n` is a finitely generated `A`-module. An
*Euler–Poincaré function* assigns an integer to every finitely generated `A`-module, additively
in short exact sequences; evaluating it on the homogeneous pieces of a locally finite graded
module gives the module's *Hilbert function*. The module *has a Hilbert polynomial* when its
Hilbert function eventually agrees with a numerical polynomial.

## Main definitions

* `GradedModule.IsLocallyFinite`: every homogeneous piece is finitely generated.
* `GradedModule.finitePiece`: a homogeneous piece of a locally finite graded module, bundled as
  an object of `FGModuleCat`.
* `GradedModule.EulerPoincareFunction`: an integer-valued function on finitely generated
  modules, additive in short exact sequences.
* `GradedModule.hilbertFunction`: the Hilbert function of a locally finite graded module with
  respect to an Euler–Poincaré function.
* `GradedModule.HasHilbertPolynomial`: eventual agreement of the Hilbert function with a
  numerical polynomial.

## Implementation notes

Mathlib represents a grading of an already given module by a family of submodules carrying a
`DirectSum.Decomposition` instance; that representation is adopted directly rather than
rebundled, so all of the definitions below take the family and the instance as arguments.
Finitely generated modules are bundled as `FGModuleCat` objects where an Euler–Poincaré function
is evaluated. Eventual agreement is expressed with the filter at infinity on `ℤ`.

No Noetherian hypothesis on the base ring is needed: the hypothesis the source carries is not
used once local finiteness of the graded module is assumed.

## References

* [Stacks Project, Tag 027Y](https://stacks.math.columbia.edu/tag/027Y)
-/

@[expose] public section

namespace GradedModule

universe u v

add_to_stacks 027Y "graded modules" DirectSum.Decomposition

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

/-- A graded module is locally finite when every homogeneous piece is finitely generated over
the base ring. -/
@[stacks 027Y "locally finite graded modules"]
abbrev IsLocallyFinite (piece : ℤ → Submodule A M) [DirectSum.Decomposition piece] : Prop :=
  ∀ n : ℤ, Module.Finite A (piece n)

/-- A homogeneous piece of a locally finite graded module, bundled as a finitely generated
module. -/
def finitePiece (piece : ℤ → Submodule A M) [DirectSum.Decomposition piece]
    (hpiece : IsLocallyFinite piece) (n : ℤ) : FGModuleCat.{v} A :=
  ⟨ModuleCat.of A (piece n), hpiece n⟩

/-- An Euler–Poincaré function assigns an integer to every finitely generated module and is
additive in short exact sequences. -/
@[stacks 027Y "Euler-Poincare functions", ext]
structure EulerPoincareFunction (A : Type u) [Ring A] where
  /-- The value on a finitely generated module. -/
  toFun : FGModuleCat.{v} A → ℤ
  /-- Additivity on a short exact sequence. -/
  add_of_short_exact : ∀ {M' M M'' : FGModuleCat.{v} A} (f : M' →ₗ[A] M) (g : M →ₗ[A] M''),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
      toFun M = toFun M' + toFun M''

/-- An Euler–Poincaré function is applied to a finitely generated module through its value
`toFun`. -/
instance : CoeFun (EulerPoincareFunction.{u, v} A) (fun _ ↦ FGModuleCat.{v} A → ℤ) :=
  ⟨EulerPoincareFunction.toFun⟩

/-- The Hilbert function of a locally finite graded module with respect to an Euler–Poincaré
function: its value at `n` is the value of the function on the degree-`n` piece. -/
@[stacks 027Y "Hilbert functions"]
def hilbertFunction (piece : ℤ → Submodule A M) [DirectSum.Decomposition piece]
    (hpiece : IsLocallyFinite piece) (φ : EulerPoincareFunction.{u, v} A) : ℤ → ℤ :=
  fun n ↦ φ (finitePiece piece hpiece n)

/-- The value of the Hilbert function at `n` is the value of `φ` on the degree-`n` piece. -/
@[simp] theorem hilbertFunction_apply (piece : ℤ → Submodule A M)
    [DirectSum.Decomposition piece] (hpiece : IsLocallyFinite piece)
    (φ : EulerPoincareFunction.{u, v} A) (n : ℤ) :
    hilbertFunction piece hpiece φ n = φ (finitePiece piece hpiece n) := rfl

/-- A locally finite graded module has a Hilbert polynomial with respect to `φ` when its Hilbert
function eventually agrees, on integer arguments, with a numerical polynomial. -/
@[stacks 027Y "Hilbert polynomials"]
abbrev HasHilbertPolynomial (piece : ℤ → Submodule A M) [DirectSum.Decomposition piece]
    (hpiece : IsLocallyFinite piece) (φ : EulerPoincareFunction.{u, v} A) : Prop :=
  ∃ P : Polynomial ℚ, P.IsNumerical ∧
    ∀ᶠ n : ℤ in Filter.atTop, (hilbertFunction piece hpiece φ n : ℚ) = P.eval (n : ℚ)

end GradedModule
