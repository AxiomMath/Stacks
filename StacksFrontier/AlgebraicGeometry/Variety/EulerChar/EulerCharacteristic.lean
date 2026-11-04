module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Euler characteristic of a coherent sheaf on a proper scheme

For a proper scheme over a field, the Euler characteristic of a coherent sheaf is the
alternating sum of the dimensions of its cohomology groups over the ground field.

## Main definitions

* `AlgebraicGeometry.eulerCharacteristic` is the Euler characteristic of a coherent sheaf on a
  proper scheme over a field.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_eq_finsum` gives the defining alternating sum.

## Implementation notes

The cohomology groups are `AlgebraicGeometry.cohomologyOverField`, which equips the
right-derived global sections with their canonical action of the base field. The sum is
`finsum` over nonnegative degrees; properness and coherence ensure that only finitely many
terms are nonzero and that each cohomology group has finite dimension. The field and structure
morphism are explicit so base change and additivity statements can use the same definition.

## References

* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The alternating sum of the dimensions of the cohomology groups of a coherent sheaf on a
proper scheme over a field. -/
@[stacks 0BEJ,
  ega "III 2.5.1" "field base"]
public noncomputable def eulerCharacteristic (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules) [F.IsCoherent] : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f F n) : ℤ)

/-- The defining alternating-sum formula for the Euler characteristic. -/
public theorem eulerCharacteristic_eq_finsum (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules) [F.IsCoherent] :
    eulerCharacteristic k f F =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f F n) : ℤ) :=
  rfl

end AlgebraicGeometry
