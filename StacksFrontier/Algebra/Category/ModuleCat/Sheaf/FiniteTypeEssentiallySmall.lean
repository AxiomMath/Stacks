module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.Geometry.RingedSpace.Basic
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Properties.CardinalGeneratedSmall

/-!
# Finite type sheaves of modules on a ringed space form a set up to isomorphism

For a ringed space `(X, O_X)`, the sheaves of `O_X`-modules of finite type have only a set of
isomorphism classes.

## Main results

* `Stacks.SheafOfModules.essentiallySmall_isFiniteType`: the sheaves of modules of finite type
  on a ringed space form an essentially small class.

## Implementation notes

The structure sheaf is regarded as a sheaf of not-necessarily-commutative rings by applying
`forget₂ CommRingCat RingCat`. Having a set containing exactly one representative of every
isomorphism class is expressed as essential smallness of the finite-type object property. A
module of finite type is `ℵ₀`-generated, so the result is the case `κ = ℵ₀` of
`AlgebraicGeometry.CardinalGenerated.essentiallySmall_isCardinalGenerated`.

## References

* [Stacks Project, Tag 01BC](https://stacks.math.columbia.edu/tag/01BC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.SheafOfModules

-- The statement below is elaborated with this finite-limits instance; the imports provide
-- another candidate.
attribute [local instance 101] CategoryTheory.Limits.hasFiniteLimits_of_hasLimits

/-- The finite type sheaves of modules over the structure sheaf of a ringed
space have only a set of isomorphism classes. -/
@[stacks 01BC]
theorem essentiallySmall_isFiniteType (X : RingedSpace.{u, u}) :
    ObjectProperty.EssentiallySmall.{u}
      (fun M : SheafOfModules.{u}
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat RingCat)).obj X.sheaf) ↦
        SheafOfModules.IsFiniteType M) := by
  refine (AlgebraicGeometry.CardinalGenerated.essentiallySmall_isCardinalGenerated X
    Cardinal.aleph0).of_le fun M hM ↦ ?_
  obtain ⟨σ, hσ⟩ := hM.exists_localGeneratorsData
  exact ⟨σ, fun i ↦ have := (hσ.isFiniteType i).finite; Cardinal.mk_le_aleph0⟩

end Stacks.SheafOfModules

end
