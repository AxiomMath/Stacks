module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.GermInjective
public import StacksFrontier.RingTheory.Localization.AwayToAtPrime

/-!
# Injecting sections into a local ring

For an integral scheme, a locally Noetherian scheme, or a reduced scheme with only finitely many
irreducible components, every point has an affine open neighbourhood on which the canonical germ
map from sections to the local ring is injective.

## Main results

* `AlgebraicGeometry.exists_affineOpen_germ_injective_of_isIntegral` treats integral schemes.
* `AlgebraicGeometry.exists_affineOpen_germ_injective_of_isLocallyNoetherian` treats locally
  Noetherian schemes.
* `AlgebraicGeometry.exists_affineOpen_germ_injective_of_isReduced` treats reduced schemes with
  finitely many irreducible components.
-/

public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On an integral scheme, every point admits an affine open neighbourhood whose canonical
map from its ring of sections to the local ring at the point is injective. -/
@[stacks 0BX3 "part (1)"]
theorem exists_affineOpen_germ_injective_of_isIntegral (X : Scheme.{u}) (x : X)
    [IsIntegral X] :
    ∃ (U : X.Opens) (hx : x ∈ U),
      IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx) :=
  X.exists_germ_injective x

/-- On a locally Noetherian scheme, every point admits an affine open neighbourhood whose
canonical map from its ring of sections to the local ring at the point is injective. -/
@[stacks 0BX3 "part (2)"]
theorem exists_affineOpen_germ_injective_of_isLocallyNoetherian (X : Scheme.{u}) (x : X)
    [IsLocallyNoetherian X] :
    ∃ (U : X.Opens) (hx : x ∈ U),
      IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx) :=
  X.exists_germ_injective x

/-- On a reduced scheme with finitely many irreducible components, every point admits an
affine open neighbourhood whose canonical map from its ring of sections to the local ring at
the point is injective. -/
@[stacks 0BX3 "part (3)"]
theorem exists_affineOpen_germ_injective_of_isReduced (X : Scheme.{u}) (x : X)
    [IsReduced X] (hX : (irreducibleComponents X).Finite) :
    ∃ (U : X.Opens) (hx : x ∈ U),
      IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx) := by
  have := X.isGermInjective_of_isReduced_of_finite_irreducibleComponents hX
  exact X.exists_germ_injective x

end AlgebraicGeometry

end
