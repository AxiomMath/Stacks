module

public import StacksFrontier.LinearAlgebra.ExteriorPower.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange
public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy

/-!
# Further results on `Localization`

Results about the objects of `StacksFrontier.LinearAlgebra.ExteriorPower.Localization` that need
imports beyond those of that module.
-/

@[expose] public noncomputable section

open scoped TensorProduct

variable {R : Type*} [CommRing R]
  (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
  {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [Module Rₛ M'] [IsScalarTower R Rₛ M']
  (f : M →ₗ[R] M') (n : ℕ)

namespace exteriorPower

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- **`exteriorPower.mapTower` followed by `exteriorPower.map` is `exteriorPower.mapTower` of
the composite.** Both sides send a wedge `m₁ ∧ ⋯ ∧ mₙ` to `g (f m₁) ∧ ⋯ ∧ g (f mₙ)`. -/
theorem map_comp_mapTower {P : Type*} [AddCommGroup P] [Module R P] [Module A P]
    [IsScalarTower R A P] (f : M →ₗ[R] N) (g : N →ₗ[A] P) (n : ℕ) :
    (map n g).restrictScalars R ∘ₗ mapTower (S := A) n f =
      mapTower (S := A) n (g.restrictScalars R ∘ₗ f) := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  show map n g (mapTower (S := A) n f (ιMulti R n v)) =
    mapTower (S := A) n (g.restrictScalars R ∘ₗ f) (ιMulti R n v)
  rw [mapTower_ιMulti, map_apply_ιMulti, mapTower_ιMulti]
  rfl

/-- **`exteriorPower.map` followed by `exteriorPower.mapTower` is `exteriorPower.mapTower` of
the composite.** Both sides send a wedge `m₁ ∧ ⋯ ∧ mₙ` to `f (g m₁) ∧ ⋯ ∧ f (g mₙ)`. -/
theorem mapTower_comp_map {M' : Type*} [AddCommGroup M'] [Module R M'] (g : M' →ₗ[R] M)
    (f : M →ₗ[R] N) (n : ℕ) :
    mapTower (S := A) n f ∘ₗ map n g = mapTower (S := A) n (f ∘ₗ g) := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  show mapTower (S := A) n f (map n g (ιMulti R n v)) =
    mapTower (S := A) n (f ∘ₗ g) (ιMulti R n v)
  rw [map_apply_ιMulti, mapTower_ιMulti, mapTower_ιMulti]
  rfl

end exteriorPower

end
