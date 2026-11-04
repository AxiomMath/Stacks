module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The reflexive powers of a module and the system `R → M → M^{[2]} → ⋯`

The *reflexive powers* of a module `M` over a commutative ring `R` are

`M^{[1]} = M`,   `M^{[n + 1]} = (M ⊗_R M^{[n]})^{∨∨}`,

and an element `s : M` gives the `ℕ`-indexed system

`R → M → M^{[2]} → M^{[3]} → ⋯`

whose transition maps are multiplication by `s`. This file defines both, with `R` as the term of
index `0`.

## Main definitions

* `reflexivePower M n`: the `n`-th term `M^{[n]}` of the system, with `M^{[0]} = R`.
* `reflexivePowerTransition M s n`: the transition `M^{[n]} ⟶ M^{[n + 1]}`, multiplication by
  `s` followed by the canonical map to the double dual.
* `reflexivePowerSystem M s`: the system as a functor `ℕ ⥤ ModuleCat R`.

## Main results

* `finite_reflexivePower`: over a Noetherian ring, every reflexive power of a finite module is
  finite.

## References

* [Stacks Project, Tag 0EBQ](https://stacks.math.columbia.edu/tag/0EBQ)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.ModuleReflexivePower

/-- The reflexive powers of a module: `M^{[0]} = R`, `M^{[1]} = M` and
`M^{[n + 1]} = (M ⊗_R M^{[n]})^{∨∨}` for `n ≥ 1`. -/
noncomputable def reflexivePower {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | 1 => M
  | n + 2 => ModuleCat.of R
      (Module.Dual R (Module.Dual R (M ⊗ reflexivePower M (n + 1) : ModuleCat.{u} R)))

/-- The zeroth term of the system is the ring itself. -/
@[simp]
theorem reflexivePower_zero {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    reflexivePower M 0 = ModuleCat.of R R := rfl

/-- The first reflexive power is `M` itself. -/
@[simp]
theorem reflexivePower_one {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    reflexivePower M 1 = M := rfl

/-- `M^{[n + 2]} = (M ⊗_R M^{[n + 1]})^{∨∨}`. -/
@[simp]
theorem reflexivePower_succ_succ {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (n : ℕ) :
    reflexivePower M (n + 2) = ModuleCat.of R
      (Module.Dual R (Module.Dual R (M ⊗ reflexivePower M (n + 1) : ModuleCat.{u} R))) := rfl

/-- The transition maps of the system: in degree `0` the map `R → M`, `r ↦ r • s`, and in degrees
`≥ 1` multiplication by `s` followed by the canonical map to the double dual. -/
noncomputable def reflexivePowerTransition {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (s : M) :
    (n : ℕ) → (reflexivePower M n ⟶ reflexivePower M (n + 1))
  | 0 => ModuleCat.ofHom (LinearMap.toSpanSingleton R M s)
  | n + 1 => ModuleCat.ofHom
      ((Module.Dual.eval R (M ⊗ reflexivePower M (n + 1) : ModuleCat.{u} R)).comp
        (TensorProduct.mk R M (reflexivePower M (n + 1)) s))

/-- The transition out of degree `0` is the map `R → M` sending `r` to `r • s`. -/
theorem reflexivePowerTransition_zero {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (s : M) :
    reflexivePowerTransition M s 0 = ModuleCat.ofHom (LinearMap.toSpanSingleton R M s) := rfl

/-- The transition out of degree `n + 1` is multiplication by `s` into the double dual. -/
theorem reflexivePowerTransition_succ {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (s : M)
    (n : ℕ) :
    reflexivePowerTransition M s (n + 1) = ModuleCat.ofHom
      ((Module.Dual.eval R (M ⊗ reflexivePower M (n + 1) : ModuleCat.{u} R)).comp
        (TensorProduct.mk R M (reflexivePower M (n + 1)) s)) := rfl

/-- Over a Noetherian ring every reflexive power of a finite module is finite. -/
instance finite_reflexivePower {R : CommRingCat.{u}} [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] (n : ℕ) : Module.Finite R (reflexivePower M n) := by
  induction n with
  | zero => exact inferInstanceAs (Module.Finite R R)
  | succ n ih =>
    match n, ih with
    | 0, _ => exact inferInstanceAs (Module.Finite R M)
    | m + 1, ih =>
      have : Module.Finite R (M ⊗ reflexivePower M (m + 1) : ModuleCat.{u} R) :=
        Module.Finite.tensorProduct R M (reflexivePower M (m + 1))
      exact inferInstanceAs (Module.Finite R (Module.Dual R
        (Module.Dual R (M ⊗ reflexivePower M (m + 1) : ModuleCat.{u} R))))

/-! ### The system as a diagram -/

/-- The system `R → M → M^{[2]} → ⋯` as a functor `ℕ ⥤ ModuleCat R`: its value at `n` is the
`n`-th reflexive power and its successor maps are the transition maps
`reflexivePowerTransition M s`. -/
noncomputable def reflexivePowerSystem {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (s : M) :
    CategoryTheory.Functor ℕ (ModuleCat.{u} R) :=
  CategoryTheory.Functor.ofSequence (reflexivePowerTransition M s)

/-- The value of the system at `n` is the `n`-th reflexive power. -/
@[simp]
theorem reflexivePowerSystem_obj {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (s : M) (n : ℕ) :
    (reflexivePowerSystem M s).obj n = reflexivePower M n := rfl

/-- The successor step of the system is the transition map. -/
@[simp]
theorem reflexivePowerSystem_map_succ {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (s : M)
    (n : ℕ) :
    (reflexivePowerSystem M s).map (CategoryTheory.homOfLE (Nat.le_add_right n 1)) =
      reflexivePowerTransition M s n :=
  CategoryTheory.Functor.ofSequence_map_homOfLE_succ _ n


end Stacks.AlgebraicGeometry.ModuleReflexivePower

end
