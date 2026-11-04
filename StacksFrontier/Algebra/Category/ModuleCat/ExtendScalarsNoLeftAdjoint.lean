module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of modules has a left adjoint only if the ring map is flat

Let `f : R →+* S` be a ring map. Base change `ModuleCat.extendScalars f : M ↦ S ⊗_R M` has a
right adjoint, namely restriction of scalars `ModuleCat.restrictScalars f`; this is Mathlib's
`ModuleCat.extendRestrictScalarsAdj`. It does *not* in general have a left adjoint: a functor
with a left adjoint preserves all limits, in particular monomorphisms, and base change
preserves monomorphisms exactly when `S ⊗_R -` preserves injective maps, which is flatness of
`S` over `R`. So a left adjoint can only exist when `f` is flat, and for a non-flat ring map
such as `ℤ → ℤ/2ℤ` there is none.

## Main results

* `Stacks.ChangeOfRings.hasRightAdjoint_extendScalars`: base change along `f : R →+* S` always
  has a right adjoint, namely restriction of scalars.
* `Stacks.ChangeOfRings.flat_of_preservesMonomorphisms_extendScalars`: if base change along
  `f : R →+* S` preserves monomorphisms of modules, then `f` is flat.
* `Stacks.ChangeOfRings.flat_of_isRightAdjoint_extendScalars`: if base change along `f` has a
  left adjoint, then `f` is flat.
* `Stacks.ChangeOfRings.not_isRightAdjoint_extendScalars_of_not_flat`: base change along a
  non-flat ring map has no left adjoint.
* `Stacks.ChangeOfRings.not_flat_intCastRingHom_zmodTwo` and
  `Stacks.ChangeOfRings.not_isRightAdjoint_extendScalars_zmodTwo`: the ring map `ℤ → ℤ/2ℤ` is
  not flat, so base change along it has no left adjoint.

## References

* [Stacks Project, Tag 04BI](https://stacks.math.columbia.edu/tag/04BI)
-/

@[expose] public section

open CategoryTheory

universe v u₁ u₂

namespace Stacks.ChangeOfRings

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

/-- Base change `M ↦ S ⊗_R M` along a ring map `f : R →+* S` always has a right adjoint, namely
restriction of scalars along `f`. -/
@[stacks 04BI "base change has a right adjoint, namely restriction of scalars"]
theorem hasRightAdjoint_extendScalars :
    (ModuleCat.extendScalars.{u₁, u₂, max v u₂} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{v, u₁, u₂} f).isLeftAdjoint

add_to_stacks 04BI "the right adjoint of base change is restriction of scalars, as an adjunction"
  ModuleCat.extendRestrictScalarsAdj

/-- If base change `M ↦ S ⊗_R M` along a ring map `f : R →+* S` preserves monomorphisms of
modules, then `f` is flat. -/
theorem flat_of_preservesMonomorphisms_extendScalars [Small.{v} R]
    (h : (ModuleCat.extendScalars.{u₁, u₂, v} f).PreservesMonomorphisms) : f.Flat := by
  let : Algebra R S := f.toAlgebra
  show Module.Flat R S
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap'.{v}]
  intro N N' _ _ _ _ g hg
  have : Mono (ModuleCat.ofHom g) := (ModuleCat.mono_iff_injective _).2 hg
  exact (ModuleCat.mono_iff_injective _).1
    ((ModuleCat.extendScalars.{u₁, u₂, v} f).map_mono (ModuleCat.ofHom g))

/-- If base change `M ↦ S ⊗_R M` along a ring map `f : R →+* S` has a left adjoint, then `f` is
flat. -/
@[stacks 04BI "a left adjoint of base change forces flatness"]
theorem flat_of_isRightAdjoint_extendScalars [Small.{v} R]
    (h : (ModuleCat.extendScalars.{u₁, u₂, v} f).IsRightAdjoint) : f.Flat := by
  have := h
  exact flat_of_preservesMonomorphisms_extendScalars f inferInstance

/-- Base change along a non-flat ring map has no left adjoint. -/
theorem not_isRightAdjoint_extendScalars_of_not_flat [Small.{v} R] (hf : ¬ f.Flat) :
    ¬ (ModuleCat.extendScalars.{u₁, u₂, v} f).IsRightAdjoint := fun h =>
  hf (flat_of_isRightAdjoint_extendScalars f h)

/-- The ring map `ℤ → ℤ/2ℤ` is not flat. -/
theorem not_flat_intCastRingHom_zmodTwo : ¬ (Int.castRingHom (ZMod 2)).Flat := by
  rw [show Int.castRingHom (ZMod 2) = algebraMap ℤ (ZMod 2) from
    (algebraMap_int_eq (R := ZMod 2)).symm, RingHom.flat_algebraMap_iff]
  intro h
  have h2 : IsSMulRegular (ZMod 2) (2 : ℤ) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero two_ne_zero)
  have hz : (2 : ℤ) • (1 : ZMod 2) = (2 : ℤ) • (0 : ZMod 2) := by decide
  exact one_ne_zero (h2 hz)

/-- Base change `M ↦ ℤ/2ℤ ⊗_ℤ M` along the ring map `ℤ → ℤ/2ℤ` has no left adjoint. -/
@[stacks 04BI "no left adjoint in general"]
theorem not_isRightAdjoint_extendScalars_zmodTwo :
    ¬ (ModuleCat.extendScalars.{0, 0, v} (Int.castRingHom (ZMod 2))).IsRightAdjoint :=
  not_isRightAdjoint_extendScalars_of_not_flat _ not_flat_intCastRingHom_zmodTwo

end Stacks.ChangeOfRings
