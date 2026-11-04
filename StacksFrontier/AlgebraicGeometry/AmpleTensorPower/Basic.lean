module

public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.NormAmple.TensorPower
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensor powers of tensor powers and their nonvanishing opens

Let `X` be a ringed space and `L` an invertible module sheaf on it. This file proves
`(L^{⊗ n})^{⊗ k} ≅ L^{⊗ (n k)}`, identifies the nonvanishing opens of a global section and of its
powers, `X_{s^k} = X_s`, and ascribes the integer tensor powers of an invertible module sheaf on a
scheme at `X.Modules`. These are the facts behind Stacks Tag 01PT, that `L` is ample exactly when a
positive tensor power `L^{⊗ n}` is, which is `AlgebraicGeometry.isAmple_iff_tensorPower_isAmple`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tensorPowerModules`: the integer tensor power of Tag 01CU
  ascribed at `X.Modules`, which is the spelling `IsAmple` is stated for.

## Main results

* `Stacks.SheafOfModules.Invertible.nonempty_tensorPowerModule'_pow_iso`: a tensor power of a
  tensor power is a tensor power, `(L^{⊗ n})^{⊗ k} ≅ L^{⊗ (n k)}`.
* `Stacks.SheafOfModules.Invertible.nonvanishingOpen_sectionPow'`: `X_{s^k} = X_s` for `k ≥ 1`.
* `Stacks.SheafOfModules.nonvanishingOpen_sectionsMap`: the nonvanishing open of a global section
  is invariant under an isomorphism of invertible module sheaves.

## Implementation notes

The comparison `(L^{⊗ n})^{⊗ k} ≅ L^{⊗ (n k)}` is stated as `Nonempty`: it is read off the
Picard group (`Stacks.SheafOfModules.Invertible.picardClass_tensorPowerModule'` and
`Stacks.SheafOfModules.picardClass_eq_iff`) rather than built by induction. Its target exponent
is a separate argument `t` with `n * k = t` supplied as an equation, rather than being written
`n * k`.

`tensorPowerModules` is an `abbrev` whose declared type is `X.Modules`: `IsAmple X M` needs
`M : X.Modules` together with an invertibility instance for it, and
`tensorPower X.toRingedSpace.presheaf _ L n` is only *definitionally* an object of `X.Modules`, so
with that spelling the instance is not found. `Stacks.SheafOfModules.Invertible.tensorPowerModule'`
does the same at `SheafOfModules (structureSheafRing X)` for a ringed space, and
`Stacks.SheafOfModules.Invertible.tensorPowerModule` at `X.ringCatSheaf`.

## References

* [EGA II, Proposition 4.5.6(i)]
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing
  (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x)]

/-- The nonvanishing open of a global section transported along an isomorphism of invertible
module sheaves is the nonvanishing open of the section:
`Stacks.SheafOfModules.nonvanishingLocus_sectionsMap` as an equality of opens. -/
theorem nonvanishingOpen_sectionsMap
    {L M : _root_.SheafOfModules.{u} (structureSheafRing X)}
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    [IsInvertible X.presheaf (structureSheafRing X).property M]
    (e : L ≅ M) (s : L.sections) :
    nonvanishingOpen M (_root_.SheafOfModules.sectionsMap e.hom s) = nonvanishingOpen L s :=
  Opens.ext (nonvanishingLocus_sectionsMap X e s)

namespace Invertible

variable (L : _root_.SheafOfModules.{u} (structureSheafRing X))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L]

/-- Every integer tensor power of an invertible module sheaf is invertible, in the class
`AlgebraicGeometry.SheafOfModules.IsInvertible` and at the ascribed spelling
`tensorPowerModule'`. The sibling `isInvertible_tensorPowerModule'` is the same statement for
the other of the two invertibility classes of Tag 01CS. -/
instance algebraicGeometryIsInvertible_tensorPowerModule' (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property
      (tensorPowerModule' L n) :=
  tensorPower_isInvertible X.presheaf (structureSheafRing X).property L n

omit [∀ x : X.carrier, IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x)]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L] in
/-- **A tensor power of a tensor power is a tensor power**: `(L^{⊗ n})^{⊗ k} ≅ L^{⊗ t}` whenever
`n k = t`. -/
theorem nonempty_tensorPowerModule'_pow_iso
    (hL : IsInvertible X.presheaf (structureSheafRing X).property L) (n k t : ℕ)
    (h : n * k = t) :
    Nonempty (tensorPowerModule' (tensorPowerModule' L (n : ℤ)) (k : ℤ)
      ≅ tensorPowerModule' L (t : ℤ)) := by
  subst h
  refine (picardClass_eq_iff X.presheaf (structureSheafRing X).property _ _
    (isInvertible_tensorPowerModule' (tensorPowerModule' L (n : ℤ)) (k : ℤ))
    (isInvertible_tensorPowerModule' L ((n * k : ℕ) : ℤ))).1 ?_
  rw [picardClass_tensorPowerModule' (tensorPowerModule' L (n : ℤ))
      (isInvertible_tensorPowerModule' L (n : ℤ)) k,
    picardClass_tensorPowerModule' L hL n,
    picardClass_tensorPowerModule' L hL (n * k), smul_smul, Nat.mul_comm]

/-- `X_{s^k} = X_s` for `k ≥ 1`: `Stacks.SheafOfModules.Invertible.nonvanishingLocus_sectionPow'`
as an equality of opens. -/
theorem nonvanishingOpen_sectionPow' {n : ℕ}
    (s : (tensorPowerModule' L (n : ℤ)).sections) (k : ℕ) (hk : 1 ≤ k) :
    nonvanishingOpen (tensorPowerModule' L ((n * k : ℕ) : ℤ)) (sectionPow' L s k)
      = nonvanishingOpen (tensorPowerModule' L (n : ℤ)) s :=
  Opens.ext (nonvanishingLocus_sectionPow' L s k hk)

end Invertible

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- The `n`-th integer tensor power of an invertible module sheaf on a scheme, ascribed at
`X.Modules` and at the spelling of the sheaf of rings that `IsAmple` is stated for. -/
noncomputable abbrev tensorPowerModules {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (n : ℤ) : X.Modules :=
  Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L n

/-- Every integer tensor power of an invertible module sheaf on a scheme is invertible, at the
ascribed spelling `tensorPowerModules`. -/
instance algebraicGeometryIsInvertible_tensorPowerModules {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (tensorPowerModules L n) :=
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L n

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]


end AlgebraicGeometry.Scheme.Modules

end
