module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Basic

/-!
# The ideal sheaves of a scheme are bounded by its size

An ideal sheaf on `X` is determined by its components at the affine opens
(`AlgebraicGeometry.Scheme.IdealSheafData.ext`), each of which is an ideal of the ring of
sections there. Both the affine opens and their sections are bounded by
`AlgebraicGeometry.Scheme.size`, so the ideal sheaves are bounded by `2 ^ size`.

## Main results

* `AlgebraicGeometry.Scheme.mk_idealSheafData_le_two_power_size`: a scheme has at most
  `2 ^ size` ideal sheaves.
* `AlgebraicGeometry.Scheme.mk_idealSheafData_lt_of_size_lt`: fewer than `κ` of them, for `κ`
  a strong prelimit above the size.

## References

* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.Scheme

/-- **A scheme has at most `2 ^ size` ideal sheaves.** -/
theorem mk_idealSheafData_le_two_power_size (X : Scheme.{u}) :
    #X.IdealSheafData ≤ 2 ^ X.size := by
  have hinj : Function.Injective (fun I : X.IdealSheafData => I.ideal) :=
    fun _ _ h => Scheme.IdealSheafData.ext h
  have hcomp : ∀ U : X.affineOpens, #(Ideal Γ(X, U.1)) ≤ 2 ^ X.size := by
    intro U
    calc #(Ideal Γ(X, U.1))
        ≤ #(Set Γ(X, U.1)) := Cardinal.mk_le_of_injective SetLike.coe_injective
      _ = 2 ^ #Γ(X, U.1) := Cardinal.mk_set
      _ ≤ 2 ^ X.size :=
          Cardinal.power_le_power_left two_ne_zero (X.mk_sections_le_size U)
  calc #X.IdealSheafData
      ≤ #(∀ U : X.affineOpens, Ideal Γ(X, U.1)) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.prod (fun U : X.affineOpens => #(Ideal Γ(X, U.1))) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod (fun _ : X.affineOpens => (2 : Cardinal.{u}) ^ X.size) :=
        Cardinal.prod_le_prod _ _ hcomp
    _ = ((2 : Cardinal.{u}) ^ X.size) ^ #X.affineOpens := Cardinal.prod_const' _ _
    _ ≤ ((2 : Cardinal.{u}) ^ X.size) ^ X.size :=
        Cardinal.power_le_power_left (Cardinal.power_ne_zero _ two_ne_zero)
          X.mk_affineOpens_le_size
    _ = (2 : Cardinal.{u}) ^ (X.size * X.size) := Cardinal.power_mul.symm
    _ = (2 : Cardinal.{u}) ^ X.size := by rw [Cardinal.mul_eq_self X.aleph0_le_size]

/-- **A scheme has fewer than `κ` ideal sheaves** for a strong prelimit cardinal `κ` exceeding
its size. -/
theorem mk_idealSheafData_lt_of_size_lt (X : Scheme.{u}) {κ : Cardinal.{u}}
    (hκ : κ.IsStrongPrelimit) (hX : X.size < κ) :
    #X.IdealSheafData < κ :=
  X.mk_idealSheafData_le_two_power_size.trans_lt (hκ hX)

end AlgebraicGeometry.Scheme

end
