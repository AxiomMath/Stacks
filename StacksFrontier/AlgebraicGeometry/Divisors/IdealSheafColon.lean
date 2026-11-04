module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksFrontier.RingTheory.Localization.ColonIdeal

/-!
# The quotient of two quasi-coherent ideal sheaves

Let `X` be a scheme and let `ℐ`, `𝒥` be quasi-coherent sheaves of ideals on `X`, presented as
`AlgebraicGeometry.Scheme.IdealSheafData`. If `𝒥` is finitely generated on every affine open,
the affine-local colon ideals

`(ℐ : 𝒥)(U) = {a ∈ Γ(X, U) | a · 𝒥(U) ⊆ ℐ(U)}`

are again the sections of a quasi-coherent sheaf of ideals, the *quotient* `ℐ : 𝒥`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.colon`: the quotient `ℐ : 𝒥`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.mul_colon_le`: `𝒥 · (ℐ : 𝒥) ≤ ℐ`.
* `AlgebraicGeometry.Scheme.IdealSheafData.le_colon_iff`: the universal property, `𝒦 ≤ ℐ : 𝒥`
  if and only if `𝒥 · 𝒦 ≤ ℐ`.

## Implementation notes

The only thing to check is the compatibility `(ℐ : 𝒥)(D(f)) = (ℐ : 𝒥)(U)_f` that
`Scheme.IdealSheafData` demands, and that is `Ideal.map_colon_of_fg`, the statement that colon
ideals commute with localization at a finitely generated second argument. The sections of `𝒪_X`
over a basic open of an affine open are a localization by
`AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`, whose `algebraMap` is the restriction
map of the structure sheaf.

Finite generation of `𝒥` cannot be dropped: without it the colon ideals do not localize, and the
family is not the sections of a quasi-coherent sheaf. It is passed as a hypothesis rather than
imposed on the type, since the divisor applications verify it by hand.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **The quotient of two quasi-coherent ideal sheaves.** For sheaves of ideals `ℐ` and `𝒥` on a
scheme `X`, with `𝒥` finitely generated on every affine open, this is the sheaf of ideals whose
sections over an affine open `U` are the colon ideal

`(ℐ : 𝒥)(U) = {a ∈ Γ(X, U) | a · 𝒥(U) ⊆ ℐ(U)}`.

It is the largest sheaf of ideals `𝒦` with `𝒥 · 𝒦 ≤ ℐ`; see
`AlgebraicGeometry.Scheme.IdealSheafData.le_colon_iff`. -/
def colon (I J : X.IdealSheafData)
    (hJ : ∀ U : X.affineOpens, (J.ideal U : Submodule Γ(X, U) Γ(X, U)).FG) :
    X.IdealSheafData where
  ideal U := (I.ideal U).colon ((J.ideal U : Ideal Γ(X, U)) : Set Γ(X, U))
  map_ideal_basicOpen U f := by
    let _ := U.2.isLocalization_basicOpen f
    have h := Ideal.map_colon_of_fg (Submonoid.powers f) Γ(X, X.basicOpen f)
      (I.ideal U) (J.ideal U) (hJ U)
    rw [show (algebraMap Γ(X, U) Γ(X, X.basicOpen f)) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom from
        RingHom.algebraMap_toAlgebra _] at h
    rw [h, I.map_ideal_basicOpen U f, J.map_ideal_basicOpen U f]
    rfl

/-- The ideal of sections of `ℐ : 𝒥` over an affine open `U` is the colon ideal
`(ℐ(U) : 𝒥(U))`. -/
@[simp]
theorem ideal_colon (I J : X.IdealSheafData)
    (hJ : ∀ U : X.affineOpens, (J.ideal U : Submodule Γ(X, U) Γ(X, U)).FG)
    (U : X.affineOpens) :
    (I.colon J hJ).ideal U =
      (I.ideal U).colon ((J.ideal U : Ideal Γ(X, U)) : Set Γ(X, U)) := rfl

/-- The defining property of the quotient: multiplying by `𝒥` lands back inside `ℐ`. -/
theorem mul_colon_le (I J : X.IdealSheafData)
    (hJ : ∀ U : X.affineOpens, (J.ideal U : Submodule Γ(X, U) Γ(X, U)).FG) :
    J * I.colon J hJ ≤ I := fun U => by
  refine Ideal.mul_le.mpr fun a ha b hb => ?_
  simpa only [smul_eq_mul, mul_comm a b] using (Submodule.mem_colon.mp hb) a ha

/-- **The universal property of the quotient of ideal sheaves.** A sheaf of ideals `𝒦` is
contained in `ℐ : 𝒥` exactly when `𝒥 · 𝒦 ≤ ℐ`. -/
theorem le_colon_iff {I J K : X.IdealSheafData}
    (hJ : ∀ U : X.affineOpens, (J.ideal U : Submodule Γ(X, U) Γ(X, U)).FG) :
    K ≤ I.colon J hJ ↔ J * K ≤ I := by
  refine ⟨fun h => le_trans (fun U => Ideal.mul_mono_right (h U)) (mul_colon_le I J hJ),
    fun h U => fun a ha => Submodule.mem_colon.mpr fun b hb => ?_⟩
  simpa only [smul_eq_mul, mul_comm a b] using h U (Ideal.mul_mem_mul hb ha)

end AlgebraicGeometry.Scheme.IdealSheafData

end
