module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatAtDivisor

/-!
# The stalk of the structure sheaf of a closed subscheme, in length

Let `j : Z ⟶ X` be a closed immersion of schemes and `v` a point of `Z`. The stalk map
`𝒪_{X, j v} ⟶ 𝒪_{Z, v}` is surjective, so `𝒪_{Z, v}` is the quotient of `𝒪_{X, j v}` by the
stalk of the ideal sheaf of `Z`. This file records the consequence for lengths: the length of
`𝒪_{Z, v}` *over itself* is the length over `𝒪_{X, j v}` of the quotient of `𝒪_{X, j v}` by that
ideal stalk.

## Main results

* `AlgebraicGeometry.Module.length_self_eq_length_quotient_ker`: for a surjective ring homomorphism
  the length of the target over itself is the colength of the kernel.
* `AlgebraicGeometry.length_stalk_self_eq_length_quotient_ker_stalkMap`: the length of `𝒪_{Z, v}`
  over itself is the length over `𝒪_{X, j v}` of `𝒪_{X, j v} ⧸ ker (j.stalkMap v)`.
* `AlgebraicGeometry.length_stalk_self_eq_length_quotient_stalk_ker`: the same with the kernel
  written as the stalk of the ideal sheaf of `Z`, which needs an affine open of `X` around
  `j v`.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The length of `T` over itself is the colength of the kernel, for a surjective ring
homomorphism `f : R →+* T`.** -/
theorem Module.length_self_eq_length_quotient_ker {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (hf : Function.Surjective f) :
    Module.length T T = Module.length R (R ⧸ RingHom.ker f) := by
  let alg : Algebra R T := f.toAlgebra
  have htow : IsScalarTower R T T := IsScalarTower.right
  have h1 : Module.length R T = Module.length T T := Module.length_eq_of_surjective hf
  have h2 := length_quotient_ker_eq_length f hf
  rw [← h1, ← h2]

variable {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j] (v : Z)

/-- **The length of the stalk of a closed subscheme, over itself, is the colength of the kernel
of the stalk map.** -/
theorem length_stalk_self_eq_length_quotient_ker_stalkMap :
    Module.length (Z.presheaf.stalk v) (Z.presheaf.stalk v) =
      Module.length (X.presheaf.stalk (j v))
        (X.presheaf.stalk (j v) ⧸ RingHom.ker (j.stalkMap v).hom) :=
  Module.length_self_eq_length_quotient_ker (j.stalkMap v).hom (j.stalkMap_surjective v)

/-- **The length of the stalk of a closed subscheme, over itself, is the colength of the stalk of
its ideal sheaf.** -/
theorem length_stalk_self_eq_length_quotient_stalk_ker (U : X.Opens) (hU : IsAffineOpen U)
    (hv : j v ∈ U) :
    Module.length (Z.presheaf.stalk v) (Z.presheaf.stalk v) =
      Module.length (X.presheaf.stalk (j v))
        (X.presheaf.stalk (j v) ⧸ IdealSheafData.stalk j.ker (j v)) := by
  rw [length_stalk_self_eq_length_quotient_ker_stalkMap j v,
    stalk_ker_eq_of_affine_target j v U hU hv]

end AlgebraicGeometry

end
