module

public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminant
public import StacksFrontier.LinearAlgebra.ExteriorAlgebra.Prod
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange
public import StacksFrontier.RingTheory.Koszul.ContractionDeterminant

/-!
# Homomorphisms out of an exterior power of a free module, with values in an algebra

Let `R` be a commutative ring, let `S` be an `R`-algebra, and let `ι` be a finite type. The
`R`-linear maps from the `n`-th exterior power of the free module `Rⁱ` to `S` are the
`S`-linear functionals on the `n`-th exterior power of the free `S`-module `Sⁱ`:

`Hom_R(⋀ⁿ_R(Rⁱ), S) ≅ Hom_S(⋀ⁿ_S(Sⁱ), S)`.

The point is that the right-hand side is a *dual* in the sense of `Module.Dual S`, over a ring
for which `Sⁱ` is free of finite rank. The duality pairing of exterior powers,
`exteriorPower.pairingDual`, and its bijectivity for a finite free module are available there and
are not available on the left: `Hom_R(⋀ⁿ_R(Rⁱ), S)` is a module of maps into a coefficient module
rather than into the base ring, and the pairing has no coefficient-general form — its
characterising formula is a determinant of scalars, which for `n ≥ 2` has no analogue valued in a
module.

Composing the two gives the identification this file exists for,

`⋀ⁿ_S(Hom_S(Sⁱ, S)) ≅ Hom_R(⋀ⁿ_R(Rⁱ), S)`,

which carries a wedge of `n` functionals to their `n`-fold iterated contraction. It is an
isomorphism because `Sⁱ` is free of finite rank over `S`, so `exteriorPower.bijective_pairingDual`
applies to it.

## Main definitions

* `exteriorPower.homFreeBaseChangeEquiv`: the base-change identification displayed first.
* `exteriorPower.exteriorDualFreeBaseChangeEquiv`: its composite with the duality pairing.

## Main statements

* `exteriorPower.homFreeBaseChangeEquiv_exteriorDualFreeBaseChangeEquiv_ιMulti`: the
  identification carries a wedge of functionals to their iterated contraction.

## Implementation notes

The first identification is the composite of three standard equivalences, in this order: the
tensor-restriction adjunction on linear maps, `LinearMap.liftBaseChangeEquiv`, which replaces an
`R`-linear map into `S` by an `S`-linear map out of `S ⊗_R -`; base change of an exterior power,
`ExteriorAlgebra.exteriorPowerBaseChange`, which moves the tensor factor inside; and the
trivialisation `S ⊗_R Rⁱ ≅ Sⁱ` of `Algebra.TensorProduct.piScalarRight`, transported through
exterior powers by `exteriorPowerCongr`. Each of the three is an equivalence with no hypothesis
beyond `ι` being finite, so the composite needs none either — in particular `S` is an arbitrary
`R`-algebra here, not necessarily a quotient of `R`.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra

namespace exteriorPower

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ)

/-- **Homomorphisms out of an exterior power of a free module, after base change.** The
`R`-linear maps `⋀ⁿ_R(Rⁱ) ⟶ S` are the `S`-linear functionals on `⋀ⁿ_S(Sⁱ)`. -/
def homFreeBaseChangeEquiv :
    ((⋀[R]^n (ι → R)) →ₗ[R] S) ≃ₗ[S] Module.Dual S (⋀[S]^n (ι → S)) :=
  LinearMap.liftBaseChangeEquiv S ≪≫ₗ
    LinearEquiv.arrowCongr
      (ExteriorAlgebra.exteriorPowerBaseChange R S (ι → R) n) (LinearEquiv.refl S S) ≪≫ₗ
    LinearEquiv.arrowCongr
      (exteriorPowerCongr n (Algebra.TensorProduct.piScalarRight R S S ι).toLinearEquiv)
      (LinearEquiv.refl S S)

/-- **The exterior power of the dual of a finite free module computes the homomorphisms out of
the exterior power.** Combining the duality pairing of `Sⁱ`, which is bijective because `Sⁱ` is
free of finite rank over `S`, with the base-change identification:

`⋀ⁿ_S(Hom_S(Sⁱ, S)) ≅ Hom_R(⋀ⁿ_R(Rⁱ), S)`. -/
def exteriorDualFreeBaseChangeEquiv :
    (⋀[S]^n (Module.Dual S (ι → S))) ≃ₗ[S] ((⋀[R]^n (ι → R)) →ₗ[R] S) :=
  exteriorPower.pairingDualEquiv S (ι → S) n ≪≫ₗ (homFreeBaseChangeEquiv R S ι n).symm

/-- **The identification is iterated contraction on wedges.** The wedge of `n` functionals on
`Sⁱ` corresponds to the functional on `⋀ⁿ_S(Sⁱ)` given by contracting with them in turn. -/
theorem homFreeBaseChangeEquiv_exteriorDualFreeBaseChangeEquiv_ιMulti
    (f : Fin n → Module.Dual S (ι → S)) :
    homFreeBaseChangeEquiv R S ι n
        (exteriorDualFreeBaseChangeEquiv R S ι n (exteriorPower.ιMulti S n f))
      = Koszul.listContractionDual n (List.ofFn f) := by
  rw [exteriorDualFreeBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact Koszul.pairingDual_ιMulti n f

end exteriorPower

end
