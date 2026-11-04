module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSection
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk

/-!
# A generator of the stalk of an invertible module is a basis

Let `X` be a scheme and let `L` be an invertible `𝒪_X`-module. The stalk `L_x` is free of rank one
over the local ring `𝒪_{X, x}`, so an element of `L_x` which generates it already freely generates
it: `Stacks.Divisors.IsStalkBasis L x m`, the bijectivity of `r ↦ r • m`, holds as soon as `m`
spans `L_x`.

## Main results

* `Stacks.Divisors.bijective_smul_of_span_eq_top`: over a local ring, a generator of an invertible
  module is a basis.
* `Stacks.Divisors.isStalkBasis_iff_span_eq_top`: for an invertible module on a scheme, an element
  of a stalk is a stalk basis if and only if it spans the stalk.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- Over a local ring `R`, if `m` spans the invertible `R`-module `M`, then `r ↦ r • m` is a
bijection `R → M`. -/
theorem bijective_smul_of_span_eq_top {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Invertible R M] {m : M}
    (hm : Submodule.span R {m} = ⊤) : Function.Bijective fun r : R => r • m := by
  obtain ⟨e⟩ := Stacks.SheafOfModules.Invertible.nonempty_linearEquiv_of_module_invertible R M
  have hsurj : Function.Surjective fun r : R => r • m := fun z =>
    Submodule.mem_span_singleton.mp (hm ▸ Submodule.mem_top : z ∈ Submodule.span R {m})
  refine ⟨fun a b hab => ?_, hsurj⟩
  obtain ⟨r, hr⟩ := hsurj (e.symm 1)
  have hu : IsUnit (e m) := by
    refine IsUnit.of_mul_eq_one r ?_
    have h := congrArg e hr
    rwa [map_smul, e.apply_symm_apply, smul_eq_mul, mul_comm] at h
  have h : e (a • m) = e (b • m) := congrArg e hab
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact hu.mul_right_cancel h

/-- For an invertible module `L` on a scheme `X`, an element `m` of the stalk `L_x` is a stalk
basis if and only if it spans `L_x` over `𝒪_{X, x}`. -/
theorem isStalkBasis_iff_span_eq_top {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : X) (m : L.presheaf.stalk x) :
    IsStalkBasis L x m ↔ Submodule.span ↑(X.presheaf.stalk x) {m} = ⊤ := by
  have _ := Stacks.ChernCap42.isInvertible_stacks_of_algebraicGeometry L
  have _hinv : Module.Invertible ↑(X.presheaf.stalk x) ↑(L.presheaf.stalk x) :=
    Stacks.ChernCap42.moduleInvertible_stalk (X := X) (L := L) x
  exact ⟨fun h => Submodule.eq_top_iff'.2 fun z =>
    Submodule.mem_span_singleton.mpr (h.surjective z), bijective_smul_of_span_eq_top⟩

end Stacks.Divisors

end
