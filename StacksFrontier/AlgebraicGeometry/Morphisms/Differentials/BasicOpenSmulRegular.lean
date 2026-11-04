module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartOverlapRefinement

/-!
# Multiplication by a power of a section is injective on the sections over its principal open

Let `X` be a scheme, let `U` be an open of `X` and let `f` be a section of the structure sheaf over
`U`. On the principal open `X.basicOpen f` the restriction of `f` is a unit, so for any sheaf of
modules `M` on `X` multiplication by any power of `f` is injective on `Γ(M, X.basicOpen f)`, where
`Γ(X, U)` acts by restriction of scalars along the restriction map of the structure sheaf.

## Main results

* `AlgebraicGeometry.injective_smul_powers_basicOpen`: multiplication by an element of the
  submonoid of powers of `f` is injective on `Γ(M, X.basicOpen f)`.

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Multiplication by a power of a section is injective on the sections over its principal
open.** -/
theorem injective_smul_powers_basicOpen {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (f : Γ(X, U)) (r : Submonoid.powers f) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen f) :=
      Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
    Function.Injective fun x : Γ(M, X.basicOpen f) ↦ (r : Γ(X, U)) • x := by
  let : Module Γ(X, U) Γ(M, X.basicOpen f) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  obtain ⟨n, hn⟩ := r.2
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op (r : Γ(X, U))) := by
    rw [← hn, map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen f).pow n
  exact hu.isSMulRegular _

end AlgebraicGeometry

end
