module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardAssociatedPoints.Basic

/-!
# Associated points and injections of the residue field

A point `x` of a scheme `X` is associated to an `𝒪_X`-module `F` exactly when the residue field
`κ(x)` injects into the stalk `F_x` as a module over the local ring `𝒪_{X, x}`.

This is the form in which the associated-point hypothesis is used in the proof of
[Stacks, Tag 0BJZ]: "choose a nonzero map `φ_x : κ(x) → F_x`, which exists exactly because `x` is
an associated point of `F`". The definition of an associated point in this library,
`Stacks.Divisors.IsAssociatedPoint`, says instead that the maximal ideal of `𝒪_{X, x}` is the
annihilator of some element of `F_x`.

## Main results

* `isAssociatedPoint_iff_exists_injective_residueField`: the criterion for a point of a scheme
  and a sheaf of modules.
* `mem_associatedPoints_iff_exists_injective_residueField`: the membership form.

## Implementation notes

The commutative algebra is not redone here. The ring-level statement, for an arbitrary prime, is
`PushforwardAssociatedPoints.isAssociatedPrimeStacks_iff_exists_injective`; all that is added is
its specialisation to the maximal ideal of the local ring at a point, where the primality clause
is automatic and can be discharged, leaving a bare existence statement.

The residue field is spelled as the quotient `𝒪_{X, x} ⧸ 𝔪` rather than as
`IsLocalRing.ResidueField 𝒪_{X, x}`. The two are the same object, but they carry *different*
`Module 𝒪_{X, x}` instances — `Submodule.Quotient.module` on the quotient and
`IsLocalRing.instModuleResidueFieldOfAlgebra` on the residue field — which are definitionally
equal but are not unified by `rw`. The quotient spelling is the one the ring-level lemma uses.

## References

* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AssociatedPointResidueField

/-- **A point of a scheme is associated to an `𝒪_X`-module exactly when the residue field there
injects into the stalk.** The residue field `κ(x)` is spelled as the quotient of the local ring
`𝒪_{X, x}` by its maximal ideal.

This is the step of the proof of [Stacks, Tag 0BJZ] that produces the map `φ_x : κ(x) → F_x`
from `x ∈ Ass(F)`. Unlike the ring-level statement it specialises, there is no primality clause:
the maximal ideal of a local ring is prime. -/
theorem isAssociatedPoint_iff_exists_injective_residueField {X : Scheme.{u}} (F : X.Modules)
    (x : X) :
    Stacks.Divisors.IsAssociatedPoint F x ↔
      ∃ φ : (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              →ₗ[X.presheaf.stalk x]
            TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x,
        Function.Injective φ :=
  PushforwardAssociatedPoints.isAssociatedPrimeStacks_iff_exists_injective.trans
    (and_iff_right inferInstance)

/-- Membership form of `isAssociatedPoint_iff_exists_injective_residueField`. -/
theorem mem_associatedPoints_iff_exists_injective_residueField {X : Scheme.{u}} (F : X.Modules)
    (x : X) :
    x ∈ Stacks.Divisors.associatedPoints F ↔
      ∃ φ : (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              →ₗ[X.presheaf.stalk x]
            TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x,
        Function.Injective φ :=
  isAssociatedPoint_iff_exists_injective_residueField F x

end Stacks.AlgebraicGeometry.AssociatedPointResidueField

end
