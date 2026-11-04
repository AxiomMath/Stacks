module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorPowers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.EssentiallySmallTensorPerfect

/-!
# Products of integer tensor powers of perfect objects on an algebraic space are perfect

Let `X` be an algebraic space and let `E_1, …, E_r` be perfect objects of `D(𝒪_X)`. For every
`n ∈ ℤ^{⊕ r}` the object

`E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`

of `D(𝒪_X)` is perfect. This is what makes `n ↦ E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` a family of
perfect objects indexed by `ℤ^{⊕ r}`, the family Stacks 0DNE considers.

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedDual`: the dual `E^∨ = RSheafHom(E, 𝒪_X)` of a
  perfect object is perfect (Stacks 08JJ).
* `AlgebraicGeometry.Space.isPerfect_derivedTensorProductFunctor_obj_obj`: the derived tensor
  product of two perfect objects is perfect (Stacks 09JB).
* `AlgebraicGeometry.Space.isPerfect_derivedTensorPower`: an integer tensor power `E^{⊗ n}` of a
  perfect object is perfect.
* `AlgebraicGeometry.Space.isPerfect_derivedTensorPowerProduct`: **the objects
  `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` are perfect** when the `E_j` are.

## Implementation notes

The small étale site of `X` is essentially small at the universe of its structure sheaf, and the
statements are the ones of an essentially small ringed site:
`AlgebraicGeometry.RingedSite.isPerfect_essentiallySmallDerivedDual` for the dual, which is
computed on a small model, and
`AlgebraicGeometry.RingedSite.isPerfect_derivedTensorProduct_of_essentiallySmall` for the
tensor product. The product of powers is then handled by
`AlgebraicGeometry.Space.derivedTensorPowerProduct_mem`, perfectness holding for `𝒪_X`
(`AlgebraicGeometry.Space.isPerfect_derivedStructureSheaf`), for the `E_j` and their duals, and
being stable under the derived tensor product.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 09JB](https://stacks.math.columbia.edu/tag/09JB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The dual of a perfect object of `D(𝒪_X)` is perfect** (Stacks 08JJ). -/
theorem isPerfect_derivedDual (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : (smallEtaleRingedSite B S hS F hF).IsPerfect E) :
    (smallEtaleRingedSite B S hS F hF).IsPerfect (derivedDual B S hS F hF E) :=
  RingedSite.isPerfect_essentiallySmallDerivedDual _ E hE

/-- **The derived tensor product of two perfect objects of `D(𝒪_X)` is perfect**
(Stacks 09JB). -/
theorem isPerfect_derivedTensorProductFunctor_obj_obj
    (E E' : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : (smallEtaleRingedSite B S hS F hF).IsPerfect E)
    (hE' : (smallEtaleRingedSite B S hS F hF).IsPerfect E') :
    (smallEtaleRingedSite B S hS F hF).IsPerfect
      (((Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedSite B S hS F hF)).obj E).obj E') :=
  RingedSite.isPerfect_derivedTensorProduct_of_essentiallySmall _ _ E E' hE hE'

/-- **An integer tensor power of a perfect object of `D(𝒪_X)` is perfect.** -/
theorem isPerfect_derivedTensorPower (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : (smallEtaleRingedSite B S hS F hF).IsPerfect E) (n : ℤ) :
    (smallEtaleRingedSite B S hS F hF).IsPerfect (derivedTensorPower B S hS F hF E n) := by
  simpa [derivedTensorPowerProduct_eq] using
    derivedTensorPowerProduct_mem (r := 1) (E := fun _ => E)
      (smallEtaleRingedSite B S hS F hF).IsPerfect (isPerfect_derivedStructureSheaf B S hS F hF)
      isPerfect_derivedTensorProductFunctor_obj_obj (fun _ => hE)
      (fun _ => isPerfect_derivedDual E hE) (fun _ => n)

/-- **The objects `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` of `D(𝒪_X)` are perfect** when
`E_1, …, E_r` are perfect: perfectness holds for `𝒪_X`, for each `E_j` and for each dual
`E_j^∨`, and it is stable under the derived tensor product. -/
theorem isPerfect_derivedTensorPowerProduct {r : ℕ}
    (E : Fin r → DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : ∀ j, (smallEtaleRingedSite B S hS F hF).IsPerfect (E j)) (n : Fin r → ℤ) :
    (smallEtaleRingedSite B S hS F hF).IsPerfect (derivedTensorPowerProduct B S hS F hF E n) :=
  derivedTensorPowerProduct_mem _ (isPerfect_derivedStructureSheaf B S hS F hF)
    isPerfect_derivedTensorProductFunctor_obj_obj hE (fun j => isPerfect_derivedDual _ (hE j)) n

end AlgebraicGeometry.Space

end
