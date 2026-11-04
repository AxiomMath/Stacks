module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatCokernel
import StacksCore.Tactic.StacksAttribute

/-!
# The lowest cokernel of a flat complex of Tor amplitude in `[a, b]`, for the site's `⊗^L`

Stacks 08G0 says: let `(C, O)` be a ringed site and let `E` be a bounded above complex of flat
`O`-modules with Tor amplitude in `[a, b]`; then `Coker(d^{a-1} : E^{a-1} ⟶ E^a)` is a flat
`O`-module.

`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitude` proves this with
Tor amplitude measured against a *given* derived tensor product datum `T`. This file states it
with Tor amplitude measured against the derived tensor product of the site itself,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` of Stacks 06YU, so that nothing beyond the
ringed site, the complex and the universe of the localization is supplied.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitude_canonical`:
  **Stacks 08G0** for the derived tensor product of the site.

## Implementation notes

The site, its structure sheaf and its modules share one universe `u`, as in the sibling
statement of Stacks 08G1 for the same derived tensor product,
`Stacks.SheafOfModules.DerivedTensorProduct`
`.hasTorAmplitude_canonical_iff_exists_flatRepresentative`.
At that universe the site is small, and the sheafification, additivity and totalisation
infrastructure that the datum-relative statement takes as instance arguments are all instances,
so none of them appears in the statement. The universe `d` of the localization is free and the
derived category is any model, `HasDerivedCategory.{d}`.

## References

* [Stacks Project, Tag 08G0](https://stacks.math.columbia.edu/tag/08G0)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, u, u}} [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]

/-- **Stacks 08G0, for the derived tensor product of the site.** Let `(C, O)` be a ringed site
and let `K` be a bounded above complex of flat `O`-modules which, as an object of `D(O)`, has
Tor amplitude in `[a, b]` for the derived tensor product
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` of Stacks 06YU. Then the cokernel of the
differential `K^{a-1} ⟶ K^a` is a flat `O`-module.

No derived tensor product datum is supplied: the one Tor amplitude is measured against is the
one Stacks 06YU constructs. -/
@[stacks 08G0]
theorem isFlat_cokernel_of_hasTorAmplitude_canonical
    (K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a b : ℤ)
    (hbound : ∃ n : ℤ, K.IsStrictlyLE n)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) :
    letI : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
    letI : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
    HasTorAmplitude (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X)
        (DerivedCategory.Q.obj K) a b →
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
        (cokernel (K.d (a - 1) a)) :=
  let : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
  isFlat_cokernel_of_hasTorAmplitude
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X) K a b hbound hflat

end Stacks.SheafOfModules.DerivedTensorProduct

end
