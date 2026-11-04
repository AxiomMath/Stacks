module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionBySumsOfExtensionsByZero

/-!
# Transport of flatness along isomorphisms, and flatness of a zero module

Flatness of a sheaf of modules is a property of its isomorphism class, and the zero sheaf of
modules is flat.

## Main results

* `AlgebraicGeometry.SheafOfModules.IsFlat.of_iso`: flatness transports along an isomorphism.
* `AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero`: a zero sheaf of modules is flat.

## Implementation notes

Flatness is `exactFunctor` applied to `· ⊗_O F`, an `ObjectProperty` of the functor category,
and `ObjectProperty.prop_of_iso` transports it; the isomorphism of functors is the image of
the given isomorphism of modules under `(⊗_O)ᶠˡᶦᵖ`. This two-line transport was previously
written out inline at three places in the tree (twice in Tag 06YS, once in Tag 03EX); it is
named here so that it is written once.

Flatness of a zero module is the empty case of Tag 03EU, a direct sum of flat modules being
flat: a coproduct over `PEmpty` is initial, hence zero, hence isomorphic to any zero module.

The `Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the sheaf of rings is used, which is the
spelling of both the K-flatness development and Tag 03EU.

## References

* [The Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [The Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- Flatness of a sheaf of modules transports along an isomorphism. -/
theorem IsFlat.of_iso
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)}
    (e : M ≅ N) (hM : IsFlat.{u, u, u, u} (O := R) M) : IsFlat.{u, u, u, u} (O := R) N :=
  (Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R N).2
    ((exactFunctor _ _).prop_of_iso
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).flip.mapIso e)
      ((Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R M).1 hM))

/-- A zero sheaf of modules is flat: it is the direct sum of the empty family of flat
modules. -/
theorem IsFlat.of_isZero
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)}
    (hM : IsZero M) : IsFlat.{u, u, u, u} (O := R) M := by
  let E : PEmpty.{u + 1} →
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) := fun i ↦ nomatch i
  exact IsFlat.of_iso R (IsZero.iso (Stacks.Cohomology.isInitial_coproduct_of_isEmpty E).isZero hM)
    (Stacks.SheafOfModules.FlatCoproduct.isFlat_coproduct.{u, u} E (fun i ↦ nomatch i))

end AlgebraicGeometry.SheafOfModules

end

end
