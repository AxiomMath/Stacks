module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison

/-!
# The unit constraint of the derived tensor product, in the internal-Hom spelling

A ringed site carries two derived tensor products on `D(Mod(𝒪))`, and
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` identifies them.  The unit
constraint `𝒪 ⊗^L_𝒪 E ≅ E` of [Stacks, Tag 0FPT] is stated over the second of the two, as
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso`.  This file reads it over the
first, which is the one the derived internal Hom and the tensor–internal-Hom bijection of
[Stacks, Tag 08J8] are stated over.

That is the form the general case of [Stacks, Tag 08EH] needs: there a map `α : E|_U ⟶ E'|_U` is
transposed by Tag 08J8 at source variable the structure sheaf, and the transpose lands on
`(𝒪_X ⊗^L_{𝒪_X} E)|_U` rather than on `E|_U`.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.interfaceLeftUnitIso`: the unit constraint
  `𝒪 ⊗^L_𝒪 E ≅ E` over `Stacks.SheafOfModules.derivedTensorProductFunctor`.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.interfaceLeftUnitIso_hom`: it is the comparison of the
  two derived tensor products followed by the unit constraint of Tag 0FPT.

## Implementation notes

No project tag is attached.  Tag 0FPT already sits on
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso`, and the content below is
that isomorphism transported along a comparison of two spellings of one bifunctor, not a second
account of the tag.

The derived category is the standard one, as it is in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit`: the unit
constraint there is stated with `CategoryTheory.HasDerivedCategory.standard` in force rather
than generically in the derived category's hom universe.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DerivedTensor.RingedSite (unitObject)

namespace Stacks.SheafOfModules.DerivedMonoidal

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (RingedSite.Modules X) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The unit constraint of [Stacks, Tag 0FPT] over
`Stacks.SheafOfModules.derivedTensorProductFunctor`**: the structure sheaf in degree zero is a
unit for the derived tensor product the derived internal Hom is stated over,

`𝒪 ⊗^L_𝒪 E ≅ E`.

It is `Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` followed by the unit
constraint `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso`. -/
def interfaceLeftUnitIso (E : DerivedCategory (RingedSite.Modules X)) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj (unitObject X)).obj E ≅ E :=
  ((interfaceTensorCanonicalIso X).app (unitObject X)).app E ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).leftUnitIso X E

/-- The unit constraint in the internal-Hom spelling, written out: the comparison of the two
derived tensor products of the site followed by the unit constraint of [Stacks, Tag 0FPT]. -/
theorem interfaceLeftUnitIso_hom (E : DerivedCategory (RingedSite.Modules X)) :
    (interfaceLeftUnitIso X E).hom =
      (((interfaceTensorCanonicalIso X).app (unitObject X)).app E).hom ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).leftUnitIso X E).hom :=
  rfl

end Stacks.SheafOfModules.DerivedMonoidal

end
