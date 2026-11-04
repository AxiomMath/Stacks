module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.OfIsSmooth
public import StacksFrontier.Deformation.Artin.Versality.RepresentableSmoothVersality
public import StacksFrontier.Deformation.Artin.Versality.SmoothPredeformation

/-!
# Smoothness on predeformation categories from a representable smooth morphism

A 1-morphism `p : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf category of a
locally Noetherian scheme `S` which is representable by algebraic spaces and smooth induces, at
every finite type field-valued point of `𝒳`, a smooth functor of predeformation categories. This
is case (3) of Stacks 07WK.

The statement is already in the library as
`Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth'`, registered there as
the representable-and-smooth clause of Stacks 07XW, which the source proves as a reformulation of
07WK. This file records case (3) of Stacks 07WK on that declaration instead of restating it.

## Main results

* `Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth'`:
  **Stacks 07WK**, case (3): representability by algebraic spaces together with smoothness.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 07WK](https://stacks.math.columbia.edu/tag/07WK)
* [Stacks Project, Tag 07XW](https://stacks.math.columbia.edu/tag/07XW)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

add_to_stacks 07WK "representably smooth"
  Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth'

end Deformation.Artin

end
