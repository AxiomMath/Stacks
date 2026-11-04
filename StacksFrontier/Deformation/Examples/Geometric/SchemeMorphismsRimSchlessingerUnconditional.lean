module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessinger
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerSquares

/-!
# The deformation category of a morphism of schemes, unconditionally (Stacks 0E3U)

`Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategory` of
`StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessinger` proves the second
assertion of Stacks Tag 0E3U granting condition (RS) for the category of all flat families of
morphisms of schemes, the first assertion. That condition is
`Deformation.Examples.satisfiesRS_schemeMorphismFamilyFunctor`, proved in
`StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerSquares` by gluing the
sources and the targets over one cocartesian square of spectra; this file records the assertion
with no hypothesis.

## Main results

* `Deformation.Examples.schemeMorphismDeformationCategoryProjection_cofiberedInGroupoids`: the
  deformation category of a morphism of schemes over the residue field is cofibered in
  groupoids over `𝒞_Λ`, with no hypothesis. The ambient category of flat families of morphisms
  of schemes is cofibered in groupoids outright, and the base of the special fibre is terminal,
  so the passage to the slice keeps the property.
* `Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategoryProjection`: the
  deformation category of a morphism of schemes over the residue field is a deformation
  category, with no hypothesis.

## References

* [Stacks Project, Tag 0E3U](https://stacks.math.columbia.edu/tag/0E3U)
* [Stacks Project, Tag 06JC](https://stacks.math.columbia.edu/tag/06JC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation.Examples

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The deformation category of a morphism of schemes over the residue field is cofibered in
groupoids over `𝒞_Λ`. Unlike the Rim-Schlessinger condition, this needs no hypothesis: base
change makes the ambient category of all flat families of morphisms of schemes cofibered in
groupoids (`Deformation.Examples.schemeMorphismFamilyFunctor_cofiberedInGroupoids`), the base
of the special fibre of a morphism of schemes over the residue field is terminal
(`Deformation.Examples.isTerminal_residueFieldBase`), and a slice over an object with terminal
base inherits the property. -/
theorem schemeMorphismDeformationCategoryProjection_cofiberedInGroupoids {X Y : Scheme.{v}}
    (f : X ⟶ Y) (pX : X ⟶ baseSpec (residueFieldBase Λ k))
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k)) (hf : f ≫ pY = pX) :
    IsCofiberedInGroupoids (schemeMorphismDeformationCategoryProjection f pX pY hf) :=
  isCofiberedInGroupoids_overForget
    (schemeMorphismFamilyFunctor_cofiberedInGroupoids.{u, v} (Λ := Λ) (k := k)) _
    isTerminal_residueFieldBase

/-- **Stacks Project, Tag 0E3U, second assertion.** The deformation category of a fixed morphism
`X ⟶ Y` of schemes over the residue field is a deformation category: a predeformation category
satisfying the Rim-Schlessinger condition (RS), with no hypothesis.

This is `Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategory` with its
hypothesis supplied by `Deformation.Examples.satisfiesRS_schemeMorphismFamilyFunctor`. -/
@[stacks 0E3U "the in-particular assertion, with nothing assumed: the deformation category \
Def_{X ⟶ Y} of a morphism of schemes X ⟶ Y over k is a deformation category, by the \
localization argument of Tag 06JC. Condition (RS) for the category of all flat families of \
morphisms of schemes of Example 0E3T -- the first assertion -- is \
Deformation.Examples.satisfiesRS_schemeMorphismFamilyFunctor, proved by gluing the sources and \
the targets over one cocartesian square of spectra"]
theorem isDeformationCategory_schemeMorphismDeformationCategoryProjection {X Y : Scheme.{v}}
    (f : X ⟶ Y)
    (pX : X ⟶ baseSpec (residueFieldBase Λ k))
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
    (hf : f ≫ pY = pX) :
    IsDeformationCategory (schemeMorphismDeformationCategoryProjection f pX pY hf) :=
  isDeformationCategory_schemeMorphismDeformationCategory
    satisfiesRS_schemeMorphismFamilyFunctor f pX pY hf

end Deformation.Examples

end
