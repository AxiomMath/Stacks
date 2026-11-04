module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleGeneral
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceFundamentalTriangle
import all StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceFundamentalTriangle

/-!
# The fundamental triangle of the tower of a pair of morphisms of ringed spaces

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces. On the site of open subsets of
`X` the structure maps of `f` and `g ∘ f` assemble into the tower
`(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of commutative rings of
`StacksFrontier/Cotangent/SheavesOfRings/RingedSpaceFundamentalTriangle.lean`. This file proves that
its fundamental triangle

`L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ ⋯`

on the two canonical arrows `Stacks.Sheaves.RingedSpaceCotangent.cotangentBaseChange` and
`Stacks.Sheaves.RingedSpaceCotangent.cotangentChangeOfBase` is distinguished in `D(𝒪_X)`, with
no hypothesis.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.exists_distTriang_cotangentTower`: the triangle on
  `cotangentBaseChange` and `cotangentChangeOfBase` is distinguished.

## Implementation notes

This is Tag 08SZ, `CategoryTheory.Sheaf.exists_distTriang_towerCotangent`, at the tower
`(Stacks.Sheaves.RingedSpaceCotangent.baseStructureMap f g, inverseImageStructureMap f)`, read
on `L_{X/Z}` through the equality
`Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_comp_eq`. The first vertex is the
degreewise base change `Stacks.Sheaves.RingedSpaceCotangent.baseChangedCotangentComplex f g`;
it is the derived base change by `CategoryTheory.Sheaf.baseChangedCotangentComplexDerivedIso`.

## References

* [Stacks Project, Tag 08T4](https://stacks.math.columbia.edu/tag/08T4)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageStructureMap)

universe u t

namespace Stacks.Sheaves.RingedSpaceCotangent

variable {X Y Z : RingedSpace.{u, u}} [HasDerivedCategory.{t} (structureModules X)]

/-- **The fundamental triangle of the tower `(g ∘ f)⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`.** For morphisms of
ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` the triangle

`L_{f⁻¹𝒪_Y/(g ∘ f)⁻¹𝒪_Z} ⊗_{f⁻¹𝒪_Y} 𝒪_X ⟶ L_{X/Z} ⟶ L_{X/Y} ⟶ ⋯`

on the two canonical arrows `cotangentBaseChange` and `cotangentChangeOfBase` is distinguished in
`D(𝒪_X)`. -/
theorem exists_distTriang_cotangentTower (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ δ : (DerivedCategory.Q (C := structureModules X)).obj (cotangentComplex f) ⟶
        ((DerivedCategory.Q (C := structureModules X)).obj
          (baseChangedCotangentComplex f g))⟦(1 : ℤ)⟧,
      Triangle.mk ((DerivedCategory.Q (C := structureModules X)).map (cotangentBaseChange f g))
          ((DerivedCategory.Q (C := structureModules X)).map (cotangentChangeOfBase f g)) δ ∈
        distTriang (DerivedCategory (structureModules X)) := by
  obtain ⟨δ, hδ⟩ := CategoryTheory.Sheaf.exists_distTriang_towerCotangent.{u, u, u, t}
    (D := structureSheafOfSite X) (Opens.grothendieckTopology X.carrier)
    (baseStructureMap f g) (inverseImageStructureMap f)
  exact exists_mem_distTriang_of_eq (cotangentComplex_comp_eq f g) _ _ δ hδ

end Stacks.Sheaves.RingedSpaceCotangent

end
