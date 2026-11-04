module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.StackOfSheafTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorComparison
public import StacksFrontier.CategoryTheory.FibredOneMorphism

/-!
# The comparison functor of Stacks 04UT is a 1-morphism of fibred categories

Let `B` be an algebraic space over a scheme `S` and let `G` be a group algebraic space over `B`,
with `𝒢` and `ℬ` the sheaves they define on the big fppf site of `S`. The comparison functor
`G-Torsors ⥤ 𝒢/ℬ-Torsors` of Stacks 04UT lies over the big fppf site of `S` and preserves
strongly cartesian morphisms, so it is a 1-morphism of fibred categories over the site in the
sense of Stacks Definition 4.33.9 (2).

## Main results

* `AlgebraicGeometry.Space.FppfTorsors.isFibredOneMorphism_comparison`: the comparison functor
  is a 1-morphism of fibred categories over the big fppf site of `S`.

## References

* [Stacks Project, Tag 04UT](https://stacks.math.columbia.edu/tag/04UT)
* [Stacks Project, Tag 04UM](https://stacks.math.columbia.edu/tag/04UM)
* [Stacks Project, Tag 0CQJ](https://stacks.math.columbia.edu/tag/0CQJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.FppfTorsors

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  {G : GroupAlgebraicSpace 𝒞 S hS B hB}

/-- The comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors` is a 1-morphism of fibred categories over
the big fppf site of `S`: it lies over the site and preserves strongly cartesian morphisms. -/
@[stacks 04UT "the comparison functor is a 1-morphism of fibred categories"]
theorem isFibredOneMorphism_comparison (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    Functor.IsFibredOneMorphism (projection hB G) (SheafTorsors.projection G.obj)
      (comparison hB G) where
  comp_eq := comparison_comp_projection hB G
  map_isStronglyCartesian := by
    intro R T f a b φ hφ
    have _ : (projection hB G).IsHomLift f φ := hφ.toIsHomLift
    have _ : (SheafTorsors.projection G.obj).IsHomLift f ((comparison hB G).map φ) :=
      Functor.isHomLift_map_of_comp_eq (comparison_comp_projection hB G) f φ
    exact (SheafTorsors.projection_isFiberedInGroupoids G.obj).isStronglyCartesian_homLift f
      ((comparison hB G).map φ)

/- The canonical functor comparing `G`-torsors with torsors for the sheaf of groups that `G`
defines is one of the comparisons whose equivalence Stacks 0CQJ asserts. -/
add_to_stacks 0CQJ "the canonical functor G-Torsors ⥤ 𝒢/ℬ-Torsors"
  AlgebraicGeometry.Space.FppfTorsors.comparison

end AlgebraicGeometry.Space.FppfTorsors

end
