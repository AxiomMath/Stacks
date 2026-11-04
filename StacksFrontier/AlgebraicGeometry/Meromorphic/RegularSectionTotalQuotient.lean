module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicPullback
public import StacksFrontier.AlgebraicGeometry.Meromorphic.TotalQuotientSheafSections

/-!
# A regular function becomes a unit in the sheaf of meromorphic functions

Let `O` be a sheaf of commutative rings on a topological space and let `𝒦 = totalQuotientSheaf O`
be its sheaf of meromorphic functions. A section of `O` over an open set `U` whose germ at every
point of `U` is a nonzerodivisor (a *denominator* over `U`, equivalently a section regular on
`U`) becomes a unit in `𝒦(U)`. Consequently, for a morphism of locally ringed spaces along which
pullbacks of meromorphic functions are defined, the pullback of a section regular on `V` becomes a
unit in the sheaf of meromorphic functions of the source over the preimage of `V`.

## Main results

* `Stacks.Meromorphic.isUnit_toTotalQuotientSheaf_app` — a denominator over `U` becomes a unit
  in `𝒦(U)`, for an arbitrary sheaf of rings on an arbitrary topological space.
* `Stacks.Meromorphic.mem_nonZeroDivisors_toTotalQuotientSheaf_app` — hence a nonzerodivisor.
* `Stacks.Meromorphic.isUnit_toTotalQuotientSheaf_app_of_isRegularSectionOn` — the same for a
  section regular on `U`, on a locally ringed space.
* `Stacks.Meromorphic.isUnit_toTotalQuotientSheaf_app_appPullback` — the pullback of a section
  regular on `V` is a unit in `𝒦` of the source over the whole of `f ⁻¹ V`.

## References

* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 01WZ](https://stacks.math.columbia.edu/tag/01WZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

open scoped nonZeroDivisors

universe u

namespace Stacks.Meromorphic

/-- A section of `O` over `U` whose germ at every point of `U` is a nonzerodivisor becomes a
unit in the sheaf of meromorphic functions over `U`. -/
theorem isUnit_toTotalQuotientSheaf_app {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X)
    {U : Opens X} {b : O.presheaf.obj (op U)}
    (hb : b ∈ (O.presheaf.submonoidPresheafOfStalk
      fun y => (O.presheaf.stalk y)⁰).obj (op U)) :
    IsUnit ((toTotalQuotientSheaf O).hom.app (op U) b) :=
  (isUnit_toTotalQuotientPresheaf_app O.presheaf hb).map
    ((toSheafify (Opens.grothendieckTopology X) O.presheaf.totalQuotientPresheaf).app (op U)).hom

/-- A section of `O` over `U` whose germ at every point of `U` is a nonzerodivisor becomes a
nonzerodivisor in the sheaf of meromorphic functions over `U`. -/
theorem mem_nonZeroDivisors_toTotalQuotientSheaf_app {X : TopCat.{u}}
    (O : TopCat.Sheaf CommRingCat.{u} X) {U : Opens X} {b : O.presheaf.obj (op U)}
    (hb : b ∈ (O.presheaf.submonoidPresheafOfStalk
      fun y => (O.presheaf.stalk y)⁰).obj (op U)) :
    (toTotalQuotientSheaf O).hom.app (op U) b ∈
      ((totalQuotientSheaf O).presheaf.obj (op U))⁰ :=
  (isUnit_toTotalQuotientSheaf_app O hb).mem_nonZeroDivisors

/-- A section of the structure sheaf of a locally ringed space regular on an open `U` becomes a
unit in the sheaf of meromorphic functions over `U`. -/
theorem isUnit_toTotalQuotientSheaf_app_of_isRegularSectionOn (Z : LocallyRingedSpace.{u})
    (U : Opens Z) (s : Z.presheaf.obj (op U)) (hs : IsRegularSectionOn Z U s) :
    IsUnit ((toTotalQuotientSheaf Z.sheaf).hom.app (op U) s) :=
  isUnit_toTotalQuotientSheaf_app Z.sheaf ((mem_denominators_iff Z U s).2 hs)

/-- If pullbacks of meromorphic functions are defined for `f : Z ⟶ W`, the pullback of a section
of the structure sheaf of `W` regular on `V` is a unit in the sheaf of meromorphic functions of
`Z` over `f ⁻¹ V`. -/
theorem isUnit_toTotalQuotientSheaf_app_appPullback {Z W : LocallyRingedSpace.{u}} (f : Z ⟶ W)
    (hf : PullbacksMeromorphicSections f) (V : Opens W) (s : W.presheaf.obj (op V))
    (hs : IsRegularSectionOn W V s) :
    IsUnit ((toTotalQuotientSheaf Z.sheaf).hom.app (op ((Opens.map f.base).obj V))
      (f.c.app (op V) s)) :=
  isUnit_toTotalQuotientSheaf_app_of_isRegularSectionOn Z _ _
    (isRegularSectionOn_appPullback f hf V s hs)

end Stacks.Meromorphic

end
