module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.GlobalMorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothPulledBackFormsToTarget
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence

/-!
# The two morphisms of inverse-image ringed spaces underlying `f : X ⟶ Y` over `S` agree

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S`, two constructions of the morphism of
ringed spaces `(X, (f ≫ g)^{-1}𝒪_S) ⟶ (Y, g^{-1}𝒪_S)` with underlying map that of `f` occur in
the library: `Stacks.DeRhamSmooth.relativeBase f g`, along which the relative de Rham complex is
pushed forward in the triangle of [Stacks, Tag 0FUV], and
`AlgebraicGeometry.DeRhamLerayHirsch.baseMap f g`, the morphism attached to the commutative
square of `f` over the identity of `S`, along which the Leray--Hirsch morphism of
[Stacks, Tag 0FMR] is formed. This file proves that they are equal.

Both lie over `S`, and a morphism into `(Y, g^{-1}𝒪_S)` is determined by its underlying
continuous map and its composite with the projection to `S`
(`AlgebraicGeometry.RingedSpace.inverseImage_hom_ext`).

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.baseMap_eq_relativeBase`: the two morphisms agree.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.DeRhamLerayHirsch

open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The two morphisms `(X, (f ≫ g)^{-1}𝒪_S) ⟶ (Y, g^{-1}𝒪_S)` underlying `f` agree**: the one
of the square of `f` over the identity of `S` and `Stacks.DeRhamSmooth.relativeBase f g`. -/
theorem baseMap_eq_relativeBase : baseMap f g = Stacks.DeRhamSmooth.relativeBase f g := by
  refine RingedSpace.inverseImage_hom_ext S.toRingedSpace g.base _ _ rfl ?_
  refine (inverseImageBaseMap_comp_inverseImageBaseProjection f (f ≫ g) g (𝟙 S) _).trans ?_
  refine ((congrArg (inverseImageBaseProjection (f ≫ g) ≫ ·) rfl).trans
    (Category.comp_id _)).trans ?_
  exact (RingedSpace.inverseImageCompProjection_comp S.toRingedSpace g.base f.base).symm

end AlgebraicGeometry.DeRhamLerayHirsch

end
