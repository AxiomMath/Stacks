module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.CoherentModules
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.IsomorphismClasses
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedSizeBounded

/-!
# Codes for polarized families over a scheme

A polarized family `(X ⟶ K, ℒ)` with `X` of finite type over `K` is described, up to isomorphism
over `K`, by the isomorphism class of `X` among the schemes of finite type over `K` together with
the isomorphism class of `ℒ`, transported to the chosen representative of that class, among the
coherent modules there. Over a countable field there are countably many isomorphism classes of
schemes of finite type (Stacks 0G0U), and on each of them countably many isomorphism classes of
coherent modules (Stacks 0G0W).

## Main definitions

* `AlgebraicGeometry.PolarizedFibreCode.Code`: the pairs of an isomorphism class of schemes of
  finite type over `K` and an isomorphism class of coherent modules on its chosen representative.

## References

* [Stacks Project, Tag 0G0U](https://stacks.math.columbia.edu/tag/0G0U)
* [Stacks Project, Tag 0G0W](https://stacks.math.columbia.edu/tag/0G0W)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace PolarizedFibreCode

variable {B : BigFppfSite.{u}} {hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ)))}

/-- A code for a polarized family over `K`: the isomorphism class of its total space among the
schemes of finite type over `K`, and the isomorphism class of a coherent module on the chosen
representative of that class. -/
abbrev Code (K : Scheme.{u}) :=
  Σ c : Quotient (isIsomorphicSetoid (ObjectProperty.FullSubcategory
      (fun X : Over K => LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom))),
    Skeleton (SheafOfModules.CoherentModules c.out.obj.left.ringCatSheaf)

end PolarizedFibreCode

open PolarizedFibreCode

variable (B : BigFppfSite.{u}) (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))

end AlgebraicGeometry

end
