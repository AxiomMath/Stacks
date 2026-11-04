module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact

/-!
# The stalk functor of modules at a geometric point

For a geometric point `z` of an algebraic space `Z`, the stalk functor of `𝒪_Z`-modules at the
point of the small étale site determined by `z`, valued in modules over the stalk of the
structure sheaf.

## Main definitions

* `AlgebraicGeometry.Space.structureModuleStalkFunctorAtPoint`: that functor.

## References

* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The stalk functor at a geometric point on `𝒪`-modules, valued in modules over the
`CommRingCat`-valued stalk of the structure sheaf.

This is `Stacks.sheafModuleFiberOfCommRing` at the point of the small étale site determined by
the geometric point; the declared source and target fix the spelling of the two categories, so
that the implicit category arguments of `CategoryTheory.Limits.PreservesFiniteLimits` match on
the nose in composites. -/
def structureModuleStalkFunctorAtPoint (Z : AlgebraicSpaces B S hS)
    (z : GeometricPoint B S hS Z.1) :
    Modules.{u, u} B S hS Z.1 Z.2 ⥤
      ModuleCat.{u} (Stacks.ringFiber (etaleSitePoint B S hS Z.1 z Z.2)
        (smallEtaleRingedTopos B S hS Z).O.obj) :=
  Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Z.1 z Z.2)
    (smallEtaleRingedTopos B S hS Z).O

end AlgebraicGeometry.Space

end
