module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentPullbackRepresentable
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived

/-!
# The stalk of a pullback of a complex of modules on algebraic spaces

For a morphism `f : X ⟶ Y` of algebraic spaces and a geometric point `x̄` of `X`, the stalk at
`x̄` of the degreewise pullback of a complex `K` of `𝒪_Y`-modules is the extension of scalars
along `𝒪_{Y, f(x̄)} ⟶ 𝒪_{X, x̄}` of the stalk of `K` at `f(x̄)`, degreewise.  This is Stacks
05V5 (`AlgebraicGeometry.Space.modulePullbackFiberIso`) applied to each term of the complex.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackStalkComplexIso`: the isomorphism of complexes.

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 05V5 for complexes.**  The stalk at `x̄` of the degreewise pullback of a complex of
`𝒪_Y`-modules is the degreewise extension of scalars of its stalk at `f(x̄)`. -/
def modulePullbackStalkComplexIso (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)
    (K : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) :
    ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f x)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
            (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (modulePullbackFiberIso B S hS f x).app (K.X i))
    (fun i j _ => ((modulePullbackFiberIso B S hS f x).hom.naturality (K.d i j)).symm)

end AlgebraicGeometry.Space

end
