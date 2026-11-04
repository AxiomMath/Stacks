module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms

/-!
# Exterior powers of sheaves of modules commute with pullback

For a morphism of schemes `f : X' ⟶ X` and a sheaf of `𝒪_X`-modules `F`, the canonical
comparison `f^*(⋀ⁿ F) ⟶ ⋀ⁿ(f^*F)` is an isomorphism in every degree. This is
[Stacks, Tag 01CI] for the exterior algebra, which
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullbackIso` proves for a morphism
of ringed spaces; the declaration below is that statement read at the exterior powers
`AlgebraicGeometry.Scheme.Modules.exteriorPower` of a sheaf of modules on a scheme.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.exteriorPowerPullbackIso`: **the isomorphism
  `f^*(⋀ⁿ F) ≅ ⋀ⁿ(f^*F)`.**

## Implementation notes

Both exterior algebras are the chosen ones of
`AlgebraicGeometry.Scheme.Modules.exteriorAlgebra`, and both enter
`Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso` through their universal property
`AlgebraicGeometry.Scheme.Modules.isExteriorAlgebra_exteriorAlgebra`, so no second notion of
exterior power appears. A sheaf of modules on a scheme is a sheaf of modules over the structure
sheaf of the underlying ringed space on the nose, which is the form Tag 01CI is stated in, so
nothing is transported. The degree-one instance of this isomorphism is already the first factor
of `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The exterior power of a sheaf of modules on a scheme commutes with pullback**:
`f^*(⋀ⁿ F) ≅ ⋀ⁿ(f^*F)`, the exterior-algebra case of [Stacks, Tag 01CI] in degree `n`. -/
noncomputable def exteriorPowerPullbackIso {X' X : Scheme.{u}} (f : X' ⟶ X) (F : X.Modules)
    (n : ℤ) :
    (Scheme.Modules.pullback f).obj (exteriorPower F n) ≅
      exteriorPower ((Scheme.Modules.pullback f).obj F) n :=
  (Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso f.toLRSHom.toShHom
      (exteriorAlgebra F) (exteriorGenerator F)
      (exteriorAlgebra ((Scheme.Modules.pullback f).obj F))
      (exteriorGenerator ((Scheme.Modules.pullback f).obj F))
      (isExteriorAlgebra_exteriorAlgebra F)
      (isExteriorAlgebra_exteriorAlgebra _)).app n

end AlgebraicGeometry.Scheme.Modules

end
