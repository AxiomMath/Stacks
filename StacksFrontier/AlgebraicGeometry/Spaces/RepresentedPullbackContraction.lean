module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentPullbackIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePullbackHomotopyFactorQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChangeComp
public import StacksFrontier.CategoryTheory.Functor.Derived.ComparisonSquareChase

/-!
# The contraction of the pullbacks along a composite of represented morphisms

Let `U'' --h--> U' --g--> U` be morphisms of the big fppf site over `S`.  The pullbacks of modules
along the induced morphisms of algebraic spaces contract: `g^* ⋙ h^* ≅ (h ≫ g)^*`, on modules, on
unbounded homotopy categories of complexes, and on derived categories.  The contraction on modules
is `AlgebraicGeometry.Space.representedSpacePullbackCompIso`; this file builds the other two and
proves the fact a chase of base change squares consumes: that the derived one is compatible with
the comparison `Lf^* ⟶ f^*` of Stacks 06YY.

No affineness is needed here; the contraction exists for every composite of morphisms of the site.

## Main definitions

* `AlgebraicGeometry.Space.representedSpaceHomotopyPullbackCompIso` and
  `AlgebraicGeometry.Space.representedSpaceDerivedPullbackCompIso`: the contraction
  `g^* ⋙ h^* ≅ (h ≫ g)^*` on homotopy categories and on derived categories.

## Main results

* `AlgebraicGeometry.Space.representedSpaceDerivedPullbackCompIso_inv_app_comparison`: the
  contraction of the derived pullbacks is compatible with the comparison `Lf^* ⟶ f^*` of
  Stacks 06YY.

## Implementation notes

The composition law of the derived pullbacks,
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp`, is stated with the
contraction read forwards and the degreewise contraction on the other side of the equation; a
chase consumes it with both inverted.  The transposition is
`StacksDraft.ComparisonSquare.inv_comp_eq_of_comp_eq`, on variables, together with
`StacksDraft.ComparisonSquare.map_hom_inv_id_app`; performed on the concrete goal the `isDefEq`
checks a `simp` would run exhaust the heartbeat budget.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Inverse image of modules along a represented morphism is additive, at the spelling used
below. -/
local instance additive_pullbackModules_representedSpaceMap_of_hom {V V' : BigFppfOver B S hS}
    (k : V' ⟶ V) :
    ((smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS k)).toModulesHom.pullbackModules).Additive :=
  pullbackModules_smallEtale_additive _

variable {U'' U' U : BigFppfOver B S hS} (h : U'' ⟶ U') (g : U' ⟶ U)

/-- **The contraction `g^* ⋙ h^* ≅ (h ≫ g)^*`** of degreewise pullbacks of complexes of modules
along represented morphisms, on the unbounded homotopy categories. -/
def representedSpaceHomotopyPullbackCompIso :
    smallEtalePullbackMapHomotopy B S hS (representedSpaceMap B S hS g) ⋙
        smallEtalePullbackMapHomotopy B S hS (representedSpaceMap B S hS h) ≅
      smallEtalePullbackMapHomotopy B S hS (representedSpaceMap B S hS (h ≫ g)) :=
  smallEtalePullbackMapHomotopyFactorIso (representedSpaceMap B S hS h)
    (representedSpaceMap B S hS g) (representedSpaceMap B S hS (h ≫ g))
    (representedSpaceMap_comp B S hS h g)

/-- **The contraction `Lg^* ⋙ Lh^* ≅ L(h ≫ g)^*`** of the derived pullbacks of modules along
represented morphisms of algebraic spaces: the composition isomorphism of Stacks 0D6D, read
through the factorisation `AlgebraicGeometry.Space.representedSpaceMap_comp`. -/
def representedSpaceDerivedPullbackCompIso :
    smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS h) ≅
      smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (h ≫ g)) :=
  smallEtaleDerivedPullbackFactorIso B S hS (representedSpaceMap B S hS h)
    (representedSpaceMap B S hS g) (representedSpaceMap B S hS (h ≫ g))
    (representedSpaceMap_comp B S hS h g)

/-- **The contraction of the derived pullbacks is compatible with the comparison `Lf^* ⟶ f^*` of
Stacks 06YY**, in the shape a chase consumes: read on the inverse of the contraction, the
comparisons of `g` and of `h` are the comparison of `h ≫ g` followed by the inverse of the
degreewise contraction.

This is `AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp` transposed along
the inverses of two of the sides of the square. -/
theorem representedSpaceDerivedPullbackCompIso_inv_app_comparison
    (N : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)) (ComplexShape.up ℤ)) :
    (representedSpaceDerivedPullbackCompIso B S hS h g).inv.app (DerivedCategory.Qh.obj N) ≫
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS h)).map
          ((smallEtaleDerivedModulePullbackComparison B S hS
            (representedSpaceMap B S hS g)).app N) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS
            (representedSpaceMap B S hS h)).app
          ((smallEtalePullbackMapHomotopy B S hS (representedSpaceMap B S hS g)).obj N) =
      (smallEtaleDerivedModulePullbackComparison B S hS
          (representedSpaceMap B S hS (h ≫ g))).app N ≫
        DerivedCategory.Qh.map
          ((representedSpaceHomotopyPullbackCompIso B S hS h g).inv.app N) :=
  StacksDraft.ComparisonSquare.inv_comp_eq_of_comp_eq
    ((representedSpaceDerivedPullbackCompIso B S hS h g).inv_hom_id_app
      (DerivedCategory.Qh.obj N))
    (StacksDraft.ComparisonSquare.map_hom_inv_id_app
      (representedSpaceHomotopyPullbackCompIso B S hS h g) DerivedCategory.Qh N)
    ((smallEtaleDerivedPullbackFactorIso_hom_app_comp (representedSpaceMap B S hS h)
      (representedSpaceMap B S hS g) (representedSpaceMap B S hS (h ≫ g))
      (representedSpaceMap_comp B S hS h g) N).trans (Category.assoc _ _ _).symm)

end AlgebraicGeometry.Space

end
