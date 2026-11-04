module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraRestrictOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictOpenSpellings

/-!
# Exterior algebras restricted along an open immersion of schemes

The restriction of an exterior algebra of a sheaf of `𝒪_X`-modules `M` along the open immersion
`U.ι`, via `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, is an exterior algebra of the
restriction of `M`, and so is degreewise isomorphic to any exterior algebra of `M|_U`, compatibly
with the generator, the multiplication and the unit.

## Main definitions

* `Stacks.SheafOfModules.RestrictOpen.restrictFunctorGen`: the degree-one generator of the
  restriction of `A` along `U.ι`.
* `Stacks.SheafOfModules.RestrictOpen.restrictFunctorPieceIso`: the degreewise isomorphism between
  the restriction of `A` to the open subspace and an exterior algebra `B` of `M|_U`.
* `Stacks.SheafOfModules.RestrictOpen.exteriorRestrictFunctorIso`: the degreewise isomorphism
  `(⋀ⁿM)|_U ≅ ⋀ⁿ(M|_U)`.

## Main results

* `Stacks.SheafOfModules.RestrictOpen.isExteriorAlgebra_restrictFunctor`: the restriction of an
  exterior algebra of `M` along the open immersion `U.ι` is an exterior algebra of the
  restriction of `M`.
* `Stacks.SheafOfModules.RestrictOpen.restrictFunctorPieceIso_generator`,
  `Stacks.SheafOfModules.RestrictOpen.restrictFunctorPieceIso_mul`,
  `Stacks.SheafOfModules.RestrictOpen.restrictFunctorPieceIso_one`: `restrictFunctorPieceIso`
  respects the generator, the multiplication and the unit.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open SheafOfModules SheafOfModules.GradedAlgebra

universe u

namespace Stacks.SheafOfModules.RestrictOpen

variable {X : Scheme.{u}} (U : X.Opens)
  (M : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  (A : _root_.SheafOfModules.GradedAlgebra.{u, u} (structureSheafRing X.toRingedSpace))
  (gen : M ⟶ A.piece 1)
  (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen)

/-- The degree-one generator of `A` restricted along the open immersion `U.ι`: the inverse of
`Stacks.SheafOfModules.RestrictOpen.overFunctorIsoRestrictFunctor` at `M` followed by
`SheafOfModules.openSubspaceGen`. -/
abbrev restrictFunctorGen :=
  ((overFunctorIsoRestrictFunctor X U).app M).inv ≫
    _root_.SheafOfModules.openSubspaceGen M A gen U

include hA in
/-- **The restriction of an exterior algebra of `M` along an open immersion of schemes is an
exterior algebra of the restriction of `M`**, the restriction being
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`. -/
theorem isExteriorAlgebra_restrictFunctor :
    _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra
      (_root_.SheafOfModules.openSubspaceAlg A U) (restrictFunctorGen U M A gen) :=
  _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso
    (_root_.SheafOfModules.isExteriorAlgebra_openSubspaceAlg M A gen hA U)
    (((overFunctorIsoRestrictFunctor X U).app M).inv)
    ((overFunctorIsoRestrictFunctor X U).app M).isIso_inv

variable (B : _root_.SheafOfModules.GradedAlgebra.{u, u} U.toScheme.ringCatSheaf)
  (gen' : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶ B.piece 1)
  (hB : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra B gen')

include hA hB

/-- The degreewise isomorphism between the restriction of `A` to the open subspace and `B`, given
by the universal property of the two exterior algebras of the restriction of `M`. -/
abbrev restrictFunctorPieceIso (n : ℤ) :=
  _root_.SheafOfModules.GradedAlgebra.IsUniversal.pieceIso
    (isExteriorAlgebra_restrictFunctor U M A gen hA).isUniversal hB.isUniversal n

/-- **`(⋀ⁿM)|_U ≅ ⋀ⁿ(M|_U)` along the open immersion `U.ι`**, for an arbitrary exterior algebra
`A` of `M` on `X` and an arbitrary exterior algebra `B` of `M|_U` on the open subscheme: the
inverse of `Stacks.SheafOfModules.RestrictOpen.overFunctorIsoRestrictFunctor` at `A.piece n`
followed by `Stacks.SheafOfModules.RestrictOpen.restrictFunctorPieceIso`. -/
def exteriorRestrictFunctorIso (n : ℤ) :
    (Scheme.Modules.restrictFunctor U.ι).obj (A.piece n) ≅ B.piece n :=
  ((overFunctorIsoRestrictFunctor X U).app (A.piece n)).symm ≪≫
    restrictFunctorPieceIso U M A gen hA B gen' hB n

/-- `restrictFunctorPieceIso` carries the restricted generator to the generator of `B`. -/
theorem restrictFunctorPieceIso_generator :
    restrictFunctorGen U M A gen ≫
        (restrictFunctorPieceIso U M A gen hA B gen' hB 1).hom =
      gen' :=
  _root_.SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_generator _ _

/-- `restrictFunctorPieceIso` is multiplicative on homogeneous local sections. -/
theorem restrictFunctorPieceIso_mul (i j : ℤ) (V : (Opens ↥U)ᵒᵖ)
    (x : ((_root_.SheafOfModules.openSubspaceAlg A U).piece i).val.obj V)
    (y : ((_root_.SheafOfModules.openSubspaceAlg A U).piece j).val.obj V) :
    (restrictFunctorPieceIso U M A gen hA B gen' hB (i + j)).hom.val.app V
        (((_root_.SheafOfModules.openSubspaceAlg A U).mul i j).app V x y) =
      (B.mul i j).app V
        ((restrictFunctorPieceIso U M A gen hA B gen' hB i).hom.val.app V x)
        ((restrictFunctorPieceIso U M A gen hA B gen' hB j).hom.val.app V y) :=
  _root_.SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_mul _ _ i j V x y

/-- `restrictFunctorPieceIso` carries the unit to the unit. -/
theorem restrictFunctorPieceIso_one (V : (Opens ↥U)ᵒᵖ) :
    (restrictFunctorPieceIso U M A gen hA B gen' hB 0).hom.val.app V
        ((_root_.SheafOfModules.openSubspaceAlg A U).one.eval V) =
      B.one.eval V :=
  _root_.SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_one _ _ V

end Stacks.SheafOfModules.RestrictOpen

end
