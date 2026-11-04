module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.KFlatIntoKInjectiveIsKInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The internal Hom complex from a K-flat complex into a K-injective complex, on a space

Let `(X, O_X)` be a ringed space, let `L` be a K-flat complex of `O_X`-modules and let `I` be a
K-injective complex of `O_X`-modules. Then the internal Hom complex `SheafHom^•(L, I)` is again
K-injective.

## Main results

* `Stacks.SheafOfModules.isKInjective_sheafHomComplex_of_isKFlat`: K-injectivity of the internal
  Hom complex out of a K-flat complex.

## References

* [Stacks Project, Tag 0A8T](https://stacks.math.columbia.edu/tag/0A8T)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.SheafOfModules

universe u

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The internal Hom complex `SheafHom^•(L, I)` from a K-flat complex `L` of `O_X`-modules into a
K-injective complex `I` of `O_X`-modules is K-injective. -/
@[stacks 0A8T]
theorem isKInjective_sheafHomComplex_of_isKFlat
    (L I : CochainComplex (StructureSheafModules Rc) ℤ)
    (hL : IsKFlat Rc L) [I.IsKInjective] :
    (sheafHomComplex Rc L I).obj.IsKInjective :=
  @AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_of_isKFlat (ringedSite Rc)
    inferInstance inferInstance inferInstance inferInstance inferInstance L I hL ‹I.IsKInjective›

end Stacks.SheafOfModules

end
