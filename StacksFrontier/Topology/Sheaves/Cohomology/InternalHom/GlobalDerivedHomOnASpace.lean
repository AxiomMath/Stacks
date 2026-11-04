module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHom
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The global derived hom on a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `L` be objects of the derived category `D(O_X)`.
Taking derived global sections of the derived internal Hom gives the *global derived hom*

`RHom_X(K, L) = RΓ(X, RSheafHom(K, L))`,

an object of the derived category `D(Γ(X, O_X))` of modules over the ring of global sections of the
structure sheaf, whose degree-zero cohomology is the group of morphisms `K ⟶ L` in `D(O_X)`.

## Main definitions

* `Stacks.SheafOfModules.globalDerivedHom`: the bifunctor `RHom_X(-, -)` valued in `D(Γ(X, O_X))`.

## Main results

* `Stacks.SheafOfModules.globalDerivedHomDegreeZeroEquiv`: the degree-zero cohomology of
  `RHom_X(K, L)` is `Hom_{D(O_X)}(K, L)`.

## References

* [Stacks Project, Tag 0B6A](https://stacks.math.columbia.edu/tag/0B6A)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.SiteModules

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- The global derived hom `RHom_X(K, L) = RΓ(X, RSheafHom(K, L))` of a ringed space: the derived
internal Hom of two objects of `D(O_X)`, followed by derived global sections valued in modules over
the ring `Γ(X, O_X)` of global sections of the structure sheaf. -/
@[stacks 0B6A "the global derived hom RHom_X(K, L) = RΓ(X, RSheafHom(K, L)) in D(Γ(X, O_X)) \
of a ringed space"]
def globalDerivedHom :
    (DerivedCategory (StructureSheafModules Rc))ᵒᵖ ⥤
      DerivedCategory (StructureSheafModules Rc) ⥤
        DerivedCategory (ModuleCat.{u} (GlobalSectionRing (structureSheaf Rc))) :=
  RingedSite.globalDerivedHomModules (ringedSite Rc)

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The degree-zero cohomology of `RHom_X(K, L)`, read on its underlying complex of abelian groups,
is the group of morphisms `K ⟶ L` in the derived category of `O_X`-modules. -/
@[stacks 0B6A "the degree-zero cohomology of RHom_X(K, L) is Hom_{D(O_X)}(K, L)"]
def globalDerivedHomDegreeZeroEquiv (K L : DerivedCategory (StructureSheafModules Rc)) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((RingedSite.underlyingDerivedGroup (ringedSite Rc)).obj
          (((globalDerivedHom Rc).obj (op K)).obj L)) : Type u) ≃+ (K ⟶ L) :=
  RingedSite.globalDerivedHomModulesDegreeZeroEquiv (ringedSite Rc) K L

end Stacks.SheafOfModules

end
