module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CohomologyAsExtOutOfTheStructureSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso

/-!
# Cohomology on a ringed space is derived Hom out of the structure sheaf

Let `(X, O_X)` be a ringed space and let `M` be an object of the unbounded derived category
`D(O_X)` of `O_X`-modules. Its cohomology is the Hom out of the structure sheaf in the derived
category:

`H^n(X, M) = Hom_{D(O_X)}(O_X[0], M[n]) = Ext^n_{D(O_X)}(O_X[0], M)`,

where `H^n(X, M)` is the degree-`n` cohomology of the derived global sections `RΓ(X, M)` and
`O_X[0]` is the structure sheaf placed in degree zero. The identification is additive and natural
in `M`.

## Main results

* `Stacks.SheafOfModules.derivedGlobalSectionsExtEquiv`: the identification
  `H^n(X, M) ≃+ Hom_{D(O_X)}(O_X[0], M[n])`.
* `Stacks.SheafOfModules.derivedGlobalSectionsExtEquiv_naturality`: it is natural in `M`.

## Implementation notes

A topological space together with a sheaf of commutative rings on it is a ringed site, namely the
site of its opens with the open-cover topology, and under that reading its derived global
sections and the structure sheaf in degree zero are those of the site. So both statements are the
ones for a ringed site, read off along `Stacks.SheafOfModules.ringedSite` exactly as
`Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv` is; the content is
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsExtEquiv` and
`AlgebraicGeometry.RingedSite.derivedGlobalSectionsExtEquiv_naturality`.

The structure sheaf in degree zero is spelled with `DerivedCategory.singleFunctor`, which is the
spelling the consumers of `Ext` out of the structure sheaf use; it is the same object as
`AlgebraicGeometry.RingedSite.derivedStructureSheaf` of the associated ringed site by
`AlgebraicGeometry.RingedSite.derivedStructureSheaf_eq_singleFunctor_obj`.

*The degree-zero case* is `Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv` read at
`L = O_X[0]`; the content added here is that the degree may be arbitrary.

*No attribute is placed in this file*, for the reason recorded in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CohomologyAsExtOutOfTheStructureSheaf`:
the statement is the composition of Tag 0B6E with Tag 08JD at `K = O`, which neither tag asserts
on its own.

## References

* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The structure sheaf of a ringed space, placed in degree zero as an object of the derived
category of `O_X`-modules. -/
abbrev derivedStructureSheaf : DerivedCategory (StructureSheafModules Rc) :=
  (DerivedCategory.singleFunctor (StructureSheafModules Rc) 0).obj
    (SheafOfModules.unit (Tensor.ringSheaf Rc))

/-- **Cohomology on a ringed space is derived Hom out of the structure sheaf.** For an object `M`
of the unbounded derived category of `O_X`-modules on a ringed space `(X, O_X)` and every integer
`n`, the degree-`n` cohomology of the derived global sections `RΓ(X, M)` is the group of
morphisms `O_X[0] ⟶ M[n]` in `D(O_X)`, that is the `Ext`-group `Ext^n_{D(O_X)}(O_X[0], M)`:

`H^n(X, M) = Hom_{D(O_X)}(O_X[0], M[n])`.

The identification is additive, and it is natural in `M` by
`Stacks.SheafOfModules.derivedGlobalSectionsExtEquiv_naturality`. There is no hypothesis on `M`:
it is an arbitrary object of the unbounded derived category.

The target is the `Ext`-group on the nose: `DerivedCategory.Ext X Y i` is by definition
`X ⟶ Y⟦i⟧`, so the right-hand side is `DerivedCategory.Ext (O_X[0]) M n`.

This is `AlgebraicGeometry.RingedSite.derivedGlobalSectionsExtEquiv` read along
`Stacks.SheafOfModules.ringedSite`. -/
def derivedGlobalSectionsExtEquiv (M : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections (ringedSite Rc)).obj M) : Type u) ≃+
      (derivedStructureSheaf Rc ⟶ M⟦n⟧) :=
  RingedSite.derivedGlobalSectionsExtEquiv (ringedSite Rc) M n

/-- **The identification of cohomology with derived Hom out of the structure sheaf is natural in
`M`.** For a morphism `ψ : M ⟶ M'` of `D(O_X)` the map induced on degree-`n` cohomology of derived
global sections is carried by `Stacks.SheafOfModules.derivedGlobalSectionsExtEquiv` to
postcomposition with `ψ[n]`, so that `H^n(X, -) = Hom_{D(O_X)}(O_X[0], (-)[n])` is an
identification of functors `D(O_X) ⥤ Ab` and not merely of groups. -/
theorem derivedGlobalSectionsExtEquiv_naturality
    {M M' : DerivedCategory (StructureSheafModules Rc)} (ψ : M ⟶ M') (n : ℤ)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj M) : Type u)) :
    derivedGlobalSectionsExtEquiv Rc M' n
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map ψ) ξ) =
      derivedGlobalSectionsExtEquiv Rc M n ξ ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (StructureSheafModules Rc)) n).map ψ :=
  RingedSite.derivedGlobalSectionsExtEquiv_naturality (ringedSite Rc) ψ n ξ

end Stacks.SheafOfModules

end
