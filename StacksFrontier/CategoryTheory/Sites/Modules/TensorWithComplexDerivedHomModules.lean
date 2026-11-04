module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleMap
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexBaseRing
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHom

/-!
# The canonical map of Stacks 0CS6 over the universal base ring

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra, taken over the
ring `Γ(C, O)` of global sections of the structure sheaf. Stacks 0CS6 asserts a canonical map

`RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)`

in `D(R)`, for `R` a ring and `O` a sheaf of commutative `R`-algebras. Every such `R` maps to
`Γ(C, O)` by `AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections`, so `Γ(C, O)` is the
universal base ring and a map in `D(Γ(C, O))` gives the map in `D(R)` by restricting scalars
along it. This file builds that map in `D(Γ(C, O))`.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexModulesMap`: the map of
  `Γ(C, O)`-module-valued differential graded Hom complexes induced by the differential graded
  tensor functor of Tag 09LV.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModules`: the canonical map of
  Stacks 0CS6 in `D(Γ(C, O))`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexModulesMap_forget`: forgetting the
  scalars of the first leg returns the map of Hom complexes of abelian groups out of which the
  first leg of the `D(ℤ)`-valued canonical map,
  `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap`, is built.

## Implementation notes

*Why the two legs compose without a comparison.* The source of the canonical map over
`Γ(C, O)` is the `Γ(C, O)`-module-valued Hom complex of the differential graded category
`Comp^dg(O)` read over `Γ(C, O)`, which is
`Stacks.Cohomology.SiteModules.compDGGlobalSections`; the target of the map a differential
graded functor induces on module-valued Hom complexes
(`DGCategory.DGFunctor.homComplexModulesMap`) is the Hom complex of
`AlgebraicGeometry.RingedSite.CompDG X Γ(C, O)`. At the diagonal universes of the site those two
differential graded categories are the same: both are
`CochainComplex.dgCategoryLinear (SheafOfModules O) Γ(C, O)`, the instance on the second coming
from `AlgebraicGeometry.RingedSite.scalarSectionsGlobalSectionRing`. So the first leg lands
exactly on the source of `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules`, the
canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` over `Γ(C, O)`, and the composite needs no
intermediate identification.

*What this map is, and what superseded it.* It is the canonical map of Stacks 0CS6 over the
universal base ring `Γ(C, O)`. Three things separated it from the registrations of the tag, and
all three are now in place, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleRestrict` and
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver`:

* the base ring here is `Γ(C, O)` and not the source's arbitrary `R`. Restricting along
  `AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections` needed the identification of
  `AlgebraicGeometry.RingedSite.CompDG X R`'s module-valued Hom complex with the restriction of
  `Γ(C, O)`'s; that is `AlgebraicGeometry.RingedSite.homComplexModulesRestrictIso`, and its
  content is `AlgebraicGeometry.RingedSite.ScalarSections.smul_eq_globalSections_smul` read on
  cochains;
* the target is the global derived hom of the *ordinary* tensor products and not of the derived
  ones. The transport along
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso` applied to
  `AlgebraicGeometry.RingedSite.globalDerivedHomModules` is
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver`;
* and the identification of the map over the source's `R` with the `D(ℤ)`-valued one is
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver_forget`. Its first leg
  is `AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexModulesMap_forget` below, carried
  through `CategoryTheory.Functor.mapDerivedCategoryFactors`, and its second is
  `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModulesOver_forget`.

The map below is accordingly the `R = Γ(C, O)` case of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapModulesOver`, and it is the latter
that carries the registration of Stacks 0CS6.

*The universe parameters* are the diagonal ones of the site, as everywhere around the global
derived hom.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule AlgebraicGeometry Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (K : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-- The ring of global sections of the structure sheaf, read as a base ring for Tags 09LV–09LX.
It is the universal one: every base ring of Stacks 0CS6 maps to it by
`AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections`. -/
abbrev scalarGlobalSections := ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The category of sheaves of `O`-modules on `X` is linear over the ring `Γ(C, O)` of global
sections, by `Stacks.Cohomology.SiteModules.linearSheafOfModules` at the universes of the site. -/
local instance : Linear (scalarGlobalSections.{u} X) (TensorModO.{u, u, u, u, u} X) :=
  Stacks.Cohomology.SiteModules.linearSheafOfModules.{u, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- **The map of `Γ(C, O)`-module-valued differential graded Hom complexes induced by tensoring
with `K`.** This is `DGCategory.DGFunctor.homComplexModulesMap` at the
differential graded functor of Tag 09LV taken over `Γ(C, O)`; forgetting the scalars returns
`AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap`. -/
def tensorWithComplexHomComplexModulesMap
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X) K).algebra).Obj) :
    (DifferentialGradedModule.dgCategory.{_, _, u}
        (Rep.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X) K).algebra).homComplexModules
          M N ⟶
      (compDGGlobalSections.{u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModules
        ((tensorWithComplexDG.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X) K).functor.obj M)
        ((tensorWithComplexDG.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X)
          K).functor.obj N) :=
  DGCategory.DGFunctor.homComplexModulesMap
    (tensorWithComplexDG.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X) K).functor M N

/-- **The first leg of the canonical map forgets.** Forgetting the `Γ(C, O)`-module structure of
the map of module-valued Hom complexes returns the map of Hom complexes of abelian groups
induced by the same differential graded functor. Composing with
`CochainComplex.dgCategoryHomComplexIso`, which reads the Hom complex of the differential graded
category of complexes as Mathlib's Hom complex, that map is
`AlgebraicGeometry.RingedSite.tensorWithComplexHomComplexMap`, the first leg of the
`D(ℤ)`-valued canonical map; the composition is left to the caller, because the two spellings of
the Hom complex of `Comp^dg(O)` over `Γ(C, O)` and over `ℤ` are equal only definitionally, and a
statement composing them is not type-correct at `implicit` transparency — see the implementation
notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleMap`. -/
theorem tensorWithComplexHomComplexModulesMap_forget
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X) K).algebra).Obj) :
    ((forget₂ (ModuleCat.{u} (scalarGlobalSections.{u} X))
            AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (tensorWithComplexHomComplexModulesMap.{u} X K M N) ≫
        ((compDGGlobalSections.{u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).homComplexModulesForget _ _).hom =
      ((DifferentialGradedModule.dgCategory.{_, _, u}
            (Rep.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X)
              K).algebra).homComplexModulesForget M N).hom ≫
        (tensorWithComplexDG.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X)
          K).functor.homComplexMap M N :=
  DGCategory.DGFunctor.homComplexModulesMap_forget _ M N

/-- **Stacks 0CS6, the canonical map over the universal base ring.** The differential graded
functor of Tag 09LV acts on the `Γ(C, O)`-module-valued differential graded Hom complexes, and
the Hom complex of two complexes of `O`-modules over `Γ(C, O)` maps canonically to their global
derived hom of Tag 0B6E over `Γ(C, O)`
(`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHomModules`); the composite is the map
below, a morphism of `D(Γ(C, O))`.

Since every base ring of Stacks 0CS6 maps to `Γ(C, O)`, restricting scalars along that map gives
the source's map in `D(R)` for each of them. Its source is the differential graded Hom complex of
two differential graded modules rather than `RHom(M, N)` for two objects of `D(E, d)`, and its
target is the global derived hom of the ordinary tensor products rather than of the derived ones;
both of those are supplied for the map over the source's base ring in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHomModulesOver`, which is
where the registration of Stacks 0CS6 sits. Accordingly this declaration carries none. -/
def tensorWithComplexDerivedHomMapModules
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X) K).algebra).Obj) :
    DerivedCategory.Q.obj
        ((DifferentialGradedModule.dgCategory.{_, _, u}
          (Rep.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X) K).algebra).homComplexModules
            M N) ⟶
      ((globalDerivedHomModules X).obj (op (DerivedCategory.Q.obj
            ((tensorWithComplexDG.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X)
              K).functor.obj M)))).obj
        (DerivedCategory.Q.obj
          ((tensorWithComplexDG.{u, u, u, u, u, u} X (scalarGlobalSections.{u} X)
            K).functor.obj N)) :=
  DerivedCategory.Q.map (tensorWithComplexHomComplexModulesMap.{u} X K M N) ≫
    homComplexToGlobalDerivedHomModules _ _

end AlgebraicGeometry.RingedSite

end
