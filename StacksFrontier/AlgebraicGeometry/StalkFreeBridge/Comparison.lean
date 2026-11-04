module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank

/-!
# From slice-site local generators to trivializations on an open subspace

Local freeness of a sheaf of modules on a scheme has two formulations.

* Mathlib's `SheafOfModules.LocalGeneratorsData` lives on the **slice site**: for a covering
  family `q.X : q.I → X.Opens` of the terminal object it carries, for each `i`, generating
  sections of `M.over (q.X i)`, a sheaf of modules over `X.ringCatSheaf.over (q.X i)` on the
  category `Over (q.X i)`. Local freeness, `LocalGeneratorsData.IsLocallyFreeData`, says each
  structure map `(q.generators i).π : free (q.generators i).I ⟶ M.over (q.X i)` is an
  isomorphism.
* `LocallyFreeRank.Trivialization`, from Stacks Tag 01C9, lives on the **open subspace**: it is
  an isomorphism `M|_U ≅ free ι` of sheaves of modules over `O_X|_U` on the category
  `Opens ↥U`, where the restrictions are the pushforwards along the open inclusion
  `Opens ↥U ⥤ Opens X`.

This file turns the first into the second, by composing the comparison functors
`AlgebraicGeometry.Scheme.Modules.overEquiv`, `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`
and `AlgebraicGeometry.Scheme.Modules.restrictFunctor` with
`SheafOfModules.GeneratingSections.map`, which transports generating sections along a
colimit-preserving functor matching the units. Tag 01C9's `restrictRing` is definitionally the
structure sheaf of the open subscheme, and its `inclF` is definitionally
`Scheme.Opens.ι.opensFunctor`.

## Main definitions

* `Stacks.StalkFreeBridge.restrictModIso`: Tag 01C9's restriction `restrictMod` of a sheaf of
  modules to an open set agrees with Mathlib's `Scheme.Modules.restrictFunctor` along the
  canonical open immersion.
* `Stacks.StalkFreeBridge.overEquivFunctor`: `Scheme.Modules.overEquiv`, written at the
  `SheafOfModules` spelling of its codomain.
* `Stacks.StalkFreeBridge.trivializationOfGeneratingSections`: generating sections of
  `M.over U` whose structure map is an isomorphism give a `LocallyFreeRank.Trivialization` of
  `M` on `U`, with the same index type.
* `Stacks.StalkFreeBridge.trivializationOfIsLocallyFreeData`: the same for the `i`-th member of
  locally free local generators data.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` carrying its
own `Category` instance, so an object or functor obtained at the `Scheme.Modules` spelling is one
unfolding away from the `SheafOfModules` spelling that `GeneratingSections.map` demands, and
instance search for `PreservesColimitsOfSize` does not cross that gap even with the instance in
the local context. `overEquivFunctor` states the comparison functor at the `SheafOfModules`
type, where the `PreservesColimitsOfSize` instance is found.

## References

* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe w u

namespace Stacks.StalkFreeBridge

variable {X : Scheme.{u}}

/-- Tag 01C9's restriction of a sheaf of modules to an open set is Mathlib's restriction along
the canonical open immersion of that open set. -/
def restrictModIso (U : X.Opens) (M : X.Modules) :
    LocallyFreeRank.restrictMod (X : TopCat.{u}) U X.ringCatSheaf M
      ≅ (Scheme.Modules.restrictFunctor U.ι).obj M :=
  (SheafOfModules.pushforwardCongr (by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl)).app M

/-- `AlgebraicGeometry.Scheme.Modules.overEquiv`, written with its codomain spelled as a
category of sheaves of modules rather than as `Scheme.Modules`. -/
def overEquivFunctor (U : X.Opens) :
    SheafOfModules.{u} (X.ringCatSheaf.over U) ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
  (Scheme.Modules.overEquiv U).functor

/-- The functor `overEquivFunctor U` preserves colimits. -/
instance preservesColimitsOfSize_overEquivFunctor (U : X.Opens) :
    PreservesColimitsOfSize.{u, u} (overEquivFunctor U) :=
  Adjunction.leftAdjoint_preservesColimits (Scheme.Modules.overEquiv U).toAdjunction

/-- The comparison of units for `overEquivFunctor`: the equivalence takes the structure sheaf of
the slice site to the structure sheaf of the open subscheme. -/
def overEquivUnitIso (U : X.Opens) :
    SheafOfModules.unit.{u} U.toScheme.ringCatSheaf ≅
      (overEquivFunctor U).obj (SheafOfModules.unit.{u} (X.ringCatSheaf.over U)) :=
  (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm

/-- A family of generating sections of `M.over U` whose structure map is an isomorphism is a
trivialization of `M` on `U` in the sense of Stacks Tag 01C9, on the same index type. -/
def trivializationOfGeneratingSections (U : X.Opens) (M : X.Modules)
    (G : (M.over U).GeneratingSections) [IsIso G.π] :
    LocallyFreeRank.Trivialization (X : TopCat.{u}) X.ringCatSheaf M U where
  ι := G.I
  iso := restrictModIso U M ≪≫ ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (asIso (G.map (overEquivFunctor U) (overEquivUnitIso U)).π).symm

/-- The index type of `trivializationOfGeneratingSections U M G` is that of `G`. -/
@[simp]
lemma trivializationOfGeneratingSections_ι (U : X.Opens) (M : X.Modules)
    (G : (M.over U).GeneratingSections) [IsIso G.π] :
    (trivializationOfGeneratingSections U M G).ι = G.I :=
  rfl

/-- The `i`-th member of locally free local generators data is a trivialization of `M` on
`q.X i` in the sense of Stacks Tag 01C9, on the index type `(q.generators i).I`. -/
def trivializationOfIsLocallyFreeData {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{w} M) [hq : q.IsLocallyFreeData] (i : q.I) :
    LocallyFreeRank.Trivialization (X : TopCat.{u}) X.ringCatSheaf M (q.X i) :=
  have := hq.isIso i
  trivializationOfGeneratingSections (q.X i) M (q.generators i)

/-- The index type of `trivializationOfIsLocallyFreeData q i` is `(q.generators i).I`. -/
@[simp]
lemma trivializationOfIsLocallyFreeData_ι {M : X.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{w} M) [q.IsLocallyFreeData] (i : q.I) :
    (trivializationOfIsLocallyFreeData q i).ι = (q.generators i).I :=
  rfl

end Stacks.StalkFreeBridge

end
