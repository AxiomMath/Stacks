module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Topology.Sheaves.Sheaf.Module
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of complexes of sheaves of modules

Let `𝒪` be a sheaf of rings on a topological space `X`. The category of sheaves of
`𝒪`-modules is abelian, and a short complex of such sheaves is exact precisely when the
induced short complex of stalks is exact at every point of `X`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor`: the functor sending a sheaf of
  `𝒪`-modules to the stalk at a point of its underlying presheaf of abelian groups.
* `AlgebraicGeometry.SheafOfModules.stalkShortComplex`: the short complex of stalks at a point
  induced by a short complex of sheaves of `𝒪`-modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`: a short complex of
  sheaves of `𝒪`-modules is exact if and only if all of its stalk complexes are exact.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

add_to_stacks 01AG "the category of sheaves of modules is abelian"
  SheafOfModules.instAbelian

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The functor taking a sheaf of `𝒪`-modules to the stalk of its underlying
presheaf of abelian groups at `x`. -/
noncomputable def stalkAddCommGroupFunctor (x : X) :
    _root_.SheafOfModules.{u} 𝒪 ⥤ AddCommGrpCat.{u} :=
  _root_.SheafOfModules.forget 𝒪 ⋙
    PresheafOfModules.toPresheaf 𝒪.obj ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

/-- The stalk functor on sheaves of modules preserves zero morphisms. -/
instance stalkAddCommGroupFunctor_preservesZeroMorphisms (x : X) :
    (stalkAddCommGroupFunctor 𝒪 x).PreservesZeroMorphisms where
  map_zero Y Z := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf 𝒪.obj).map
        ((_root_.SheafOfModules.forget 𝒪).map (0 : Y ⟶ Z))) = 0
    simp only [Functor.map_zero]

/-- The short complex on stalks induced by a short complex of sheaves of
modules. -/
noncomputable def stalkShortComplex
    (S : ShortComplex (_root_.SheafOfModules.{u} 𝒪)) (x : X) :
    ShortComplex AddCommGrpCat.{u} :=
  S.map (stalkAddCommGroupFunctor 𝒪 x)

/-- A complex of sheaves of modules is exact at its middle term if and only
if the corresponding complex of stalks is exact at every point. -/
@[stacks 01AG "exactness on stalks"]
theorem exact_iff_stalkShortComplex_exact
    (S : ShortComplex (_root_.SheafOfModules.{u} 𝒪)) :
    S.Exact ↔ ∀ x : X, (stalkShortComplex 𝒪 S x).Exact := by
  let F : _root_.SheafOfModules.{u} 𝒪 ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := _root_.SheafOfModules.toSheaf 𝒪
  exact (S.exact_map_iff_of_faithful F).symm.trans
    (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
      (@ShortComplex.map _ _ _ _ _ _ S F (inferInstance : F.PreservesZeroMorphisms)))

end AlgebraicGeometry.SheafOfModules
