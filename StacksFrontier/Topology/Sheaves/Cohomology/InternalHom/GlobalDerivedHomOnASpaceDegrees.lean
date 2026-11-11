module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.GlobalDerivedHomOnASpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology of the global derived hom on a ringed space, in every degree

Let `(X, O_X)` be a ringed space and let `K`, `L` be objects of `D(O_X)`. The global derived hom
`RHom_X(K, L) = RΓ(X, RSheafHom(K, L))` of `Stacks.SheafOfModules.globalDerivedHom` is an object
of `D(Γ(X, O_X))`, and by Stacks 08DK its cohomology is

`H^0(RHom_X(K, L)) = Hom_{D(O_X)}(K, L)`, `H^p(RHom_X(K, L)) = Ext^p_{D(O_X)}(K, L)`,

where `Ext^p_{D(O_X)}(K, L) = Hom_{D(O_X)}(K, L[p])`. This file states both identifications for
an arbitrary ringed space, with no hypothesis beyond the space and its structure sheaf.

## Main results

* `Stacks.SheafOfModules.globalDerivedHomHomologyZeroEquiv`: `H^0(RHom_X(K, L)) = Hom(K, L)`.
* `Stacks.SheafOfModules.globalDerivedHomHomologyEquiv`: `H^p(RHom_X(K, L)) = Hom(K, L[p])` for
  every integer `p`.

## Implementation notes

The statements of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.GlobalDerivedHomOnASpace` carry, as instance
arguments, the existence of sheafification and the comparison of local bijectivity for abelian
sheaves on `Opens X`, the additivity of `- ⊗_{O_X} -` in each variable, and the existence of the
total tensor complexes. None of these is an assumption on the ringed space: the site `Opens X`
is essentially small, which gives the first two, and the last three are the instances
`Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive`,
`Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive` and
`Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor`, which instance search
cannot reach unaided because of a universe equation `max ?v u =?= u`, and which are therefore
opened as scoped instances here. So the statements below are unconditional.

The degree-`p` identification is the ringed-site statement
`AlgebraicGeometry.RingedSite.globalDerivedHomModulesDegreeEquiv` (Stacks 0B6E, proved by moving
the degree into the covariant variable of `RSheafHom`) at the ringed site of `(X, O_X)`; the
cohomology is read on the underlying complex of abelian groups, as Stacks 08DK states it.

## References

* [Stacks Project, Tag 0B6A](https://stacks.math.columbia.edu/tag/0B6A)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.SiteModules
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **The degree-zero cohomology of the global derived hom of a ringed space**, with no
hypothesis: `H^0(RHom_X(K, L))`, read on its underlying complex of abelian groups, is the group
of morphisms `K ⟶ L` in `D(O_X)`. -/
@[stacks 0B6A "H^0(RHom_X(K, L)) = Hom_{D(O_X)}(K, L), for an arbitrary ringed space"]
def globalDerivedHomHomologyZeroEquiv (K L : DerivedCategory (StructureSheafModules Rc)) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((RingedSite.underlyingDerivedGroup (ringedSite Rc)).obj
          (((globalDerivedHom Rc).obj (op K)).obj L)) : Type u) ≃+ (K ⟶ L) :=
  globalDerivedHomDegreeZeroEquiv Rc K L

/-- **The cohomology of the global derived hom of a ringed space in every degree**, with no
hypothesis: for every integer `p`, `H^p(RHom_X(K, L))`, read on its underlying complex of abelian
groups, is the group `Ext^p_{D(O_X)}(K, L) = Hom_{D(O_X)}(K, L[p])`. -/
@[stacks 0B6A "H^p(RHom_X(K, L)) = Ext^p_{D(O_X)}(K, L) = Hom_{D(O_X)}(K, L[p]) for every \
p ∈ ℤ, for an arbitrary ringed space"]
def globalDerivedHomHomologyEquiv (K L : DerivedCategory (StructureSheafModules Rc)) (p : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
        ((RingedSite.underlyingDerivedGroup (ringedSite Rc)).obj
          (((globalDerivedHom Rc).obj (op K)).obj L)) : Type u) ≃+ (K ⟶ L⟦p⟧) :=
  RingedSite.globalDerivedHomModulesDegreeEquiv (ringedSite Rc) K L p

end Stacks.SheafOfModules

end
