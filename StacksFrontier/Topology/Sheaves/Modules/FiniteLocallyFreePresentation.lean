module

public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# A finite locally free sheaf of modules is of finite type and of finite presentation

A sheaf of modules with a local free basis of `r` elements over each member of a covering of the
final object is of finite type and of finite presentation. Both statements hold over an arbitrary
site: a `SheafOfModules.LocalGeneratorsData` which is both `IsLocallyFreeData` and `IsFiniteType`
has an associated quasi-coherent datum whose relations are indexed by the empty type.

## Main results

* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.toFiniteLocallyFree`: finite local
  freeness in the sense of this library implies it in the sense of
  `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`.
* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteType` and
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFinitePresentation`: a sheaf of
  modules which is finite locally free of rank `r` is of finite type and of finite presentation.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u₁

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Finite local freeness of a sheaf of modules on a site in the sense of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` implies it in the sense of
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`. -/
theorem IsFiniteLocallyFree.toFiniteLocallyFree (M : _root_.SheafOfModules.{u} R)
    (hM : IsFiniteLocallyFree.{u, v, u₁} M) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, v, u₁} M :=
  ⟨hM.exists_isFiniteLocallyFreeData⟩

/-- A sheaf of modules which is finite locally free of rank `r` is of finite type. -/
theorem IsFiniteLocallyFreeOfRank.isFiniteType (M : _root_.SheafOfModules.{u} R) (r : ℕ)
    [hM : IsFiniteLocallyFreeOfRank.{u, v, u₁} M r] : _root_.SheafOfModules.IsFiniteType M :=
  let := IsFiniteLocallyFree.toFiniteLocallyFree M (hM.isFiniteLocallyFree M r)
  Stacks.FiniteLocallyFree.isFiniteType M

/-- A sheaf of modules which is finite locally free of rank `r` is of finite presentation: over
each member of the covering, its local free basis of `r` elements is a presentation with no
relations. -/
@[ega "0 5.4.1" "quasi-coherence"]
theorem IsFiniteLocallyFreeOfRank.isFinitePresentation (M : _root_.SheafOfModules.{u} R) (r : ℕ)
    [hM : IsFiniteLocallyFreeOfRank.{u, v, u₁} M r] : M.IsFinitePresentation := by
  let (V : C) : HasSheafify (J.over V) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let := IsFiniteLocallyFree.toFiniteLocallyFree M (hM.isFiniteLocallyFree M r)
  exact Stacks.FiniteLocallyFree.isFinitePresentation M

end AlgebraicGeometry.SheafOfModules

end
