module

public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# A finite locally free sheaf of modules is of finite presentation

Let `M` be a sheaf of modules over a sheaf of rings `R` on a site `(C, J)` which is finite
locally free in the sense of [Stacks, Tag 01C6] (2), i.e. carries local generators data which is
simultaneously a local free basis and finite on each member of the covering. Then `M` is of
finite presentation: on each member of the covering the generating map is an isomorphism, so the
presentation it induces needs no relations at all, and the generators are finite in number by
hypothesis.

## Main results

* `Stacks.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree`: **a finite locally free
  sheaf of modules is of finite presentation**, for the class
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`.

## Implementation notes

The quasi-coherent data with no relations attached to locally free data is Mathlib's
`SheafOfModules.LocalGeneratorsData.quasiCoherentData`, and the fact that it is a *finite*
presentation when the local generators are finite in number is
`Stacks.FiniteLocallyFree.isFinitePresentation_quasiCoherentData`. The only work left here is
that `SheafOfModules.IsFinitePresentation` quantifies over quasi-coherent data whose index type
lives in the universe of the site, which is arranged by
`SheafOfModules.LocalGeneratorsData.shrink`; shrinking preserves both local freeness and
finiteness.

This is the statement for the class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of
`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean`, which is a second spelling of
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`; the latter already has the conclusion as
`Stacks.FiniteLocallyFree.isFinitePresentation`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public section

open CategoryTheory

universe u v₁ u₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A finite locally free sheaf of modules is of finite presentation.** The local free basis
provided by `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` is finite and its generating
map is an isomorphism, so the induced local presentation has finitely many generators and no
relations. This is the finite-presentation half of the implications (4) ⟹ (1) and (4) ⟹ (2) of
Stacks Tag 05P2. -/
theorem isFinitePresentation_of_isFiniteLocallyFree (M : _root_.SheafOfModules.{u} R)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, v₁, u₁} M] :
    M.IsFinitePresentation := by
  obtain ⟨q, hq, hq'⟩ := h.exists_isFiniteLocallyFreeData
  exact ⟨q.shrink.quasiCoherentData, inferInstance⟩

end Stacks.SheafOfModules

end
