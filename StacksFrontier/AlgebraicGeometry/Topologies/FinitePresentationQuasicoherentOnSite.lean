module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation implies quasi-coherence on a ringed site

`SheafOfModules.IsFinitePresentation` and `SheafOfModules.IsQuasicoherentOnSite` are two
readings of "locally a cokernel of a map between coproducts of copies of the structure
sheaf": the first is Mathlib's, packaged as a `SheafOfModules.QuasicoherentData` whose local
presentations are finite, and the second is the sheafification-free reading of Stacks 03DL (6)
used throughout this tree.  Mathlib already records that a finitely presented sheaf of modules
is quasi-coherent in its own sense; this file transports that along
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_quasicoherentData`, so that a finitely
presented module satisfies the tree's predicate as well.

## Main results

* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentation`: **a sheaf of modules
  of finite presentation is quasi-coherent on the site.**

## Implementation notes

No `@[stacks]` attribute is carried.  The implication from clause (7) to clause (6) of Stacks
03DL is not a numbered statement of the source, which simply lists the conditions; the
corresponding implication for the tree's own `SheafOfModules.IsFinitePresentationOnSite` is
already an instance, `SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite`,
and also carries no attribute.

This is stated as a theorem rather than an instance.  Mathlib's `SheafOfModules.QuasicoherentData`
lives in a universe that the statement of `SheafOfModules.IsFinitePresentation` fixes but that
`SheafOfModules.IsQuasicoherentOnSite` does not mention, so instance search cannot recover it
from the goal.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory

universe u v r

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A sheaf of modules of finite presentation is quasi-coherent on the site.**  Finite
presentation provides a `SheafOfModules.QuasicoherentData` — a family of objects covering the
terminal object together with a presentation of the module restricted to each — and
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_quasicoherentData` turns such a datum into
quasi-coherence on the site.  The finiteness of the presentations is not used. -/
@[ega "0 5.2.5" "more general"]
theorem isQuasicoherentOnSite_of_isFinitePresentation
    [∀ W : C, HasWeakSheafify (J.over W) AddCommGrpCat.{r}]
    [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{r}]
    (M : _root_.SheafOfModules.{r} R) [M.IsFinitePresentation] :
    M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_quasicoherentData
    (_root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose

end Stacks.SheafOfModules

end
