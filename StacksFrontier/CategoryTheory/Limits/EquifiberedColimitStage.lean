module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit

/-!
# The stage squares of an equifibered morphism of diagrams are Cartesian

Let `α : F ⟶ G` be a morphism of diagrams indexed by the same category whose naturality squares
are Cartesian (`CategoryTheory.NatTrans.Equifibered`). If the colimits under each object of the
index are exact, then each stage of `F` is the base change of `colim F ⟶ colim G` along the
coprojection of `G` at that stage:

```
F.obj i ⟶ colimit F
   |          |
   v          v
G.obj i ⟶ colimit G
```

is Cartesian. This is the descent half of the van Kampen property for such a colimit; its converse
half — that the pulled-back cocone is still a colimit — is universality, and for a filtered colimit
of sheaves of sets that is `CategoryTheory.Limits.sheaf_filteredColimit_isUniversalColimit`.

Equifiberedness is not merely sufficient but *equivalent* to the conclusion
(`CategoryTheory.Limits.equifibered_of_isPullback_colimit_ι`), so no weaker hypothesis on `α`
can give it. In particular it is not enough for the transition morphisms of `G` to be
monomorphisms: with the index `{0 ≤ 1}`, which is filtered, `G` constant at a terminal object —
so that all its transitions are isomorphisms — and `F` the diagram `⊥ ⟶ ⊤` given by the unique
morphism out of an initial object, both colimits are `⊤` and both morphisms out of them are the
identity, so the square at `0` is Cartesian only if the initial and terminal objects agree.

## Main results

* `AlgebraicGeometry.FormalSpace.CartesianColimit.equifibered_colimit_isPullback`: the stage
  squares of an equifibered morphism of diagrams are Cartesian.
* `CategoryTheory.Limits.equifibered_of_isPullback_colimit_ι`: its converse, which needs no
  exactness.

## Implementation notes

The hypotheses are about the category `Under i` of objects of the index receiving a morphism
from `i`: that `Under.forget i` is final, that `Under i` is connected, and that colimits of
shape `Under i` are exact. A filtered index satisfies all three, the first by
`CategoryTheory.Under.final_forget` and the second by
`CategoryTheory.IsFiltered.isConnected`, and the third holds in a category of sheaves of sets.
They are the right hypotheses because the whole square is read as the image under
`CategoryTheory.Limits.colim` of a Cartesian square of diagrams over `Under i`: the transitions
out of `i` form a morphism from the constant diagram on `F.obj i` to `Under.forget i ⋙ F`
(`AlgebraicGeometry.FormalSpace.CartesianColimit.underTransition`), the two of them sit in a square
over the corresponding morphism for `G` which is Cartesian objectwise by equifiberedness, and
exactness of the colimit carries that square to the colimits. Finality identifies
`colimit (Under.forget i ⋙ F)` with `colimit F` and connectedness identifies the colimit of the
constant diagram with `F.obj i`
(`AlgebraicGeometry.FormalSpace.CartesianColimit.constantColimitIso`), which turns the resulting
square into the stage square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Limits

/-- If every square comparing `α` at a stage with the morphism it induces on the colimits is
Cartesian, then `α` is equifibered. This is the converse of
`AlgebraicGeometry.FormalSpace.CartesianColimit.equifibered_colimit_isPullback`, and needs no
exactness: the naturality square of `α` at a transition `f : i ⟶ j`, pasted with the Cartesian
square at `j`, is the Cartesian square at `i`, so it is Cartesian by cancellation. -/
theorem equifibered_of_isPullback_colimit_ι {J : Type w} [Category J] {C : Type u}
    [Category.{v} C] {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G)
    (h : ∀ i, IsPullback (colimit.ι F i) (α.app i) (colimMap α) (colimit.ι G i)) :
    α.Equifibered :=
  fun _ _ f => (IsPullback.paste_horiz_iff (h _) (α.naturality f)).1 (by simpa using h _)

end CategoryTheory.Limits

end
