module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The direct image of abelian sheaves preserves injective objects

For a continuous map `f : X ⟶ Y` of topological spaces, the inverse image `f⁻¹` of sheaves of
abelian groups is left exact, hence preserves monomorphisms, and therefore its right adjoint
`f_*` carries injective sheaves to injective sheaves.

Left exactness of `f⁻¹` is a formal consequence of `Opens.map f` being representably flat: for
an open `U ⊆ X` the opens `V ⊆ Y` with `U ⊆ f⁻¹V` are nonempty (take `V = ⊤`) and closed under
intersection, so they are cofiltered.  Mathlib's
`CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits` turns that into
preservation of all finite limits by `(Opens.map f).sheafPullback`.

## Main results

* `TopCat.Sheaf.pullback_preservesFiniteLimits`: `f⁻¹` preserves finite limits.
* `TopCat.Sheaf.pullback_preservesMonomorphisms`: `f⁻¹` preserves monomorphisms.
* `TopCat.Sheaf.pushforward_preservesInjectiveObjects`: `f_*` preserves injective objects.

## Implementation notes

The three results are stated for Mathlib's `TopCat.Sheaf.pullback` and
`TopCat.Sheaf.pushforward`, which is the spelling the systems of abelian sheaves of
`StacksFrontier/Topology/Sheaves/Limits/AbelianSystemCategory.lean` use for their transition
functor `SpectralDiagram.pushFunctor`; that is an `abbrev`, so the instances below fire on it
directly.  `Stacks.Cohomology.Leray.pushforward_preservesInjectiveObjects`
(Stacks Tag 01F2) is the same fact stated for the
`Functor.sheafPushforwardContinuous` spelling, which `TopCat.Sheaf.pushforward` is a
non-reducible `def` for, so neither statement fires on the other's spelling.

`PreservesFiniteLimits` is supplied by the named construction rather than by instance search:
Mathlib's instance for `Functor.sheafPullback` of a representably flat functor is proved with a
local `reflectsLimits_of_reflectsIsomorphisms` instance, and without it the search for the
sheafification and concrete-category side conditions does not terminate inside the default
budget.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe w

noncomputable section

namespace TopCat.Sheaf

variable {X Y : TopCat.{w}} (f : X ⟶ Y)

/-- **The inverse image of sheaves of abelian groups is left exact.**  `Opens.map f` is
representably flat, the opens of `Y` containing the image of a given open of `X` being nonempty
and closed under intersection, and the sheaf pullback along a representably flat functor
preserves finite limits. -/
instance pullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{w} f) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f) AddCommGrpCat.{w}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- **The inverse image of sheaves of abelian groups preserves monomorphisms.**  A monomorphism
is a morphism whose cospan with itself has a pullback square, so a functor preserving pullbacks
preserves monomorphisms. -/
instance pullback_preservesMonomorphisms :
    (TopCat.Sheaf.pullback AddCommGrpCat.{w} f).PreservesMonomorphisms :=
  inferInstance

/-- **The direct image of sheaves of abelian groups preserves injective objects.**  Its left
adjoint is the inverse image, which preserves monomorphisms, so a lift against a monomorphism
of the inverse image transposes to a lift against the monomorphism itself. -/
instance pushforward_preservesInjectiveObjects :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{w} f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{w} f)

end TopCat.Sheaf

end

end
