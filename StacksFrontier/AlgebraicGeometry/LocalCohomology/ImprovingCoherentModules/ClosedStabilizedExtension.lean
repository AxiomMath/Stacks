module

public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ExistenceDepthOutside
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.OpenExtension

import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence

/-!
# The stabilized open extension across a closed subset is a single pushforward

Let `X` be a Noetherian scheme, let `T ⊆ X` be a subset and let `V` be an open of `X` whose
underlying set is the complement of `T`.  For any module `F` on `X` the unit of the
pullback--pushforward adjunction

`F ⟶ j_{V,*}(F|_V)`

is a *stabilized open extension along `T`* (`AlgebraicGeometry.IsStabilizedOpenExtension`) as
soon as its target is coherent.  Three of the four clauses of that predicate hold for the single
open `V` with nothing to prove beyond two formal facts about the adjunction, the invertibility of
the unit at a pushforward (`AlgebraicGeometry.isIso_unit_app_pushforward`, in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.OpenExtension`) and the
stalk clause `AlgebraicGeometry.isIso_stalkFunctor_map_unit_of_mem`; the fourth clause,
coherence of `j_{V,*}(F|_V)`, is the hypothesis.

Such a `V` exists exactly when `T` is closed.  So for a closed `T` the hypothesis `hext` of
[Stacks, Tag 0EI3]'s existence half in this library — the existence of a coherent stabilized
open extension of the depth-one quotient, which is where the source's filtered colimit of
pushforwards sits — collapses to coherence of the one module `j_{V,*}(F'|_V)`, with `F'` the
depth-one quotient of `F` along `T` and `V` the complement of `T`.  That is the content of the
last result here.

## Main results

* `AlgebraicGeometry.isStabilizedOpenExtension_unit`: the unit at `F` is a stabilized open
  extension along the complement of the open, as soon as its target is coherent.
* `AlgebraicGeometry.exists_isDepthTwoExtension_of_isCoherent_pushforward`:
  **[Stacks, Tag 0EI3], existence** for a closed subset, conditional only on coherence of the
  single pushforward `j_{V,*}(F'|_V)`.

## Implementation notes

Invertibility of the unit at a pushforward is the right triangle identity
`η_{R G} ≫ R(ε_G) = 𝟙` with `R(ε_G)` invertible, the counit along an open immersion being
invertible; it is `AlgebraicGeometry.isIso_unit_app_pushforward` and is used from there.

The stalk clause is `AlgebraicGeometry.isIso_stalkFunctor_map_unit_of_mem`, which has no
hypothesis on the module at all, read in `ModuleCat` over the local ring rather than in `Ab`.

The subset `T` and the open `V` are both taken as arguments, related by `hV : (V : Set X) = Tᶜ`,
rather than building `V` out of a closedness hypothesis on `T`: the statements are then usable
at whichever of the two the caller has in hand, and `IsClosed.isOpen_compl` supplies `V` when
only `T` is given.

## What is *not* proved here, and why the remaining hypothesis is not droppable

Coherence of `j_{V,*}(F'|_V)` is exactly where the two hypotheses of [Stacks, Tag 0EI3] that
`AlgebraicGeometry.exists_isDepthTwoExtension` omits — that `X` locally has a dualizing complex,
and that `depth(F_x) ≥ 1` at every `x ∉ T` admitting an immediate specialization into `T` —
have to re-enter.  It is not automatic for a closed `T`: on the spectrum of a one-dimensional
Noetherian local domain with `T` the closed point and `F = 𝒪_X`, the depth-one quotient is `F`
and `j_{V,*}(F|_V)` is the ring of sections over the punctured spectrum, which is not finite over
a non-normal such ring.  So the statement below is conditional, not a weakening of the source,
and no hypothesis of the source may be dropped on the strength of it.  See the implementation
notes of the sibling module `DepthTwoExtensionExistence` (in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/ImprovingCoherentModules/`)
for the `Spec ℤ` witness showing the same for a merely specialization-stable `T`.

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The unit as a stabilized open extension -/

/-- **The canonical map to a single pushforward is a stabilized open extension.** Let `V` be an
open of `X` whose complement is `T`.  If `j_{V,*}(F|_V)` is coherent, then the unit
`F ⟶ j_{V,*}(F|_V)` of the pullback--pushforward adjunction is a stabilized open extension of
`F` along `T` in the sense of `AlgebraicGeometry.IsStabilizedOpenExtension`.

All four clauses are witnessed by the single open `V`, which is legitimate because `V` is the
whole complement of `T`: its complement is `T` itself, it misses every point of `T`, the unit is
a stalk isomorphism at each of its points by
`AlgebraicGeometry.isIso_stalkFunctor_map_unit_of_mem`, and its target is the pushforward of its
own restriction to `V` by `AlgebraicGeometry.isIso_unit_app_pushforward`.  No filtered colimit is
taken: for this `T` the system of opens whose complement lies in `T` has `V` as its least
element. -/
public theorem isStabilizedOpenExtension_unit {X : Scheme.{u}} (T : Set X) (V : X.Opens)
    (hV : (V : Set X) = Tᶜ) (F : X.Modules)
    (hcoh : ((Scheme.Modules.pushforward V.ι).obj
      ((Scheme.Modules.pullback V.ι).obj F)).IsCoherent) :
    IsStabilizedOpenExtension T
      ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app F) := by
  refine ⟨hcoh, fun _ => ⟨V, ?_, ?_, ?_, ?_⟩⟩
  · rw [hV, compl_compl]
  · rw [hV]
    exact fun hx hx' => hx' hx
  · exact fun y hy => isIso_stalkMap_of_isIso_stalkFunctor _ y
      (isIso_stalkFunctor_map_unit_of_mem X V F y hy)
  · exact isIso_unit_app_pushforward V ((Scheme.Modules.pullback V.ι).obj F)

/-- **Stacks Project, Tag 0EI3, existence for a closed subset.** A coherent module `F` on a
Noetherian scheme admits a map to a coherent module which is an isomorphism on the stalks away
from a closed subset `T` and whose stalks on `T` have depth at least two, as soon as the single
pushforward `j_{V,*}(F'|_V)` is coherent — where `V` is the complement of `T` and `F'` is the
depth-one quotient of `F` along `T`.

Together with `AlgebraicGeometry.isStabilizedOpenExtension_unit` this replaces the hypothesis
`hext` of `AlgebraicGeometry.exists_isDepthTwoExtension_of_isStabilizedOpenExtension`, which asks
for a coherent stabilized open extension, by coherence of one explicit module: for a closed `T`
no colimit of pushforwards over the opens whose complement lies in `T` is needed, because the
complement of `T` is itself such an open and is the smallest one.

The remaining hypothesis is not removable; it is where the two hypotheses of [Stacks, Tag 0EI3]
absent from `AlgebraicGeometry.exists_isDepthTwoExtension` — a dualizing complex and a depth
bound across the boundary of `T` — must re-enter.  See the implementation notes of this
module. -/
@[stacks 0EI3 "existence for a closed subset, conditional only on coherence of the single \
pushforward of the restriction of the depth-one quotient to the complement; the hypothesis \
hext of exists_isDepthTwoExtension_of_isStabilizedOpenExtension, namely a coherent stabilized \
open extension, is discharged here for a closed subset"]
public theorem exists_isDepthTwoExtension_of_isCoherent_pushforward
    (X : Scheme.{u}) [IsNoetherian X] (T : Set X) (hT : IsClosed T) (V : X.Opens)
    (hV : (V : Set X) = Tᶜ) (F : X.Modules) [F.IsCoherent]
    (hcoh : ((Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.pullback V.ι).obj
      (depthOneQuotient X T hT.stableUnderSpecialization F))).IsCoherent) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ :=
  exists_isDepthTwoExtension_of_isStabilizedOpenExtension X T
    hT.stableUnderSpecialization F
    ⟨_, _, isStabilizedOpenExtension_unit T V hV _ hcoh⟩

end AlgebraicGeometry

end
