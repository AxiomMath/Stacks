module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Specialization.Lifting

/-!
# Openness from lifting generalizations

A morphism of schemes which is locally of finite presentation and along which generalizations lift
is open; if generalizations lift along every base change of such a morphism, it is universally
open.

## Main results

* `AlgebraicGeometry.isOpenMap_of_liftsGeneralizations`: part (1) of the tag.
* `AlgebraicGeometry.universallyOpen_of_universally_liftsGeneralizations`: part (2) of the tag.

## Implementation notes

The Stacks condition that generalizations lift along a map is `LiftsGeneralizations` of Tag 0063,
which agrees with Mathlib's `GeneralizingMap`; part (1) is therefore Mathlib's
`AlgebraicGeometry.isOpenMap_of_generalizingMap`, whose proof reduces to the affine case and
applies going-down for a ring map of finite presentation. Lifting generalizations along every base
change is the universal closure
`MorphismProperty.universally (topologically @LiftsGeneralizations)` of the corresponding
topological morphism property, matching Mathlib's formulation of
`AlgebraicGeometry.UniversallyOpen`; part (2) follows by applying part (1) to each base change,
which is again locally of finite presentation.

## References

* [Stacks Project, Tag 01U1](https://stacks.math.columbia.edu/tag/01U1)
* [Stacks Project, Tag 0063](https://stacks.math.columbia.edu/tag/0063)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01U1**, part (1). A morphism of schemes which is locally of finite
presentation and along which generalizations lift is open. -/
@[stacks 01U1 "part (1): locally of finite presentation and generalizations lift implies open",
  ega "IV 1.10.4" "b) ⇒ a)",
  ega "IV 14.1.6" "partial"]
public lemma isOpenMap_of_liftsGeneralizations {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (hf : LiftsGeneralizations f) : IsOpenMap f :=
  isOpenMap_of_generalizingMap f ((liftsGeneralizations_iff_generalizingMap f).mp hf)

/-- **Stacks Project, Tag 01U1**, part (2). A morphism of schemes which is locally of finite
presentation and along every base change of which generalizations lift is universally open. -/
@[stacks 01U1 "part (2): lfp and generalizations lift along every base change implies univ. open",
  ega "IV 1.10.4" "b) ⇒ a), special case"]
public lemma universallyOpen_of_universally_liftsGeneralizations {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f]
    (hf : universally (topologically @LiftsGeneralizations) f) : UniversallyOpen f := by
  refine ⟨universally_mk' (topologically @IsOpenMap) f fun {T} g _ => ?_⟩
  exact isOpenMap_of_liftsGeneralizations (pullback.fst g f)
    (hf (pullback.snd g f) g (pullback.fst g f) (IsPullback.of_hasPullback g f))

end AlgebraicGeometry
