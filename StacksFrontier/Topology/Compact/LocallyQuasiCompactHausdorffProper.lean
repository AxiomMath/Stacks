module

public import StacksFrontier.Topology.Compact.LocallyQuasiCompactHausdorffCat
public import StacksFrontier.Topology.Maps.Proper

/-!
# Hausdorff, locally quasi-compact spaces and their proper maps

The Stacks project says "Hausdorff and locally quasi-compact" where the literature often says
"locally compact", meaning a Hausdorff space in which every point has a quasi-compact
neighbourhood. For a Hausdorff space the two agree: if every point has one quasi-compact
neighbourhood then every point has a fundamental system of them.

Every morphism `f : X → Y` of the category `LC` of Hausdorff, locally quasi-compact spaces is a
separated continuous map, because its source is Hausdorff. Since a proper map is by definition a
separated, universally closed one, a morphism of `LC` is proper if and only if it is universally
closed.

## Main results

* `Stacks.Topology.t2Space_and_locallyCompactSpace_iff`: a space is Hausdorff and locally
  quasi-compact iff it is Hausdorff and every point has a quasi-compact neighbourhood.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.isSeparatedMap_hom`: every morphism of `LC` is
  separated.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.isProperMap_iff_isUniversallyClosedMap`: a
  morphism of `LC` is proper iff it is universally closed.

## References

* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
* [Stacks Project, Tag 005O](https://stacks.math.columbia.edu/tag/005O)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Topology

universe u v w

/-- **The convention "Hausdorff and locally quasi-compact".** A topological space is Hausdorff
and locally quasi-compact (every point has a fundamental system of quasi-compact
neighbourhoods) if and only if it is *locally compact* in the sense often used in the
literature: Hausdorff, with every point having a quasi-compact neighbourhood. -/
@[stacks 09WY "Hausdorff and locally quasi-compact is the literature's locally compact"]
theorem t2Space_and_locallyCompactSpace_iff (X : Type u) [TopologicalSpace X] :
    T2Space X ∧ LocallyCompactSpace X ↔ T2Space X ∧ WeaklyLocallyCompactSpace X :=
  ⟨fun ⟨h₁, _⟩ => ⟨h₁, inferInstance⟩, fun ⟨h₁, _⟩ => ⟨h₁, inferInstance⟩⟩

namespace LocallyQuasiCompactHausdorff

/-- **Morphisms of `LC` are separated.** The source of a morphism of `LC` is Hausdorff, so the
morphism is a separated continuous map. -/
@[stacks 09WY "any morphism of LC is a separated continuous map"]
theorem isSeparatedMap_hom {X Y : LocallyQuasiCompactHausdorff.{u}} (f : X ⟶ Y) :
    IsSeparatedMap f.hom :=
  T2Space.isSeparatedMap _

/-- **A morphism of `LC` is proper iff it is universally closed.** Proper means separated and
universally closed, and every morphism of `LC` is separated. -/
@[stacks 09WY "a morphism of LC is proper iff it is universally closed"]
theorem isProperMap_iff_isUniversallyClosedMap {X Y : LocallyQuasiCompactHausdorff.{u}}
    (f : X ⟶ Y) :
    StacksDraft.Topology.IsProperMap.{u, u, w} f.hom ↔
      StacksDraft.Topology.IsUniversallyClosedMap.{u, u, w} f.hom :=
  ⟨And.right, fun h => ⟨isSeparatedMap_hom f, h⟩⟩

end LocallyQuasiCompactHausdorff

end Stacks.Topology
