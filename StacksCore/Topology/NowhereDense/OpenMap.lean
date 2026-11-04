module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# Closed nowhere dense subsets and open maps

A closed set is nowhere dense exactly when its complement is open and dense. Open maps
preserve density under preimages; continuous open surjections also detect density and
openness of subsets. These facts give both parts of Stacks tag 03HR.

## Main results

* `isClosedNowhereDense_preimage_of_isOpenMap` (Stacks 03HR, part 1): the preimage of a closed
  nowhere dense subset under a continuous open map is closed nowhere dense.
* `isClosedNowhereDense_preimage_iff_of_surjective_isOpenMap` (Stacks 03HR, part 2): for a
  surjective continuous open map the converse holds as well.

## References

* [Stacks Project, Tag 03HR](https://stacks.math.columbia.edu/tag/03HR)
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Stacks 03HR** (part 1). If `f : X → Y` is a continuous open map and `T ⊆ Y` is closed
nowhere dense, then `f⁻¹(T)` is closed nowhere dense in `X`. -/
@[stacks 03HR "(1)"]
theorem isClosedNowhereDense_preimage_of_isOpenMap
    (f : X → Y) (hfc : Continuous f) (hfo : IsOpenMap f)
    (T : Set Y) (hT_closed : IsClosed T) (hT : IsNowhereDense T) :
    IsClosed (f ⁻¹' T) ∧ IsNowhereDense (f ⁻¹' T) := by
  have hT_compl := isClosed_isNowhereDense_iff_compl.mp ⟨hT_closed, hT⟩
  rw [isClosed_isNowhereDense_iff_compl]
  simpa only [Set.preimage_compl] using
    And.intro (hT_compl.1.preimage hfc) (hT_compl.2.preimage hfo)

/-- **Stacks 03HR** (part 2). If `f : X → Y` is a surjective continuous open map, then `T ⊆ Y` is
closed nowhere dense if and only if `f⁻¹(T)` is closed nowhere dense in `X`. -/
@[stacks 03HR "(2)"]
theorem isClosedNowhereDense_preimage_iff_of_surjective_isOpenMap
    (f : X → Y) (hfc : Continuous f) (hfo : IsOpenMap f) (hfs : Function.Surjective f)
    (T : Set Y) :
    (IsClosed T ∧ IsNowhereDense T) ↔
      (IsClosed (f ⁻¹' T) ∧ IsNowhereDense (f ⁻¹' T)) := by
  refine ⟨fun hT ↦ isClosedNowhereDense_preimage_of_isOpenMap f hfc hfo T hT.1 hT.2,
    fun hT ↦ ?_⟩
  rw [isClosed_isNowhereDense_iff_compl] at hT ⊢
  simp only [← Set.preimage_compl] at hT
  refine ⟨(hfo.isQuotientMap hfc hfs).isCoinducing.isOpen_preimage.mp hT.1, ?_⟩
  simpa only [hfs.image_preimage] using hfs.denseRange.dense_image hfc hT.2
