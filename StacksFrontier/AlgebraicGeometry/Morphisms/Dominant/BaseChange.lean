module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.Topology.Specialization.Lifting

/-!
# Dominance under base change

Dominance is not stable under arbitrary base change, but it survives two kinds. Along an open
morphism the range of the base change is the preimage of the range, and the preimage of a dense
set under an open map is dense. Along a morphism that merely lifts generalizations one still
wins, provided the original morphism is quasi-compact: lifting generalizations carries generic
points of the new base to generic points of the old one, where quasi-compactness lets dominance
be tested on generic points alone.

## Main results

* `AlgebraicGeometry.isDominant_pullback_snd_of_isOpenMap` states that dominance is preserved by
  an open base change.
* `AlgebraicGeometry.isDominant_pullback_snd_of_liftsGeneralizations` states that dominance is
  preserved by a base change which lifts generalizations, provided the original morphism is
  quasi-compact.

## Implementation notes

In both results the base change is represented by the chosen categorical pullback, so its
structural morphism is `pullback.snd f g`. An open morphism is expressed by openness of its
underlying continuous map, and the condition in the second result by `LiftsGeneralizations` on
that map.

## References

* [Stacks Project, Tag 0H3F](https://stacks.math.columbia.edu/tag/0H3F)
* [Stacks Project, Tag 0H8F](https://stacks.math.columbia.edu/tag/0H8F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0H8F.** The base change of a dominant morphism of schemes along an
open morphism is dominant. -/
@[stacks 0H8F]
public theorem isDominant_pullback_snd_of_isOpenMap {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [IsDominant f] (hg : IsOpenMap g) :
    IsDominant (pullback.snd f g) := by
  simpa only [isDominant_iff, DenseRange, Scheme.Pullback.range_snd] using
    Dense.preimage IsDominant.denseRange hg

/-- A map lifting generalizations carries generic points of irreducible components to generic
points of irreducible components. -/
private lemma mem_genericPoints_of_liftsGeneralizations
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T0Space X] [QuasiSober Y] (f : X → Y) (hf : LiftsGeneralizations f)
    {x : X} (hx : x ∈ genericPoints X) : f x ∈ genericPoints Y := by
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({f x} : Set Y)) isIrreducible_singleton.closure
  obtain ⟨x', hx'x, hfx'⟩ := hf rfl
    ((genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩).specializes
      (hsub (subset_closure (Set.mem_singleton (f x)))))
  have : x' = x := (hx'x.antisymm (specializes_iff_closure_subset.mpr
    ((genericPoints.component ⟨x, hx⟩).2.2 isIrreducible_singleton.closure
      (specializes_iff_closure_subset.mp hx'x)))).eq
  rw [this] at hfx'
  rw [hfx']
  exact (genericPoints.ofComponent ⟨W, hW⟩).2

/-- **Stacks Project, Tag 0H3F.** A generizing base change of a quasi-compact dominant morphism
of schemes is dominant. -/
@[stacks 0H3F]
public theorem isDominant_pullback_snd_of_liftsGeneralizations
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [QuasiCompact f] [IsDominant f]
    (hg : LiftsGeneralizations g) : IsDominant (pullback.snd f g) := by
  rw [isDominant_iff_genericPoints_subset_range]
  intro η' hη'
  obtain ⟨x, hx⟩ :=
    (isDominant_iff_genericPoints_subset_range f).mp inferInstance
      (mem_genericPoints_of_liftsGeneralizations g hg hη')
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x η' hx
  exact ⟨z, hz⟩

end AlgebraicGeometry
