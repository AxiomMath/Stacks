module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertyClassClosure
public import StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocal

/-!
# Tautness is a local property, with the source's hypotheses only

The axioms `TopologicalRing.isTaut_localizationPreserves`,
`TopologicalRing.isTaut_faithfullyFlatDescent` and `TopologicalRing.isTaut_finiteProductPreserves`
of `StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocal` are stated through the abbreviations
`LocalizationPreserves`, `FaithfullyFlatDescent` and `FiniteProductPreserves`, which ask for
the four corners of a localization diagram, the two completed ones included, to lie in
`WAdm^{count}`. In Situation 0CBA the source only asks this of `A` and `B`, and deduces it
for `(A')^∧` and `(B')^∧` from **Stacks 0ANB**: the completion `(A')^∧ = lim A'/IA'` of
Example 0AN6 along any ring map `A → A'` out of a ring of `WAdm^{count}` is again in
`WAdm^{count}`. That is
`TopologicalRing.isCountablyWeaklyAdmissible_completionOver` (weak admissibility by
`TopologicalRing.completionOver_isWeaklyAdmissible`, countability of the neighbourhoods of zero
by `TopologicalRing.completionOver_isCountablyGenerated_nhds_zero`, the 0ANB clause for
`WAdm^{count}`).

The theorems `TopologicalRing.isTaut_completedMap_of_isTaut`,
`TopologicalRing.isTaut_map_of_isTaut_completedMap` and `TopologicalRing.isTaut_pi` below
discharge those hypotheses with it, and so state axioms 0AND, 0ANE and 0ANF for tautness with
exactly the hypotheses of the source: a localization diagram, whose fields say that `A` and `B`
are countably indexed weakly admissible, that `A → A'` and `B → B'` are étale and that the
vertical maps are continuous; faithful flatness of `A → A'` for descent; and for products,
arrows `B → A_i` of `WAdm^{count}`.

## Main results

* `TopologicalRing.isTaut_completedMap_of_isTaut`: **Stacks 0ANJ**, axiom 0AND.
* `TopologicalRing.isTaut_map_of_isTaut_completedMap`: **Stacks 0ANJ**, axiom 0ANE.
* `TopologicalRing.isTaut_pi`: **Stacks 0ANJ**, axiom 0ANF.

## References

* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0ANB](https://stacks.math.columbia.edu/tag/0ANB)
* [Stacks Project, Tag 0ANJ](https://stacks.math.columbia.edu/tag/0ANJ)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public section

namespace TopologicalRing

universe u

/-- **Stacks 0ANJ**, axiom 0AND for tautness, with the hypotheses of Situation 0CBA only.
Given a diagram (0ANC) — `A`, `B` countably indexed weakly admissible, `A → A'` and `B → B'`
étale, `φ : B → A` and `φ' : (B')^∧ → (A')^∧` continuous and commuting with the canonical
maps — if `φ` is taut then so is `φ'`. The completed corners `(A')^∧` and `(B')^∧` are objects of
`WAdm^{count}` by Stacks 0ANB (`isCountablyWeaklyAdmissible_completionOver`), which is how the
source reads the axiom. -/
@[stacks 0ANJ "axiom 0AND for tautness, the completed corners in WAdm^count by 0ANB"]
public theorem isTaut_completedMap_of_isTaut {A B A' B' : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A'] [CommRing B'] (D : LocalizationDiagram A B A' B')
    (h : RingHom.IsTaut D.map) : RingHom.IsTaut D.completedMap :=
  isTaut_localizationPreserves D ⟨D.weaklyAdmissibleA, D.countableA⟩
    ⟨D.weaklyAdmissibleB, D.countableB⟩
    (isCountablyWeaklyAdmissible_completionOver D.toA' ⟨D.weaklyAdmissibleA, D.countableA⟩)
    (isCountablyWeaklyAdmissible_completionOver D.toB' ⟨D.weaklyAdmissibleB, D.countableB⟩) h

/-- **Stacks 0ANJ**, axiom 0ANE for tautness, with the hypotheses of Situation 0CBA only.
Given a diagram (0ANC) whose map `A → A'` is faithfully flat, if `φ' : (B')^∧ → (A')^∧` is taut
then so is `φ : B → A`. The completed corners are objects of `WAdm^{count}` by Stacks 0ANB
(`isCountablyWeaklyAdmissible_completionOver`). -/
@[stacks 0ANJ "axiom 0ANE for tautness, the completed corners in WAdm^count by 0ANB"]
public theorem isTaut_map_of_isTaut_completedMap {A B A' B' : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A'] [CommRing B'] (D : LocalizationDiagram A B A' B')
    (hff : D.toA'.FaithfullyFlat) (h : RingHom.IsTaut D.completedMap) :
    RingHom.IsTaut D.map :=
  isTaut_faithfullyFlatDescent D ⟨D.weaklyAdmissibleA, D.countableA⟩
    ⟨D.weaklyAdmissibleB, D.countableB⟩
    (isCountablyWeaklyAdmissible_completionOver D.toA' ⟨D.weaklyAdmissibleA, D.countableA⟩)
    (isCountablyWeaklyAdmissible_completionOver D.toB' ⟨D.weaklyAdmissibleB, D.countableB⟩)
    hff h

/-- **Stacks 0ANJ**, axiom 0ANF for tautness, stated once: if `B → A_i` are taut arrows of
`WAdm^{count}` for `i` in a finite index set, then `B → ∏ A_i` is taut. -/
@[stacks 0ANJ "axiom 0ANF for tautness"]
public theorem isTaut_pi {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (hB : IsCountablyWeaklyAdmissible B)
    {ι : Type u} [Finite ι] (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] [∀ i, IsLinearTopology (A i) (A i)]
    (hA : ∀ i, IsCountablyWeaklyAdmissible (A i))
    (f : ∀ i, B →+* A i) (hf : ∀ i, Continuous (f i)) (h : ∀ i, RingHom.IsTaut (f i)) :
    RingHom.IsTaut (RingHom.pi f) := by
  have := Fintype.ofFinite ι
  exact isTaut_finiteProductPreserves hB.1 hB.2 A (fun i ↦ (hA i).1) (fun i ↦ (hA i).2) f hf hB hA h

end TopologicalRing

end
