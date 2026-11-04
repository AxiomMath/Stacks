module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverNoetherian
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# The locality axioms of Situation 0CBA on a class closed under completed étale localization

Situation 0CBA tests a property `P` of arrows of `WAdm^{count}` on the localization diagrams
`A → (A')^∧`, `B → (B')^∧` of `TopologicalRing.LocalizationDiagram`, and the source observes in
passing — this is the lemma preceding the situation, **Stacks 0ANB** — that the two completed
rings belong to `WAdm^{count}` as soon as `A` and `B` do. The Lean reading of the three axioms,
`TopologicalRing.LocalizationPreserves`, `TopologicalRing.FaithfullyFlatDescent` and
`TopologicalRing.FiniteProductPreserves`, restricts all four corners to a subclass `C` and so
asks the consumer for `C ((A')^∧)` and `C ((B')^∧)` alongside `C A` and `C B`. For an arbitrary
`C` those two are genuine extra hypotheses: `C R := IsField R` gives a class which is not closed
under the construction, and for it the axioms constrain nothing at the completed corners.

This file discharges them for the three classes the consumers of Situation 0CBA actually use —
`WAdm^{count}`, `WAdm^{adic*}` and `WAdm^{Noeth}` — from the five clauses of Stacks 0ANB, so
that for those classes each axiom reads as the source states it: a hypothesis on `A` and `B`
only.

## Main results

* `TopologicalRing.isCountablyWeaklyAdmissible_completionOver`: `WAdm^{count}` is closed under
  the completion of Stacks 0AN6, by the clauses of Stacks 0ANB for weak admissibility and for
  countable generation of the neighbourhoods of zero.
* `TopologicalRing.isCountablyWeaklyAdmissible_of_ringEquiv` and
  `TopologicalRing.isNoetherianAdic_of_ringEquiv`: `WAdm^{count}` and `WAdm^{Noeth}` are
  invariant under an isomorphism of topological rings. This is the second closure condition the
  consumers of Situation 0CBA need: the finite-product clause of the chart-map predicates of
  Stacks 0ANG asks for membership of the *product* of the chart rings of a covering, which is
  the completion of a single étale ring map only up to the bicontinuous isomorphism
  `TopologicalRing.CompletionOver.piRingEquiv`.
* `TopologicalRing.PropertyIsLocal'.localizationPreserves_countablyWeaklyAdmissible` and
  `TopologicalRing.PropertyIsLocal'.faithfullyFlatDescent_countablyWeaklyAdmissible`: axioms (1)
  and (2) of Situation 0CBA on `WAdm^{count}`, with no hypothesis on the completed corners.
* `TopologicalRing.PropertyIsLocal'.localizationPreserves_adicStar` and
  `TopologicalRing.PropertyIsLocal'.faithfullyFlatDescent_adicStar`: the same two axioms on
  `WAdm^{adic*}`, the class of Stacks 0ANH.
* `TopologicalRing.PropertyIsLocal'.localizationPreserves_noetherianAdic` and
  `TopologicalRing.PropertyIsLocal'.faithfullyFlatDescent_noetherianAdic`: the same two axioms on
  `WAdm^{Noeth}`, the class of Stacks 0ANI.

## Implementation notes

The weak admissibility of `A` and of `B` that the clauses of Stacks 0ANB need is not an extra
hypothesis here: it is carried by the localization diagram itself, as its fields
`weaklyAdmissibleA` and `weaklyAdmissibleB`.

For `WAdm^{Noeth}` the clause of Stacks 0ANB also needs the ring being completed to be
Noetherian, and that is where the étaleness of the horizontal map enters: an étale algebra is of
finite presentation, hence of finite type, so `A'` is Noetherian over the Noetherian ring `A`.
The other two classes are closed under completion along an arbitrary ring map.

These declarations are untagged. Stacks 0ANB is already registered on its five clauses in
`StacksFrontier/Topology/Algebra/AdicTopology/CompletionOver.lean` and
`StacksFrontier/Topology/Algebra/AdicTopology/CompletionOverNoetherian.lean`, and Stacks 0CBA on
`TopologicalRing.PropertyIsLocal'`; what is below is the composition of the two, not a further
clause of either.

## References

* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
* [Stacks Project, Tag 0ANB](https://stacks.math.columbia.edu/tag/0ANB)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public section

namespace TopologicalRing

universe u v

/-- The class `WAdm^{count}` of countably indexed weakly admissible topological rings is closed
under the completion of Stacks 0AN6: the completion of a ring `A` over a countably indexed
weakly admissible ring `B` is again one. This is the conjunction of two clauses of **Stacks
0ANB**, and needs nothing of the ring map `B →+* A`. -/
public theorem isCountablyWeaklyAdmissible_completionOver {B : Type u} {A : Type v}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B] [CommRing A]
    (f : B →+* A) (hB : IsCountablyWeaklyAdmissible B) :
    IsCountablyWeaklyAdmissible (CompletionOver f) :=
  ⟨completionOver_isWeaklyAdmissible f hB.1,
    completionOver_isCountablyGenerated_nhds_zero f hB.1 hB.2⟩

/-- The class `WAdm^{count}` is invariant under an isomorphism of topological rings: weak
admissibility transports by `TopologicalRing.isWeaklyAdmissible_of_ringEquiv`, and the
neighbourhoods of zero of the second ring are the image of those of the first under a
homeomorphism, so countable generation transports too. -/
public theorem isCountablyWeaklyAdmissible_of_ringEquiv {A C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (e : A ≃+* C) (he : Continuous e) (he' : Continuous e.symm)
    (hA : IsCountablyWeaklyAdmissible A) : IsCountablyWeaklyAdmissible C := by
  refine ⟨isWeaklyAdmissible_of_ringEquiv e he he' hA.1, ?_⟩
  have := hA.2
  have hnhds : nhds (0 : C) = Filter.map (e : A → C) (nhds (0 : A)) := by
    refine le_antisymm ?_ (he.tendsto' 0 0 (map_zero e))
    calc nhds (0 : C)
        = Filter.map (e : A → C) (Filter.map (e.symm : C → A) (nhds (0 : C))) := by
          rw [Filter.map_map]
          simp [Function.comp_def]
      _ ≤ Filter.map (e : A → C) (nhds (0 : A)) :=
          Filter.map_mono (he'.tendsto' 0 0 (map_zero e.symm))
  rw [hnhds]
  infer_instance

/-- The class `WAdm^{Noeth}` of Situation 0ANI is invariant under an isomorphism of topological
rings: adicness transports by `TopologicalRing.isAdic_of_ringEquiv` and being Noetherian is a
property of the underlying ring. -/
public theorem isNoetherianAdic_of_ringEquiv {A C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (e : A ≃+* C) (he : Continuous e) (he' : Continuous e.symm)
    (hA : IsNoetherianAdic A) : IsNoetherianAdic C := by
  have : IsNoetherianRing A := hA.2
  exact ⟨isAdic_of_ringEquiv e he he' hA.1, isNoetherianRing_of_ringEquiv A e⟩

namespace PropertyIsLocal'

variable {P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop}
  {A B A' B' : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [CommRing A'] [CommRing B']

/-- **Axiom (1) of Situation 0CBA on `WAdm^{count}`.** A property of arrows of `WAdm^{count}`
which is local ascends along a localization diagram as soon as its two lower corners are
countably indexed weakly admissible: the two completed corners are then so by **Stacks 0ANB**,
which is how the source reads the axiom. -/
public theorem localizationPreserves_countablyWeaklyAdmissible
    (hP : TopologicalRing.PropertyIsLocal' P IsCountablyWeaklyAdmissible)
    (D : LocalizationDiagram A B A' B')
    (hA : IsCountablyWeaklyAdmissible A) (hB : IsCountablyWeaklyAdmissible B)
    (h : P D.map) : P D.completedMap :=
  hP.localizationPreserves D hA hB (isCountablyWeaklyAdmissible_completionOver D.toA' hA)
    (isCountablyWeaklyAdmissible_completionOver D.toB' hB) h

/-- **Axiom (2) of Situation 0CBA on `WAdm^{count}`.** A property of arrows of `WAdm^{count}`
which is local descends along a localization diagram whose horizontal map on the source side is
faithfully flat, as soon as its two lower corners are countably indexed weakly admissible. -/
public theorem faithfullyFlatDescent_countablyWeaklyAdmissible
    (hP : TopologicalRing.PropertyIsLocal' P IsCountablyWeaklyAdmissible)
    (D : LocalizationDiagram A B A' B')
    (hA : IsCountablyWeaklyAdmissible A) (hB : IsCountablyWeaklyAdmissible B)
    (hff : D.toA'.FaithfullyFlat) (h : P D.completedMap) : P D.map :=
  hP.faithfullyFlatDescent D hA hB (isCountablyWeaklyAdmissible_completionOver D.toA' hA)
    (isCountablyWeaklyAdmissible_completionOver D.toB' hB) hff h

/-- **Axiom (1) of Situation 0CBA on `WAdm^{adic*}`.** A local property of arrows of
`WAdm^{adic*}` in the sense of Stacks 0ANH ascends along a localization diagram whose two lower
corners have a finitely generated ideal of definition: the completed corners have one too, by
the clause of **Stacks 0ANB** for that class, whose weak admissibility hypothesis is a field of
the diagram. -/
public theorem localizationPreserves_adicStar
    (hP : TopologicalRing.AdicStarPropertyIsLocal' P)
    (D : LocalizationDiagram A B A' B')
    (hA : ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I) (hB : ∃ I : Ideal B, I.FG ∧ _root_.IsAdic I)
    (h : P D.map) : P D.completedMap :=
  hP.localizationPreserves D hA hB
    (completionOver_exists_fg_isAdic D.toA' D.weaklyAdmissibleA hA)
    (completionOver_exists_fg_isAdic D.toB' D.weaklyAdmissibleB hB) h

/-- **Axiom (2) of Situation 0CBA on `WAdm^{adic*}`.** The descent axiom of Stacks 0ANH along a
localization diagram with faithfully flat horizontal map on the source side, with no hypothesis
on the completed corners. -/
public theorem faithfullyFlatDescent_adicStar
    (hP : TopologicalRing.AdicStarPropertyIsLocal' P)
    (D : LocalizationDiagram A B A' B')
    (hA : ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I) (hB : ∃ I : Ideal B, I.FG ∧ _root_.IsAdic I)
    (hff : D.toA'.FaithfullyFlat) (h : P D.completedMap) : P D.map :=
  hP.faithfullyFlatDescent D hA hB
    (completionOver_exists_fg_isAdic D.toA' D.weaklyAdmissibleA hA)
    (completionOver_exists_fg_isAdic D.toB' D.weaklyAdmissibleB hB) hff h

/-- The ring completed in the source-side corner of a localization diagram over a Noetherian
base is Noetherian: the horizontal map is étale, hence of finite presentation, hence of finite
type. -/
private theorem isNoetherianRing_toA' (D : LocalizationDiagram A B A' B')
    (hA : IsNoetherianRing A) : IsNoetherianRing A' := by
  let : Algebra A A' := D.toA'.toAlgebra
  have hetale : Algebra.Etale A A' := D.etaleA
  have : Algebra.FinitePresentation A A' := hetale.finitePresentation
  have : IsNoetherianRing A := hA
  exact Algebra.FiniteType.isNoetherianRing A A'

/-- The same for the target-side corner. -/
private theorem isNoetherianRing_toB' (D : LocalizationDiagram A B A' B')
    (hB : IsNoetherianRing B) : IsNoetherianRing B' := by
  let : Algebra B B' := D.toB'.toAlgebra
  have hetale : Algebra.Etale B B' := D.etaleB
  have : Algebra.FinitePresentation B B' := hetale.finitePresentation
  have : IsNoetherianRing B := hB
  exact Algebra.FiniteType.isNoetherianRing B B'

/-- **Axiom (1) of Situation 0CBA on `WAdm^{Noeth}`.** A local property of arrows of
`WAdm^{Noeth}` in the sense of Stacks 0ANI ascends along a localization diagram whose two lower
corners are adic and Noetherian: the completed corners are then adic and Noetherian by the
clause of **Stacks 0ANB** for that class, the rings being completed being Noetherian because
the horizontal maps of the diagram are étale. -/
public theorem localizationPreserves_noetherianAdic
    (hP : TopologicalRing.PropertyIsLocalNoetherian' P)
    (D : LocalizationDiagram A B A' B')
    (hA : TopologicalRing.IsAdic A ∧ IsNoetherianRing A)
    (hB : TopologicalRing.IsAdic B ∧ IsNoetherianRing B)
    (h : P D.map) : P D.completedMap :=
  hP.localizationPreserves D hA hB
    (completionOver_isNoetherianAdic D.toA' hA (isNoetherianRing_toA' D hA.2))
    (completionOver_isNoetherianAdic D.toB' hB (isNoetherianRing_toB' D hB.2)) h

/-- **Axiom (2) of Situation 0CBA on `WAdm^{Noeth}`.** The descent axiom of Stacks 0ANI along a
localization diagram with faithfully flat horizontal map on the source side, with no hypothesis
on the completed corners. -/
public theorem faithfullyFlatDescent_noetherianAdic
    (hP : TopologicalRing.PropertyIsLocalNoetherian' P)
    (D : LocalizationDiagram A B A' B')
    (hA : TopologicalRing.IsAdic A ∧ IsNoetherianRing A)
    (hB : TopologicalRing.IsAdic B ∧ IsNoetherianRing B)
    (hff : D.toA'.FaithfullyFlat) (h : P D.completedMap) : P D.map :=
  hP.faithfullyFlatDescent D hA hB
    (completionOver_isNoetherianAdic D.toA' hA (isNoetherianRing_toA' D hA.2))
    (completionOver_isNoetherianAdic D.toB' hB (isNoetherianRing_toB' D hB.2)) hff h

end PropertyIsLocal'

end TopologicalRing

end
