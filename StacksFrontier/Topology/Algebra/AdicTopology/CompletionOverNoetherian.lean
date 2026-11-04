module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical

/-!
# Completion over a Noetherian adic base

Let `B` be an object of `WAdm` and let `f : B →+* A` be a ring map, `A` carrying no topology.
The completion `CompletionOver f` of Tag 0AN6 is again an object of `WAdm`, and the full
subcategories of `WAdm` listed in Tag 0ANB are stable under the construction.  This file records
the last of those five clauses, the one for `WAdm^{Noeth}`: if `B` is adic and Noetherian and
the ring `A` being completed is Noetherian, then `CompletionOver f` is adic and Noetherian.

Adicness of the completion is the clause of the same lemma for `WAdm^{adic*}`, available as
`TopologicalRing.completionOver_exists_fg_isAdic`: an ideal of definition of a Noetherian ring is
finitely generated, so the hypothesis of that clause is met, and an ideal whose powers are a
basis of the neighbourhoods of zero is in particular an ideal of definition.  Noetherianity is
then Tag 0316 transported along `TopologicalRing.CompletionOver.adicCompletionRingEquiv`, which
identifies the completion over an adic base with the `IA`-adic completion of `A`.

## Main results

* `TopologicalRing.completionOver_isNoetherianAdic`: **Stacks 0ANB (5)**.
* `TopologicalRing.IsPreAdic.isWeaklyPreAdmissible` and
  `TopologicalRing.IsAdic.isWeaklyAdmissible`: `WAdm^{Noeth}` is a full subcategory of `WAdm`,
  which is what lets the clause for `WAdm^{adic*}` be applied to a Noetherian adic base.

## References

* [Stacks Project, Tag 0ANB](https://stacks.math.columbia.edu/tag/0ANB)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
-/

@[expose] public section

namespace TopologicalRing

universe u v

/-- A pre-adic topological ring is weakly pre-admissible: an ideal of definition is a weak ideal
of definition. -/
public lemma IsPreAdic.isWeaklyPreAdmissible {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsPreAdic R) : IsWeaklyPreAdmissible R :=
  let ⟨I, hdef, _⟩ := hR
  ⟨I, isWeakIdealOfDefinition_of_isIdealOfDefinition hdef⟩

/-- An adic topological ring is weakly admissible, so `WAdm^{Noeth}` is a full subcategory
of `WAdm`. -/
public lemma IsAdic.isWeaklyAdmissible {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (hR : IsAdic R) : IsWeaklyAdmissible R :=
  ⟨hR.1.isWeaklyPreAdmissible, hR.2.2, hR.2.1⟩

/-- **Stacks 0ANB (5).** Let `B` be an adic Noetherian topological ring and let `f : B →+* A` be
a ring map, `A` carrying no topology.  If `A` is Noetherian then the completion of `A` over `B`,
the limit of the rings `A ⧸ JA` over the weak ideals of definition `J` of `B`, is again an adic
Noetherian topological ring.

The topology of the completion is adic by the clause of this lemma for `WAdm^{adic*}`, which
applies because an ideal of definition of the Noetherian ring `B` is finitely generated.  The
completion is then the `IA`-adic completion of `A` for `I` an ideal of definition of `B`, hence
Noetherian by Tag 0316. -/
@[stacks 0ANB "completion_in_sub_noetherian"]
public theorem completionOver_isNoetherianAdic {B : Type u} {A : Type v}
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing A] (f : B →+* A) (hB : IsNoetherianAdic B) (hA : IsNoetherianRing A) :
    IsNoetherianAdic (CompletionOver f) := by
  obtain ⟨hBadic, hBnoeth⟩ := hB
  obtain ⟨I, hdef, hIadic⟩ := hBadic.1
  have hBnoeth' : IsNoetherianRing B := hBnoeth
  obtain ⟨J, -, hJadic⟩ := completionOver_exists_fg_isAdic f hBadic.isWeaklyAdmissible
    ⟨I, IsNoetherian.noetherian I, hIadic⟩
  have hAnoeth : IsNoetherianRing A := hA
  refine ⟨⟨⟨J, isIdealOfDefinition_of_isAdic hJadic, hJadic⟩, inferInstance, inferInstance⟩, ?_⟩
  exact isNoetherianRing_of_ringEquiv (AdicCompletion (I.map f) A)
    (CompletionOver.adicCompletionRingEquiv hdef hIadic f).symm

end TopologicalRing

end
