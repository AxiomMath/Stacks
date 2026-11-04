module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties

/-!
# The cancellation property for morphism properties of `WAdm^{adic*}`

Let `P` be a local property of morphisms of `WAdm^{adic*}`, the full subcategory of weakly
admissible topological rings whose topology is the adic topology of a finitely generated
ideal.  Then `P` *has the cancellation property* when, for every pair of composable arrows
`C → B → A` of `WAdm^{adic*}`, the property of the composite `C → A` together with the
property of `C → B` forces the property of `B → A`.

Objects of `WAdm^{adic*}` are encoded, as elsewhere in this chapter, by the conjunction of
`TopologicalRing.IsWeaklyAdmissible` with the existence of a finitely generated ideal defining
the topology; arrows are continuous ring homomorphisms.  No countability is imposed, since
`WAdm^{adic*}` imposes none.

Locality of `P` is not part of the predicate below.  It is the ambient hypothesis of the
source statement rather than a clause of the defined notion, and keeping the two apart matches
the Noetherian twin `TopologicalRing.HasNoetherianCancellationProperty` and the way its
consumers supply locality as a separate hypothesis.

## Main definitions

* `TopologicalRing.HasAdicStarCancellationProperty`: **Stacks 0GBN**.

## References

* [Stacks Project, Tag 0GBN](https://stacks.math.columbia.edu/tag/0GBN)
* [Stacks Project, Tag 0ANH](https://stacks.math.columbia.edu/tag/0ANH)
* [Stacks Project, Tag 0GBP](https://stacks.math.columbia.edu/tag/0GBP)
-/

@[expose] public section

namespace TopologicalRing

universe u

/-- **Cancellation for a morphism property of `WAdm^{adic*}`** (Stacks 0GBN).  Given arrows
`f : B →+* A` and `g : C →+* B` of `WAdm^{adic*}` — continuous homomorphisms of weakly
admissible topological rings each carrying the adic topology of a finitely generated ideal —
the property of the composite `C → A` and the property of `C → B` together imply the property
of `B → A`. -/
@[stacks 0GBN "the cancellation property"]
public abbrev HasAdicStarCancellationProperty
    (P : ∀ {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [CommRing A]
      [TopologicalSpace A] [IsTopologicalRing A], (B →+* A) → Prop) : Prop :=
  ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (f : B →+* A) (g : C →+* B),
    TopologicalRing.IsWeaklyAdmissible A → (∃ I : Ideal A, I.FG ∧ _root_.IsAdic I) →
    TopologicalRing.IsWeaklyAdmissible B → (∃ I : Ideal B, I.FG ∧ _root_.IsAdic I) →
    TopologicalRing.IsWeaklyAdmissible C → (∃ I : Ideal C, I.FG ∧ _root_.IsAdic I) →
    Continuous f → Continuous g →
    ((P (f.comp g) ∧ P g) → P f)

end TopologicalRing

end
