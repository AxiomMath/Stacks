module

public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.JacobiZariski
public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiSixTerm

/-!
# The Jacobi--Zariski sequence for a filtered colimit of local complete intersections

Let `A → B → C` be ring maps with `B → C` a filtered colimit of local complete intersection
homomorphisms, let `α : A[x_s] → B` and `β : B[y_t] → C` be presentations with kernels `I` and
`J`, and let `γ = β.comp α : A[x_s, y_t] → C` be the induced presentation, with kernel `K`.
Stacks 07D5 asserts that the whole conclusion of Stacks 07D4 holds: in the canonical
commutative diagram
```
0 ⟶ C ⊗_B Ω_{A[x]/A} ⟶ Ω_{A[x,y]/A} ⊗ C ⟶ Ω_{B[y]/B} ⊗ C ⟶ 0
          ↑                    ↑                  ↑
0 ⟶   C ⊗_B I/I²     ⟶       K/K²        ⟶      J/J²      ⟶ 0
```
both rows are exact, and the Jacobi--Zariski sequence extends with a zero on the left to the
exact sequence
```
0 → H₁(NL(α) ⊗_B C) → H₁(NL(γ)) → H₁(NL(β)) → H₀(NL(α) ⊗_B C) → H₀(NL(γ)) → H₀(NL(β)) → 0,
```
that is `0 → H₁(NL_{B/A} ⊗_B C) → H₁(L_{C/A}) → H₁(L_{C/B}) → C ⊗_B Ω_{B/A} → Ω_{C/A} →
Ω_{C/B} → 0` in the source's notation.

## Main results

* `RingHom.jacobiZariski_exact_of_isFilteredColimit_isLocalCompleteIntersection`: Stacks 07D5,
  both exact rows of the diagram and the seven-term exact sequence.

## Implementation notes

The colimit is encoded as in
`RingHom.cotangentMap_toComp_injective_of_isFilteredColimit_isLocalCompleteIntersection`: a
`RingMapSystemUnbundled` over a nonempty directed preorder together with ring equivalences of its
two direct limits with `B` and `C` and a commuting square. The only assertion not already part
of Stacks 00S2 (`NaiveCotangent.jacobiZariski_sixTerm_exact`) or of Mathlib's description of the
two rows is the injectivity of `C ⊗_B I/I² → K/K²`, which is that theorem; injectivity on `H₁`
follows because `H₁` is a submodule of the degree-`1` term. As for 00S2 in this library, the
sequence is stated for the naive cotangent complexes of the three presentations of the source's
proof; their homology is the presentation-independent one by Stacks 00S1.

## References

* [Stacks Project, Tag 07D5](https://stacks.math.columbia.edu/tag/07D5)
* [Stacks Project, Tag 07D4](https://stacks.math.columbia.edu/tag/07D4)
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2)
-/

@[expose] public section

namespace RingHom

universe w w' u₁ u₂ u₃ u₄ u₅

open Algebra Function NaiveCotangent

/-- **Stacks 07D5.** Let `A → B → C` be ring maps and suppose that `B → C` is a filtered
colimit of local complete intersection homomorphisms, exhibited by a directed system `sys` of
ring maps each of which is a local complete intersection, together with `eB`, `eC` and `hcomm`
identifying the system's colimit map with `B → C`. Let `α : A[x_s] → B` and `β : B[y_t] → C` be
presentations and `γ = β.comp α` the induced presentation of `C` over `A`. Then the conclusion
of Stacks 07D4 holds:

* the degree-`0` row `0 → C ⊗_B Ω_{A[x]/A} → Ω_{A[x,y]/A} ⊗ C → Ω_{B[y]/B} ⊗ C → 0` and the
  degree-`1` row `0 → C ⊗_B I/I² → K/K² → J/J² → 0` of the canonical diagram are exact;
* the sequence
  `0 → H₁(NL(α) ⊗_B C) → H₁(NL(γ)) → H₁(NL(β)) → H₀(NL(α) ⊗_B C) → H₀(NL(γ)) → H₀(NL(β)) → 0`
  is exact, its connecting map being `NaiveCotangent.jacobiZariskiConnecting β α`. -/
@[stacks 07D5 "The complete conclusion of 07D4 for a filtered colimit of lci maps: both exact
rows of the conormal/differential diagram and the seven-term Jacobi-Zariski sequence with a zero
on the left, for the naive cotangent complexes of the three presentations."]
public theorem jacobiZariski_exact_of_isFilteredColimit_isLocalCompleteIntersection
    {A : Type u₁} {B : Type u₂} [CommRing A] [CommRing B] [Algebra A B]
    {C : Type u₃} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {S : Type w} {T : Type w'} (α : Generators A B S) (β : Generators B C T)
    {J : Type u₄} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (sys : RingMapSystemUnbundled.{u₅} J)
    (eB : sys.Rinf ≃+* B) (eC : sys.Sinf ≃+* C)
    (hcomm : eC.toRingHom.comp sys.gInf = (algebraMap B C).comp eB.toRingHom)
    (h : ∀ i : J, RingHom.IsLocalCompleteIntersection (sys.g i)) :
    (Injective (nlToComp β α).f₀ ∧ Exact (nlToComp β α).f₀ (nlOfComp β α).f₀ ∧
        Surjective (nlOfComp β α).f₀) ∧
      (Injective (nlToComp β α).f₁ ∧ Exact (nlToComp β α).f₁ (nlOfComp β α).f₁ ∧
        Surjective (nlOfComp β α).f₁) ∧
      Injective (nlToComp β α).onH₁ ∧
      Exact (nlToComp β α).onH₁ (nlOfComp β α).onH₁ ∧
      Exact (nlOfComp β α).onH₁ (jacobiZariskiConnecting β α) ∧
      Exact (jacobiZariskiConnecting β α) (nlToComp β α).onH₀ ∧
      Exact (nlToComp β α).onH₀ (nlOfComp β α).onH₀ ∧
      Surjective (nlOfComp β α).onH₀ := by
  have hinj : Injective (nlToComp β α).f₁ :=
    cotangentMap_toComp_injective_of_isFilteredColimit_isLocalCompleteIntersection
      α β sys eB eC hcomm h
  exact ⟨⟨Generators.CotangentSpace.map_toComp_injective β α,
      Generators.CotangentSpace.exact β α, Generators.CotangentSpace.map_ofComp_surjective β α⟩,
    ⟨hinj, Generators.Cotangent.exact β α, Generators.Cotangent.surjective_map_ofComp β α⟩,
    fun x y hxy ↦ Subtype.ext (hinj (congrArg Subtype.val hxy)),
    jacobiZariski_sixTerm_exact β α⟩

end RingHom
