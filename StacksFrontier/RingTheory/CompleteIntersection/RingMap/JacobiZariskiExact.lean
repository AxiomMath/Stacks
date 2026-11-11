module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.JacobiZariski
public import StacksFrontier.RingTheory.NaiveCotangent.JacobiZariskiSixTerm

/-!
# The exact rows of the Jacobi-Zariski diagram of a local complete intersection

Let `A → B → C` be ring maps with `B → C` a local complete intersection, let
`α : A[x_s] → B` be a presentation with kernel `I`, let `β : B[y₁, …, yₘ] → C` be a finite
presentation with kernel `J`, and let `γ = β.comp α : A[x_s, y_t] → C` be the induced
presentation, with kernel `K`. The canonical commutative diagram
```
0 ⟶ C ⊗_B Ω_{A[x]/A} ⟶ Ω_{A[x,y]/A} ⊗ C ⟶ Ω_{B[y]/B} ⊗ C ⟶ 0
          ↑                    ↑                   ↑
0 ⟶   C ⊗_B I/I²     ⟶       K/K²        ⟶      J/J²      ⟶ 0
```
has exact rows, and the six-term sequence of Stacks 00S2 extends by a zero on the left:
```
0 → H₁(NL(α) ⊗_B C) → H₁(NL(γ)) → H₁(NL(β)) → H₀(NL(α) ⊗_B C) → H₀(NL(γ)) → H₀(NL(β)) → 0
```
is exact.

## Main results

* `NaiveCotangent.jacobiZariski_exact_of_isLocalCompleteIntersection`: **Stacks 07D4**.

## Implementation notes

The diagram is the pair of chain maps `NaiveCotangent.nlToComp` and `NaiveCotangent.nlOfComp`,
and its two squares are their commutativity fields. The top row is Mathlib's
`Algebra.Generators.CotangentSpace.map_toComp_injective`,
`Algebra.Generators.CotangentSpace.exact` and
`Algebra.Generators.CotangentSpace.map_ofComp_surjective`. In the bottom row, exactness in the
middle and on the right is Mathlib's `Algebra.Generators.Cotangent.exact` and
`Algebra.Generators.Cotangent.surjective_map_ofComp`, and injectivity on the left is
`RingHom.cotangentMap_toComp_injective_of_isLocalCompleteIntersection`. The six-term sequence is
`NaiveCotangent.jacobiZariski_sixTerm_exact` (Stacks 00S2), and its zero on the left is
inherited from the injectivity in degree `1`, `H₁` being a submodule of the degree-`1` term.

## References

* [Stacks Project, Tag 07D4](https://stacks.math.columbia.edu/tag/07D4)
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2)
-/

@[expose] public section

universe w u₁ u₂ u₃

open Algebra Function

namespace NaiveCotangent

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- **Stacks 07D4.** Let `A → B → C` be ring maps with `B → C` a local complete intersection,
let `α : A[x_s] → B` be a presentation with kernel `I`, let `β : B[y₁, …, yₘ] → C` be a
presentation with kernel `J`, and let `γ = β.comp α : A[x_s, y_t] → C` be the induced
presentation, with kernel `K`. Then the canonical diagram, whose vertical maps are the
differentials of `NL(α) ⊗_B C`, `NL(γ)` and `NL(β)`, commutes, and both of its rows
```
0 ⟶ C ⊗_B Ω_{A[x]/A} ⟶ Ω_{A[x,y]/A} ⊗ C ⟶ Ω_{B[y]/B} ⊗ C ⟶ 0
0 ⟶   C ⊗_B I/I²     ⟶       K/K²        ⟶      J/J²      ⟶ 0
```
are exact. In particular the six-term sequence of Stacks 00S2 can be completed with a zero on
the left: the sequence
```
0 → H₁(NL(α) ⊗_B C) → H₁(NL(γ)) → H₁(NL(β)) --δ--> H₀(NL(α) ⊗_B C) → H₀(NL(γ)) → H₀(NL(β)) → 0
```
is exact, that is
`0 → H₁(NL_{B/A} ⊗_B C) → H₁(L_{C/A}) → H₁(L_{C/B}) → Ω_{B/A} ⊗_B C → Ω_{C/A} → Ω_{C/B} → 0`,
with `δ` the connecting map `NaiveCotangent.jacobiZariskiConnecting`. -/
@[stacks 07D4]
theorem jacobiZariski_exact_of_isLocalCompleteIntersection {S : Type w} {m : ℕ}
    (α : Generators A B S) (β : Generators B C (Fin m))
    (h : RingHom.IsLocalCompleteIntersection (algebraMap B C)) :
    -- the two squares of the canonical diagram commute
    ((NL (β.comp α)).d ∘ₗ (nlToComp β α).f₁ = (nlToComp β α).f₀ ∘ₗ (nlBaseChange C α).d ∧
      (NL β).d ∘ₗ (nlOfComp β α).f₁ = (nlOfComp β α).f₀ ∘ₗ (NL (β.comp α)).d) ∧
    -- the row of Kähler differentials is exact
    (Injective (nlToComp β α).f₀ ∧ Exact (nlToComp β α).f₀ (nlOfComp β α).f₀ ∧
      Surjective (nlOfComp β α).f₀) ∧
    -- the row of conormal modules is exact
    (Injective (nlToComp β α).f₁ ∧ Exact (nlToComp β α).f₁ (nlOfComp β α).f₁ ∧
      Surjective (nlOfComp β α).f₁) ∧
    -- the six-term sequence of Stacks 00S2, completed with a zero on the left, is exact
    (Injective (nlToComp β α).onH₁ ∧
      Exact (nlToComp β α).onH₁ (nlOfComp β α).onH₁ ∧
      Exact (nlOfComp β α).onH₁ (jacobiZariskiConnecting β α) ∧
      Exact (jacobiZariskiConnecting β α) (nlToComp β α).onH₀ ∧
      Exact (nlToComp β α).onH₀ (nlOfComp β α).onH₀ ∧
      Surjective (nlOfComp β α).onH₀) := by
  have hinj : Injective (nlToComp β α).f₁ :=
    RingHom.cotangentMap_toComp_injective_of_isLocalCompleteIntersection α β h
  exact ⟨⟨(nlToComp β α).comm, (nlOfComp β α).comm⟩,
    ⟨Generators.CotangentSpace.map_toComp_injective β α, Generators.CotangentSpace.exact β α,
      Generators.CotangentSpace.map_ofComp_surjective β α⟩,
    ⟨hinj, Generators.Cotangent.exact β α, Generators.Cotangent.surjective_map_ofComp β α⟩,
    fun x y hxy => Subtype.ext (hinj (congrArg Subtype.val hxy)),
    jacobiZariski_sixTerm_exact β α⟩

end NaiveCotangent

end
