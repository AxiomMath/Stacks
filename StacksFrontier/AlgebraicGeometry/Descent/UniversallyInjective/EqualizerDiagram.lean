module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import StacksCore.Tactic.StacksAttribute

/-!
# Equalizer diagrams

Fix an ambient category. For two morphisms `g₁, g₂ : B ⟶ C`, an equalizer of `g₁` and `g₂` is
a morphism `f : A ⟶ B` which satisfies `g₁ ∘ f = g₂ ∘ f` and is universal for this property:
every `e : A' ⟶ B` with `g₁ ∘ e = g₂ ∘ e` is `e = f ∘ d` for a unique `d : A' ⟶ A`. One then
says that the displayed diagram
```
      f      g₁
  A ----> B ====> C
             g₂
```
is an equalizer. Reversing the arrows gives the dual notion of a coequalizer, which is
`CategoryTheory.Limits.IsColimit` on a `CategoryTheory.Limits.Cofork`.

## Main definitions

* `Stacks.Descent.IsEqualizerDiagram f g₁ g₂` says that the displayed diagram is an equalizer.

## Main results

* `Stacks.Descent.isEqualizerDiagram_iff_nonempty_isLimit` identifies the notion with the
  statement that the fork on `f` is a limit cone, which is how Mathlib records an equalizer.
* `Stacks.Descent.IsEqualizerDiagram.of_isSplitEqualizer`: a split equalizer is an equalizer.

## Implementation notes

The predicate is stated with the universal property spelled out as a unique factorisation,
which is the formulation used in the source, rather than as a limit cone. The two are
interchangeable through `CategoryTheory.Limits.Fork.IsLimit.existsUnique` and
`CategoryTheory.Limits.Fork.IsLimit.ofExistsUnique`; both directions are recorded below. The
ambient category is written `𝒞` so that the three objects of the diagram can keep the names
`A`, `B`, `C` they have in the source.

## References

* [Stacks Project, Tag 08WG](https://stacks.math.columbia.edu/tag/08WG)
-/

@[expose] public section

universe v u

namespace Stacks.Descent

open CategoryTheory CategoryTheory.Limits

variable {𝒞 : Type u} [Category.{v} 𝒞] {A B C : 𝒞}

/-- The diagram `A ⟶ B ⇉ C` consisting of `f : A ⟶ B` and a parallel pair `g₁, g₂ : B ⟶ C`
*is an equalizer*: the two composites `f ≫ g₁` and `f ≫ g₂` agree, and `f` is universal for
that property, meaning that every `e : A' ⟶ B` equalizing `g₁` and `g₂` factors as `e = d ≫ f`
for a unique `d : A' ⟶ A`. -/
@[stacks 08WG "the displayed diagram is an equalizer"]
structure IsEqualizerDiagram (f : A ⟶ B) (g₁ g₂ : B ⟶ C) : Prop where
  /-- The two composites along the diagram agree. -/
  comp_eq : f ≫ g₁ = f ≫ g₂
  /-- Every morphism to `B` equalizing `g₁` and `g₂` factors uniquely through `f`. -/
  existsUnique_factorisation {A' : 𝒞} (e : A' ⟶ B) (he : e ≫ g₁ = e ≫ g₂) :
    ∃! d : A' ⟶ A, d ≫ f = e

variable {f : A ⟶ B} {g₁ g₂ : B ⟶ C}

/-- An equalizer diagram presents `f` as a limit of the parallel pair `g₁, g₂`. -/
noncomputable def IsEqualizerDiagram.isLimit (h : IsEqualizerDiagram f g₁ g₂) :
    IsLimit (Fork.ofι f h.comp_eq) :=
  Fork.IsLimit.ofExistsUnique fun s => h.existsUnique_factorisation s.ι s.condition

/-- A fork on `g₁, g₂` which is a limit cone is an equalizer diagram. -/
theorem IsEqualizerDiagram.of_isLimit (w : f ≫ g₁ = f ≫ g₂) (hl : IsLimit (Fork.ofι f w)) :
    IsEqualizerDiagram f g₁ g₂ where
  comp_eq := w
  existsUnique_factorisation e he := Fork.IsLimit.existsUnique hl e he

/-- Being an equalizer diagram is exactly being a limit fork, which is how an equalizer is
recorded in Mathlib. -/
theorem isEqualizerDiagram_iff_nonempty_isLimit (w : f ≫ g₁ = f ≫ g₂) :
    IsEqualizerDiagram f g₁ g₂ ↔ Nonempty (IsLimit (Fork.ofι f w)) :=
  ⟨fun h => ⟨h.isLimit⟩, fun ⟨hl⟩ => .of_isLimit w hl⟩

/-- A split equalizer is an equalizer: the auxiliary retractions factor `e` through `f` as
`e = (e ≫ h) ≫ f`, and that factorisation is forced. -/
theorem IsEqualizerDiagram.of_isSplitEqualizer (q : IsSplitEqualizer g₁ g₂ f) :
    IsEqualizerDiagram f g₁ g₂ :=
  .of_isLimit q.condition q.isEqualizer

end Stacks.Descent
