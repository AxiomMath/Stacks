module

public import Mathlib.RingTheory.Extension.Cotangent.Basis
public import StacksCore.Tactic.StacksAttribute

/-!
# Presentations whose conormal module is free on the relations

Let `S` be a finitely presented `R`-algebra admitting a presentation
`S = R[x₁, …, xₙ]/I` whose conormal module `I/I²` is free over `S`. Then `S` admits a
presentation `S = R[y₁, …, y_m]/(f₁, …, f_c)` whose conormal module is free with basis the
classes of `f₁, …, f_c`.

## Main results

- `Algebra.exists_presentation_basis_cotangent_of_free_cotangent`: the existence statement
  above, in the form of an `Algebra.Presentation` with finite variable and relation index
  types together with a basis of its conormal module sending each index to the class of the
  corresponding relation.

## Implementation notes

The conormal module `I/I²` of a presentation is `Algebra.Extension.Cotangent` of its
associated extension, and a presentation `S = R[y₁, …, y_m]/(f₁, …, f_c)` is an
`Algebra.Presentation R S ι σ` with `ι` and `σ` finite, as in `Algebra.IsStandardSmooth`.

## References

- [Stacks, Tag 07CF](https://stacks.math.columbia.edu/tag/07CF)
-/

@[expose] public section

namespace Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- A finitely presented `R`-algebra `S` admitting a presentation `S = R[x₁, …, xₙ]/I` with
`I/I²` free over `S` admits a presentation `S = R[y₁, …, y_m]/(f₁, …, f_c)` whose conormal
module is free with basis the classes of `f₁, …, f_c`. -/
@[stacks 07CF]
theorem exists_presentation_basis_cotangent_of_free_cotangent [FinitePresentation R S]
    (h : ∃ (ι : Type) (_ : Finite ι) (P : Generators R S ι),
      Module.Free S P.toExtension.Cotangent) :
    ∃ (ι σ : Type) (_ : Finite ι) (_ : Finite σ) (P : Presentation R S ι σ)
      (b : Module.Basis σ S P.toExtension.Cotangent),
      ∀ r, b r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩ := by
  obtain ⟨ι, hι, P, hfree⟩ := h
  have : Finite ι := hι
  have : Module.Free S P.toExtension.Cotangent := hfree
  obtain ⟨P', b, -, hb⟩ := P.exists_presentation_of_free_cotangent
  exact ⟨_, _, inferInstance, inferInstance, P', b, hb⟩

end Algebra
