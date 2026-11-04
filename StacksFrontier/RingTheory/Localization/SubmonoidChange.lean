module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Shrinking the submonoid of a localization of modules

Whether a map of modules is a localization at a submonoid `T` depends on `T` only through how
its elements *act*. So if every element of `T` acts on both modules exactly as some element of a
smaller submonoid `T₀ ≤ T` does, the map is already a localization at `T₀`.

The situation this is for: a module annihilated by a power of an ideal `J`. An element of the
`J`-adic completion `A = R^∧` outside a prime `𝔮` over `𝔭` agrees modulo `JⁿA` with the image of
an element of `R` outside `𝔭`, so on a module annihilated by `JⁿA` the two act identically. A
localization at `𝔮`'s complement is then a localization at the image of `𝔭`'s complement, and
`IsLocalizedModule.restrictScalars` carries that down to a localization at `𝔭`'s complement
over `R` itself. That is what identifies the completed stalk of a coherent adic system with the
completion of a localization, level by level.

## Main results

* `IsLocalizedModule.of_le_of_smul_eq` — a localization at `T` is a localization at `T₀ ≤ T`
  when every element of `T` acts as one of `T₀`.

## Implementation notes

The hypothesis asks for the agreement on both modules, because the three conditions defining
`IsLocalizedModule` live on both: surjectivity of the denominators is a statement about the
target and the cancellation condition is one about the source.

No declaration here carries a `stacks` attribute: this is substrate, not the content of a tag.
-/

@[expose] public section

namespace IsLocalizedModule

variable {A : Type*} [CommRing A] {X Y : Type*} [AddCommGroup X] [Module A X]
  [AddCommGroup Y] [Module A Y]

/-- **A localization at `T` is a localization at a smaller submonoid `T₀` whose elements realize
all the actions of `T`.**

Being a localization at `T` constrains `T` only through the action of its elements: the
denominators that must become invertible, the denominators that must suffice to write every
element of the target, and the denominators that must witness every identification in the
source. If each `t ∈ T` acts on `X` and on `Y` exactly as some `t₀ ∈ T₀` does, each of the three
can be re-read with that `t₀`. -/
public theorem of_le_of_smul_eq (T T₀ : Submonoid A) (g : X →ₗ[A] Y) [IsLocalizedModule T g]
    (hle : T₀ ≤ T)
    (hsmul : ∀ t ∈ T, ∃ t₀ ∈ T₀,
      (∀ x : X, t • x = t₀ • x) ∧ (∀ y : Y, t • y = t₀ • y)) :
    IsLocalizedModule T₀ g where
  map_units t₀ := IsLocalizedModule.map_units g ⟨(t₀ : A), hle t₀.2⟩
  surj y := by
    obtain ⟨⟨x, t⟩, ht⟩ := IsLocalizedModule.surj T g y
    obtain ⟨t₀, ht₀, -, hy⟩ := hsmul (t : A) t.2
    refine ⟨⟨x, ⟨t₀, ht₀⟩⟩, ?_⟩
    simp only [Submonoid.smul_def] at ht ⊢
    rw [← hy]
    exact ht
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g) e
    obtain ⟨t₀, ht₀, hx, -⟩ := hsmul (c : A) c.2
    refine ⟨⟨t₀, ht₀⟩, ?_⟩
    simp only [Submonoid.smul_def] at hc ⊢
    rw [← hx x₁, ← hx x₂]
    exact hc

end IsLocalizedModule

end
