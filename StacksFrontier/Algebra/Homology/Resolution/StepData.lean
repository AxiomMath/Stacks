module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# One step of a descending resolution by objects of a class

A bounded above cochain complex `X` in an abelian category is resolved by objects of a class
`R : ObjectProperty A` degree by degree downwards. One step of that induction, passing from a
layer `Y₁` in degree `j` to a new layer in degree `i`, produces: the new layer `Y₀`, a witness
that it lies in `R`, a differential `d₀ : Y₀ ⟶ Y₁` composing to zero with the previous one, a map
`f₀ : Y₀ ⟶ Xⁱ` commuting with the differentials, a witness that `Y₀` covers the degree-`i`
cohomology of `X`, and a witness that every cocycle of `Y₁` whose image in `X` is a boundary
becomes a boundary of `d₀` after a refinement. `StepData` is that package.

The class `R` enters only through the field asserting that the new layer lies in it, so the
structure needs no hypothesis on `R` at all: the Serre-class assumptions belong to the lemmas
that *construct* a step, which differ from one development to the next, and are stated there.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.Homology.BoundedAboveResolution

variable {A : Type u} [Category.{v} A] [Abelian A] (R : ObjectProperty A)
  (X : CochainComplex A ℤ)

/-- The data produced by one step of the descending induction: an object `Y₀` of the ambient
class, a differential `d₀` into the previous layer, a map `f₀` to the degree-`i` term of `X`
commuting with the differentials, a witness that `Y₀` covers the degree-`i` cohomology of `X`,
and the property that every cocycle of the previous layer whose image in `X` is a boundary is,
up to refinement, a boundary of `d₀`. -/
structure StepData (i j : ℤ) {Y₁ Y₂ : A} (d₁ : Y₁ ⟶ Y₂) (f₁ : Y₁ ⟶ X.X j) where
  /-- The new layer. -/
  Y₀ : A
  /-- The new layer lies in the ambient class. -/
  hY₀ : R Y₀
  /-- The differential into the previous layer. -/
  d₀ : Y₀ ⟶ Y₁
  /-- The map to the degree-`i` term of `X`. -/
  f₀ : Y₀ ⟶ X.X i
  /-- The composite of two consecutive differentials vanishes. -/
  zero : d₀ ≫ d₁ = 0
  /-- The maps to `X` commute with the differentials. -/
  comm : f₀ ≫ X.d i j = d₀ ≫ f₁
  /-- The new layer covers the degree-`i` cohomology of `X`. -/
  epiH : ∃ (C : A) (γ : C ⟶ Y₀) (c : C ⟶ X.cycles i), γ ≫ d₀ = 0 ∧
    c ≫ X.iCycles i = γ ≫ f₀ ∧ Epi (c ≫ X.homologyπ i)
  /-- Cocycles of the previous layer which become boundaries in `X` are, up to refinement,
  boundaries of `d₀`. -/
  cover : ∀ ⦃T : A⦄ (t : T ⟶ Y₁), t ≫ d₁ = 0 → (∃ u : T ⟶ X.X i, t ≫ f₁ = u ≫ X.d i j) →
    ∃ (T' : A) (p : T' ⟶ T) (_ : Epi p) (s : T' ⟶ Y₀), p ≫ t = s ≫ d₀

end Stacks.Homology.BoundedAboveResolution

end
