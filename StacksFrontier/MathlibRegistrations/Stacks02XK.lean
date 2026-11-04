module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import StacksCore.Tactic.StacksAttribute

/-! Mathlib already states Stacks tag 02XK as `CategoryTheory.Functor.IsStronglyCartesian`.

The Stacks definition characterizes a strongly cartesian morphism `φ : y ⟶ x` over a
functor `p : 𝒮 ⥤ 𝒞` by bijectivity of
  `Mor_𝒮(z, y) → Mor_𝒮(z, x) ×_{Mor_𝒞(p z, p x)} Mor_𝒞(p z, p y)`.
Mathlib's `IsStronglyCartesian` packages the equivalent existence-and-uniqueness
universal property (see `CategoryTheory.Functor.IsStronglyCartesian.universal_property`). -/

@[expose] public section
