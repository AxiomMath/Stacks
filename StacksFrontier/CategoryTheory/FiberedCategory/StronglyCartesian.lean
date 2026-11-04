module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksCore.Tactic.StacksAttribute

/-! # Stacks 02XL: stability properties of strongly cartesian morphisms

For a functor `p : 𝒮 ⥤ 𝒞`: a composite of strongly cartesian morphisms is strongly cartesian;
every isomorphism of `𝒮` is strongly cartesian over its image under `p`; and a strongly
cartesian morphism lying over an isomorphism of `𝒞` is itself an isomorphism.
-/

@[expose] public section

open CategoryTheory Functor

namespace Stacks.StronglyCartesian

/-- The conjunction of the three stability claims of Stacks 02XL for a functor `p : 𝒮 ⥤ 𝒞`:
strongly cartesian morphisms are closed under composition; every isomorphism of `𝒮` is
strongly cartesian over its `p`-image; a strongly cartesian morphism lying over an
isomorphism of `𝒞` is itself an isomorphism. -/
def StronglyCartesianStability {𝒞 : Type*} [Category 𝒞] {𝒮 : Type*} [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) : Prop :=
    (∀ {a b c : 𝒮} {R S T : 𝒞} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}
        [p.IsStronglyCartesian f φ] [p.IsStronglyCartesian g ψ],
        p.IsStronglyCartesian (f ≫ g) (φ ≫ ψ))
    ∧ (∀ {a b : 𝒮} (φ : a ⟶ b) [IsIso φ], p.IsStronglyCartesian (p.map φ) φ)
    ∧ (∀ {a b : 𝒮} {f : p.obj a ⟶ p.obj b} (φ : a ⟶ b) [p.IsStronglyCartesian f φ] [IsIso f],
        IsIso φ)

/-- **Stacks 02XL.** All three claims of `StronglyCartesianStability` hold for every `p : 𝒮 ⥤ 𝒞`,
each supplied by Mathlib: `Functor.IsStronglyCartesian.comp`, `.of_isIso` and
`.isIso_of_base_isIso`. -/
@[stacks 02XL, sga "1 VI 6.12" "iso ⇒ Cartesian"]
theorem isStronglyCartesian_conditions_hold {𝒞 : Type*} [Category 𝒞] {𝒮 : Type*} [Category 𝒮]
    (p : 𝒮 ⥤ 𝒞) : StronglyCartesianStability p := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c R S T f g φ ψ _ _
    exact IsStronglyCartesian.comp p
  · intro a b φ _
    exact IsStronglyCartesian.of_isIso p (p.map φ) φ
  · intro a b f φ _ _
    exact IsStronglyCartesian.isIso_of_base_isIso p f φ

end Stacks.StronglyCartesian
