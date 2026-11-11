module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Homomorphisms out of a localized module

For a localization `f : M →ₗ[R] M'` of `M` at `S`, and a module `N` on which every element of
`S` acts invertibly, precomposition with `f` is a bijection `Hom_R(M', N) → Hom_R(M, N)`.
-/

@[expose] public section

/-- Let `S ⊆ R` be a multiplicative subset and `f : M → M'` a localization of `M` at `S`
(e.g. `M' = S⁻¹M`). If every element of `S` acts invertibly on `N`, then the canonical
map `Hom_R(M', N) → Hom_R(M, N)`, `l ↦ l ∘ₗ f`, is bijective; as it is `R`-linear, it is an
isomorphism of `R`-modules. Injectivity is `IsLocalizedModule.lift_unique` and surjectivity is
`IsLocalizedModule.lift_comp`. This is the full statement of Lemma 10.9.7, so it supersedes the
registration of `IsLocalizedModule.lift_unique` (only injectivity) for that tag. -/
@[stacks 07K0 "The full lemma: the canonical map `Hom_R(S⁻¹M, N) → Hom_R(M, N)` induced by the
localization map is bijective, stated for any localization `f : M →ₗ[R] M'` of `M` at `S`. It
supersedes the registration of `IsLocalizedModule.lift_unique`, which is only injectivity."]
theorem IsLocalizedModule.bijective_comp {R : Type*} [CommSemiring R] (S : Submonoid R)
    {M M' N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] M') [IsLocalizedModule S f]
    (h : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s)) :
    Function.Bijective fun l : M' →ₗ[R] N ↦ l ∘ₗ f := by
  refine ⟨fun l₁ l₂ e ↦ ?_, fun g ↦ ⟨lift S f g h, lift_comp S f g h⟩⟩
  rw [← lift_unique S f (l₂ ∘ₗ f) h l₁ e, lift_unique S f (l₂ ∘ₗ f) h l₂ rfl]
