module

public import StacksFrontier.RingTheory.MilnorPatching.BaseChangeGlueing

/-!
# A base change followed by a surjection

If `f : M ⟶ N` exhibits `N` as the base change of `M` along `φ : R ⟶ S` and `g : N ⟶ N'` is a
surjective `S`-linear map, then `S ⊗_R M ⟶ N'`, `s ⊗ m ↦ s • g (f m)`, is surjective.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace MilnorPatching

section BaseChangeAlong

variable {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S}
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- A base change followed by a surjective linear map generates its target: if `f` exhibits `N`
as the base change of `M` and `g : N ⟶ N'` is surjective, then `S ⊗_R M ⟶ N'`,
`s ⊗ m ↦ s • g (f m)`, is surjective. -/
theorem IsBaseChangeAlong.surjective_liftAlong_of_comp {f : M →ₛₗ[φ] N}
    (hf : IsBaseChangeAlong φ f) {N' : Type u} [AddCommGroup N'] [Module S N'] {f' : M →ₛₗ[φ] N'}
    (g : N →ₗ[S] N') (hg : Function.Surjective g) (hgf : ∀ m, g (f m) = f' m) :
    Function.Surjective (liftAlong φ f') := by
  let := φ.toAlgebra
  have e : ∀ t, g (liftAlong φ f t) = liftAlong φ f' t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul s m =>
      change g (s • f m) = s • f' m
      rw [map_smul, hgf]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  intro y
  obtain ⟨x, rfl⟩ := hg y
  obtain ⟨t, rfl⟩ := hf.2 x
  exact ⟨t, (e t).symm⟩

end BaseChangeAlong

end MilnorPatching

end
