module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-!
# Restriction of scalars along a bijective ring map is strong monoidal

For a ring map `f : R →+* S` of commutative rings, restriction of scalars
`ModuleCat.restrictScalars f : ModuleCat S ⥤ ModuleCat R` is lax monoidal (Mathlib, as the right
adjoint of extension of scalars), with tensorator `M ⊗_R N ⟶ M ⊗_S N`, `m ⊗ n ↦ m ⊗ n`. When `f` is
bijective that tensorator is bijective: its inverse is the lift of `m ⊗ n ↦ m ⊗ n`, which is
`S`-balanced because every element of `S` is the image of an element of `R`.

## Main results

* `ModuleCat.bijective_μ_restrictScalars`: the tensorator of `restrictScalars f` is bijective
  when `f` is.

## References

* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace ModuleCat

open Functor.LaxMonoidal

/-- **Restriction of scalars along a bijective ring map is strong monoidal on tensor products**:
the comparison `M ⊗_R N ⟶ M ⊗_S N` is bijective. -/
theorem bijective_μ_restrictScalars {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) (M N : ModuleCat.{u} S) :
    Function.Bijective (μ (restrictScalars f) M N).hom := by
  let toM : M → (restrictScalars f).obj M := id
  let toN : N → (restrictScalars f).obj N := id
  have hbal : ∀ (s : S) (m : M) (n : N), toM (s • m) ⊗ₜ[R] toN n = toM m ⊗ₜ[R] toN (s • n) := by
    intro s m n
    obtain ⟨r, rfl⟩ := hf.2 s
    exact TensorProduct.smul_tmul (R := R) r (toM m) (toN n)
  let g : (restrictScalars f).obj (M ⊗ N) →+
      (restrictScalars f).obj M ⊗[R] (restrictScalars f).obj N :=
    TensorProduct.liftAddHom
      { toFun := fun m =>
          { toFun := fun n => toM m ⊗ₜ[R] toN n
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
        map_zero' := AddMonoidHom.ext fun _ => TensorProduct.zero_tmul _ _
        map_add' := fun _ _ => AddMonoidHom.ext fun _ => TensorProduct.add_tmul _ _ _ }
      hbal
  have h1 : ∀ t, g ((μ (restrictScalars f) M N).hom t) = t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul m n => exact congrArg g (restrictScalars_μ_tmul f M N m n)
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have h2 : Function.Surjective (μ (restrictScalars f) M N).hom := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul m n => exact ⟨toM m ⊗ₜ[R] toN n, restrictScalars_μ_tmul f M N m n⟩
    | add a b ha hb =>
      obtain ⟨⟨a', rfl⟩, b', rfl⟩ := And.intro ha hb
      exact ⟨a' + b', map_add _ a' b'⟩
  exact ⟨Function.LeftInverse.injective h1, h2⟩

end ModuleCat

end
