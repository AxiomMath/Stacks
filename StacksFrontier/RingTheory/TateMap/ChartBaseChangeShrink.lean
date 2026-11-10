module

public import StacksFrontier.RingTheory.TateMap.ChartBaseChange

/-!
# Shrinking the base chart of a chart base change

If `B'` is a chart base change of `A → B` along `A → A'`, and `A → A'` and `A → B` both factor
through a principal localization `A₀` of `A`, then `B'` is a chart base change of `A₀ → B` along
`A₀ → A'`: the base changes `A' ⊗_{A₀} B` and `A' ⊗_A B` agree, `A → A₀` being a localization.

## Main definitions

* `Stacks.TateMap.ChartBaseChange.ofBaseAway`: the chart base change with the smaller base.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.TateMap.ChartBaseChange

variable {A B A' B' A₀ : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [CommRing A₀] [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']
  [Algebra A A₀] [Algebra A₀ B] [IsScalarTower A A₀ B] [Algebra A₀ A'] [IsScalarTower A A₀ A']

/-- **Shrinking the base chart of a chart base change.** If `D` is a chart base change from
`A → B` to `A' → B'` and the maps `A → B`, `A → A'` factor through a principal localization `A₀`
of `A`, then `D` induces a chart base change from `A₀ → B` to `A' → B'`. -/
def ofBaseAway (D : ChartBaseChange A B A' B') (a : A) [IsLocalization.Away a A₀] :
    ChartBaseChange A₀ B A' B' :=
  letI := D.algebra
  let ε : A' ⊗[A₀] B ≃ₐ[A₀] A' ⊗[A] B :=
    IsLocalization.algebraTensorEquiv (Submonoid.powers a) A₀ A' B
  have hε : ∀ (y : A') (x : B), ε (y ⊗ₜ[A₀] x) = y ⊗ₜ[A] x := fun _ _ ↦ rfl
  { algebra := ((algebraMap (A' ⊗[A] B) B').comp ε.toRingHom).toAlgebra
    base_left := fun y ↦ by
      change algebraMap (A' ⊗[A] B) B' (ε (y ⊗ₜ 1)) = _
      rw [hε]
      exact D.base_left y
    base_right := fun x ↦ by
      change algebraMap (A' ⊗[A] B) B' (ε (1 ⊗ₜ x)) = _
      rw [hε]
      exact D.base_right x
    elt := ε.symm D.elt
    isLocalization := by
      have := D.isLocalization
      have h := IsLocalization.isLocalization_of_base_ringEquiv (S := B')
        (Submonoid.powers D.elt) ε.symm.toRingEquiv
      rwa [Submonoid.map_powers] at h }

end Stacks.TateMap.ChartBaseChange
