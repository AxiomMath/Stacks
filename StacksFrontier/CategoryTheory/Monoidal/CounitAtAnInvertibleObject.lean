module

public import Mathlib.CategoryTheory.Yoneda
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# The evaluation morphism at an invertible object is an isomorphism

Let `C` be a monoidal category, let `L`, `M`, `H` be objects of `C` and let `c : H ⊗ L ⟶ M` be a
morphism which exhibits `H` as an internal hom from `L` to `M`, in the sense that for every `Z`
the map

`(Z ⟶ H) → (Z ⊗ L ⟶ M)`, `a ↦ a ▷ L ≫ c`

is a bijection. If `L` is invertible ([Stacks, Tag 0FFN]) then `c` is an isomorphism.

## Main results

* `CategoryTheory.MonoidalCategory.isIso_of_isInvertible_of_tensorHomBijective`: the evaluation
  morphism at an invertible object is an isomorphism.

## References

* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Let `c : H ⊗ L ⟶ M` be a morphism such that for every object `Z` the map `a ↦ a ▷ L ≫ c` from
`Z ⟶ H` to `Z ⊗ L ⟶ M` is a bijection — that is, `c` exhibits `H` as an internal hom from `L`
to `M`. If `L` is invertible then `c` is an isomorphism. -/
theorem isIso_of_isInvertible_of_tensorHomBijective {L M H : C} (c : H ⊗ L ⟶ M)
    (hc : ∀ Z : C, Function.Bijective fun a : Z ⟶ H => a ▷ L ≫ c)
    (hL : IsInvertible L) : IsIso c := by
  obtain ⟨h⟩ := hL
  have : (tensorRight L).IsEquivalence := h.tensorRightEquivalence.isEquivalence_functor
  let ε : (M ⊗ h.inv) ⊗ L ≅ M := α_ M h.inv L ≪≫ whiskerLeftIso M h.isoRight ≪≫ ρ_ M
  obtain ⟨φ, hφ : φ ▷ L ≫ c = ε.hom⟩ := (hc (M ⊗ h.inv)).surjective ε.hom
  have : IsIso φ := by
    refine isIso_of_yoneda_map_bijective φ fun Z => ?_
    have point : ∀ a : Z ⟶ M ⊗ h.inv,
        a ≫ φ = (Equiv.ofBijective _ (hc Z)).symm ((tensorRight L).map a ≫ ε.hom) := by
      intro a
      refine (Equiv.ofBijective _ (hc Z)).injective ?_
      rw [Equiv.apply_symm_apply]
      change (a ≫ φ) ▷ L ≫ c = _
      rw [comp_whiskerRight, Category.assoc, hφ]
      rfl
    have key : (fun a : Z ⟶ M ⊗ h.inv => a ≫ φ) =
        (Equiv.ofBijective _ (hc Z)).symm ∘
          (fun g : Z ⊗ L ⟶ (M ⊗ h.inv) ⊗ L => g ≫ ε.hom) ∘ (tensorRight L).map :=
      funext point
    have hswap : Function.Bijective
        (fun g : Z ⊗ L ⟶ (M ⊗ h.inv) ⊗ L => g ≫ ε.hom) :=
      ⟨fun g₁ g₂ hg => by simpa using congrArg (fun g : Z ⊗ L ⟶ M => g ≫ ε.inv) hg,
        fun g => ⟨g ≫ ε.inv, by simp⟩⟩
    have hmap : Function.Bijective
        ((tensorRight L).map : (Z ⟶ M ⊗ h.inv) → (Z ⊗ L ⟶ (M ⊗ h.inv) ⊗ L)) :=
      ⟨(tensorRight L).map_injective, (tensorRight L).map_surjective⟩
    exact key ▸ (Equiv.ofBijective _ (hc Z)).symm.bijective.comp (hswap.comp hmap)
  have : IsIso (φ ▷ L ≫ c) := by rw [hφ]; infer_instance
  exact IsIso.of_isIso_comp_left (φ ▷ L) c

end CategoryTheory.MonoidalCategory

end
