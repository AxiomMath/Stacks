module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassPushforwardGrassmannian
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalPushforwardComp

/-!
# Cancellation for the compatibility of `γ` with pushforward

Let `H^*` be data (D0)–(D3) of Section 45.9 satisfying axiom (A)(b). If `γ` commutes with
pushforward along `u : Y ⟶ X` and along `u ≫ v`, and `u_*` is surjective on Chow groups, then `γ`
commutes with pushforward along `v`: every `β ∈ CH^*(X)` is `u_*α`, and
`γ(v_*u_*α) = (u ≫ v)_*γ(α) = v_*u_*γ(α) = v_*γ(u_*α)` by Stacks 02R5 and Stacks 0FHB. This is
the last step of the proof of Stacks 0FIQ.

## Main results

* `Stacks.WeilCohomology.WeilData.PushforwardCompatible.of_comp`: the cancellation step.
* `Stacks.WeilCohomology.WeilData.PushforwardCompatible.comp_of_forall`: compatibility along a
  composite, the middle scheme being equidimensional when source and target are.

## References

* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
* [Stacks Project, Tag 0FHB](https://stacks.math.columbia.edu/tag/0FHB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

/-- **Cancellation**: if `γ` commutes with pushforward along `u : Y ⟶ X` and along `u ≫ v`, and
`u_*` is surjective on Chow groups, then `γ` commutes with pushforward along `v : X ⟶ Z`. Every
`β ∈ CH^*(X)` is `u_*α`, and `γ(v_*u_*α) = (u ≫ v)_*γ(α) = v_*u_*γ(α) = v_*γ(u_*α)`. This is
the last step of the proof of Stacks 0FIQ. -/
theorem PushforwardCompatible.of_comp {hA : W.PerfectPairing}
    {Y X Z : (SmoothProjectiveScheme k).FullSubcategory} {u : Y ⟶ X} {v : X ⟶ Z}
    (hYdim : ∀ d c : ℕ, IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Z c →
      ∃ e : ℕ, RelativeDimension Y.obj.hom e ∧
        ∀ (p q : ℤ) (h : q = p + d - e),
          Function.Surjective (equidimensionalPushforward u e d p q h))
    (hu : W.PushforwardCompatible hA u) (huv : W.PushforwardCompatible hA (u ≫ v)) :
    W.PushforwardCompatible hA v := by
  intro d c hX hZ q r hr β
  obtain ⟨e, hYe, hsurj⟩ := hYdim d c hX hZ
  obtain ⟨α, rfl⟩ := hsurj (q + e - d) q (by omega) β
  by_cases hne : Nonempty Y.obj.left
  · have hY : IsNonemptyEquidimensional Y e := ⟨hne, hYe⟩
    rw [equidimensionalPushforward_comp u v hX.relativeDimension (q + e - d) q r (by omega) hr α,
      huv e c hY hZ, hu e d hY hX, W.pushforward_comp hA u v hY hX hZ]
  · have : IsEmpty Y.obj.left := not_nonempty_iff.mp hne
    have : Subsingleton (codimensionChowGroup k Y.obj.hom (q + e - d)) := by
      refine ⟨fun a b ↦ funext fun d' ↦ ?_⟩
      have : IsEmpty (dimPart Y.obj.hom d').toScheme :=
        ⟨fun y ↦ isEmptyElim (y.1 : Y.obj.left)⟩
      exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _
    simp only [Subsingleton.elim α 0, map_zero]

/-- **Compatibility along a composite**, when the middle scheme is nonempty equidimensional
whenever source and target are (`WeilData.PushforwardCompatible.comp` with the middle dimension
depending on those of the source and the target). -/
theorem PushforwardCompatible.comp_of_forall {hA : W.PerfectPairing}
    {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hYdim : ∀ d c : ℕ, IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Z c →
      ∃ e : ℕ, IsNonemptyEquidimensional Y e)
    (hrat : ∀ (n : ℤ) (a a' : codimensionChowGroup k Z.obj.hom n),
      codimensionToRationalChow k Z.obj.hom n a = codimensionToRationalChow k Z.obj.hom n a' →
        W.cycleClass Z n a = W.cycleClass Z n a')
    (hf : W.PushforwardCompatible hA f) (hg : W.PushforwardCompatible hA g) :
    W.PushforwardCompatible hA (f ≫ g) := by
  intro d c hX hZ
  obtain ⟨e, hY⟩ := hYdim d c hX hZ
  exact PushforwardCompatible.comp hY hrat hf hg d c hX hZ

end WeilData

end Stacks.WeilCohomology

end
