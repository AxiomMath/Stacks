module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The coeffacement step of a descending induction on the homology sequence

Let `φ : S₁ ⟶ S₂` be a morphism of short exact sequences `0 → X₁ → X₂ → X₃ → 0` of homological
complexes in an abelian category, and `c.Rel i j`. Suppose that `X₂ → X₃` induces zero on `Hᵢ` in
both sequences (a *coeffacement* of `X₃` in degree `i`). Then the connecting morphisms identify
`Hᵢ(X₃)` with the kernel of `Hⱼ(X₁) → Hⱼ(X₂)` in both sequences, so `φ` induces an isomorphism on
`Hᵢ(X₃)` as soon as it induces an isomorphism on `Hⱼ(X₁)` and a monomorphism on `Hⱼ(X₂)`
(`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃_of_homologyMap_g_eq_zero`).

This is the inductive step in the proof that a pairing of cohomology theories is perfect in all
degrees once it is perfect in the extreme degree and both theories admit compatible
coeffacements (the derived Poincaré duality of Tag 03VM).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public section

open CategoryTheory Limits

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

namespace HomologicalComplex.HomologySequence

include hS₁ in
/-- If `X₂ → X₃` induces zero on `Hᵢ`, the connecting morphism `Hᵢ(X₃) ⟶ Hⱼ(X₁)` is a
monomorphism. -/
theorem mono_δ_of_homologyMap_g_eq_zero (i j : ι) (hij : c.Rel i j)
    (h : homologyMap S₁.g i = 0) : Mono (hS₁.δ i j hij) :=
  (hS₁.homology_exact₃ i j hij).mono_g h

include hS₁ hS₂ in
/-- **The coeffacement step.** If `X₂ → X₃` induces zero on `Hᵢ` in both short exact sequences,
`φ` induces an isomorphism on `Hⱼ(X₁)` and a monomorphism on `Hⱼ(X₂)`, then it induces an
isomorphism on `Hᵢ(X₃)`. -/
theorem isIso_homologyMap_τ₃_of_homologyMap_g_eq_zero (i j : ι) (hij : c.Rel i j)
    (h₁ : homologyMap S₁.g i = 0) (h₂ : homologyMap S₂.g i = 0)
    [IsIso (homologyMap φ.τ₁ j)] [Mono (homologyMap φ.τ₂ j)] :
    IsIso (homologyMap φ.τ₃ i) := by
  have hm₁ := mono_δ_of_homologyMap_g_eq_zero hS₁ i j hij h₁
  have hm₂ := mono_δ_of_homologyMap_g_eq_zero hS₂ i j hij h₂
  have hnat := δ_naturality φ hS₁ hS₂ i j hij
  have : Mono (homologyMap φ.τ₃ i) := by
    have : Mono (homologyMap φ.τ₃ i ≫ hS₂.δ i j hij) := by
      rw [← hnat]
      exact mono_comp _ _
    exact mono_of_mono _ (hS₂.δ i j hij)
  have hk : (hS₂.δ i j hij ≫ inv (homologyMap φ.τ₁ j)) ≫ homologyMap S₁.f j = 0 := by
    rw [← cancel_mono (homologyMap φ.τ₂ j), Category.assoc, Category.assoc, zero_comp,
      ← homologyMap_comp, ← φ.comm₁₂, homologyMap_comp, IsIso.inv_hom_id_assoc,
      hS₂.δ_comp]
  let ψ := (hS₁.homology_exact₁ i j hij).lift _ hk
  have hψ : ψ ≫ hS₁.δ i j hij = hS₂.δ i j hij ≫ inv (homologyMap φ.τ₁ j) :=
    (hS₁.homology_exact₁ i j hij).lift_f _ hk
  have hψ' : ψ ≫ homologyMap φ.τ₃ i = 𝟙 _ := by
    rw [← cancel_mono (hS₂.δ i j hij), Category.assoc, ← hnat, reassoc_of% hψ,
      IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  have : IsSplitEpi (homologyMap φ.τ₃ i) := ⟨⟨ψ, hψ'⟩⟩
  exact isIso_of_mono_of_epi _

end HomologicalComplex.HomologySequence
