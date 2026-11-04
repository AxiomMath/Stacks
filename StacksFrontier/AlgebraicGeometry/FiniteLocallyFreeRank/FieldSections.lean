module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field

/-!
# The sections of a finite locally free morphism to the spectrum of a field

A morphism `f : Z ⟶ Spec K` to the spectrum of a field which is finite locally free of rank
`r` has at most `r` sections. Consequently `r` pairwise distinct sections already exhaust the
sections, so any further section is one of them.

## Main results

* `Stacks.Morphisms.finite_and_card_sections_le_of_isFiniteLocallyFreeOfRank`: the sections of
  a finite locally free morphism of rank `r` to the spectrum of a field form a finite set of
  cardinality at most `r`.
* `Stacks.Morphisms.exists_eq_of_isFiniteLocallyFreeOfRank`: **as many distinct sections as the
  rank allows are all the sections.** Any section of such a morphism equals one of a given
  injectively indexed family of `n ≥ r` sections.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 09HS](https://stacks.math.columbia.edu/tag/09HS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

/-- **A finite locally free morphism of rank `r` to the spectrum of a field has at most `r`
sections.** -/
theorem finite_and_card_sections_le_of_isFiniteLocallyFreeOfRank {K : Type u} [Field K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of K)) (r : ℕ)
    (hf : IsFiniteLocallyFreeOfRank f r) :
    Finite {σ : Spec (CommRingCat.of K) ⟶ Z // σ ≫ f = 𝟙 _} ∧
      Nat.card {σ : Spec (CommRingCat.of K) ⟶ Z // σ ≫ f = 𝟙 _} ≤ r := by
  let _ : Algebra K ↑Γ(Z, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  obtain ⟨_, _, hrank⟩ := (isFiniteLocallyFreeOfRank_iff_finrank_sections_eq f r).1 hf
  have _ : IsAffine Z := isAffine_of_isAffineHom f
  have halg : ∀ σ : Spec (CommRingCat.of K) ⟶ Z, σ ≫ f = 𝟙 _ →
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫ σ.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom = 𝟙 _ := by
    intro σ hσ
    rw [← Category.assoc f.appTop, ← Scheme.Hom.comp_appTop, hσ, Scheme.Hom.id_appTop,
      Category.id_comp, Iso.inv_hom_id]
  let Ψ : {σ : Spec (CommRingCat.of K) ⟶ Z // σ ≫ f = 𝟙 _} → (↑Γ(Z, ⊤) →ₐ[K] K) := fun σ ↦
    { (σ.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom with
      commutes' := fun x ↦ by
        have hx : algebraMap K ↑Γ(Z, ⊤) x =
            (Scheme.Hom.appTop f).hom
              ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom x) := rfl
        have h := congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of K ↦
          (ConcreteCategory.hom φ) x) (halg σ.1 σ.2)
        rw [hx]
        simpa using h }
  have hinj : Function.Injective Ψ := by
    intro σ τ h
    refine Subtype.ext (ext_of_isAffine ?_)
    have h' : σ.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
        τ.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
      refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
      exact congrFun (congrArg (fun ψ : ↑Γ(Z, ⊤) →ₐ[K] K ↦ (ψ : ↑Γ(Z, ⊤) → K)) h) x
    exact (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1 h'
  refine ⟨Finite.of_injective Ψ hinj, ?_⟩
  calc Nat.card {σ : Spec (CommRingCat.of K) ⟶ Z // σ ≫ f = 𝟙 _}
      ≤ Nat.card (↑Γ(Z, ⊤) →ₐ[K] K) := Nat.card_le_card_of_injective Ψ hinj
    _ ≤ Module.finrank K ↑Γ(Z, ⊤) := card_algHom_le_finrank K _ K
    _ = r := hrank

/-- **As many distinct sections as the rank allows are all the sections.** If a morphism to the
spectrum of a field is finite locally free of rank `r` and `n ≥ r` of its sections are pairwise
distinct, then every section is one of those `n`. -/
theorem exists_eq_of_isFiniteLocallyFreeOfRank {K : Type u} [Field K] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (CommRingCat.of K)) (r n : ℕ) (hf : IsFiniteLocallyFreeOfRank f r)
    (hrn : r ≤ n) (σ : Fin n → (Spec (CommRingCat.of K) ⟶ Z)) (hσ : ∀ k, σ k ≫ f = 𝟙 _)
    (hinj : Function.Injective σ) (τ : Spec (CommRingCat.of K) ⟶ Z) (hτ : τ ≫ f = 𝟙 _) :
    ∃ k, τ = σ k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨_, hcard⟩ := finite_and_card_sections_le_of_isFiniteLocallyFreeOfRank f r hf
  let F : Option (Fin n) → {σ : Spec (CommRingCat.of K) ⟶ Z // σ ≫ f = 𝟙 _} := fun a ↦
    a.elim ⟨τ, hτ⟩ fun k ↦ ⟨σ k, hσ k⟩
  have hFinj : Function.Injective F := by
    rintro (_ | a) (_ | b) hab
    · rfl
    · exact absurd (congrArg Subtype.val hab) (hcon b)
    · exact absurd (congrArg Subtype.val hab).symm (hcon a)
    · exact congrArg _ (hinj (congrArg Subtype.val hab))
  have hle := Nat.card_le_card_of_injective F hFinj
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hle
  lia

end Stacks.Morphisms

end
