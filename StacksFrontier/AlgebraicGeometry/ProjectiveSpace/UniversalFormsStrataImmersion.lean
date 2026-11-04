module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.UniversalFormsStrata

/-!
# The flat strata of the universal family of forms are locally closed in its base

The flat strata `Tᵢ` of the universal family `Proj (R[T₀, …, Tₙ] ⧸ (f_1, …, f_M)) ⟶ Spec R` of
`Stacks.UniversalForms.exists_flat_families_of_forms`, over the coefficient ring
`R = ℤ[a_{j,E}]`, come with immersions `Tᵢ ⟶ Spec R` (Stacks 0H3Z). This file records them, so
that the strata, being of finite type over `ℤ`, lie in every big fppf site.

## Main results

* `Stacks.UniversalForms.exists_flat_families_of_forms_isImmersion`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace Stacks.UniversalForms

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n M m : ℕ)

/-- **Finitely many flat proper families over Noetherian locally closed strata of the coefficient
space contain every projective scheme cut out by `M` forms of degree `m` over a field.** This is
`Stacks.UniversalForms.exists_flat_families_of_forms` together with the immersions of the strata
into `Spec ℤ[a_{j,E}]`. -/
theorem exists_flat_families_of_forms_isImmersion :
    ∃ (t : ℕ) (T : Fin t → Scheme.{u}) (Z : Fin t → Scheme.{u}) (π : ∀ i, Z i ⟶ T i),
      (∀ i, ∃ j : T i ⟶ Spec (.of (CoeffRing.{u} n M m)), IsImmersion j) ∧
      (∀ i, IsNoetherian (T i)) ∧ (∀ i, Flat (π i)) ∧ (∀ i, IsProper (π i)) ∧
      ∀ (K : Type u) [Field K] (s : Fin M → MvPolynomial (Fin (n + 1)) K)
        (hs : ∀ j, (s j).IsHomogeneous m),
        ∃ i, ∃ (x : Spec (.of K) ⟶ T i) (q : Proj (formsGrading K s hs) ⟶ Z i),
          IsPullback q (formsToSpec K s hs) (π i) x := by
  obtain ⟨t, T, j, himm, hT, hflat, hpts⟩ :=
    exists_flat_strata_of_isNoetherian (univToBase.{u} n M m)
  refine ⟨t, T, fun i => pullback (univToBase.{u} n M m) (j i),
    fun i => pullback.snd (univToBase.{u} n M m) (j i), fun i => ⟨j i, himm i⟩, hT, hflat,
    fun i => inferInstance, ?_⟩
  intro K _ s hs
  let : Algebra (CoeffRing.{u} n M m) K := (specialize K s).toAlgebra
  obtain ⟨i, x, hx⟩ := hpts K (Spec.map (CommRingCat.ofHom (specialize K s)))
  have hsq := isPullback_univToBase n M m K
  rw [← hx] at hsq
  have hbig := IsPullback.of_right (h₁₂ := pullback.fst (univToBase.{u} n M m) (j i))
    (v₁₂ := pullback.snd (univToBase.{u} n M m) (j i))
    (h₁₁ := pullback.lift (Proj.map (baseChangeGradedRingHom n M m K)
      (irrelevant_le_map_baseChangeGradedRingHom n M m K)) (baseToSpec n M m K ≫ x)
        (by rw [hsq.w]; simp only [Category.assoc]))
    (by rw [pullback.lift_fst]; exact hsq) (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback _ _)
  have key : ∀ (s₁ : Fin M → MvPolynomial (Fin (n + 1)) K) (h₁ : ∀ j, (s₁ j).IsHomogeneous m),
      s₁ = s → (∃ (q : Proj (formsGrading K s₁ h₁) ⟶ pullback (univToBase.{u} n M m) (j i)),
        IsPullback q (formsToSpec K s₁ h₁) (pullback.snd (univToBase.{u} n M m) (j i)) x) →
      ∃ (q : Proj (formsGrading K s hs) ⟶ pullback (univToBase.{u} n M m) (j i)),
        IsPullback q (formsToSpec K s hs) (pullback.snd (univToBase.{u} n M m) (j i)) x := by
    rintro s₁ h₁ rfl h
    exact h
  obtain ⟨q, hq⟩ := key (baseForms n M m K) (isHomogeneous_baseForms n M m K)
    (funext fun j => map_specialize_form K s hs j) ⟨_, hbig⟩
  exact ⟨i, x, q, hq⟩

end Stacks.UniversalForms

end
