module

public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence

/-!
# The abutment of a first-quadrant spectral sequence in low degrees

For a first-quadrant `E₂` cohomological spectral sequence abutting to `H^*`, the only term of
total degree `0` is `E_2^{0,0}`, and no differential reaches or leaves it from the second page
on, so `H^0 = E_∞^{0,0} = E_2^{0,0}`. In degrees `1` and `2` there is the five term exact sequence
`0 → E_2^{1,0} → H^1 → E_2^{0,1} → E_2^{2,0} → H^2` of
`Stacks.Cohomology.Leray.FirstQuadrantAbutment`; this file records it with each of its five
terms replaced by an isomorphic object.

## Main definitions

* `Stacks.Cohomology.Leray.FirstQuadrantAbutment.zeroIso`: the identification
  `H^0 ≅ E_2^{0,0}` carried by a `FirstQuadrantAbutment`.

## Main results

* `Stacks.Cohomology.Leray.FirstQuadrantAbutment.exists_exact_of_iso`: the five term exact
  sequence, transported along isomorphisms of its five terms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.Leray.FirstQuadrantAbutment

variable {C : Type*} [Category* C] [Abelian C]
  {E : CohomologicalSpectralSequenceNat C 2} {H : ℕ → C} (D : FirstQuadrantAbutment E H)

/-- **`H^0 = E_2^{0,0}`** for a first-quadrant `E₂` spectral sequence abutting to `H^*`: the
filtration of `H^0` has the single graded piece `E_∞^{0,0}`, and `E_∞^{0,0} = E_2^{0,0}` since
every differential into or out of `(0, 0)` vanishes from the second page on. -/
def zeroIso : H 0 ≅ (E.page 2).X (0, 0) :=
  (D.topIso 0).symm ≪≫ (D.topGradedIso 0).symm ≪≫ E.pageInfinityIso (0, 0) 2

include D in
/-- **The five term exact sequence, up to isomorphism of its terms.** If `E_2^{1,0} ≅ A`,
`H^1 ≅ M`, `E_2^{0,1} ≅ B`, `E_2^{2,0} ≅ C'` and `H^2 ≅ N`, then there is an exact sequence
`0 → A → M → B → C' → N`. The maps are the inflation, the restriction, the differential
`d_2^{0,1}` and the transgression, conjugated by the given isomorphisms. -/
theorem exists_exact_of_iso {A M B C' N : C} (e₁₀ : (E.page 2).X (1, 0) ≅ A) (h₁ : H 1 ≅ M)
    (e₀₁ : (E.page 2).X (0, 1) ≅ B) (e₂₀ : (E.page 2).X (2, 0) ≅ C') (h₂ : H 2 ≅ N) :
    ∃ (a : A ⟶ M) (b : M ⟶ B) (c : B ⟶ C') (t : C' ⟶ N) (hab : a ≫ b = 0) (hbc : b ≫ c = 0)
      (hct : c ≫ t = 0), Mono a ∧ (ShortComplex.mk a b hab).Exact ∧
        (ShortComplex.mk b c hbc).Exact ∧ (ShortComplex.mk c t hct).Exact := by
  have := D.mono_inflation
  refine ⟨e₁₀.inv ≫ D.inflation ≫ h₁.hom, h₁.inv ≫ D.restriction ≫ e₀₁.hom,
    e₀₁.inv ≫ (E.page 2).d (0, 1) (2, 0) ≫ e₂₀.hom, e₂₀.inv ≫ D.transgression ≫ h₂.hom,
    by simp [reassoc_of% D.inflation_restriction], by simp [reassoc_of% D.restriction_d],
    by simp [reassoc_of% D.d_transgression], inferInstance, ?_, ?_, ?_⟩
  · exact (ShortComplex.exact_iff_of_iso
      (ShortComplex.isoMk e₁₀ h₁ e₀₁ (by simp) (by simp))).1 D.exact_inflation_restriction
  · exact (ShortComplex.exact_iff_of_iso
      (ShortComplex.isoMk h₁ e₀₁ e₂₀ (by simp) (by simp))).1 D.exact_restriction_d
  · exact (ShortComplex.exact_iff_of_iso
      (ShortComplex.isoMk e₀₁ e₂₀ h₂ (by simp) (by simp))).1 D.exact_d_transgression

end Stacks.Cohomology.Leray.FirstQuadrantAbutment

end
