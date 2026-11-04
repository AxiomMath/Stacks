module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamFormsData
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsOfCompletion
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPoincareCurvature

/-!
# The completed divided power forms as a ring with forms

For a divided power ring `(B, J, δ)` over `A` with `p` nilpotent modulo `J`, the `p`-adic
completion `B̂` with the completed divided power forms `Ω̂^*_B` of [Stacks, Tag 07J9] is a ring
with forms in the sense of `Crystalline.FormsData`
(`Crystalline.FormsData.ofDividedPowers`), and every divided power morphism `B̂₁ → B̂₂` of the
completions over `A` is a morphism of rings with forms
(`Crystalline.FormsData.Hom.ofCompletion`), through the comparison of completed forms of
`Crystalline.completedFormsMapOfCompletion`.  This is functorial
(`Crystalline.FormsData.Hom.ofCompletion_comp`, `Crystalline.FormsData.Hom.ofCompletion_id`).

## Main definitions

* `Crystalline.FormsData.ofDividedPowers`: the completed divided power forms as a ring with forms.
* `Crystalline.FormsData.Hom.ofCompletion`: a divided power morphism of the completions as a
  morphism of rings with forms.

## References

* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

open DividedPowers

universe u

namespace Crystalline

namespace FormsData

section OfDividedPowers

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J)

/-- **The completed divided power forms of a divided power ring, as a ring with forms**: the ring
is the `p`-adic completion `B̂` and the forms are the completed forms `Ω̂^i_B`. -/
abbrev ofDividedPowers : FormsData.{u} p where
  ring := completedDividedPowerRing p (B := B)
  Om := completedDividedPowerForms p A hJ
  wedge := completedDividedPowerWedge p A hJ
  deRham := completedDividedPowerDeRham p A hJ
  diff := completedFormsDifferential p A hJ
  diff_add := completedFormsDifferential_add p A hJ
  diff_mul := completedFormsDifferential_mul p A hJ
  isGradedLeibniz := isGradedLeibniz_completedDividedPower p A hJ
  wedge_anti η ζ := by
    have h := (isGradedExterior_completedDividedPower p A hJ).wedge_comm (i := 0)
      (ω := completedUnitZeroForm p A hJ) (η := η) (ζ := ζ)
    rwa [completedDividedPowerWedge_completedUnitZeroForm,
      completedDividedPowerWedge_completedUnitZeroForm] at h
  deRham_diff := deRham_completedFormsDifferential p A hJ
  isSquareZero nabla h :=
    isSquareZero_completedDividedPowerForms_of_hasIntegrableConnection p A hJ nabla h

/-- The ring of `Crystalline.FormsData.ofDividedPowers` is the completion `B̂`. -/
@[simp] theorem ofDividedPowers_ring :
    (ofDividedPowers p A hJ).ring = completedDividedPowerRing p (B := B) := rfl

/-- The `i`-forms of `Crystalline.FormsData.ofDividedPowers` are the completed forms `Ω̂^i_B`. -/
@[simp] theorem ofDividedPowers_Om (i : ℕ) :
    (ofDividedPowers p A hJ).Om i = completedDividedPowerForms p A hJ i := rfl

/-- A module with connection over `Crystalline.FormsData.ofDividedPowers` is a module over the
completed ring. -/
instance connModuleModule (M : ConnModule (ofDividedPowers p A hJ)) :
    Module (completedDividedPowerRing p (B := B)) M.carrier :=
  M.module

end OfDividedPowers

section OfCompletion

variable (p : ℕ) (A : Type u) [CommRing A]
  {B₁ : Type u} [CommRing B₁] [Algebra A B₁] {J₁ : Ideal B₁} (h₁ : DividedPowers J₁)
  (hp₁ : IsNilpotent (Ideal.Quotient.mk J₁ (p : B₁)))
  {B₂ : Type u} [CommRing B₂] [Algebra A B₂] {J₂ : Ideal B₂} (h₂ : DividedPowers J₂)
  (hp₂ : IsNilpotent (Ideal.Quotient.mk J₂ (p : B₂)))
  {B₃ : Type u} [CommRing B₃] [Algebra A B₃] {J₃ : Ideal B₃} (h₃ : DividedPowers J₃)
  (hp₃ : IsNilpotent (Ideal.Quotient.mk J₃ (p : B₃)))

/-- **A divided power morphism of the completions as a morphism of rings with forms**, the forms
being compared by `Crystalline.completedFormsMapOfCompletion`. -/
abbrev Hom.ofCompletion
    (φ : AdicCompletion (pAdicIdeal (A := B₁) p) B₁ →ₐ[A]
      AdicCompletion (pAdicIdeal (A := B₂) p) B₂)
    (hφ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
      φ.toRingHom) :
    Hom (ofDividedPowers p A h₁) (ofDividedPowers p A h₂) where
  toRingHom := φ.toRingHom
  psi := completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ
  psi_diff := completedFormsMapOfCompletion_differential p A h₁ hp₁ h₂ hp₂ φ hφ
  psi_wedge := completedFormsMapOfCompletion_wedge p A h₁ hp₁ h₂ hp₂ φ hφ
  psi_deRham := completedFormsMapOfCompletion_deRham p A h₁ hp₁ h₂ hp₂ φ hφ

/-- The ring map of `Crystalline.FormsData.Hom.ofCompletion` is the given morphism. -/
@[simp] theorem Hom.ofCompletion_toRingHom
    (φ : AdicCompletion (pAdicIdeal (A := B₁) p) B₁ →ₐ[A]
      AdicCompletion (pAdicIdeal (A := B₂) p) B₂)
    (hφ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
      φ.toRingHom) :
    (Hom.ofCompletion p A h₁ hp₁ h₂ hp₂ φ hφ).toRingHom = φ.toRingHom := rfl

/-- **Composites of morphisms of completions are morphisms of completions.** -/
theorem Hom.ofCompletion_comp
    (φ : AdicCompletion (pAdicIdeal (A := B₁) p) B₁ →ₐ[A]
      AdicCompletion (pAdicIdeal (A := B₂) p) B₂)
    (hφ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
      φ.toRingHom)
    (ψ : AdicCompletion (pAdicIdeal (A := B₂) p) B₂ →ₐ[A]
      AdicCompletion (pAdicIdeal (A := B₃) p) B₃)
    (hψ : IsDPMorphism (completionDividedPowers p h₂ hp₂) (completionDividedPowers p h₃ hp₃)
      ψ.toRingHom)
    (hψφ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₃ hp₃)
      (ψ.comp φ).toRingHom) :
    (Hom.ofCompletion p A h₂ hp₂ h₃ hp₃ ψ hψ).comp (Hom.ofCompletion p A h₁ hp₁ h₂ hp₂ φ hφ) =
      Hom.ofCompletion p A h₁ hp₁ h₃ hp₃ (ψ.comp φ) hψφ :=
  Hom.ext rfl fun i ω ↦
    completedFormsMapOfCompletion_comp p A h₁ hp₁ h₂ hp₂ h₃ hp₃ φ hφ ψ hψ hψφ i ω

/-- **The identity of the completion is the identity morphism.** -/
theorem Hom.ofCompletion_id
    (hid : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₁ hp₁)
      (AlgHom.id A (AdicCompletion (pAdicIdeal (A := B₁) p) B₁)).toRingHom) :
    Hom.ofCompletion p A h₁ hp₁ h₁ hp₁ (AlgHom.id A _) hid = Hom.id _ :=
  Hom.ext rfl fun i ω ↦ completedFormsMapOfCompletion_id p A h₁ hp₁ hid i ω

/-- Equal ring maps give equal morphisms. -/
theorem Hom.ofCompletion_congr
    {φ φ' : AdicCompletion (pAdicIdeal (A := B₁) p) B₁ →ₐ[A]
      AdicCompletion (pAdicIdeal (A := B₂) p) B₂} (h : φ = φ')
    (hφ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
      φ.toRingHom)
    (hφ' : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
      φ'.toRingHom) :
    Hom.ofCompletion p A h₁ hp₁ h₂ hp₂ φ hφ = Hom.ofCompletion p A h₁ hp₁ h₂ hp₂ φ' hφ' := by
  subst h
  rfl

/-- **The morphism of completions extending a morphism of the uncompleted rings compares the
forms by the comparison along that morphism.** -/
theorem Hom.ofCompletion_psi_eq
    (φ : AdicCompletion (pAdicIdeal (A := B₁) p) B₁ →ₐ[A]
      AdicCompletion (pAdicIdeal (A := B₂) p) B₂)
    (hφ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
      φ.toRingHom) (g : B₁ →ₐ[A] B₂) (hg : IsDPMorphism h₁ h₂ g.toRingHom)
    (hφg : ∀ b, φ (AdicCompletion.of _ B₁ b) = AdicCompletion.of _ B₂ (g b)) (i : ℕ)
    (x : completedDividedPowerForms p A h₁ i) :
    (Hom.ofCompletion p A h₁ hp₁ h₂ hp₂ φ hφ).psi i x =
      completedMapDifferentialForms p A h₁ h₂ g hg i x :=
  completedFormsMapOfCompletion_eq p A h₁ hp₁ h₂ hp₂ φ hφ g hg hφg i x

/-- **A composite of morphisms of completions equal to a third one.** -/
theorem Hom.ofCompletion_comp_eq
    {φ : AdicCompletion (pAdicIdeal (A := B₁) p) B₁ →ₐ[A]
      AdicCompletion (pAdicIdeal (A := B₂) p) B₂}
    (hφ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
      φ.toRingHom)
    {ψ : AdicCompletion (pAdicIdeal (A := B₂) p) B₂ →ₐ[A]
      AdicCompletion (pAdicIdeal (A := B₃) p) B₃}
    (hψ : IsDPMorphism (completionDividedPowers p h₂ hp₂) (completionDividedPowers p h₃ hp₃)
      ψ.toRingHom)
    {χ : AdicCompletion (pAdicIdeal (A := B₁) p) B₁ →ₐ[A]
      AdicCompletion (pAdicIdeal (A := B₃) p) B₃}
    (hχ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₃ hp₃)
      χ.toRingHom) (h : ψ.comp φ = χ) :
    (Hom.ofCompletion p A h₂ hp₂ h₃ hp₃ ψ hψ).comp (Hom.ofCompletion p A h₁ hp₁ h₂ hp₂ φ hφ) =
      Hom.ofCompletion p A h₁ hp₁ h₃ hp₃ χ hχ := by
  subst h
  exact Hom.ofCompletion_comp p A h₁ hp₁ h₂ hp₂ h₃ hp₃ φ hφ ψ hψ hχ

end OfCompletion

end FormsData

end Crystalline

end
