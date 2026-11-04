module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamFormsDataUnit
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BigradedForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseRingChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeCompletionFormsBasis

/-!
# Isomorphisms of completed divided power de Rham complexes

The completed divided power de Rham complex `B̂ → Ω̂¹_B → Ω̂²_B → ⋯` of a divided power ring
`(B, J, δ)` over `A` (`Crystalline.FormsData.formsComplex`) is invariant under

* an isomorphism of divided power `A`-algebras (`formsComplexIsoOfAlgEquiv`);
* replacing `B` by its `p`-adic completion with the completed divided powers of
  [Stacks, Tag 07KD] (`formsComplexIsoOfCompletion`);
* replacing the base ring `A` by a ring it surjects onto (`formsComplexBaseRingIso`).

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers

universe u

namespace Crystalline

namespace FormsData

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J) {C : Type u} [CommRing C] [Algebra A C] {K : Ideal C}
  (ε : DividedPowers K)

/-- A family of additive equivalences of the terms commuting with the de Rham differentials is an
isomorphism of completed de Rham complexes. -/
def formsComplexIsoOfEquivs {A' : Type u} [CommRing A'] [Algebra A' C]
    (e : ∀ i, completedDividedPowerForms p A hJ i ≃+ completedDividedPowerForms p A' ε i)
    (he : ∀ i x, e (i + 1) (completedDividedPowerDeRham p A hJ i x) =
      completedDividedPowerDeRham p A' ε i (e i x)) :
    formsComplex p A hJ ≅ formsComplex p A' ε :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ (e i).toAddCommGrpIso)
    (by
      rintro i j (rfl : i + 1 = j)
      refine AddCommGrpCat.ext fun x ↦ ?_
      change (formsComplex p A' ε).d i (i + 1) (e i x) =
        e (i + 1) ((formsComplex p A hJ).d i (i + 1) x)
      exact (formsComplex_d p A' ε i (e i x)).trans
        ((he i x).symm.trans (congrArg (e (i + 1)) (formsComplex_d p A hJ i x).symm)))

/-- **An isomorphism of divided power `A`-algebras induces an isomorphism of the completed
divided power de Rham complexes.** -/
def formsComplexIsoOfAlgEquiv (f : B ≃ₐ[A] C) (hf : IsDPMorphism hJ ε f.toAlgHom.toRingHom)
    (hg : IsDPMorphism ε hJ f.symm.toAlgHom.toRingHom) :
    formsComplex p A hJ ≅ formsComplex p A ε :=
  have hgf : IsDPMorphism hJ hJ (f.symm.toAlgHom.comp f.toAlgHom).toRingHom :=
    IsDPMorphism.comp _ hg hf
  have hfg : IsDPMorphism ε ε (f.toAlgHom.comp f.symm.toAlgHom).toRingHom :=
    IsDPMorphism.comp _ hf hg
  formsComplexIsoOfEquivs p A hJ ε
    (fun i ↦
      { toFun := completedMapDifferentialForms p A hJ ε f.toAlgHom hf i
        invFun := completedMapDifferentialForms p A ε hJ f.symm.toAlgHom hg i
        left_inv := fun x ↦ by
          rw [← completedMapDifferentialForms_comp p A hJ ε f.toAlgHom hf hJ f.symm.toAlgHom hg
            hgf]
          exact completedMapDifferentialForms_eq_self p A hJ _ hgf
            (AlgHom.ext fun b ↦ f.symm_apply_apply b) i x
        right_inv := fun x ↦ by
          rw [← completedMapDifferentialForms_comp p A ε hJ f.symm.toAlgHom hg ε f.toAlgHom hf
            hfg]
          exact completedMapDifferentialForms_eq_self p A ε _ hfg
            (AlgHom.ext fun b ↦ f.apply_symm_apply b) i x
        map_add' := map_add _ })
    (fun i x ↦ completedMapDifferentialForms_deRham p A hJ ε f.toAlgHom hf i x)

/-- **The completed de Rham complex of `B` is that of its completion `B̂`**, with the completed
divided powers of [Stacks, Tag 07KD]: `Crystalline.completedFormsOfCompletionEquiv`. -/
def formsComplexIsoOfCompletion (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) :
    formsComplex p A hJ ≅ formsComplex p A (completionDividedPowers p hJ hp) :=
  formsComplexIsoOfEquivs p A hJ (completionDividedPowers p hJ hp)
    (fun i ↦ (completedFormsOfCompletionEquiv p A hJ hp i).toAddEquiv)
    (fun i x ↦ completedMapDifferentialForms_deRham p A hJ (completionDividedPowers p hJ hp)
      (completionAlgHom p A) (isDPMorphism_completionAlgHom p A hJ hp) i x)

/-- **The completed de Rham complex does not see a surjection of base rings.** -/
def formsComplexBaseRingIso (R₁ R₂ : Type u) [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]
    [Algebra R₂ B] [Algebra R₁ B] [IsScalarTower R₁ R₂ B]
    (hR : Function.Surjective (algebraMap R₁ R₂)) :
    formsComplex p R₁ hJ ≅ formsComplex p R₂ hJ :=
  formsComplexIsoOfEquivs p R₁ hJ hJ (A' := R₂)
    (fun i ↦ (completedFormsBaseRingEquiv R₁ R₂ B hR hJ p i).toAddEquiv)
    (fun i x ↦ completedFormsBaseRingEquiv_deRham R₁ R₂ B hR hJ p i x)

end FormsData

end Crystalline

end
