module

public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.Perfect.MatrixActionFibre

/-!
# Perfectness over a Noetherian ring from tensoring with truncated free resolutions

Let `A` be a Noetherian ring and `M` a pseudo-coherent object of `D(A)`.  Stacks 068V says that
`M` is perfect as soon as the derived fibres `M ⊗^L_A κ(m)` at the maximal ideals have no
cohomology outside a fixed window.  By
`CategoryTheory.MatrixAction.fibreCohomologyVanishes_of_resolution` the lower half of that
condition is read off the tensor products `M ⊗_A σ^{≥k}R` of `M` with the stupid truncations of
a resolution `R` of `κ(m)` by finite free modules with chosen bases, and the upper half is
automatic for a bounded above `M`.  This file records the resulting criterion, which is the form
in which perfectness is proved on the affine étale charts of the base in Stacks 08IS.

## Main results

* `CategoryTheory.MatrixAction.isPerfect_of_forall_resolution`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.MatrixAction

open StacksDraft.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- **Perfectness over a Noetherian ring from tensoring with truncated free resolutions.**  Let
`A` be Noetherian and `M ∈ D(A)` pseudo-coherent.  Suppose that for every bounded above complex
`R` of finite free `A`-modules with chosen bases which resolves a module (its realization has no
cohomology off degree `0`), every `i < a` admits a bound `k₀` such that `H^i(M ⊗_A σ^{≥k}R) = 0`
for all `k ≤ k₀`.  Then `M` is perfect.

This is the fibrewise criterion Stacks 068V at the maximal ideals, read through
`CategoryTheory.MatrixAction.exists_resolution_fibreCohomologyVanishes`; the residue field at a
maximal ideal of a Noetherian ring is a finite module, hence pseudo-coherent (Stacks 066E). -/
theorem isPerfect_of_forall_resolution [IsNoetherianRing A]
    (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsPseudoCoherent M) (a : ℤ)
    (h : ∀ (R : CochainComplex (Mat_ (SingleObj A)) ℤ) (c : ℤ) [R.IsStrictlyLE c],
      (∀ j : ℤ, j ≠ 0 → IsZero ((((realizeModule A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj R).homology j)) →
      ∀ i : ℤ, i < a → ∃ k₀ : ℤ, ∀ k : ℤ, k ≤ k₀ →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((derivedTot A (R.stupidTrunc (ComplexShape.embeddingUpIntGE k)) k c).obj M))) :
    StacksDraft.Perfect.IsPerfect M := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := hM
  obtain ⟨c, hc⟩ := hP.upperBound
  have hfib : ∀ (m : MaximalSpectrum A) (i : ℤ), i < a ∨ c < i →
      StacksDraft.Perfect.FibreCohomologyVanishes.{u, u} m.asIdeal M i := by
    intro m i hi
    have hfin : Module.Finite A m.asIdeal.ResidueField := by
      have hbij := Ideal.bijective_algebraMap_quotient_residueField m.asIdeal
      exact Module.Finite.of_surjective
        ((Algebra.linearMap (A ⧸ m.asIdeal) m.asIdeal.ResidueField).restrictScalars A ∘ₗ
          (Submodule.mkQ m.asIdeal))
        (hbij.2.comp Ideal.Quotient.mk_surjective)
    have hpc : IsModulePseudoCoherent (R := A) m.asIdeal.ResidueField :=
      ((pseudoCoherent_iff_boundedAbove_finite_homology.{u, u}
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A m.asIdeal.ResidueField)) 0 m.asIdeal.ResidueField).2.2).2 hfin
    rcases hi with hi | hi
    · obtain ⟨E, hE, ⟨eE⟩⟩ := hpc
      obtain ⟨c', hc'⟩ := hE.upperBound
      obtain ⟨R, ⟨eR⟩⟩ := exists_realizeModule_iso A E fun n =>
        ⟨(hE.finiteFree n).1, (hE.finiteFree n).2⟩
      have hRc : R.IsStrictlyLE c' := by
        rw [CochainComplex.isStrictlyLE_iff]
        intro n hn
        have hz : IsZero ((realizeModule A).obj (R.X n)) :=
          (E.isZero_of_isStrictlyLE c' n hn).of_iso ((HomologicalComplex.eval _ _ n).mapIso eR)
        rw [IsZero.iff_id_eq_zero] at hz ⊢
        exact (realizeModuleFullyFaithful A).map_injective
          (by rw [Functor.map_id, Functor.map_zero, hz])
      have e₁ : DerivedCategory.Q.obj
          (((realizeModule A).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) ≅
            (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A m.asIdeal.ResidueField) :=
        (DerivedCategory.Q.mapIso eR) ≪≫ eE
      obtain ⟨k₀, hk₀⟩ := h R c' (fun j hj => isZero_homology_of_iso_single A _ _ e₁ j hj) i hi
      exact fibreCohomologyVanishes_of_resolution A m.asIdeal R c' E hE eR eE M P hP eP c i
        (min k₀ (i - c - 1)) (by omega) (hk₀ _ (min_le_left _ _))
    · refine ⟨P, hP, ⟨eP⟩, ?_⟩
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact HomologicalComplex.ExactAt.of_isZero
        ((ModuleCat.extendScalars _).map_isZero (P.isZero_of_isStrictlyLE c i hi))
  have h068V := StacksDraft.Perfect.isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes.{u, u}
    M ⟨P, hP, ⟨eP⟩⟩ a c
  exact (h068V.1.2 (h068V.2.2 hfib)).1

end CategoryTheory.MatrixAction

end
