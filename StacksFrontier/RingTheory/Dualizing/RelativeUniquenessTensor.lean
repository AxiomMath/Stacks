module

public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTensorForm
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessCrossFlat
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessMixed
public import StacksFrontier.RingTheory.Dualizing.RelativeCoprojections
public import StacksFrontier.Homology.RelativelyPerfect.FlatComplex
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Uniqueness of relative dualizing complexes

Let `R → A` be a flat ring map of finite presentation. Any two relative dualizing complexes for
`R → A` are isomorphic. No Noetherian hypothesis is made.

## Main results

* `Dualizing.IsRelativeDualizingComplex.nonempty_iso`: any two relative dualizing complexes for a
  flat ring map of finite presentation are isomorphic.

## References

* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

/-- Let `R → A` be a flat ring map of finite presentation. Any two relative dualizing complexes
for `R → A` are isomorphic. -/
@[stacks 0E2D]
theorem IsRelativeDualizingComplex.nonempty_iso {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K L : DerivedCategory (ModuleCat.{u} A)}
    (hK : IsRelativeDualizingComplex R A K) (hL : IsRelativeDualizingComplex R A L) :
    Nonempty (K ≅ L) := by
  let Δ : A ⊗[R] A →+* A := (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
  let p₁ : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  let p₂ : A →+* A ⊗[R] A := (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom
  have hΔ₁ : Δ.comp p₁ = RingHom.id A := by ext a; simp [Δ, p₁]
  have hΔ₂ : Δ.comp p₂ = RingHom.id A := by ext a; simp [Δ, p₂]
  have hker : (RingHom.ker Δ).FG := KaehlerDifferential.ideal_fg R A
  obtain ⟨N, ⟨⟨d, hd⟩, hNff⟩, ⟨eN⟩⟩ := isPseudoCoherent_diagonal R A
  have : ∀ i, Module.Finite (A ⊗[R] A) (N.X i) := fun i ↦ (hNff i).1
  have : ∀ i, Module.Free (A ⊗[R] A) (N.X i) := fun i ↦ (hNff i).2
  have perf (M : DerivedCategory (ModuleCat.{u} A)) (hM : IsRelativeDualizingComplex R A M) :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ M).1 hM.relativelyPerfect
  obtain ⟨PK, aK, bK, hKGE, hKLE, hKflat, -, ⟨eK⟩⟩ := perf K hK
  obtain ⟨PL, aL, bL, hLGE, hLLE, hLflat, -, ⟨eL⟩⟩ := perf L hL
  let a := min aK aL
  have : PK.IsStrictlyGE a := CochainComplex.isStrictlyGE_of_ge _ a aK (min_le_left _ _)
  have : PL.IsStrictlyGE a := CochainComplex.isStrictlyGE_of_ge _ a aL (min_le_right _ _)
  have hK₁ := hK.diagonalDerivedHom.map fun e ↦
    (derivedHom.{u, u} Δ).mapIso (diagonalDerivedExtensionIso R A K PK eK.symm).symm ≪≫ e
  have hL₂ := hL.diagonalDerivedHom_includeRight.map fun e ↦
    (derivedHom.{u, u} Δ).mapIso (rightCoprojectionDerivedExtensionIso R A L PL eL.symm).symm ≪≫ e
  have hflat₂ : ∀ n, Module.Flat A (((CochainComplex.restrictScalars p₂).obj
      (TensorForm.dual N ⊗ (CochainComplex.extendScalars p₁).obj PK)).X n) :=
    TensorForm.flat_restrictScalars_dual_tensor_X p₂ N _ fun j ↦
      CrossFlat.flat_restrictScalars_includeRight_extendScalars_includeLeft R A (PK.X j)
        (hKflat j)
  have hflat₁ : ∀ n, Module.Flat A (((CochainComplex.restrictScalars p₁).obj
      (TensorForm.dual N ⊗ (CochainComplex.extendScalars p₂).obj PL)).X n) :=
    TensorForm.flat_restrictScalars_dual_tensor_X p₁ N _ fun j ↦
      CrossFlat.flat_restrictScalars_includeLeft_extendScalars_includeRight R A (PL.X j)
        (hLflat j)
  obtain ⟨fL⟩ := TensorForm.nonempty_iso_derivedHom_tensor Δ p₂ N d p₁ hΔ₂ hker eN PL PK a
    hflat₂ hL₂ hK₁
  obtain ⟨fK⟩ := TensorForm.nonempty_iso_derivedHom_tensor Δ p₁ N d p₂ hΔ₁ hker eN PK PL a
    hflat₁ hK₁ hL₂
  let := CochainComplex.Koszul.koszulSymmetric (A ⊗[R] A)
  exact ⟨eK ≪≫ fK ≪≫ (derivedHom.{u, u} Δ).mapIso (DerivedCategory.Q.mapIso (β_ _ _)) ≪≫
    fL.symm ≪≫ eL.symm⟩

end Dualizing
