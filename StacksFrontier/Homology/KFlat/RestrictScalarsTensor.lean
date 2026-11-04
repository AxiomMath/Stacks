module

public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.HomComplex.KoszulBraiding

/-!
# K-flatness over the base of a tensor product with a relatively K-flat complex

Let `φ : R → A` be a ring map, `M` a K-flat complex of `A`-modules and `N` a complex of
`A`-modules which is K-flat as a complex of `R`-modules. Then `Tot(M ⊗_A N)` is K-flat as a
complex of `R`-modules: for an acyclic complex `L` of `R`-modules,
`L ⊗_R (M ⊗_A N) ≅ M ⊗_A (N ⊗_A (A ⊗_R L))` and `N ⊗_A (A ⊗_R L) ≅ N ⊗_R L` is acyclic.

## Main results

* `CochainComplex.kFlat_restrictScalars_tensorObj`
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace CochainComplex

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Acyclicity of a tensor product of complexes does not depend on the order of the factors. -/
theorem acyclic_tensorObj_comm {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : (K ⊗ L).Acyclic) : (L ⊗ K).Acyclic :=
  HomologicalComplex.Acyclic.of_iso (Koszul.complexBraiding K L) h

/-- **A tensor product with a relatively K-flat complex is K-flat over the base.** If `M` is a
K-flat complex of `A`-modules and `N` is a complex of `A`-modules which is K-flat over `R`, then
`M ⊗_A N` is K-flat over `R`. -/
theorem kFlat_restrictScalars_tensorObj (φ : R →+* A) {M N : CochainComplex (ModuleCat.{u} A) ℤ}
    (hM : M.KFlat) (hN : ((CochainComplex.restrictScalars φ).obj N).KFlat) :
    ((CochainComplex.restrictScalars φ).obj (M ⊗ N)).KFlat := by
  intro L hL
  -- `N ⊗_A (A ⊗_R L)` is acyclic, being `N ⊗_R L` after restriction to `R`.
  have hNL : (N ⊗ (CochainComplex.extendScalars φ).obj L).Acyclic := by
    have h₁ : (L ⊗ (CochainComplex.restrictScalars φ).obj N).Acyclic := hN L hL
    have h₂ : ((CochainComplex.restrictScalars φ).obj
        (N ⊗ (CochainComplex.extendScalars φ).obj L)).Acyclic :=
      HomologicalComplex.Acyclic.of_iso (baseChangeTensorIso φ L N).symm
        (acyclic_tensorObj_comm h₁)
    exact (CochainComplex.restrictScalars_acyclic_iff φ _).mp h₂
  -- hence so is `(M ⊗_A N) ⊗_A (A ⊗_R L)`, by K-flatness of `M`.
  have hMNL : ((M ⊗ N) ⊗ (CochainComplex.extendScalars φ).obj L).Acyclic :=
    HomologicalComplex.Acyclic.of_iso (α_ M N _).symm
      (acyclic_tensorObj_comm (hM _ hNL))
  have h₃ : ((CochainComplex.restrictScalars φ).obj
      ((M ⊗ N) ⊗ (CochainComplex.extendScalars φ).obj L)).Acyclic :=
    (CochainComplex.restrictScalars_acyclic_iff φ _).mpr hMNL
  exact acyclic_tensorObj_comm
    (HomologicalComplex.Acyclic.of_iso (baseChangeTensorIso φ L (M ⊗ N)) h₃)

end CochainComplex
