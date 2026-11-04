module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Descending an isomorphism along restriction of scalars through the unit

Let `φ : S →+* T` be a ring map, let `F ⊣ φ_*` be a left adjoint of derived restriction of
scalars `φ_* : D(T) ⥤ D(S)`, let `W` be an object of `D(S)` and `V` an object of `D(T)`.
Suppose that `φ_*(F W) ≅ φ_* V` in `D(S)`, by an isomorphism `σ` of which no `T`-linearity is
known, and that the unit `η_W : W ⟶ φ_*(F W)` is surjective on every cohomology module.  Then
`F W ≅ V` in `D(T)`.

Indeed, let `ψ : F W ⟶ V` be the transpose of `η_W ≫ σ`.  Then `η_W ≫ φ_* ψ = η_W ≫ σ`, and
cancelling the epimorphisms `Hⁿ(η_W)` gives `Hⁿ(φ_* ψ) = Hⁿ(σ)`, an isomorphism for every `n`.
So `φ_* ψ` is invertible, and derived restriction of scalars reflects isomorphisms.

## Main results

* `Dualizing.nonempty_iso_of_restrictScalars_iso_of_epi_unit` -- the descent.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Dualizing

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {S T : Type u} [CommRing S] [CommRing T]

/-- **Descent of an isomorphism through a cohomologically surjective unit.**  Let `F` be left
adjoint to derived restriction of scalars along `φ : S →+* T`, let `W` be an object of `D(S)`
whose unit `W ⟶ φ_*(F W)` is surjective on every cohomology module, and let `V` be an object of
`D(T)`.  Any isomorphism `φ_*(F W) ≅ φ_* V` of `D(S)` yields an isomorphism `F W ≅ V` of
`D(T)`. -/
theorem nonempty_iso_of_restrictScalars_iso_of_epi_unit (φ : S →+* T)
    {F : DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} T)}
    (adjE : F ⊣ (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory)
    (W : DerivedCategory (ModuleCat.{u} S)) (V : DerivedCategory (ModuleCat.{u} T))
    (σ : (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj (F.obj W) ≅
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj V)
    (hη : ∀ n : ℤ, Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
      (adjE.unit.app W))) :
    Nonempty (F.obj W ≅ V) := by
  let ψ : F.obj W ⟶ V := (adjE.homEquiv W V).symm (adjE.unit.app W ≫ σ.hom)
  have hψ : adjE.unit.app W ≫ (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map ψ =
      adjE.unit.app W ≫ σ.hom :=
    (adjE.homEquiv_unit W V ψ).symm.trans ((adjE.homEquiv W V).apply_symm_apply _)
  have hiso : IsIso ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map ψ) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have := hη n
    have h := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map hψ
    simp only [Functor.map_comp, cancel_epi] at h
    rw [h]
    infer_instance
  have : IsIso ψ :=
    isIso_of_reflects_iso ψ (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory
  exact ⟨asIso ψ⟩

end

end Dualizing

end
