module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# A sheafified morphism of modules is a monomorphism when its kernel dies locally

Let `t : P ⟶ F` be a morphism from a presheaf of modules to a sheaf of modules, and let
`φ : P^♯ ⟶ F` be the morphism it induces on the sheafification.  If every section of `P` killed
by `t` vanishes locally, then `φ` is a monomorphism.

The unit `P ⟶ P^♯` is locally surjective and its composite with `φ` is `t`, which the hypothesis
makes locally injective; so `φ` is locally injective, hence injective on sections because its
source is a sheaf, hence a monomorphism.

## Main results

* `PresheafOfModules.mono_sheafificationHomEquiv_symm_of_locally_eq_zero`.
-/

@[expose] public section

open CategoryTheory

universe v u v' u'

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget AddCommGrpCat.{v})]

/-- **A sheafified morphism of modules whose kernel dies locally is a monomorphism.**  If
`t : P ⟶ F` kills a section of `P` only when that section vanishes on a covering sieve, then the
morphism `P^♯ ⟶ F` it induces on the sheafification is a monomorphism. -/
theorem mono_sheafificationHomEquiv_symm_of_locally_eq_zero
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (t : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F))
    (ht : ∀ (U : Cᵒᵖ) (x : P.obj U), t.app U x = 0 →
      ∃ S : Sieve U.unop, S ∈ J U.unop ∧ ∀ (V : C) (g : V ⟶ U.unop), S g → P.map g.op x = 0) :
    Mono ((sheafificationHomEquiv α).symm t) := by
  have hfac : CategoryTheory.toSheafify J P.presheaf ≫
      (toPresheaf R.obj).map ((sheafificationHomEquiv α).symm t).val = (toPresheaf R₀).map t := by
    rw [← toPresheaf_map_sheafificationHomEquiv_def, Equiv.apply_symm_apply]
  have ht' : Presheaf.IsLocallyInjective J ((toPresheaf R₀).map t) := by
    constructor
    intro U x y hxy
    let x' : P.obj U := x
    let y' : P.obj U := y
    have hxy' : t.app U x' = t.app U y' := hxy
    obtain ⟨S, hS, hS'⟩ := ht U (x' - y') (by rw [map_sub, hxy', sub_self])
    refine J.superset_covering (fun V g hg => ?_) hS
    have h0 := hS' V g hg
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have hφ : Presheaf.IsLocallyInjective J
      ((toPresheaf R.obj).map ((sheafificationHomEquiv α).symm t).val) := by
    have : Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.presheaf ≫
        (toPresheaf R.obj).map ((sheafificationHomEquiv α).symm t).val) := by
      rw [hfac]
      exact ht'
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J
      (CategoryTheory.toSheafify J P.presheaf) _
  have hφ' : Sheaf.IsLocallyInjective
      ((SheafOfModules.toSheaf R).map ((sheafificationHomEquiv α).symm t)) := hφ
  have := Sheaf.mono_of_isLocallyInjective
    ((SheafOfModules.toSheaf R).map ((sheafificationHomEquiv α).symm t))
  exact (SheafOfModules.toSheaf R).mono_of_mono_map this

end PresheafOfModules

end
