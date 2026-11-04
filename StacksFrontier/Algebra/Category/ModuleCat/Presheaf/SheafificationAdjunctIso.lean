module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# When the adjunct of a map into a sheaf of modules is an isomorphism

Let `α : R₀ ⟶ R.obj` exhibit a sheaf of rings `R` as the sheafification of a presheaf of rings
`R₀`, let `P` be a presheaf of `R₀`-modules, `G` a sheaf of `R`-modules and `c : P ⟶ G` a map of
presheaves of `R₀`-modules. Its adjunct `c^♯ : P^♯ ⟶ G` under the sheafification adjunction is an
isomorphism if and only if `c` is a local isomorphism, that is locally injective and locally
surjective on underlying abelian presheaves.

## Main results

* `PresheafOfModules.isIso_sheafificationAdjunction_homEquiv_symm_iff`.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The adjunct `c^♯ : P^♯ ⟶ G`, under the sheafification adjunction of presheaves of modules, of
a map `c : P ⟶ G` from a presheaf of modules to a sheaf of modules is an isomorphism exactly when
`c` is locally injective and locally surjective on underlying abelian presheaves. -/
theorem isIso_sheafificationAdjunction_homEquiv_symm_iff {P : PresheafOfModules.{v} R₀}
    {G : SheafOfModules.{v} R}
    (c : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj G)) :
    IsIso (((sheafificationAdjunction α).homEquiv P G).symm c) ↔
      Presheaf.IsLocallyInjective J ((toPresheaf R₀).map c) ∧
        Presheaf.IsLocallySurjective J ((toPresheaf R₀).map c) := by
  rw [Adjunction.homEquiv_counit, ← GrothendieckTopology.W_iff_isLocallyBijective,
    GrothendieckTopology.W_iff]
  constructor
  · intro h
    have h₁ : IsIso ((sheafification α).map c) :=
      IsIso.of_isIso_comp_right _ ((sheafificationAdjunction α).counit.app G)
    exact (inferInstance : IsIso ((SheafOfModules.toSheaf _).map ((sheafification α).map c)))
  · intro h
    have : IsIso ((SheafOfModules.toSheaf _).map ((sheafification α).map c)) := h
    have : IsIso ((sheafification α).map c) := isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
    infer_instance

end PresheafOfModules

end
