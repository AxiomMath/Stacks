module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitialForget

/-!
# Global sections at an initial object, as a linear equivalence over a base ring

`Stacks.Cohomology.SiteModules.globalSectionsEquivOfIsInitial` identifies the compatible families
of sections of a sheaf of modules with its sections at an initial object `X` of `Cᵒᵖ`, with the
universes of the site, of the structure rings and of the modules independent. This file records
that identification as an isomorphism of modules over a base ring acting on both sides.

## Main definitions

* `Stacks.Cohomology.SiteModules.globalSectionsLinearEquivOfIsInitial`: evaluation at an initial
  object of `Cᵒᵖ`, as an isomorphism of modules over a base ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r w

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{r}) [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)]

variable {A : Type*} [CommRing A]

/-- Evaluation at an initial object `X` of `Cᵒᵖ`, as an isomorphism of `A`-modules, for a base
ring `A` acting on the compatible families through `ρ` and on the sections at `X` through the
composite of `ρ` with evaluation. This is
`Stacks.Cohomology.SiteModules.globalSectionsLinearEquivInitial` with the universes independent. -/
def globalSectionsLinearEquivOfIsInitial (M : SheafOfModules.{w} O) (X : Cᵒᵖ) (hX : IsInitial X)
    (ρ : A →+* ↥(GlobalSectionRing O)) (σ : A →+* O.obj.obj X)
    (hρσ : (globalSectionEval O X).comp ρ = σ) :
    letI := Module.compHom (GlobalSections O M) ρ
    letI := Module.compHom (M.val.obj X : Type _) σ
    GlobalSections O M ≃ₗ[A] (M.val.obj X : Type _) :=
  letI := Module.compHom (GlobalSections O M) ρ
  letI := Module.compHom (M.val.obj X : Type _) σ
  { globalSectionsEquivOfIsInitial O M X hX with
    map_add' := fun s t => rfl
    map_smul' := fun a s => by
      change (ρ a • s).eval X = σ a • s.eval X
      rw [globalSections_smul_apply, ← hρσ]
      rfl }

end Stacks.Cohomology.SiteModules

end
