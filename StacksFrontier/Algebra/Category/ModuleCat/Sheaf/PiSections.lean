module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# The sections of a product of sheaves of modules

For a family `F : ι → SheafOfModules R` of sheaves of modules on a site, the sections of the
product `∏ᶜ F` over an object `U` are the product of the sections: the map sending a section to
the family of its images under the projections is bijective.  The forgetful functor from sheaves
of modules to presheaves of modules and the evaluation at `U` both preserve limits, and in a
category of modules the product is the cartesian product.

## Main results

* `SheafOfModules.bijective_pi_π_val_app`: the sections of `∏ᶜ F` over `U` are the product of
  the sections of the `F i` over `U`, through the projections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u u'

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **The sections of a product of sheaves of modules are the product of the sections**: for a
family `F` indexed by a type `ι : Type` (for instance `Fin r`), the map sending a section of
`∏ᶜ F` over `U` to the family of its projections is bijective. -/
theorem bijective_pi_π_val_app {ι : Type} (F : ι → SheafOfModules.{w} R)
    [HasProduct F] (U : Cᵒᵖ) :
    Function.Bijective (fun x : (∏ᶜ F).val.obj U => fun i => ((Pi.π F i).val.app U).hom x) := by
  let E := SheafOfModules.forget.{w} R ⋙ PresheafOfModules.evaluation.{w} R.obj U
  let e := PreservesProduct.iso E F ≪≫ ModuleCat.piIsoPi (fun i => E.obj (F i))
  have he : (fun x : (∏ᶜ F).val.obj U => fun i => ((Pi.π F i).val.app U).hom x) = e.hom := by
    funext x i
    have h1 : ((Pi.π F i).val.app U).hom x =
        (Pi.π (fun i => E.obj (F i)) i).hom ((piComparison E F).hom x) := by
      exact (congrArg (fun k => ModuleCat.Hom.hom k x) (piComparison_comp_π E F i)).symm
    have h2 := congrArg (fun k => k.hom ((piComparison E F).hom x))
      (ModuleCat.piIsoPi_hom_ker_subtype (fun i => E.obj (F i)) i)
    rw [h1, ← h2]
    rfl
  rw [he]
  exact ConcreteCategory.bijective_of_isIso e.hom

end SheafOfModules

end
