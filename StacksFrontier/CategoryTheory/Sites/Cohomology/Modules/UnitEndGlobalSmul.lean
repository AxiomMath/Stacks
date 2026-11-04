module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward

/-!
# Endomorphisms of the structure sheaf as multiplication by global sections

Let `R` be a sheaf of rings on a site whose rings of sections are commutative.
`Stacks.Cohomology.SiteModules.unitEndEquiv` identifies the global sections of `R` with the
endomorphisms of the free module `R` of rank one, a section acting by right multiplication
(`Stacks.Cohomology.SiteModules.unitEnd`).  When the sections commute, right multiplication is
the multiplication `Stacks.Cohomology.SiteModules.globalSmul` by which global sections act on
every sheaf of `R`-modules; so an endomorphism `t` of `R` is multiplication by its value at `1`.

## Main results

* `Stacks.Cohomology.SiteModules.unitEnd_eq_globalSmul`: right multiplication by a global
  section on `R` is `Stacks.Cohomology.SiteModules.globalSmul` at `R`.
* `Stacks.Cohomology.SiteModules.eq_globalSmul_unitEndSection`: an endomorphism `t` of `R` is
  multiplication by the global section `Stacks.Cohomology.SiteModules.unitEndSection t`.
-/

@[expose] public section

open CategoryTheory
open scoped IsMulCommutative

universe v u w

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) [∀ X : Cᵒᵖ, IsMulCommutative (R.obj.obj X)]

/-- Right multiplication by a global section on the free module of rank one is multiplication by
that global section, the sections of `R` commuting. -/
theorem unitEnd_eq_globalSmul (a : GlobalSectionRing R) :
    unitEnd R a = globalSmul R a (SheafOfModules.unit R) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      (unitEnd_app_apply R a X x).trans (mul_comm (G := R.obj.obj X) x (a.1 X))))

/-- **An endomorphism of the free module of rank one is multiplication by its value at `1`.** -/
theorem eq_globalSmul_unitEndSection
    (t : SheafOfModules.unit R ⟶ SheafOfModules.unit R) :
    t = globalSmul R (unitEndSection R t) (SheafOfModules.unit R) :=
  ((unitEndEquiv R).apply_symm_apply t).symm.trans (unitEnd_eq_globalSmul R _)

end Stacks.Cohomology.SiteModules

end
