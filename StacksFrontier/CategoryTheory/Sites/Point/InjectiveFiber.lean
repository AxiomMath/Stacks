module

public import StacksFrontier.Algebra.Category.ModuleCat.FiniteFilteredColimit
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Fibers of sheaves of modules over a finite ring with injective sections

Let `Φ` be a point of a site and `R` a finite ring. The fiber at `Φ` of a presheaf of
`R`-modules is a filtered colimit of its modules of sections, so if every module of sections is
injective, the fiber is an injective `R`-module
(`ModuleCat.FiniteFilteredColimit.injective_pt`, Bass–Papp for a finite ring). Since sections of
an injective sheaf of modules are injective, this applies to the stalks of injective sheaves; it
is used in Step 7 of the proof of [Stacks, Tag 03UG].

## Main results

* `CategoryTheory.GrothendieckTopology.Point.moduleInjective_presheafFiber`
* `CategoryTheory.GrothendieckTopology.Point.moduleInjective_sheafFiber`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u u'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type u'} [Ring R]
  [Finite R] [LocallySmall.{max u' w} C] (Φ : Point.{max u' w} J)

/-- **The fiber of a presheaf of modules over a finite ring with injective sections is an
injective module.** -/
theorem moduleInjective_presheafFiber (P : Cᵒᵖ ⥤ ModuleCat.{max u' w} R)
    (hP : ∀ X, Module.Injective R (P.obj X)) :
    Module.Injective R ((Φ.presheafFiber (A := ModuleCat.{max u' w} R)).obj P) := by
  have :
      PreservesFilteredColimitsOfSize.{max u' w, max u' w} (forget (ModuleCat.{max u' w} R)) := by
    change PreservesFilteredColimitsOfSize.{max u' w, max u' w}
      (forget₂ (ModuleCat.{max u' w} R) AddCommGrpCat.{max u' w} ⋙ forget AddCommGrpCat.{max u' w})
    infer_instance
  exact ModuleCat.FiniteFilteredColimit.injective_pt _ (Φ.isColimitPresheafFiberCocone P)
    (fun j => hP _)

/-- **The fiber of a sheaf of modules over a finite ring with injective sections is an injective
module.** -/
theorem moduleInjective_sheafFiber (F : Sheaf J (ModuleCat.{max u' w} R))
    (hF : ∀ X, Module.Injective R (F.obj.obj X)) :
    Module.Injective R ((Φ.sheafFiber (A := ModuleCat.{max u' w} R)).obj F) :=
  Φ.moduleInjective_presheafFiber F.obj hF

end CategoryTheory.GrothendieckTopology.Point

end
