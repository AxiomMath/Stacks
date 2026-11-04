module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.SliceTransport
public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.SummandTotalRestriction

/-!
# Restriction to an object of `C/X`, two ways
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) {X₀ : X.C}

/-- The two ways of reading an object `W` of the iterated slice `(C/X)/V` as an object of `C/X`
agree: forgetting `V`, or going down to `C/V`, then along `a : V ⟶ U` and `f : U ⟶ X`. -/
def iteratedSliceForwardOverMapIso (V : Over X₀) {U : X.C} (a : V.left ⟶ U) (f : U ⟶ X₀)
    (w : a ≫ f = V.hom) :
    Over.forget V ≅ (Over.mk V.hom).iteratedSliceForward ⋙ Over.map a ⋙ Over.map f :=
  NatIso.ofComponents (fun W => Over.isoMk (Iso.refl _) (by
      simp only [Functor.comp_obj, Over.forget_obj, Over.map_obj_hom, Iso.refl_hom,
        Category.id_comp, Category.assoc, w]
      exact (Category.id_comp _).trans (Over.w W.hom))) fun {W W'} k => by
    refine Over.OverMorphism.ext ?_
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Restricting a sheaf of modules on `C/X` along `f : U ⟶ X` and `a : V ⟶ U` and transporting
it to the iterated slice `(C/X)/V` is restricting it to `V`.** -/
def sliceRestrictionOverMapModulesIso (V : Over X₀) {U : X.C} (a : V.left ⟶ U) (f : U ⟶ X₀)
    (w : a ≫ f = V.hom) :
    SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f ⋙
        SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) a ⋙
          X.iteratedSliceTransport X₀ V ≅
      SheafOfModules.overFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over X₀) V :=
  SheafOfModules.pushforwardComp₃Iso _ _ _ _ _ _ _ (X.iteratedSliceForwardOverMapIso V a f w)
    (h₃ := inferInstanceAs ((Over.mk V.hom).iteratedSliceForward.IsContinuous
      ((X.J.over X₀).over (Over.mk V.hom)) (X.J.over (Over.mk V.hom).left)))
    (hG := inferInstanceAs ((Over.forget V).IsContinuous ((X.J.over X₀).over V) (X.J.over X₀)))
    (by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun W => RingCat.hom_ext (RingHom.ext fun x => ?_))
    exact congrArg (fun g => (RingCat.Hom.hom g) x)
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map_id (op W.unop.left.left)))

/-- The component at `N` of the forward map of `sliceRestrictionOverMapModulesIso` fixes
sections. -/
theorem sliceRestrictionOverMapModulesIso_hom_app_fixesSections (V : Over X₀) {U : X.C}
    (a : V.left ⟶ U) (f : U ⟶ X₀) (w : a ≫ f = V.hom)
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over X₀)) :
    SheafOfModules.FixesSections ((X.sliceRestrictionOverMapModulesIso V a f w).hom.app N) :=
  SheafOfModules.pushforwardComp₃Iso_hom_app_fixesSections _ _ _ _ _ _ _ _
    (h₃ := inferInstanceAs ((Over.mk V.hom).iteratedSliceForward.IsContinuous
      ((X.J.over X₀).over (Over.mk V.hom)) (X.J.over (Over.mk V.hom).left)))
    (hG := inferInstanceAs ((Over.forget V).IsContinuous ((X.J.over X₀).over V) (X.J.over X₀)))
    _ N (fun W x => Stacks.SheafOfModules.heq_presheaf_map_of_left_eq_id N.val.presheaf _ rfl x)

/-- The component at `N` of the inverse map of `sliceRestrictionOverMapModulesIso` fixes
sections. -/
theorem sliceRestrictionOverMapModulesIso_inv_app_fixesSections (V : Over X₀) {U : X.C}
    (a : V.left ⟶ U) (f : U ⟶ X₀) (w : a ≫ f = V.hom)
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over X₀)) :
    SheafOfModules.FixesSections ((X.sliceRestrictionOverMapModulesIso V a f w).inv.app N) :=
  SheafOfModules.FixesSections.inv ((X.sliceRestrictionOverMapModulesIso V a f w).app N)
    (X.sliceRestrictionOverMapModulesIso_hom_app_fixesSections V a f w N)

end AlgebraicGeometry.RingedSite

end
