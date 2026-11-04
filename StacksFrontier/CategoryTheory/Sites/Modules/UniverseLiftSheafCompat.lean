module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSheaf

/-!
# Compatibilities of the transport of sheaves of modules

Let `T : RingTransport e R R'` be a ring transport along an equivalence of sites `e : C ≌ D`
(ring isomorphisms `R'(Y) ≃+* R(e⁻¹ Y)`, natural in `Y`). This file records how the induced
transport of sheaves of modules `Stacks.UniverseLift.RingTransport.sheafFunctor` interacts with
the other operations on sheaves of modules:

* with sheafification: transporting a presheaf of modules and then sheafifying is sheafifying
  and then transporting (`RingTransport.sheafificationCompSheafFunctorIso`);
* with restriction to a slice: restricting the transport to `D/U'` is transporting the
  restriction to `C/e⁻¹(U')` along the ring transport on slices `RingTransport.over`
  (`RingTransport.sheafFunctorCompOverFunctorIso`);
* with restriction along a functor of sites: for functors `F : C₀ ⥤ C` and `F' : D₀ ⥤ D`
  compatible with equivalences `e₀ : C₀ ≌ D₀` and `e : C ≌ D`, restricting along `F'` the
  transport along `e` is transporting along `e₀` the restriction along `F`
  (`RingTransport.pullback`, `RingTransport.pushforward₀CompFunctorIso`).
-/

@[expose] public section

open CategoryTheory Opposite

universe m v₀ v₀' v₁ v₂ u₀ u₀' u₁ u₂ r₁ r₂

namespace Stacks.UniverseLift.RingTransport

section Sheafification

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {e : C ≌ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{r₁}} {R' : Sheaf K RingCat.{r₂}} (T : RingTransport e R.obj R'.obj)
  [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **The transport commutes with sheafification.** Transporting a presheaf of modules and then
sheafifying is sheafifying and then transporting: both functors are left adjoint to the
forgetful functor followed by the transport back. -/
noncomputable def sheafificationCompSheafFunctorIso :
    (T.functor : PresheafOfModules.{m} R.obj ⥤ _) ⋙
        PresheafOfModules.sheafification.{m} (𝟙 R'.obj) ≅
      PresheafOfModules.sheafification.{m} (𝟙 R.obj) ⋙ T.sheafFunctor :=
  Adjunction.leftAdjointUniq
    (T.equivalence.toAdjunction.comp (PresheafOfModules.sheafificationAdjunction (𝟙 R'.obj)))
    (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).comp
      T.sheafEquivalence.toAdjunction).ofNatIsoRight (Iso.refl _))

end Sheafification

section Over

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {e : C ≌ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{r₁}} {R' : Sheaf K RingCat.{r₂}} (T : RingTransport e R.obj R'.obj)
  [e.inverse.IsContinuous K J]

/-- **The transport commutes with restriction to slices.** For `U'` in `D`, restricting the
transport of a sheaf of modules to `D/U'` is transporting its restriction to `C/e⁻¹(U')` along
the ring transport on slices. -/
noncomputable def sheafFunctorCompOverFunctorIso (U' : D)
    [(Over.postEquiv U' e.symm).symm.inverse.IsContinuous (K.over U')
      (J.over (e.inverse.obj U'))] :
    T.sheafFunctor ⋙ SheafOfModules.overFunctor.{m} R' U' ≅
      SheafOfModules.overFunctor.{m} R (e.inverse.obj U') ⋙
        (T.over U').sheafFunctor (R := R.over (e.inverse.obj U')) (R' := R'.over U') :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

end Over

section Pullback

variable {C₀ : Type u₀} [Category.{v₀} C₀] {D₀ : Type u₀'} [Category.{v₀'} D₀] {e₀ : C₀ ≌ D₀}
  {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {e : C ≌ D}
  {R : Cᵒᵖ ⥤ RingCat.{r₁}} {R' : Dᵒᵖ ⥤ RingCat.{r₂}} (T : RingTransport e R R')
  {F : C₀ ⥤ C} {F' : D₀ ⥤ D} (h : F' ⋙ e.inverse ≅ e₀.inverse ⋙ F)

/-- **The restriction of a ring transport along compatible functors.** For functors
`F : C₀ ⥤ C` and `F' : D₀ ⥤ D` with `F' ⋙ e⁻¹ ≅ e₀⁻¹ ⋙ F`, the ring isomorphisms
`R'(F' Y₀) ≃+* R(e⁻¹ F' Y₀) ≃+* R(F e₀⁻¹ Y₀)` form a ring transport along `e₀` from the
restriction of `R` along `F` to the restriction of `R'` along `F'`. -/
noncomputable def pullback : RingTransport e₀ (F.op ⋙ R) (F'.op ⋙ R') where
  iso Y₀ := (T.iso (F'.op.obj Y₀)).trans (R.mapIso (h.app Y₀.unop).op.symm).ringCatIsoToRingEquiv
  naturality {Y₀ Y₀'} f x := by
    change (R.map (h.inv.app Y₀'.unop).op).hom
        (T.iso (F'.op.obj Y₀') ((R'.map (F'.op.map f)).hom x)) =
      (R.map (F.op.map (e₀.inverse.op.map f))).hom
        ((R.map (h.inv.app Y₀.unop).op).hom (T.iso (F'.op.obj Y₀) x))
    rw [T.naturality]
    change (R.map (e.inverse.op.map (F'.op.map f)) ≫ R.map (h.inv.app Y₀'.unop).op).hom _ =
      (R.map (h.inv.app Y₀.unop).op ≫ R.map (F.op.map (e₀.inverse.op.map f))).hom _
    rw [← R.map_comp, ← R.map_comp]
    congr 3
    exact Quiver.Hom.unop_inj (h.inv.naturality f.unop).symm

/-- The component at `M` and `Y₀` of `pushforward₀CompFunctorIso`: the restriction map of `M`
along `h : e⁻¹ (F' Y₀) ≅ F (e₀⁻¹ Y₀)`. -/
noncomputable def pushforward₀CompFunctorIsoApp (M : PresheafOfModules.{m} R) (Y₀ : D₀ᵒᵖ) :
    ((T.pullback h).functor.obj ((PresheafOfModules.pushforward₀ F R).obj M)).obj Y₀ ≅
      ((PresheafOfModules.pushforward₀ F' R').obj (T.functor.obj M)).obj Y₀ :=
  LinearEquiv.toModuleIso (R := R'.obj (F'.op.obj Y₀))
    (X₁ := ((T.pullback h).functor.obj ((PresheafOfModules.pushforward₀ F R).obj M)).obj Y₀)
    (X₂ := ((PresheafOfModules.pushforward₀ F' R').obj (T.functor.obj M)).obj Y₀)
    (m₁ := ModuleCat.isModule _) (m₂ := ModuleCat.isModule _)
    { toFun := M.map (h.hom.app Y₀.unop).op
      map_add' := map_add _
      map_smul' := fun r x ↦ by
        have hr : (R.map (h.hom.app Y₀.unop).op).hom
            ((R.map (h.inv.app Y₀.unop).op).hom (T.iso (F'.op.obj Y₀) r)) =
            T.iso (F'.op.obj Y₀) r := by
          change (R.map (h.inv.app Y₀.unop).op ≫ R.map (h.hom.app Y₀.unop).op).hom _ = _
          rw [← R.map_comp, ← op_comp, Iso.hom_inv_id_app]
          simp
        refine (M.map_smul (h.hom.app Y₀.unop).op
          ((R.map (h.inv.app Y₀.unop).op).hom (T.iso (F'.op.obj Y₀) r)) x).trans ?_
        rw [hr]
        rfl
      invFun := M.map (h.inv.app Y₀.unop).op
      left_inv := map_map_of_comp_eq_id M _ _ (by rw [← op_comp, Iso.inv_hom_id_app]; rfl)
      right_inv := map_map_of_comp_eq_id M _ _ (by rw [← op_comp, Iso.hom_inv_id_app]; rfl) }

/-- **The transport commutes with restriction along compatible functors.** Restricting along
`F'` the transport along `e` of a presheaf of modules is transporting along `e₀` its restriction
along `F`. -/
noncomputable def pushforward₀CompFunctorIso :
    PresheafOfModules.pushforward₀.{m} F R ⋙ (T.pullback h).functor ≅
      T.functor ⋙ PresheafOfModules.pushforward₀.{m} F' R' :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModules.isoMk (T.pushforward₀CompFunctorIsoApp h M) (fun Y₀ Y₀' f ↦ by
      ext x
      exact map_map_eq_map_map M _ _ _ _
        (Quiver.Hom.unop_inj (h.hom.naturality f.unop).symm) x))
    (fun {M N} φ ↦ by
      ext Y₀ x
      exact (PresheafOfModules.naturality_apply φ (h.hom.app Y₀.unop).op x).symm)

section Sheaf

variable {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{r₁}} {R' : Sheaf K RingCat.{r₂}} (T : RingTransport e R.obj R'.obj)
  [F.IsContinuous J₀ J] [F'.IsContinuous K₀ K]
  [e₀.inverse.IsContinuous K₀ J₀] [e.inverse.IsContinuous K J]

/-- **The transport of sheaves of modules commutes with restriction along compatible continuous
functors.** For continuous `F : C₀ ⥤ C` and `F' : D₀ ⥤ D` with `F' ⋙ e⁻¹ ≅ e₀⁻¹ ⋙ F`,
restricting along `F'` the transport along `e` of a sheaf of modules is transporting along `e₀`
its restriction along `F`. -/
noncomputable def sheafPushforwardCompSheafFunctorIso :
    SheafOfModules.pushforward.{m}
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{r₁} J₀ J).obj R)) ⋙
      (T.pullback h).sheafFunctor
        (R := (F.sheafPushforwardContinuous RingCat.{r₁} J₀ J).obj R)
        (R' := (F'.sheafPushforwardContinuous RingCat.{r₂} K₀ K).obj R') ≅
      T.sheafFunctor ⋙ SheafOfModules.pushforward.{m}
        (𝟙 ((F'.sheafPushforwardContinuous RingCat.{r₂} K₀ K).obj R')) :=
  NatIso.ofComponents
    (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      ((T.pushforward₀CompFunctorIso h).app M.val))
    (fun φ ↦ SheafOfModules.hom_ext ((T.pushforward₀CompFunctorIso h).hom.naturality φ.val))

end Sheaf

end Pullback

end Stacks.UniverseLift.RingTransport
