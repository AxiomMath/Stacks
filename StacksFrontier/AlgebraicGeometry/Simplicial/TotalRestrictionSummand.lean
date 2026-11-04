module

public import StacksFrontier.AlgebraicGeometry.Simplicial.TotalRestrictionTransition

/-!
# Restricting to `(C/K)_total` and then to a summand is restricting to the slice

Let `(C, O_C)` be a ringed site and `K` a simplicial semi-representable object of `C`, with
`K_n = {U_{n,i}}_{i ∈ I_n}`. Restricting a sheaf of `O_C`-modules `N` along the localization
functor `j_total` to the total site `(C/K)_total`, then to the degree-`n` component `C/K_n`, and
then to its summand `C/U_{n,i}`, is the restriction `N|_{C/U_{n,i}}` of `N` to the slice: the
composite of the three functors of sites is the forgetful functor `C/U_{n,i} ⥤ C`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.totalRestrictionSummandIso`:
  `((N|_{(C/K)_total})_n)|_{C/U_{n,i}} ≅ N|_{C/U_{n,i}}`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.totalRestrictionSummandIso_hom_app_fixesSections`:
  that identification is the identity on sections.

## References

* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0DCB](https://stacks.math.columbia.edu/tag/0DCB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace SheafOfModules

/-- **Three successive pushforwards of sheaves of modules are one**, along a functor of sites
isomorphic to the composite: `pushforwardComp` twice followed by `pushforwardCongr₂`. The
continuity of the three functors is taken as named instance arguments, so that a consumer can
supply it at whichever spelling of the intermediate sites it has. -/
noncomputable def pushforwardComp₃ {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
    {J₃ : GrothendieckTopology C₃} {J₄ : GrothendieckTopology C₄}
    (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ C₃) (F₃ : C₃ ⥤ C₄) (G : C₁ ⥤ C₄)
    [h₁ : F₁.IsContinuous J₁ J₂] [h₂ : F₂.IsContinuous J₂ J₃] [h₃ : F₃.IsContinuous J₃ J₄]
    [hG : G.IsContinuous J₁ J₄]
    {R₁ : Sheaf J₁ RingCat.{u}} {R₂ : Sheaf J₂ RingCat.{u}} {R₃ : Sheaf J₃ RingCat.{u}}
    {R₄ : Sheaf J₄ RingCat.{u}}
    (φ₁ : R₁ ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} J₁ J₂).obj R₂)
    (φ₂ : R₂ ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J₂ J₃).obj R₃)
    (φ₃ : R₃ ⟶ (F₃.sheafPushforwardContinuous RingCat.{u} J₃ J₄).obj R₄)
    (ψ : R₁ ⟶ (G.sheafPushforwardContinuous RingCat.{u} J₁ J₄).obj R₄)
    (e : G ≅ (F₁ ⋙ F₂) ⋙ F₃)
    (he : haveI := Functor.isContinuous_comp F₁ F₂ J₁ J₂ J₃
      haveI := Functor.isContinuous_comp (F₁ ⋙ F₂) F₃ J₁ J₃ J₄
      ((φ₁ ≫ (F₁.sheafPushforwardContinuous RingCat.{u} J₁ J₂).map φ₂) ≫
        ((F₁ ⋙ F₂).sheafPushforwardContinuous RingCat.{u} J₁ J₃).map φ₃) ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J₁ J₄).app R₄ = ψ) :
    SheafOfModules.pushforward.{u} φ₃ ⋙ SheafOfModules.pushforward.{u} φ₂ ⋙
        SheafOfModules.pushforward.{u} φ₁ ≅ SheafOfModules.pushforward.{u} ψ :=
  haveI := Functor.isContinuous_comp F₁ F₂ J₁ J₂ J₃
  haveI := Functor.isContinuous_comp (F₁ ⋙ F₂) F₃ J₁ J₃ J₄
  Functor.isoWhiskerLeft _ (SheafOfModules.pushforwardComp φ₁ φ₂) ≪≫
    SheafOfModules.pushforwardComp _ φ₃ ≪≫ SheafOfModules.pushforwardCongr₂ _ e he

/-- `pushforwardComp₃` fixes sections when restriction along the components of `e` does. -/
theorem pushforwardComp₃_hom_app_fixesSections {C₁ C₂ C₃ C₄ : Type*} [Category C₁]
    [Category C₂] [Category C₃] [Category C₄] {J₁ : GrothendieckTopology C₁}
    {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃} {J₄ : GrothendieckTopology C₄}
    (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ C₃) (F₃ : C₃ ⥤ C₄) (G : C₁ ⥤ C₄)
    [h₁ : F₁.IsContinuous J₁ J₂] [h₂ : F₂.IsContinuous J₂ J₃] [h₃ : F₃.IsContinuous J₃ J₄]
    [G.IsContinuous J₁ J₄]
    {R₁ : Sheaf J₁ RingCat.{u}} {R₂ : Sheaf J₂ RingCat.{u}} {R₃ : Sheaf J₃ RingCat.{u}}
    {R₄ : Sheaf J₄ RingCat.{u}}
    (φ₁ : R₁ ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} J₁ J₂).obj R₂)
    (φ₂ : R₂ ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} J₂ J₃).obj R₃)
    (φ₃ : R₃ ⟶ (F₃.sheafPushforwardContinuous RingCat.{u} J₃ J₄).obj R₄)
    (ψ : R₁ ⟶ (G.sheafPushforwardContinuous RingCat.{u} J₁ J₄).obj R₄)
    (e : G ≅ (F₁ ⋙ F₂) ⋙ F₃) (he) (M : SheafOfModules.{u} R₄)
    (hM : ∀ (W : C₁) (x : M.val.obj (Opposite.op (((F₁ ⋙ F₂) ⋙ F₃).obj W))),
      HEq ((M.val.map (e.hom.app W).op).hom x) x) :
    FixesSections ((pushforwardComp₃ F₁ F₂ F₃ G φ₁ φ₂ φ₃ ψ e he).hom.app M) :=
  fun W x ↦ hM W.unop x

/-- Restriction along an identity moves no section. -/
theorem heq_val_map_id_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) (Y : C)
    (x : M.val.obj (Opposite.op Y)) : HEq ((M.val.map (𝟙 Y).op).hom x) x :=
  heq_of_eq (by simp; rfl)

end SheafOfModules

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- **`((N|_{(C/K)_total})_n)|_{C/U_{n,i}} = N|_{C/U_{n,i}}`**: restricting a sheaf of
`O_C`-modules to the total site, then to the degree-`n` component, then to the summand
`C/U_{n,i}`, is restricting it to the slice at `U_{n,i}`. -/
def totalRestrictionSummandIso (n : SimplexCategory) (i : (K.obj (op n)).I) :
    totalRestriction X K ⋙ (situation X.J K).componentModulesRestriction (structureSheaf X K) n ⋙
        summandRestriction X K n i ≅
      SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        ((K.obj (op n)).obj i) :=
  SheafOfModules.pushforwardComp₃ (h₁ := summandFunctor_isContinuous X K n i)
    (h₂ := (inferInstance : ((situation X.J K).componentFunctor n).IsContinuous
      ((situation X.J K).componentTopology n) (situation X.J K).totalTopology))
    (h₃ := totalForget_isContinuous X.J K)
    (summandFunctor X K n i) ((situation X.J K).componentFunctor n) (totalForget K)
    (Over.forget ((K.obj (op n)).obj i)) _ _ _ (𝟙 _) (summandForgetIso X K n i).symm (by
      ext W x
      change ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (𝟙 W.unop.left).op).hom x = x
      rw [op_id, CategoryTheory.Functor.map_id]
      rfl)

/-- **`totalRestrictionSummandIso` is the identity on sections.** -/
theorem totalRestrictionSummandIso_hom_app_fixesSections (n : SimplexCategory)
    (i : (K.obj (op n)).I) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.FixesSections ((totalRestrictionSummandIso X K n i).hom.app M) := by
  refine SheafOfModules.pushforwardComp₃_hom_app_fixesSections
    (h₁ := summandFunctor_isContinuous X K n i)
    (h₂ := (inferInstance : ((situation X.J K).componentFunctor n).IsContinuous
      ((situation X.J K).componentTopology n) (situation X.J K).totalTopology))
    (h₃ := totalForget_isContinuous X.J K) _ _ _ _ _ _ _ _ _ _ M fun W x ↦ ?_
  rw [Iso.symm_hom, summandForgetIso_inv_app]
  exact SheafOfModules.heq_val_map_id_apply M W.left x

omit [X.J.toCoverage.HasPullbacks] in
/-- The comparison `(N|_{C/U})|_{C/V} = N|_{C/V}` of restrictions along an arrow `V ⟶ U` of the
site is the identity on sections. -/
theorem overFunctorMap_hom_app_fixesSections {U V : X.C} (f : V ⟶ U)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.FixesSections
      ((SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).hom.app N) :=
  fun _ _ ↦ HEq.rfl

/-- **The transitions of `N|_{(C/K)_total}` are the restrictions of `N` along the arrows of
`K`**, summandwise: on the summand `C/U_{n,i}`, the transition `f_φ^*(N|)_m ⟶ (N|)_n` of
Stacks 09WF, under the identifications of `totalRestrictionSummandIso`, is the comparison
`(N|_{C/U_{m,j}})|_{C/U_{n,i}} = N|_{C/U_{n,i}}` along the arrow `U_{n,i} ⟶ U_{m,j}` of `K(φ)`. -/
theorem totalRestriction_summand_transition {m n : SimplexCategory} (φ : m ⟶ n)
    (i : (K.obj (op n)).I)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (summandRestriction X K n i).map
        (((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app
          ((totalRestriction X K).obj N)) ≫ (totalRestrictionSummandIso X K n i).hom.app N =
      (summandRestriction X K n i).map ((transitionPullbackModulesIso X K φ).hom.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj
            ((totalRestriction X K).obj N))) ≫
        (summandTransitionRestrictionIso X K φ i).hom.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj
            ((totalRestriction X K).obj N)) ≫
          (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            ((K.map φ.op).φ i)).map
              ((totalRestrictionSummandIso X K m ((K.map φ.op).f i)).hom.app N) ≫
            (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              ((K.map φ.op).φ i)).hom.app N := by
  have h : ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app
      ((totalRestriction X K).obj N) =
      (transitionPullbackModulesIso X K φ).hom.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj
            ((totalRestriction X K).obj N)) ≫
        ((transitionPullbackModulesIso X K φ).inv.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj
            ((totalRestriction X K).obj N)) ≫
        ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app
          ((totalRestriction X K).obj N)) := by
    rw [Iso.hom_inv_id_app_assoc]
  rw [h, Functor.map_comp, Category.assoc]
  refine congrArg (_ ≫ ·) (SheafOfModules.FixesSections.ext ?_ ?_)
  · exact SheafOfModules.FixesSections.comp
      (summandRestriction_map_fixesSections X K n i
        (totalRestriction_transition_fixesSections X K φ N))
      (totalRestrictionSummandIso_hom_app_fixesSections X K n i N)
  · exact SheafOfModules.FixesSections.comp
      (summandTransitionRestrictionIso_hom_app_fixesSections X K φ i _)
      (SheafOfModules.FixesSections.comp
        (overMap_map_fixesSections X ((K.map φ.op).φ i)
          (totalRestrictionSummandIso_hom_app_fixesSections X K m ((K.map φ.op).f i) N))
        (overFunctorMap_hom_app_fixesSections X ((K.map φ.op).φ i) N))

end CategoryTheory.SimplicialSemiRepresentable

end
