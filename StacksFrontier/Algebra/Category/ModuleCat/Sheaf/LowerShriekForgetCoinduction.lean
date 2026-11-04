module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianCoinduction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForget

/-!
# The two lower shrieks agree when the structure sheaf is a slicewise Kan extension

Let `F : C ⥤ D` be a continuous functor of sites, `R` a sheaf of rings on `D` and `S = F^{-1}R`
its restriction to `C`, so that restriction of sheaves of modules along `F` is pushforward along
`𝟙 S`. Lower shriek on sheaves of modules and lower shriek on the underlying abelian sheaves are
compared by the canonical transformation `Stacks.SheafOfModules.lowerShriekForgetComparison`.
This file proves that it is an isomorphism as soon as, for every object `V` of `C`, the abelian
presheaf `R|_{F(V)}` on the slice `D/F(V)` is the left Kan extension of its restriction along
`Over.post F : C/V ⥤ D/F(V)`, in the sense that restriction along `Over.post F` is bijective on
morphisms out of it.

## Main definitions

* `Stacks.SheafOfModules.restrictPost`: restriction along `Over.post F` of morphisms
  `R|_{F(V)} ⟶ G|_{F(V)}` of abelian presheaves on `D/F(V)`.
* `Stacks.SheafOfModules.coinductionRestriction`: the restriction morphism
  `F_*(coind_R N) ⟶ coind_S (F_* N)` of coinduced modules.

## Main results

* `Stacks.SheafOfModules.isIso_coinductionRestriction`: the restriction morphism of coinduced
  modules is an isomorphism when `restrictPost` is bijective.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_bijective`: under the condition
  above the comparison transformation `lowerShriekForgetComparison` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u₁ v₁ u₂ v₂

namespace Stacks.SheafOfModules

open AbelianCoinduction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{w})

/-- Restriction along `Over.post F` of a morphism `R|_{F(V)} ⟶ G|_{F(V)}` of abelian presheaves on
`D/F(V)`, giving a morphism `(F^{-1}R)|_V ⟶ (F^{-1}G)|_V` on `C/V`. -/
def restrictPost (G : Dᵒᵖ ⥤ AddCommGrpCat.{w}) (V : C) :
    Hom R.obj G (F.obj V) →+ Hom (F.op ⋙ R.obj) (F.op ⋙ G) V where
  toFun β := Hom.mk (Functor.whiskerLeft (Over.post F).op β.nat)
  map_zero' := rfl
  map_add' _ _ := rfl

variable {F R} in
/-- Evaluating `restrictPost F R G V β` at `W : Over V` is evaluating `β` at
`(Over.post F).obj W`. -/
@[simp]
lemma restrictPost_eval (G : Dᵒᵖ ⥤ AddCommGrpCat.{w}) {V : C} (β : Hom R.obj G (F.obj V))
    (W : Over V) (r : R.obj.obj (op (F.obj W.left))) :
    (restrictPost F R G V β).eval W r = β.eval ((Over.post F).obj W) r := rfl

variable {F R} in
/-- Restriction along `Over.post F` commutes with multiplication by a section of `R` over
`F(V)`. -/
lemma restrictPost_smul (G : Dᵒᵖ ⥤ AddCommGrpCat.{w}) {V : C} (a : R.obj.obj (op (F.obj V)))
    (β : Hom R.obj G (F.obj V)) :
    restrictPost F R G V (a • β) = (id a : (F.op ⋙ R.obj).obj (op V)) •
      restrictPost F R G V β := rfl

variable {F R} in
/-- Restriction along `Over.post F` commutes with restriction along a morphism `f : V' ⟶ V`
of `C`. -/
lemma restrictPost_restrict (G : Dᵒᵖ ⥤ AddCommGrpCat.{w}) {V V' : C} (f : V' ⟶ V)
    (β : Hom R.obj G (F.obj V)) :
    restrictPost F R G V' (restrict R.obj G (F.map f) β) =
      restrict (F.op ⋙ R.obj) (F.op ⋙ G) f (restrictPost F R G V β) := by
  ext W r
  exact β.eval_mk_congr (F.map_comp W.hom f).symm r

variable [∀ V : C, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})]
  [∀ V : D, LocallySmall.{w} ((Over V)ᵒᵖ ⥤ AddCommGrpCat.{w})]

/-- For an abelian sheaf `N` on `D`, the
restriction along `F` of the `R`-module coinduced by `N` maps to the `F^{-1}R`-module coinduced
by the restriction of `N`: a morphism `R|_{F(V)} ⟶ N|_{F(V)}` is restricted along
`Over.post F`. -/
def coinductionRestriction (N : Sheaf K AddCommGrpCat.{w}) :
    (_root_.SheafOfModules.pushforward.{w}
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{w} J K).obj R))).obj (obj R N) ⟶
      obj ((F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
        ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj N) :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        (X := Shrink.{w} (Hom R.obj N.obj (F.obj V.unop)))
        (Y := Shrink.{w} (Hom (F.op ⋙ R.obj) (F.op ⋙ N.obj) V.unop))
        ((sectionsEquiv (F.op ⋙ R.obj) (F.op ⋙ N.obj) V).symm.toAddMonoidHom.comp
          ((restrictPost F R N.obj V.unop).comp
            (sectionsEquiv R.obj N.obj (op (F.obj V.unop))).toAddMonoidHom))
      naturality := fun {V V'} f => by
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext
          fun (x : (presheaf R.obj N.obj).obj (op (F.obj V.unop))) => ?_)
        apply (sectionsEquiv (F.op ⋙ R.obj) (F.op ⋙ N.obj) V').injective
        change sectionsEquiv _ _ V' ((sectionsEquiv _ _ V').symm (restrictPost F R N.obj _
            (sectionsEquiv R.obj N.obj (op (F.obj V'.unop))
              ((presheaf R.obj N.obj).map (F.map f.unop).op x)))) =
          sectionsEquiv _ _ V' ((presheaf (F.op ⋙ R.obj) (F.op ⋙ N.obj)).map f
            ((sectionsEquiv _ _ V).symm (restrictPost F R N.obj _
              (sectionsEquiv R.obj N.obj (op (F.obj V.unop)) x))))
        rw [LinearEquiv.apply_symm_apply, sectionsEquiv_map (F.map f.unop).op x,
          sectionsEquiv_map f, LinearEquiv.apply_symm_apply]
        exact restrictPost_restrict N.obj f.unop _ }
    (fun V a (x : (presheaf R.obj N.obj).obj (op (F.obj V.unop))) =>
      (sectionsEquiv (F.op ⋙ R.obj) (F.op ⋙ N.obj) V).injective (by
      change sectionsEquiv _ _ V ((sectionsEquiv _ _ V).symm (restrictPost F R N.obj _
          (sectionsEquiv R.obj N.obj (op (F.obj V.unop))
            ((id a : R.obj.obj (op (F.obj V.unop))) • x)))) =
        sectionsEquiv _ _ V ((id a : (F.op ⋙ R.obj).obj V) •
          (sectionsEquiv _ _ V).symm (restrictPost F R N.obj _
          (sectionsEquiv R.obj N.obj (op (F.obj V.unop)) x)))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_smul, LinearEquiv.map_smul,
        LinearEquiv.apply_symm_apply]
      exact restrictPost_smul N.obj a _))⟩

variable {F R} in
/-- The section of `y ≫ coinductionRestriction F R N` at `m` is the restriction along
`Over.post F` of the morphism `R|_{F(V)} ⟶ N|_{F(V)}` given by the section `y m`. -/
lemma sec_comp_coinductionRestriction (N : Sheaf K AddCommGrpCat.{w})
    {M : SheafOfModules.{w} ((F.sheafPushforwardContinuous RingCat.{w} J K).obj R)}
    (y : M ⟶ (_root_.SheafOfModules.pushforward.{w}
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{w} J K).obj R))).obj (obj R N))
    (V : Cᵒᵖ) (m : M.val.obj V) :
    sec (y ≫ coinductionRestriction F R N) V m =
      restrictPost F R N.obj V.unop (sectionsEquiv R.obj N.obj (op (F.obj V.unop))
        (y.val.app V m)) :=
  LinearEquiv.apply_symm_apply _ _

variable {F R} in
/-- The restriction morphism of coinduced modules is an isomorphism as soon as restriction along
`Over.post F` is bijective on the morphisms `R|_{F(V)} ⟶ N|_{F(V)}`. -/
lemma isIso_coinductionRestriction (N : Sheaf K AddCommGrpCat.{w})
    (h : ∀ V : C, Function.Bijective (restrictPost F R N.obj V)) :
    IsIso (coinductionRestriction (J := J) F R N) := by
  have : IsIso ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      (coinductionRestriction (J := J) F R N)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun V => (ConcreteCategory.isIso_iff_bijective _).2
      (((sectionsEquiv _ _ V).symm.bijective.comp (h V.unop)).comp (sectionsEquiv _ _ _).bijective)
  exact isIso_of_reflects_iso _ (_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

/-- Let `F : C ⥤ D` be a continuous functor of sites and `R` a sheaf of rings on `D`. If for
every object `V` of `C` restriction along `Over.post F : C/V ⥤ D/F(V)` is bijective on morphisms
of abelian presheaves out of `R|_{F(V)}`, then the comparison transformation
`lowerShriekForgetComparison` between lower shriek on abelian sheaves and lower shriek on sheaves
of `F^{-1}R`-modules is an isomorphism. -/
theorem isIso_lowerShriekForgetComparison_of_bijective
    [(_root_.SheafOfModules.pushforward.{w}
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{w} J K).obj R))).IsRightAdjoint]
    [(F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    (h : ∀ (V : C) (G : (Over (F.obj V))ᵒᵖ ⥤ AddCommGrpCat.{w}),
      Function.Bijective fun β : (Over.forget (F.obj V)).op ⋙ ab R.obj ⟶ G =>
        Functor.whiskerLeft (Over.post F).op β) :
    IsIso (lowerShriekForgetComparison F
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{w} J K).obj R))) := by
  let S := (F.sheafPushforwardContinuous RingCat.{w} J K).obj R
  let adjAb := F.sheafAdjunctionContinuous AddCommGrpCat.{w} J K
  let adjM := _root_.SheafOfModules.pullbackPushforwardAdjunction.{w} (𝟙 S)
  rw [NatTrans.isIso_iff_isIso_app]
  refine fun M => isIso_of_coyoneda_map_bijective _ fun N => ?_
  let N' := (_root_.SheafOfModules.pullback.{w} (𝟙 S)).obj M
  let Φ : ((_root_.SheafOfModules.toSheaf R).obj N' ⟶ N) →
      ((_root_.SheafOfModules.toSheaf S).obj M ⟶ (F.sheafPushforwardContinuous _ J K).obj N) :=
    fun x => (_root_.SheafOfModules.toSheaf S).map (adjM.unit.app M) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map x
  have hc : (fun x => (lowerShriekForgetComparison F (𝟙 S)).app M ≫ x) =
      (adjAb.homEquiv _ _).symm ∘ Φ := by
    funext x
    rw [Function.comp_apply, Equiv.eq_symm_apply, Adjunction.homEquiv_naturality_right]
    exact congrArg (· ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map x)
      (lowerShriekForgetComparison_homEquiv F (𝟙 S) M)
  have hρ := isIso_coinductionRestriction (J := J) N (fun V => h V _)
  have hΦ : Φ = (homEquiv M ((F.sheafPushforwardContinuous _ J K).obj N)).symm ∘
      (fun y => y ≫ coinductionRestriction (J := J) F R N) ∘ (adjM.homEquiv _ _) ∘
        (homEquiv N' N) := by
    funext x
    rw [Function.comp_apply, Equiv.eq_symm_apply]
    refine hom_ext_sec fun V m => ?_
    simp only [Function.comp_apply]
    rw [sec_homEquiv, Adjunction.homEquiv_unit, sec_comp_coinductionRestriction]
    ext W r
    rw [toHom_eval]
    show ap x (op (F.obj W.left)) ((adjM.unit.app M).val.app (op W.left)
        (r • res M.val W.hom.op m)) =
      (sec (homEquiv N' N x) (op (F.obj V.unop))
        (id ((adjM.unit.app M).val.app V m) : N'.val.obj (op (F.obj V.unop)))).eval
          ((Over.post F).obj W) r
    rw [sec_homEquiv]
    show _ = ap x (op (F.obj W.left)) ((id r : R.obj.obj (op (F.obj W.left))) •
      res N'.val (F.map W.hom).op
        (id ((adjM.unit.app M).val.app V m) : N'.val.obj (op (F.obj V.unop))))
    congr 1
    refine (((adjM.unit.app M).val.app (op W.left)).hom.map_smul r
      (res M.val W.hom.op m)).trans ?_
    exact congrArg (fun z : N'.val.obj (op (F.obj W.left)) =>
        (id r : R.obj.obj (op (F.obj W.left))) • z)
      (PresheafOfModules.naturality_apply (adjM.unit.app M).val W.hom.op m)
  rw [hc, hΦ]
  refine (adjAb.homEquiv _ _).symm.bijective.comp
    ((homEquiv _ _).symm.bijective.comp (Function.Bijective.comp ?_
      ((adjM.homEquiv _ _).bijective.comp (homEquiv _ _).bijective)))
  refine Function.bijective_iff_has_inverse.2
    ⟨fun y => y ≫ inv (coinductionRestriction (J := J) F R N), fun y => ?_, fun y => ?_⟩ <;> simp

end Stacks.SheafOfModules
