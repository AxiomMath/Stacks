module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkSectionsTransitivity

/-!
# The base change map of sheaves of sets, on sections

Let
```
Y --e--> T
|h       |g
v        v
X --f--> S
```
be a commutative square of schemes and `F` a sheaf of sets on the small étale site of `T`. The
base change map `β : f⁻¹ g_* F ⟶ h_* e⁻¹ F` (`Stacks.EtaleCohomology.smallEtaleSetBaseChange`) is
the mate of the identification of the two composite direct images. This file reads the defining
identity of that mate on sections: for an étale `U ⟶ S` and a section `x` of `F` over `T ×_S U`,
the base change map carries the image of `x` under the unit of `f⁻¹ ⊣ f_*` to the image of `x`
under the unit of `e⁻¹ ⊣ e_*`, restricted along the canonical morphism
`(U ×_S X) ×_X Y ⟶ (U ×_S T) ×_T Y`.

## Main definitions

* `Stacks.EtaleCohomology.baseChangeSquareMap`: the canonical morphism
  `(U ×_S X) ×_X Y ⟶ (U ×_S T) ×_T Y` of the small étale site of `Y`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSetBaseChange_unit_apply`: the identity on sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace Stacks.EtaleCohomology

variable {X Y S T : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
  (w : e ≫ g = h ≫ f)

include w in
/-- The canonical morphism `(U ×_S X) ×_X Y ⟶ (U ×_S T) ×_T Y` of the small étale site of `Y`. -/
def baseChangeSquareMap (U : S.Etale) :
    (smallEtaleBaseChange h).obj ((smallEtaleBaseChange f).obj U) ⟶
      (smallEtaleBaseChange e).obj ((smallEtaleBaseChange g).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      (pullback.lift (pullback.fst _ h ≫ pullback.fst U.hom f) (pullback.snd _ h ≫ e)
        ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (pullback.condition (f := U.hom) (g := f))).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f)
            (pullback.condition (f := pullback.snd U.hom f) (g := h))).trans
            ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) w.symm).trans
              (Category.assoc _ _ _).symm)))))))
      (pullback.snd _ h) (pullback.lift_snd _ _ _))
    (pullback.lift_snd _ _ _) trivial

/-- For `k₁ = k₂ : Y ⟶ S`, the component at a sheaf `P` and at `U` of the `eqToHom` between the
pushforwards along `k₁` and `k₂` is the restriction map of `P` along the `eqToHom` between the
base changes of `U` along `k₂` and `k₁`. -/
theorem eqToHom_pushforward_app {k₁ k₂ : Y ⟶ S} (hk : k₁ = k₂)
    (P : Sheaf Y.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale) :
    ((eqToHom (congrArg (fun k : Y ⟶ S ↦ (smallEtaleBaseChange k).sheafPushforwardContinuous
        (Type (max (u + 1) v)) S.smallEtaleTopology Y.smallEtaleTopology) hk)).app P).hom.app
          (op U) =
      P.obj.map
        (eqToHom (congrArg (fun k : Y ⟶ S => (smallEtaleBaseChange k).obj U) hk.symm)).op := by
  subst hk
  simp
  rfl

/-- For `k₁ = k₂ : Y ⟶ S`, the `eqToHom` between the base changes of `U` along `k₁` and `k₂`
commutes with the first projections `U ×_S Y ⟶ U`. -/
theorem eqToHom_baseChange_left_fst {k₁ k₂ : Y ⟶ S} (hk : k₁ = k₂) (U : S.Etale) :
    (eqToHom (congrArg (fun k : Y ⟶ S => (smallEtaleBaseChange k).obj U) hk)).left ≫
      pullback.fst U.hom k₂ = pullback.fst U.hom k₁ := by
  subst hk
  exact Category.id_comp _

/-- For `k₁ = k₂ : Y ⟶ S`, the `eqToHom` between the base changes of `U` along `k₁` and `k₂`
commutes with the second projections `U ×_S Y ⟶ Y`. -/
theorem eqToHom_baseChange_left_snd {k₁ k₂ : Y ⟶ S} (hk : k₁ = k₂) (U : S.Etale) :
    (eqToHom (congrArg (fun k : Y ⟶ S => (smallEtaleBaseChange k).obj U) hk)).left ≫
      pullback.snd U.hom k₂ = pullback.snd U.hom k₁ := by
  subst hk
  exact Category.id_comp _

/-- The comparison of the two composite base changes around the square is the canonical morphism
`baseChangeSquareMap`. -/
theorem baseChangeComp_comp_eq (U : S.Etale) :
    (smallEtaleBaseChangeComp h f).inv.app U ≫
        eqToHom (congrArg (fun k : Y ⟶ S => (smallEtaleBaseChange k).obj U) w.symm) ≫
        (smallEtaleBaseChangeComp e g).hom.app U =
      baseChangeSquareMap e h g f w U := by
  apply smallEtaleBaseChange_hom_ext
  let a := ((smallEtaleBaseChangeComp h f).inv.app U).left
  let b := (eqToHom (congrArg (fun k : Y ⟶ S => (smallEtaleBaseChange k).obj U) w.symm)).left
  let c := ((smallEtaleBaseChangeComp e g).hom.app U).left
  show (a ≫ b ≫ c) ≫ pullback.fst (pullback.snd U.hom g) e =
    (baseChangeSquareMap e h g f w U).left ≫ pullback.fst (pullback.snd U.hom g) e
  have hκ : (baseChangeSquareMap e h g f w U).left ≫ pullback.fst (pullback.snd U.hom g) e =
      pullback.lift (pullback.fst _ h ≫ pullback.fst U.hom f) (pullback.snd _ h ≫ e) _ :=
    pullback.lift_fst _ _ _
  rw [hκ]
  apply pullback.hom_ext
  · have h1 : c ≫ pullback.fst (pullback.snd U.hom g) e ≫ pullback.fst U.hom g =
        pullback.fst U.hom (e ≫ g) := smallEtaleBaseChangeComp_hom_app_left_fst e g U
    have h2 : b ≫ pullback.fst U.hom (e ≫ g) = pullback.fst U.hom (h ≫ f) :=
      eqToHom_baseChange_left_fst w.symm U
    have h3 : a ≫ pullback.fst U.hom (h ≫ f) = pullback.fst (pullback.snd U.hom f) h ≫
        pullback.fst U.hom f := smallEtaleBaseChangeComp_inv_app_left_fst h f U
    refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
    calc ((a ≫ b ≫ c) ≫ pullback.fst (pullback.snd U.hom g) e) ≫ pullback.fst U.hom g
        = a ≫ b ≫ (c ≫ pullback.fst (pullback.snd U.hom g) e ≫ pullback.fst U.hom g) :=
          (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
            (congrArg (a ≫ ·) (Category.assoc _ _ _)))
      _ = _ := by rw [h1, h2, h3]; rfl
  · have h1 : c ≫ pullback.snd (pullback.snd U.hom g) e = pullback.snd U.hom (e ≫ g) :=
      MorphismProperty.Over.w ((smallEtaleBaseChangeComp e g).hom.app U)
    have h2 : b ≫ pullback.snd U.hom (e ≫ g) = pullback.snd U.hom (h ≫ f) :=
      eqToHom_baseChange_left_snd w.symm U
    have h3 : a ≫ pullback.snd U.hom (h ≫ f) = pullback.snd (pullback.snd U.hom f) h :=
      MorphismProperty.Over.w ((smallEtaleBaseChangeComp h f).inv.app U)
    refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
    refine (calc ((a ≫ b ≫ c) ≫ pullback.fst (pullback.snd U.hom g) e) ≫ pullback.snd U.hom g
        = a ≫ b ≫ (c ≫ pullback.snd (pullback.snd U.hom g) e) ≫ e :=
          (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
            (congrArg (a ≫ ·) ((Category.assoc _ _ _).trans (congrArg (b ≫ ·)
              ((congrArg (c ≫ ·) (pullback.condition (f := pullback.snd U.hom g) (g := e))).trans
                (Category.assoc _ _ _).symm)))))
      _ = a ≫ b ≫ pullback.snd U.hom (e ≫ g) ≫ e := by rw [h1]
      _ = a ≫ pullback.snd U.hom (h ≫ f) ≫ e :=
          congrArg (a ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ e) h2))).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ e) h3)

/-- The comparison of the composite direct images, on sections over `U`, is restriction along
`baseChangeSquareMap`. -/
theorem pushforwardCompIso_app_eq (P : Sheaf Y.smallEtaleTopology (Type (max (u + 1) v)))
    (U : S.Etale) :
    (((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
        (eqToIso (congrArg (fun k : Y ⟶ S ↦
          (smallEtaleBaseChange k).sheafPushforwardContinuous
            (Type (max (u + 1) v)) S.smallEtaleTopology Y.smallEtaleTopology) w)).hom ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv).app P).hom.app (op U) =
      P.obj.map (baseChangeSquareMap e h g f w U).op := by
  simp only [smallEtalePushforwardCompIso, Functor.sheafPushforwardContinuousComp', Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, eqToIso.hom,
    ObjectProperty.FullSubcategory.comp_hom, Functor.sheafPushforwardContinuousIso_hom,
    Functor.sheafPushforwardContinuousIso_inv, Functor.sheafPushforwardContinuousNatTrans_app_hom,
    Functor.whiskerRight_app, NatTrans.op_app]
  rw [eqToHom_pushforward_app w P U, ← baseChangeComp_comp_eq e h g f w U]
  simp only [op_comp, Functor.map_comp]
  rfl

/-- **The base change map of sheaves of sets on sections.** -/
theorem smallEtaleSetBaseChange_unit_apply (F : Sheaf T.smallEtaleTopology (Type (max (u + 1) v)))
    (U : S.Etale) (x : F.obj.obj (op ((smallEtaleBaseChange g).obj U))) :
    ((smallEtaleSetBaseChange.{u, v} e h g f w).app F).hom.app
        (op ((smallEtaleBaseChange f).obj U))
        (((smallEtaleInverseImageAdjunction.{u, v} f).unit.app
          (((smallEtaleBaseChange g).sheafPushforwardContinuous (Type (max (u + 1) v))
            S.smallEtaleTopology T.smallEtaleTopology).obj F)).hom.app (op U) x) =
      ((smallEtaleInverseImage.{u, v} e).obj F).obj.map (baseChangeSquareMap e h g f w U).op
        (((smallEtaleInverseImageAdjunction.{u, v} e).unit.app F).hom.app
          (op ((smallEtaleBaseChange g).obj U)) x) := by
  have hk := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m => m.hom)
    (smallEtaleSetBaseChange_unit.{u, v} e h g f w F)) (op U)) x
  have hα := pushforwardCompIso_app_eq e h g f w ((smallEtaleInverseImage.{u, v} e).obj F) U
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    ConcreteCategory.comp_apply] at hk
  refine hk.trans ?_
  exact congrArg (fun m => m (((smallEtaleInverseImageAdjunction.{u, v} e).unit.app F).hom.app
    (op ((smallEtaleBaseChange g).obj U)) x)) hα

end Stacks.EtaleCohomology
