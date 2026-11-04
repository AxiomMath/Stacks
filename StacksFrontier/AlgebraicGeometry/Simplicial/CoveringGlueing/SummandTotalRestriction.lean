module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.PullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSimplicialSystem

/-!
# Restriction from `C/X` to a summand of the total site

Restricting a sheaf of `O_X`-modules to the total site of a simplicial object `K` of formal
coproducts over `X`, then to the degree-`n` component, then to its `i`-th summand, is isomorphic to
restricting it to the slice over that summand, by an isomorphism which fixes sections.

## Main definitions

* `SheafOfModules.pushforwardComp₃Iso`: A threefold pushforward of sheaves of modules is the
  pushforward along a functor isomorphic to the composite.
* `CategoryTheory.SimplicialSemiRepresentable.summandTotalRestrictionIso`: Restriction to the total
  site, a component and a summand is restriction to the slice over that summand.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.summandTotalRestrictionIso_hom_app_fixesSections`:
  The forward map of `summandTotalRestrictionIso` fixes sections.
* `CategoryTheory.SimplicialSemiRepresentable.summandTotalRestrictionIso_inv_app_fixesSections`:
  The inverse of `summandTotalRestrictionIso` fixes sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace SheafOfModules

variable {A : Type*} [Category* A] {B : Type*} [Category* B] {C' : Type*} [Category* C']
  {D : Type*} [Category* D] {JA : GrothendieckTopology A} {JB : GrothendieckTopology B}
  {JC : GrothendieckTopology C'} {JD : GrothendieckTopology D}
  {RA : Sheaf JA RingCat.{u}} {RB : Sheaf JB RingCat.{u}} {RC : Sheaf JC RingCat.{u}}
  {RD : Sheaf JD RingCat.{u}}
  (F₁ : B ⥤ A) (F₂ : C' ⥤ B) (F₃ : D ⥤ C') [h₁ : F₁.IsContinuous JB JA]
  [h₂ : F₂.IsContinuous JC JB] [h₃ : F₃.IsContinuous JD JC]
  (φ₁ : RB ⟶ (F₁.sheafPushforwardContinuous RingCat.{u} JB JA).obj RA)
  (φ₂ : RC ⟶ (F₂.sheafPushforwardContinuous RingCat.{u} JC JB).obj RB)
  (φ₃ : RD ⟶ (F₃.sheafPushforwardContinuous RingCat.{u} JD JC).obj RC)
  {G : D ⥤ A} [hG : G.IsContinuous JD JA]
  (ψ : RD ⟶ (G.sheafPushforwardContinuous RingCat.{u} JD JA).obj RA)
  (e : G ≅ F₃ ⋙ F₂ ⋙ F₁)

/-- A threefold pushforward of sheaves of modules along continuous functors is the pushforward
along a functor isomorphic to their composite, when the ring maps agree. -/
def pushforwardComp₃Iso
    (he : haveI : (F₂ ⋙ F₁).IsContinuous JC JA := Functor.isContinuous_comp _ _ _ JB _
      haveI : (F₃ ⋙ F₂ ⋙ F₁).IsContinuous JD JA := Functor.isContinuous_comp _ _ _ JC _
      (φ₃ ≫ (F₃.sheafPushforwardContinuous RingCat.{u} JD JC).map
          (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} JC JB).map φ₁)) ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} JD JA).app RA = ψ) :
    pushforward.{u} φ₁ ⋙ pushforward.{u} φ₂ ⋙ pushforward.{u} φ₃ ≅ pushforward.{u} ψ :=
  haveI : (F₂ ⋙ F₁).IsContinuous JC JA := Functor.isContinuous_comp _ _ _ JB _
  haveI : (F₃ ⋙ F₂ ⋙ F₁).IsContinuous JD JA := Functor.isContinuous_comp _ _ _ JC _
  pushforwardCongr₂ (G := F₃ ⋙ F₂ ⋙ F₁)
    (φ₃ ≫ (F₃.sheafPushforwardContinuous RingCat.{u} JD JC).map
      (φ₂ ≫ (F₂.sheafPushforwardContinuous RingCat.{u} JC JB).map φ₁)) e he

/-- The hom of `pushforwardComp₃Iso` acts on sections over `U` by restriction along the component
of `e.hom` at `U`. -/
theorem pushforwardComp₃Iso_hom_app_val_app (he) (M : SheafOfModules.{u} RA) (U : Dᵒᵖ) (x) :
    ((pushforwardComp₃Iso F₁ F₂ F₃ φ₁ φ₂ φ₃ ψ e he).hom.app M).val.app U x =
      M.val.map (e.hom.app U.unop).op x :=
  rfl

/-- Restriction of sections of a presheaf of abelian groups along an `eqToHom` is the identity, up
to the identification of the types of sections. -/
theorem heq_presheaf_map_eqToHom {E : Type*} [Category* E] (Pr : E ⥤ AddCommGrpCat.{u})
    {U V : E} (h : U = V) (x : Pr.obj U) : HEq ((Pr.map (eqToHom h)).hom x) x := by
  subst h
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- When restriction along the components of the comparison of functors fixes sections, so does
the threefold comparison. -/
theorem pushforwardComp₃Iso_hom_app_fixesSections (he) (M : SheafOfModules.{u} RA)
    (hid : ∀ (U : Dᵒᵖ) (x : M.val.presheaf.obj (op ((F₃ ⋙ F₂ ⋙ F₁).obj U.unop))),
      HEq ((M.val.presheaf.map (e.hom.app U.unop).op).hom x) x) :
    FixesSections ((pushforwardComp₃Iso F₁ F₂ F₃ φ₁ φ₂ φ₃ ψ e he).hom.app M) := fun U x =>
  HEq.trans (heq_of_eq (pushforwardComp₃Iso_hom_app_val_app F₁ F₂ F₃ φ₁ φ₂ φ₃ ψ e he M U x))
    (hid U x)

end SheafOfModules

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

attribute [local instance] pretopologyRingedSite_over_hasPullbacks

/-- `j_total` is continuous, for the topologies of the total and the augmentation ringed topoi. -/
instance totalForget_isContinuous_augmentationRingedTopos :
    (totalForget K).IsContinuous
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O).J
      (structureSheafAugmentation P K OC).augmentationRingedTopos.J :=
  totalForget_isContinuous _ K

/-- The component inclusion is continuous, for the topology of the total ringed topos. -/
instance componentFunctor_isContinuous_totalRingedTopos (n : SimplexCategory) :
    ((situation (P.toGrothendieck.over X) K).componentFunctor n).IsContinuous
      ((situation (P.toGrothendieck.over X) K).componentTopology n)
      ((situation (P.toGrothendieck.over X) K).totalRingedTopos
        (structureSheafAugmentation P K OC).O).J :=
  SimplicialSiteSituation.componentFunctor_isContinuous _ n

/-- The composite of the summand inclusion, the component inclusion and `j_total` is the
forgetful functor of the slice. -/
def summandTotalForgetIso (n : SimplexCategory) (i : (K.obj (op n)).I) :
    summandFunctor ((pretopologyRingedSite P OC).over X) K n i ⋙
        SimplicialSiteSituation.componentFunctor (situation (P.toGrothendieck.over X) K) n ⋙
          totalForget K ≅
      Over.forget ((K.obj (op n)).obj i) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {W W'} f => by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact totalForget_map_ι ((pretopologyRingedSite P OC).over X) K (op n)
      (CategoryTheory.Sigma.SigmaHom.mk f)

/-- **Restricting a sheaf of `O_X`-modules to the total site, then to the degree-`n` component,
then to its `i`-th summand, is restricting it to the slice over that summand.** -/
def summandTotalRestrictionIso (n : SimplexCategory) (i : (K.obj (op n)).I) :
    totalRestrictionModules P K OC ⋙
        (situation (P.toGrothendieck.over X) K).componentModulesRestriction
          (structureSheafAugmentation P K OC).O n ⋙
        summandRestriction ((pretopologyRingedSite P OC).over X) K n i ≅
      SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X))
        ((K.obj (op n)).obj i) :=
  SheafOfModules.pushforwardComp₃Iso _ _ _ _ _ _ _ (summandTotalForgetIso P K OC n i).symm
    (h₂ := by exact SimplicialSiteSituation.componentFunctor_isContinuous _ n)
    (h₃ := by exact summandFunctor_isContinuous ((pretopologyRingedSite P OC).over X) K n i)
    (hG := by exact inferInstanceAs ((Over.forget ((K.obj (op n)).obj i)).IsContinuous
      ((P.toGrothendieck.over X).over ((K.obj (op n)).obj i)) (P.toGrothendieck.over X))) (by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun W => RingCat.hom_ext (RingHom.ext fun x => ?_))
    exact congrArg (fun g => (RingCat.Hom.hom g) x)
      (((Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X)).obj.map_id (op W.unop.left))))

/-- The forward map of `summandTotalRestrictionIso` at a module fixes sections. -/
theorem summandTotalRestrictionIso_hom_app_fixesSections (n : SimplexCategory)
    (i : (K.obj (op n)).I)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X))) :
    SheafOfModules.FixesSections ((summandTotalRestrictionIso P K OC n i).hom.app N) :=
  SheafOfModules.pushforwardComp₃Iso_hom_app_fixesSections _ _ _ _ _ _ _ _
    (h₂ := by exact SimplicialSiteSituation.componentFunctor_isContinuous _ n)
    (h₃ := by exact summandFunctor_isContinuous ((pretopologyRingedSite P OC).over X) K n i)
    (hG := by exact inferInstanceAs ((Over.forget ((K.obj (op n)).obj i)).IsContinuous
      ((P.toGrothendieck.over X).over ((K.obj (op n)).obj i)) (P.toGrothendieck.over X)))
    _ N (fun V x => heq_of_eq (congrArg (fun g => (AddCommGrpCat.Hom.hom g) x)
      (N.val.presheaf.map_id (op V.unop.left))))

/-- The inverse of `summandTotalRestrictionIso` at a module fixes sections. -/
theorem summandTotalRestrictionIso_inv_app_fixesSections (n : SimplexCategory)
    (i : (K.obj (op n)).I)
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (OC.over X))) :
    SheafOfModules.FixesSections ((summandTotalRestrictionIso P K OC n i).inv.app N) :=
  SheafOfModules.FixesSections.inv ((summandTotalRestrictionIso P K OC n i).app N)
    (summandTotalRestrictionIso_hom_app_fixesSections P K OC n i N)

end CategoryTheory.SimplicialSemiRepresentable

end
