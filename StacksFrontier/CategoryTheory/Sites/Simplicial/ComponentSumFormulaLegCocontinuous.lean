module

public import StacksFrontier.CategoryTheory.Sites.PullbackComparisonInjectivity
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormulaLeg

/-!
# The summand inclusions of the abelian sum formula, case (B) (Stacks 09WG)

The sum formula of Stacks 09WG writes `g_m^{-1} g_{n!}` on abelian sheaves as the direct sum, over
the simplex maps `φ : [n] ⟶ [m]`, of the inverse images along the transitions.  What identifies the
decomposition is that the `φ`th summand inclusion is the *canonical* map
`CategoryTheory.SimplicialSiteSituation.componentSumFormulaLeg` attached to `φ`, namely the unit of
`g_{n!} ⊣ g_n^{-1}` followed by the transition of Stacks 09WF with abelian coefficients.  This file
proves that in case (B) of Stacks 09WE, where the component inclusions are cocontinuous.

## Main results

* `CategoryTheory.Functor.sheafAdjunctionPullbackCocontinuous_unit_app_hom` and
  `.sheafAdjunctionPullbackCocontinuous_homEquiv_apply_hom`: the unit and the transposition of the
  adjunction of Stacks 00XL, in terms of the right Kan extension and the sheafification unit.
* `CategoryTheory.Functor.toSheafify_comp_sheafificationCompPushforwardContinuousIso_inv_app_hom`:
  the transport comparing sheafification with restriction along a continuous and cocontinuous
  functor is, after the sheafification unit, the restricted sheafification unit.
* `CategoryTheory.Functor.toSheafify_comp_sigma_ι_comp_`
  `sheafPullbackCompPushforwardIsoCoproductOfLan_inv_app`: on sections, the summand inclusion of
  the lan criterion's coproduct formula is the presheaf comparison of that criterion.
* `CategoryTheory.CocontinuousSimplicialSite`
  `.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg`: **Stacks 09WG in
  case (B)**, the summand inclusion is the canonical map.

The primed versions state the same results with `restrictAb` in place of `abelianComponent`.

## Implementation notes

The two spellings of a component topology,
`CategoryTheory.SimplicialSiteSituation.componentTopology` and the reduced
`topologyOfCoverings (C.coverage _)`, are not mixed within one application of a generic result,
and the topologies are passed explicitly. Instance search does not unfold the `match` defining
the component topology, so a mixed application looks for a continuity instance in a form in which
none is registered.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pseudofunctor Opposite

namespace CategoryTheory

universe v₁ v₂ v₃ w w' u₁ u₂ u₃ v u

/-- Two maps out of a sheafification agree as soon as they agree after the sheafification unit. -/
theorem Sheaf.hom_ext_toSheafify {C : Type u₁} [Category.{v₁} C] {A : Type w} [Category.{w'} A]
    (J : GrothendieckTopology C) [HasWeakSheafify J A] (P : Cᵒᵖ ⥤ A) {T : Sheaf J A}
    {f g : (presheafToSheaf J A).obj P ⟶ T}
    (h : toSheafify J P ≫ f.hom = toSheafify J P ≫ g.hom) : f = g :=
  ((sheafificationAdjunction J A).homEquiv P T).injective h

namespace Functor

section Cocontinuous

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
  (A : Type w) [Category.{w'} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsCocontinuous J K] [HasWeakSheafify J A]
  [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]

omit [HasWeakSheafify J A] in
/-- The comparison identifying the cocontinuous pushforward with a right Kan extension is the
identity on sections. -/
private theorem pushforwardCocontinuousIso_hom_app (Y : Sheaf J A) :
    ((Functor.leftUnitor (sheafToPresheaf J A ⋙ u.op.ran)).trans
      (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm).hom.app Y = 𝟙 _ := by
  have hid : (Functor.leftUnitor (sheafToPresheaf J A ⋙ u.op.ran)).hom ≫
      𝟙 (u.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A) =
      (Functor.leftUnitor (sheafToPresheaf J A ⋙ u.op.ran)).hom := Category.comp_id _
  rw [Iso.trans_hom, Iso.symm_hom,
    sheafPushforwardCocontinuousCompSheafToPresheafIso_inv, hid]
  exact Functor.leftUnitor_hom_app _ _

/-- The unit of the adjunction of Stacks 00XL is the unit of the right Kan extension along `u.op`
followed by the Kan extension of the sheafification unit. -/
theorem sheafAdjunctionPullbackCocontinuous_unit_app_hom (X : Sheaf K A) :
    ((u.sheafAdjunctionPullbackCocontinuous A J K).unit.app X).hom =
      (u.op.ranAdjunction A).unit.app X.obj ≫
        u.op.ran.map (toSheafify J (u.op ⋙ X.obj)) := by
  have hjunk : ∀ {P Q R : Dᵒᵖ ⥤ A} (a : P ⟶ Q) (b : Q ⟶ R) (j₁ j₂ : R ⟶ R),
      j₁ = 𝟙 R → j₂ = 𝟙 R → (a ≫ b) ≫ j₁ ≫ j₂ = a ≫ b := by
    rintro P Q R a b j₁ j₂ rfl rfl
    simp
  refine Eq.trans (((u.op.ranAdjunction A).comp
    (sheafificationAdjunction J A)).map_restrictFullyFaithful_unit_app
      (fullyFaithfulSheafToPresheaf K A) (Functor.FullyFaithful.id _)
      (Functor.rightUnitor _).symm
      ((Functor.leftUnitor _).trans
        (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm) X) ?_
  rw [Adjunction.comp_unit_app]
  exact hjunk _ _ _ _ (by simp) (pushforwardCocontinuousIso_hom_app u A J K _)

/-- Transposing along the adjunction of Stacks 00XL is composing with the sheafification unit and
transposing along the right Kan extension along `u.op`. -/
theorem sheafAdjunctionPullbackCocontinuous_homEquiv_apply_hom
    {X : Sheaf K A} {Y : Sheaf J A} (f : (u.sheafPullbackCocontinuous A J K).obj X ⟶ Y) :
    ((u.sheafAdjunctionPullbackCocontinuous A J K).homEquiv X Y f).hom =
      (u.op.ranAdjunction A).unit.app X.obj ≫
        u.op.ran.map (toSheafify J (u.op ⋙ X.obj)) ≫ u.op.ran.map f.hom := by
  refine Eq.trans (congrArg InducedCategory.Hom.hom
    ((u.sheafAdjunctionPullbackCocontinuous A J K).homEquiv_unit X Y f)) ?_
  refine Eq.trans (congrArg (fun k => k ≫ u.op.ran.map f.hom)
    (sheafAdjunctionPullbackCocontinuous_unit_app_hom u A J K X)) ?_
  exact Category.assoc _ _ _

/-- The sheafification unit followed by the inverse transpose along the adjunction of Stacks 00XL
is the inverse transpose along the right Kan extension along `u.op`. -/
theorem toSheafify_comp_sheafAdjunctionPullbackCocontinuous_homEquiv_symm_hom
    {X : Sheaf K A} {Y : Sheaf J A} (r : X ⟶ (u.sheafPushforwardCocontinuous A J K).obj Y) :
    toSheafify J (u.op ⋙ X.obj) ≫
        (((u.sheafAdjunctionPullbackCocontinuous A J K).homEquiv X Y).symm r).hom =
      ((u.op.ranAdjunction A).homEquiv X.obj Y.obj).symm r.hom := by
  refine ((u.op.ranAdjunction A).homEquiv X.obj Y.obj).injective ?_
  refine Eq.trans ?_
    (Equiv.apply_symm_apply ((u.op.ranAdjunction A).homEquiv X.obj Y.obj) r.hom).symm
  refine Eq.trans ((u.op.ranAdjunction A).homEquiv_unit _ _ _) ?_
  refine Eq.trans (congrArg (fun k => (u.op.ranAdjunction A).unit.app X.obj ≫ k)
    (u.op.ran.map_comp _ _)) ?_
  refine Eq.trans (sheafAdjunctionPullbackCocontinuous_homEquiv_apply_hom u A J K _).symm ?_
  exact congrArg InducedCategory.Hom.hom
    (Equiv.apply_symm_apply ((u.sheafAdjunctionPullbackCocontinuous A J K).homEquiv X Y) r)

omit [u.IsCocontinuous J K] [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F] in
/-- The sheafification unit followed by the pullback of a map of sheaves along a cocontinuous
functor is the restriction of that map followed by the sheafification unit. -/
theorem toSheafify_comp_sheafPullbackCocontinuous_map_hom {X Y : Sheaf K A} (h : X ⟶ Y) :
    toSheafify J (u.op ⋙ X.obj) ≫ ((u.sheafPullbackCocontinuous A J K).map h).hom =
      Functor.whiskerLeft u.op h.hom ≫ toSheafify J (u.op ⋙ Y.obj) :=
  (toSheafify_naturality J (Functor.whiskerLeft u.op h.hom)).symm

end Cocontinuous

section Sheafification

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (w : C ⥤ D) (A : Type w) [Category.{w'} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [w.IsContinuous J K] [w.IsCocontinuous J K] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ F : Cᵒᵖ ⥤ A, w.op.HasPointwiseRightKanExtension F]

/-- On sections, the transport comparing sheafification with restriction along a continuous and
cocontinuous functor is, after the sheafification unit of the restricted presheaf, the restriction
of the sheafification unit. -/
theorem toSheafify_comp_sheafificationCompPushforwardContinuousIso_inv_app_hom (P : Dᵒᵖ ⥤ A) :
    toSheafify J (w.op ⋙ P) ≫
        ((sheafificationCompPushforwardContinuousIso w A J K).inv.app P).hom =
      Functor.whiskerLeft w.op (toSheafify K P) := by
  refine Eq.trans (congrArg
    (fun k : ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj w.op ⋙ presheafToSheaf J A).obj P ⟶
        (presheafToSheaf K A ⋙ w.sheafPushforwardContinuous A J K).obj P =>
      toSheafify J (w.op ⋙ P) ≫ k.hom)
    (Adjunction.leftAdjointUniq_inv_app
      ((sheafificationAdjunction K A).comp (w.sheafAdjunctionCocontinuous A J K))
      ((w.op.ranAdjunction A).comp (sheafificationAdjunction J A)) P)) ?_
  exact w.toSheafify_pullbackSheafificationCompatibility A J K P

end Sheafification

section Lan

variable {I : Type w} {Cn : Type u₁} [Category.{v₁} Cn] {Cm : Type u₂} [Category.{v₂} Cm]
  {E : Type u₃} [Category.{v₃} E]
  (A : Type u) [Category.{v} A]
  (Jn : GrothendieckTopology Cn) (Jm : GrothendieckTopology Cm) (L : GrothendieckTopology E)
  (vn : Cn ⥤ E) (vm : Cm ⥤ E) (t : I → (Cm ⥤ Cn)) (σ : ∀ i, vm ⟶ t i ⋙ vn)
  [∀ F : Cnᵒᵖ ⥤ A, vn.op.HasLeftKanExtension F]
  [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  [HasWeakSheafify L A] [HasWeakSheafify Jm A]
  [∀ F : Cmᵒᵖ ⥤ A, vm.op.HasPointwiseRightKanExtension F]

omit [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  [HasWeakSheafify Jm A] [∀ F : Cmᵒᵖ ⥤ A, vm.op.HasPointwiseRightKanExtension F] in
/-- The presheaf comparison of the lan criterion, followed by the sheafification unit of the left
Kan extension, is the Kan extension unit followed by restriction along the comparison `σ i`. -/
theorem lanRestrictComparison_app_comp_whiskerLeft_toSheafify (i : I) (P : Cnᵒᵖ ⥤ A) :
    (lanRestrictComparison A vn vm t σ i).app P ≫
        Functor.whiskerLeft vm.op (toSheafify L (vn.op.lan.obj P)) =
      Functor.whiskerLeft (t i).op
          (vn.op.lanUnit.app P ≫ Functor.whiskerLeft vn.op (toSheafify L (vn.op.lan.obj P))) ≫
        Functor.whiskerRight (NatTrans.op (σ i)) (sheafify L (vn.op.lan.obj P)) := by
  refine NatTrans.ext (funext fun W => ?_)
  obtain ⟨V⟩ := W
  change ((lanRestrictComparison A vn vm t σ i).app P).app (op V) ≫
      (toSheafify L (vn.op.lan.obj P)).app (op (vm.obj V)) = _
  rw [lanRestrictComparison_app_app]
  change ((vn.op.lanUnit.app P).app (op ((t i).obj V)) ≫
        (vn.op.lan.obj P).map ((σ i).app V).op) ≫
      (toSheafify L (vn.op.lan.obj P)).app (op (vm.obj V)) =
    ((vn.op.lanUnit.app P).app (op ((t i).obj V)) ≫
        (toSheafify L (vn.op.lan.obj P)).app (op (vn.obj ((t i).obj V)))) ≫
      (sheafify L (vn.op.lan.obj P)).map ((σ i).app V).op
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun k => (vn.op.lanUnit.app P).app (op ((t i).obj V)) ≫ k)
    ((toSheafify L (vn.op.lan.obj P)).naturality ((σ i).app V).op)

variable [HasCoproduct fun i => (t i).sheafPullbackCocontinuous A Jm Jn]
  (hcofan : ∀ (P : Cnᵒᵖ ⥤ A) (V : Cm),
    IsColimit (Cofan.mk ((vn.op.lan.obj P).obj (op (vm.obj V)))
      fun i => (vn.op.lanUnit.app P).app (op ((t i).obj V)) ≫
        (vn.op.lan.obj P).map ((σ i).app V).op))

omit [vn.IsContinuous Jn L] in
/-- On sections, the `i`th summand inclusion into the lan criterion's coproduct formula, followed
by the inverse of that formula, is the presheaf comparison of that criterion followed by the
sheafification unit of the left Kan extension. -/
theorem toSheafify_comp_sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfLan_inv_app
    (i : I) (X : Sheaf Jn A) :
    toSheafify Jm ((t i).op ⋙ X.obj) ≫
        ((Sigma.ι (fun i => (t i).sheafPullbackCocontinuous A Jm Jn) i ≫
          (sheafPullbackCompPushforwardIsoCoproductOfLan A Jn Jm L vn vm t σ hcofan).inv).app
            X).hom =
      (lanRestrictComparison A vn vm t σ i).app X.obj ≫
        Functor.whiskerLeft vm.op (toSheafify L (vn.op.lan.obj X.obj)) := by
  refine Eq.trans (congrArg
    (fun α : (t i).sheafPullbackCocontinuous A Jm Jn ⟶
        sheafPullbackConstruction.sheafPullback vn A Jn L ⋙
          vm.sheafPushforwardContinuous A Jm L =>
      toSheafify Jm ((t i).op ⋙ X.obj) ≫ (α.app X).hom)
    (sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfLan_inv A Jn Jm L vn vm t σ
      hcofan i)) ?_
  change toSheafify Jm ((t i).op ⋙ X.obj) ≫
      sheafifyMap Jm ((lanRestrictComparison A vn vm t σ i).app X.obj) ≫
      ((sheafificationCompPushforwardContinuousIso vm A Jm L).inv.app
        (vn.op.lan.obj X.obj)).hom = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  exact congrArg (fun k => (lanRestrictComparison A vn vm t σ i).app X.obj ≫ k)
    (toSheafify_comp_sheafificationCompPushforwardContinuousIso_inv_app_hom vm A Jm L
      (vn.op.lan.obj X.obj))

end Lan

end Functor

namespace CocontinuousSimplicialSite

open CategoryTheory.SimplicialSiteSituation in
/-- In case (B), the abelian transition on sections is the Kan-extension transpose of restriction
along the family of total-category arrows out of the degree-`m` objects. -/
theorem restrictTransitionAb_inr_hom (C : CocontinuousSimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    (A : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) :
    ((restrictTransitionAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom =
      (((C.underlying.map φ.op).toFunctor).op.ranAdjunction Ab.{u}).homEquiv _ _
        (Functor.whiskerRight
          (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op)) A.obj) := rfl

open CategoryTheory.SimplicialSiteSituation in
/-- In case (B), the abelian transition on sections is the Kan-extension transpose of restriction
along the family of total-category arrows out of the degree-`m` objects, stated with
`restrictAb`. -/
theorem restrictTransitionAb_inr_hom' (C : CocontinuousSimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    (A : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) :
    ((restrictTransitionAb' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom =
      (((C.underlying.map φ.op).toFunctor).op.ranAdjunction Ab.{u}).homEquiv _ _
        (Functor.whiskerRight
          (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op)) A.obj) := rfl

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.SimplicialSiteSituation in
/-- In case (B), the sheafification unit followed by the inverse-image transition of Stacks 09WF
is restriction of the total-site sheaf along the cross-fibre arrows. -/
theorem toSheafify_comp_fiberTransitionAb_inr_app (C : CocontinuousSimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    (A : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) :
    toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        (((C.underlying.map φ.op).toFunctor).op ⋙
          (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).abelianComponent n).obj A).obj) ≫
        ((fiberTransitionAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom =
      Functor.whiskerRight
        (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op)) A.obj := by
  have : ((C.underlying.map φ.op).toFunctor).IsCocontinuous
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) :=
    C.isCocontinuous φ.op
  refine Eq.trans (Functor.toSheafify_comp_sheafAdjunctionPullbackCocontinuous_homEquiv_symm_hom
    ((C.underlying.map φ.op).toFunctor) Ab.{u} _ _ _) ?_
  refine Eq.trans (congrArg
    (fun k => ((((C.underlying.map φ.op).toFunctor).op.ranAdjunction Ab.{u}).homEquiv
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).abelianComponent n).obj A).obj
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).abelianComponent m).obj A).obj).symm k)
    (restrictTransitionAb_inr_hom C φ A)) ?_
  exact Equiv.symm_apply_apply _ _

open CategoryTheory.SimplicialSiteSituation in
/-- In case (B), the sheafification unit followed by the inverse-image transition of Stacks 09WF
is restriction of the total-site sheaf along the cross-fibre arrows, stated with `restrictAb`. -/
theorem toSheafify_comp_fiberTransitionAb_inr_app' (C : CocontinuousSimplicialSite.{u})
    {n m : SimplexCategory} (φ : n ⟶ m)
    (A : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) :
    toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        (((C.underlying.map φ.op).toFunctor).op ⋙
          (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).restrictAb n).obj A).obj) ≫
        ((fiberTransitionAb' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app A).hom =
      Functor.whiskerRight
        (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op)) A.obj :=
  toSheafify_comp_fiberTransitionAb_inr_app C φ A

open CategoryTheory.SimplicialSiteSituation in
/-- In case (B), the sheafification unit followed by the canonical map attached to a simplex map
is the Kan extension unit followed by restriction along the cross-fibre arrows. -/
theorem toSheafify_comp_componentSumFormulaLeg_inr_app
    (C : CocontinuousSimplicialSite.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) :
    toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        (((C.underlying.map φ.op).toFunctor).op ⋙ X.obj) ≫
        ((componentSumFormulaLeg (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app X).hom =
      Functor.whiskerLeft ((C.underlying.map φ.op).toFunctor).op
          (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentLowerShriekAbAdjunction
            n).unit.app X).hom ≫
        Functor.whiskerRight
          (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
          ((Functor.sheafPullbackConstruction.sheafPullback
            (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
            ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
            (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology).obj X).obj := by
  have : ((C.underlying.map φ.op).toFunctor).IsCocontinuous
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) :=
    C.isCocontinuous φ.op
  refine Eq.trans (congrArg
    (fun k : (transitionInverseImageAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).obj X ⟶
        (Functor.sheafPullbackConstruction.sheafPullback
          (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
          ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
          (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology ⋙
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).abelianComponent m).obj X =>
      toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        (((C.underlying.map φ.op).toFunctor).op ⋙ X.obj) ≫ k.hom)
    (componentSumFormulaLeg_app (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ X)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun k => k ≫ ((fiberTransitionAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app
      ((Functor.sheafPullbackConstruction.sheafPullback
        (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology).obj X)).hom)
    (Functor.toSheafify_comp_sheafPullbackCocontinuous_map_hom
      ((C.underlying.map φ.op).toFunctor) Ab.{u}
      (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op n)))
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentLowerShriekAbAdjunction
        n).unit.app X))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg
    (fun k => Functor.whiskerLeft ((C.underlying.map φ.op).toFunctor).op
      (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentLowerShriekAbAdjunction
        n).unit.app X).hom ≫ k)
    (toSheafify_comp_fiberTransitionAb_inr_app C φ _)

open CategoryTheory.SimplicialSiteSituation in
/-- In case (B), the sheafification unit followed by the canonical map attached to a simplex map
is the Kan extension unit followed by restriction along the cross-fibre arrows, stated with
`restrictAb`. -/
theorem toSheafify_comp_componentSumFormulaLeg_inr_app'
    (C : CocontinuousSimplicialSite.{u}) {n m : SimplexCategory} (φ : n ⟶ m)
    (X : Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) :
    toSheafify ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        (((C.underlying.map φ.op).toFunctor).op ⋙ X.obj) ≫
        ((componentSumFormulaLeg' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ).app X).hom =
      Functor.whiskerLeft ((C.underlying.map φ.op).toFunctor).op
          (((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentLowerShriekAbAdjunction'
            n).unit.app X).hom ≫
        Functor.whiskerRight
          (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
          ((Functor.sheafPullbackConstruction.sheafPullback
            (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
            ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
            (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology).obj X).obj :=
  toSheafify_comp_componentSumFormulaLeg_inr_app C φ X

open CategoryTheory.SimplicialSiteSituation in
/-- **Stacks 09WG in case (B).** The `φ`th summand inclusion into the abelian sum formula,
followed by the inverse of that formula, is the canonical map attached to `φ`: the unit of
`g_{n!} ⊣ g_n^{-1}` followed by the transition of Stacks 09WF. -/
theorem sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg
    (C : CocontinuousSimplicialSite.{u}) (n m : SimplexCategory) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
          transitionInverseImageAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) ψ) φ ≫
        (componentLowerShriekRestrictionIsoCoproduct C n m).inv =
      componentSumFormulaLeg (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ := by
  have hlanRaw : ∀ G : (C.underlying.obj (op n))ᵒᵖ ⥤ Ab.{u},
      (Grothendieck.ι C.underlying (op n)).op.HasLeftKanExtension G :=
    fun G => (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ G).hasLeftKanExtension
  have hlan : ∀ G : ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).component n)ᵒᵖ ⥤ Ab.{u},
      (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).op.HasLeftKanExtension G :=
    fun G => (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ G).hasLeftKanExtension
  refine NatTrans.ext (funext fun X => Sheaf.hom_ext_toSheafify _ _ ?_)
  refine Eq.trans
    (Functor.toSheafify_comp_sigma_ι_comp_sheafPullbackCompPushforwardIsoCoproductOfLan_inv_app
      Ab.{u} ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n)
      (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m)
      (fun ψ : n ⟶ m => (C.underlying.map ψ.op).toFunctor)
      (fun ψ => Grothendieck.ιNatTrans (F := C.underlying) ψ.op)
      (fun P V => isColimitCofanLanComponent C V P) φ X) ?_
  refine Eq.trans (Functor.lanRestrictComparison_app_comp_whiskerLeft_toSheafify
    Ab.{u} (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology
    (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n)
    (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m)
    (fun ψ : n ⟶ m => (C.underlying.map ψ.op).toFunctor)
    (fun ψ => Grothendieck.ιNatTrans (F := C.underlying) ψ.op) φ X.obj) ?_
  exact (toSheafify_comp_componentSumFormulaLeg_inr_app C φ X).symm

open CategoryTheory.SimplicialSiteSituation in
/-- **Stacks 09WG in case (B).** The `φ`th summand inclusion into the abelian sum formula,
followed by the inverse of that formula, is the canonical map attached to `φ`: the unit of
`g_{n!} ⊣ g_n^{-1}` followed by the transition of Stacks 09WF, stated with `restrictAb`. -/
theorem sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg'
    (C : CocontinuousSimplicialSite.{u}) (n m : SimplexCategory) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
          transitionInverseImageAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) ψ) φ ≫
        (componentLowerShriekRestrictionIsoCoproduct C n m).inv =
      componentSumFormulaLeg' (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ :=
  sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg C n m φ

add_to_stacks 09WG "summand inclusion is the canonical transition, case (B)"
  sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg

end CocontinuousSimplicialSite

end CategoryTheory

end
