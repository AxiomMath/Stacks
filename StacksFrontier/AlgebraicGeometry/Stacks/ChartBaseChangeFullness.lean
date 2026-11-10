module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineChart

/-!
# Full faithfulness of `h` on the chart (proof of Stacks 0DUQ)

In the setting of `StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeCartesian`, let `V` and
`V'` represent the self-intersections `R = U ×_𝒳 U` and `R' = W ×_{𝒳'} W` of the charts, with the
source square `R' = R ×_{s, U} W` cartesian, and suppose `W = M' ×_M U`. Then two points `w₁, w₂`
of `W` over `T` with one image in `M'` have the property that every vertical morphism
`h(x' w₁) ⟶ h(x' w₂)` is the image of a vertical morphism `x' w₁ ⟶ x' w₂`.

This is the step "`R' = M' ×_M R`" of the proof of Stacks 0DUQ, read on points: the arrow of `R`
named by the morphism lifts along the source square to an arrow of `R'` with source `w₂`, and its
target is `w₁` because both have the same images in `U` and in `M'`.

## Main results

* `AlgebraicGeometry.Stack.ChartBaseChange.exists_preimage_of_relation`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChartBaseChange

section Algebra

variable {C E : Type*} [Category C] [Category E]

theorem algebra₁₀ (G : E ⥤ C) {b₁ b₃ : E} (θa : b₁ ⟶ b₁) (θb : b₃ ⟶ b₃) (ha : θa = 𝟙 b₁)
    (hb : θb = 𝟙 b₃) {P Q : C} (A : P ≅ G.obj b₁) (Cc : Q ≅ G.obj b₃) (α β : P ⟶ Q)
    (h : G.map θa ≫ (A.inv ≫ α ≫ Cc.hom) = (A.inv ≫ β ≫ Cc.hom) ≫ G.map θb) : α = β := by
  rw [ha, hb, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id] at h
  rw [← cancel_epi A.inv, ← cancel_mono Cc.hom]
  simpa only [Category.assoc] using h

end Algebra

/-- Transport of a lift over an identity along an equality of base objects. -/
theorem isHomLift_id_transport {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜] (p : 𝒜 ⥤ 𝒞)
    {R R' : 𝒞} (e : R = R') {a b : 𝒜} (φ : a ⟶ b) (h : p.IsHomLift (𝟙 R) φ) :
    p.IsHomLift (𝟙 R') φ := by
  subst e
  exact h

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U W : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (eK : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
    (chartBaseChangeSquare h x).pt.val.val.p)

variable {M M' : BigFppfOver B S hS} (gM : M' ⟶ M)
  (f' : 𝒳'.val ⟶ fibredCategory B S hS (yoneda.obj M'))

/-- **`h` is full on vertical morphisms between objects of the chart with one image in `M'`.** -/
theorem exists_preimage_of_relation (fU : W ⟶ U)
    (hfU : yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK))
    (q : U ⟶ M) (q' : W ⟶ M')
    (hq' : BasedFunctor.comp (chart' h x eK).hom f'.hom =
      BasedFunctor.comp (sliceElementsComparison B S hS W)
        (associatedMap B S hS (yoneda.map q')).1.hom)
    (hH2 : IsPullback (yoneda.map fU) (yoneda.map q') (yoneda.map q) (yoneda.map gM))
    {V V' : BigFppfOver B S hS}
    (eR : StacksRepresentableCFG.EquivalenceOver (rel x).val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
    (eR' : StacksRepresentableCFG.EquivalenceOver (rel' h x eK).val.p
      (presheafOfCategories (yoneda.obj V' ⋙ typeToCat)).p)
    (s t : V ⟶ U) (s' t' : V' ⟶ W) (fV : V' ⟶ V)
    (hs : yoneda.map s = SelfIntersection.relationSourceMap
      (U := schemeSpace U)
      (R := schemeSpace V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
    (ht : yoneda.map t = SelfIntersection.relationTargetMap
      (U := schemeSpace U)
      (R := schemeSpace V)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
    (hs' : yoneda.map s' = SelfIntersection.relationSourceMap
      (U := schemeSpace W)
      (R := schemeSpace V')
      (PresheafOfCategories.sliceElementsEquivalenceOver W) eR')
    (ht' : yoneda.map t' = SelfIntersection.relationTargetMap
      (U := schemeSpace W)
      (R := schemeSpace V')
      (PresheafOfCategories.sliceElementsEquivalenceOver W) eR')
    (hfV : yoneda.map fV = representingMap B S hS _ _ (yoneda.obj V') (yoneda.obj V) eR' eR
      (relationMap h x eK))
    (hsq : IsPullback (yoneda.map fV) (yoneda.map s') (yoneda.map s) (yoneda.map fU))
    (htq : IsPullback (yoneda.map fV) (yoneda.map t') (yoneda.map t) (yoneda.map fU))
    (T : BigFppfOver B S hS) (w₁ w₂ : T ⟶ W) (hw : w₁ ≫ q' = w₂ ≫ q')
    (α : (CatFiberedInGroupoids.homFunctor h.hom).obj
        ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁)) ⟶
      (CatFiberedInGroupoids.homFunctor h.hom).obj
        ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂)))
    (hα : 𝒳.val.val.p.IsHomLift (𝟙 T) α) :
    ∃ ψ : (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₁) ⟶
        (CatFiberedInGroupoids.homFunctor (chart' h x eK)).obj (Over.mk w₂),
      𝒳'.val.val.p.IsHomLift (𝟙 T) ψ ∧ (CatFiberedInGroupoids.homFunctor h.hom).map ψ = α := by
  have hset : (schemeStack.{u, w} B S hS U).val.val.p.IsFiberedInSetoids :=
    SelfIntersection.isFiberedInSetoids_source
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
  let K := eK.hom.functor
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U
  let eW := PresheafOfCategories.sliceElementsEquivalenceOver W
  obtain ⟨αi, hαi⟩ := exists_iso_of_isHomLift_id _ 𝒳.val.isFiberedInGroupoids α hα
  have hb : ∀ w : T ⟶ W, (K.obj (Over.mk w)).base = T := fun w => comparison_base h x eK (Over.mk w)
  have hy := fun w : T ⟶ W => (K.obj (Over.mk w)).hy.trans (hb w)
  -- the arrow of `R` named by `α`
  let r : (rel x).val.obj :=
    { base := T
      x := (K.obj (Over.mk w₁)).y
      y := (K.obj (Over.mk w₂)).y
      hx := hy w₁
      hy := hy w₂
      iso := (K.obj (Over.mk w₁)).iso.symm ≪≫ αi ≪≫ (K.obj (Over.mk w₂)).iso
      vertical := by
        have h₁ : 𝒳.val.val.p.IsHomLift (𝟙 T) (K.obj (Over.mk w₁)).iso.inv :=
          isHomLift_id_transport _ (hb w₁) _
            (@IsHomLift.lift_id_inv _ _ _ _ _ _ _ _ _ (K.obj (Over.mk w₁)).vertical)
        have h₃ : 𝒳.val.val.p.IsHomLift (𝟙 T) (K.obj (Over.mk w₂)).iso.hom :=
          isHomLift_id_transport _ (hb w₂) _ (K.obj (Over.mk w₂)).vertical
        exact isHomLift_comp₃ _ _ _ _ h₁ (hαi ▸ hα) h₃ }
  let ρ : T ⟶ V := PresheafOfCategories.sectionOfObj eR r rfl
  have hsecW : ∀ a : T ⟶ W,
      PresheafOfCategories.sectionOfObj eW (Over.mk a) rfl = a := by
    intro a
    rw [sectionOfObj_sliceElementsEquivalenceOver']
    simp
  -- the images of a point of `W` and of `ρ` in `U`
  have hfUw : ∀ w : T ⟶ W, PresheafOfCategories.sectionOfObj eU (K.obj (Over.mk w)).y
      (hy w) =
        (yoneda.map fU).app (op T) w := by
    intro w
    refine (representingMap_app_sectionOfObj eW eU (chartMap h x eK) (Over.mk w) rfl).symm.trans ?_
    rw [← hfU]
    change (yoneda.map fU).app (op T) (PresheafOfCategories.sectionOfObj eW (Over.mk w) rfl) = _
    rw [hsecW]
  have hsρ : (yoneda.map s).app (op T) ρ = (yoneda.map fU).app (op T) w₂ :=
    (congrArg (fun m => m.app (op T) ρ) hs).trans ((SelfIntersection.relationSourceMap_sectionOfObj
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) eU eR r rfl).trans (hfUw w₂))
  have htρ : (yoneda.map t).app (op T) ρ = (yoneda.map fU).app (op T) w₁ :=
    (congrArg (fun m => m.app (op T) ρ) ht).trans ((SelfIntersection.relationTargetMap_sectionOfObj
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) eU eR r rfl).trans (hfUw w₁))
  -- the lift `ρ'` along the source square
  obtain ⟨ρ', hρ'₁, hρ'₂⟩ := Types.exists_of_isPullback
    (hsq.map ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj (op T))) ρ w₂ hsρ
  -- `ρ'` as an arrow of `R'`
  obtain ⟨r', hr', hr'ρ⟩ := PresheafOfCategories.exists_sectionOfObj eR' (W := T) ρ'
  -- the source and the target of `ρ'`, read on `r'`
  have hs'ρ₀ : (yoneda.map s').app (op T) ρ' = PresheafOfCategories.sectionOfObj eW r'.y
      (SelfIntersection.relation_obj_y hr') := by
    have e₁ := congrArg (fun m => m.app (op T) ρ') hs'
    have e₂ := congrArg (fun z => (SelfIntersection.relationSourceMap
      (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (R := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) eW eR').app (op T) z) hr'ρ.symm
    have e₃ := SelfIntersection.relationSourceMap_sectionOfObj
      (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (R := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) eW eR' r' hr'
    exact e₁.trans (e₂.trans e₃)
  have ht'ρ₀ : (yoneda.map t').app (op T) ρ' = PresheafOfCategories.sectionOfObj eW r'.x
      (SelfIntersection.relation_obj_x hr') := by
    have e₁ := congrArg (fun m => m.app (op T) ρ') ht'
    have e₂ := congrArg (fun z => (SelfIntersection.relationTargetMap
      (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (R := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) eW eR').app (op T) z) hr'ρ.symm
    have e₃ := SelfIntersection.relationTargetMap_sectionOfObj
      (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (R := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩) eW eR' r' hr'
    exact e₁.trans (e₂.trans e₃)
  -- the image of `r'` in `R` names `ρ`, so it is isomorphic to `r` over `T`
  have hfVr := (representingMap_app_sectionOfObj eR' eR (relationMap h x eK) r' hr').symm.trans
    ((congrArg (fun z => (representingMap B S hS _ _ (yoneda.obj V') (yoneda.obj V) eR' eR
      (relationMap h x eK)).app (op T) z) hr'ρ).trans
      ((congrArg (fun m => m.app (op T) ρ') hfV).symm.trans hρ'₁))
  let θ := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eR _ (rfl : (rel x).val.p.obj r = T)
    hfVr
  have hθ : (rel x).val.p.IsHomLift (𝟙 T) θ.hom.1 := θ.hom.2
  have hθa := isHomLift_a θ.hom.1 (𝟙 T) (hφ := hθ)
  have hθb := isHomLift_b θ.hom.1 (𝟙 T) (hφ := hθ)
  have hθw := θ.hom.1.w
  clear_value θ
  obtain ⟨b', ⟨a₁l, ⟨⟨⟩⟩, a₁h⟩, ⟨a₂l, ⟨⟨⟩⟩, a₂h⟩, ha₁, ha₂, ψ₀, hψ₀⟩ := r'
  change b' = T at hr'
  have hr'' : T = b' := hr'.symm
  subst hr''
  have ha₁' : T = a₁l := ha₁.symm
  subst ha₁'
  have ha₂' : T = a₂l := ha₂.symm
  subst ha₂'
  have hs'ρ : (yoneda.map s').app (op T) ρ' = a₂h := hs'ρ₀.trans (hsecW a₂h)
  have ht'ρ : (yoneda.map t').app (op T) ρ' = a₁h := ht'ρ₀.trans (hsecW a₁h)
  have hw₂ : a₂h = w₂ := hs'ρ.symm.trans hρ'₂
  -- the images of `a₁h` and of `w₁` in `U` agree
  have hU₁ : (yoneda.map fU).app (op T) a₁h = (yoneda.map fU).app (op T) w₁ := by
    have e := congrArg (fun m => m.app (op T) ρ') htq.w
    simp only [NatTrans.comp_app, types_comp_apply] at e
    have h₁ : (yoneda.map fV).app (op T) ρ' = ρ := hρ'₁
    rw [h₁, ht'ρ] at e
    exact e.symm.trans htρ
  -- the images of `a₁h` and of `w₁` in `M'` agree
  have hM₁ : (yoneda.map q').app (op T) a₁h = (yoneda.map q').app (op T) w₁ := by
    have hobj := obj_eq_of_isHomLift_id_fibredCategory f'.hom ψ₀.hom hψ₀
    have hq'₁ := congrArg (fun L => L.obj (Over.mk a₁h)) hq'
    have hq'₂ := congrArg (fun L => L.obj (Over.mk a₂h)) hq'
    have hb := congrArg (fun X : (fibredCategory B S hS (yoneda.obj M')).val.obj => X.base) hq'₁
    have el₁ := fibredCategory_elementOf_eq_of_obj_eq ((yoneda.map q').app (op T) a₁h) hq'₁ hb
    have el₂ := fibredCategory_elementOf_eq_of_obj_eq ((yoneda.map q').app (op T) a₂h)
      (hobj.trans hq'₂) hb
    refine el₁.symm.trans (el₂.trans ?_)
    rw [hw₂]
    exact hw.symm
  have hw₁ : a₁h = w₁ := Types.ext_of_isPullback
    (hH2.map ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj (op T))) hU₁ hM₁
  subst hw₁ hw₂
  -- the two components of `θ` are identities, so `h ψ₀` is `α`
  have hθa' := Functor.hom_unique_of_isFiberedInSetoids
    (q := (schemeStack.{u, w} B S hS U).val.val.p) (𝟙 T) _ _ hθa
    (isHomLift_id_of_obj_eq _ (hy a₁h))
  have hθb' := Functor.hom_unique_of_isFiberedInSetoids
    (q := (schemeStack.{u, w} B S hS U).val.val.p) (𝟙 T) _ _ hθb
    (isHomLift_id_of_obj_eq _ (hy a₂h))
  exact ⟨ψ₀.hom, hψ₀, (algebra₁₀ _ θ.hom.1.a θ.hom.1.b hθa' hθb' (K.obj (Over.mk a₁h)).iso
    (K.obj (Over.mk a₂h)).iso αi.hom ((CatFiberedInGroupoids.homFunctor h.hom).map ψ₀.hom)
    hθw).symm.trans hαi⟩

end ChartBaseChange

end AlgebraicGeometry.Stack

end
