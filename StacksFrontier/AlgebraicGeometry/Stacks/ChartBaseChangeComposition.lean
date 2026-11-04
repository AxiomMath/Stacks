module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRelation

/-!
# The morphism of relations of a base-changed chart respects composition (proof of Stacks 0DUQ)

The 1-morphism `R' ⟶ R` of `AlgebraicGeometry.Stack.ChartBaseChange.relationMap` between the
self-intersections of a chart `x : 𝒮_U ⟶ 𝒳` and of its base change `x' : 𝒰' ⟶ 𝒳'` along
`h : 𝒳' ⟶ 𝒳` carries the composite of a composable pair of arrows of `R'` to the composite of the
images: on representing presheaves it commutes with the composition laws of Stacks 04T4 (3).
This is what makes the pair `(U' ⟶ U, R' ⟶ R)` a morphism of groupoid schemes, the input of
Stacks 0DT9 in the proof of Stacks 0DUQ.

## Main results

* `AlgebraicGeometry.Stack.ChartBaseChange.relationMap_compositionLaw`: the compatibility, on
  sections.
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChartBaseChange

section Algebra

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Given isomorphisms `αᵢ : F.obj aᵢ ≅ Xᵢ` and a morphism `e'` with
`F.map e ≫ α₂'.hom = α₂.hom ≫ e'`, the image of `ψ₁.hom ≫ e ≫ ψ₂.hom` under `F`, transported along
the `αᵢ`, is the composite of the transported images of `ψ₁.hom`, `e` and `ψ₂.hom`. -/
theorem algebra₈ (F : D ⥤ C) {a₁ a₂ a₂' a₃ : D} (ψ₁ : a₁ ≅ a₂) (e : a₂ ⟶ a₂') (ψ₂ : a₂' ≅ a₃)
    {X₁ X₂ X₂' X₃ : C} (α₁ : F.obj a₁ ≅ X₁) (α₂ : F.obj a₂ ≅ X₂) (α₂' : F.obj a₂' ≅ X₂')
    (α₃ : F.obj a₃ ≅ X₃) (e' : X₂ ⟶ X₂') (hnat : F.map e ≫ α₂'.hom = α₂.hom ≫ e') :
    α₁.inv ≫ F.map (ψ₁.hom ≫ e ≫ ψ₂.hom) ≫ α₃.hom =
      (α₁.inv ≫ F.map ψ₁.hom ≫ α₂.hom) ≫ e' ≫ (α₂'.inv ≫ F.map ψ₂.hom ≫ α₃.hom) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnat]
  simp

/-- If `R = L`, then `G.map (𝟙 b₁) ≫ L = R ≫ G.map (𝟙 b₃)`. -/
theorem algebra₉ (G : E ⥤ C) {b₁ b₃ : E} (L R : G.obj b₁ ⟶ G.obj b₃) (h : R = L) :
    G.map (𝟙 b₁) ≫ L = R ≫ G.map (𝟙 b₃) := by
  simp [h]

end Algebra

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  {𝒰' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (eK : StacksRepresentableCFG.EquivalenceOver 𝒰'.val.p
    (chartBaseChangeSquare h x).pt.val.val.p)
  {U₀ U₀' R₀ R₀' : AlgebraicSpaces B S hS}
  (eU : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS U).val.val.p
    (presheafOfCategories (U₀.obj ⋙ typeToCat)).p)
  (eU' : StacksRepresentableCFG.EquivalenceOver 𝒰'.val.p
    (presheafOfCategories (U₀'.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver (rel x).val.p
    (presheafOfCategories (R₀.obj ⋙ typeToCat)).p)
  (eR' : StacksRepresentableCFG.EquivalenceOver (rel' h x eK).val.p
    (presheafOfCategories (R₀'.obj ⋙ typeToCat)).p)

/-- The image of a composable pair of sections of `R'` is a composable pair of sections of `R`. -/
theorem relationMap_composable {W : BigFppfOver B S hS}
    (q : (Deformation.composableArrows U₀'.obj R₀'.obj
      (SelfIntersection.relationSourceMap eU' eR')
      (SelfIntersection.relationTargetMap eU' eR')).obj (op W)) :
    (SelfIntersection.relationSourceMap eU eR).app (op W)
        ((representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK)).app (op W)
          q.1.1) =
      (SelfIntersection.relationTargetMap eU eR).app (op W)
        ((representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK)).app (op W)
          q.1.2) := by
  have hs := congrArg (fun m => m.app (op W) q.1.1)
    (isPullback_relationSource h x eK eU eU' eR eR').w
  have ht := congrArg (fun m => m.app (op W) q.1.2)
    (isPullback_relationTarget h x eK eU eU' eR eR').w
  simp only [NatTrans.comp_app, types_comp_apply] at hs ht
  rw [hs, ht, q.2]

/-- **The morphism of relations respects composition.** -/
theorem relationMap_compositionLaw
    (hset : (schemeStack.{u, w} B S hS U).val.val.p.IsFiberedInSetoids)
    (hset' : 𝒰'.val.p.IsFiberedInSetoids) {W : BigFppfOver B S hS}
    (q : (Deformation.composableArrows U₀'.obj R₀'.obj
      (SelfIntersection.relationSourceMap eU' eR')
      (SelfIntersection.relationTargetMap eU' eR')).obj (op W)) :
    (representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK)).app (op W)
        ((SelfIntersection.compositionLaw eU' eR' hset').app (op W) q) =
      (SelfIntersection.compositionLaw eU eR hset).app (op W)
        ⟨((representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK)).app (op W)
            q.1.1,
          (representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR (relationMap h x eK)).app (op W)
            q.1.2), relationMap_composable h x eK eU eU' eR eR' q⟩ := by
  obtain ⟨⟨g, r⟩, hq⟩ := q
  obtain ⟨y, hb, h₁, h₂⟩ := SelfIntersection.exists_composable eU' eR' g r hq
  subst h₁ h₂ hb
  let K := eK.hom.functor
  let fV := relationMap h x eK
  have hp := CatFiberedInGroupoids.homFunctor_comp_p (chartMap h x eK)
  let yb : SelfIntersection.composable B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val
      x.hom.hom :=
    { base := y.base
      x := (CatFiberedInGroupoids.homFunctor fV).obj y.x
      y := (CatFiberedInGroupoids.homFunctor fV).obj y.y
      hx := y.hx
      hy := y.hy
      iso := (CatFiberedInGroupoids.homFunctor (chartMap h x eK)).mapIso y.iso
      vertical := by
        have := y.vertical
        exact Functor.isHomLift_map_of_comp_eq
          hp (𝟙 y.base) y.iso.hom }
  let θ : (CatFiberedInGroupoids.homFunctor fV).obj
        ((SelfIntersection.composition B S hS 𝒰' 𝒳'.val (chart' h x eK).hom).toFunctor.obj y) ⟶
      (SelfIntersection.composition B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val
        x.hom.hom).toFunctor.obj yb :=
    { hbase := 𝟙 y.base
      a := 𝟙 _
      b := 𝟙 _
      ha := isHomLift_id_of_obj_eq _
        ((Functor.congr_obj hp y.x.x).trans (y.x.hx.trans y.hx))
      hb := isHomLift_id_of_obj_eq _
        ((Functor.congr_obj hp y.y.y).trans (y.y.hy.trans y.hy))
      w := algebra₉ (CatFiberedInGroupoids.homFunctor x.hom) _ _
        (algebra₈ (CatFiberedInGroupoids.homFunctor h.hom) y.x.iso
          ((CatFiberedInGroupoids.homFunctor (chart' h x eK)).map y.iso.hom) y.y.iso
          (K.obj y.x.x).iso (K.obj y.x.y).iso (K.obj y.y.x).iso (K.obj y.y.y).iso
          ((CatFiberedInGroupoids.homFunctor x.hom).map
            ((CatFiberedInGroupoids.homFunctor (chartMap h x eK)).map y.iso.hom))
          (K.map y.iso.hom).w) }
  calc (representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR fV).app (op y.base)
        ((SelfIntersection.compositionLaw eU' eR' hset').app (op y.base)
          ⟨(PresheafOfCategories.sectionOfObj eR' y.x (y.hx.trans rfl),
            PresheafOfCategories.sectionOfObj eR' y.y (y.hy.trans rfl)), hq⟩)
      = (representingMap B S hS _ _ R₀'.obj R₀.obj eR' eR fV).app (op y.base)
          (PresheafOfCategories.sectionOfObj eR'
            ((SelfIntersection.composition B S hS 𝒰' 𝒳'.val (chart' h x eK).hom).toFunctor.obj
              y) (SelfIntersection.composition_obj_over rfl)) :=
        congrArg _ (SelfIntersection.compositionLaw_app_sectionOfObj eU' eR' hset' y)
    _ = PresheafOfCategories.sectionOfObj eR ((CatFiberedInGroupoids.homFunctor fV).obj
          ((SelfIntersection.composition B S hS 𝒰' 𝒳'.val (chart' h x eK).hom).toFunctor.obj
            y)) _ :=
        representingMap_app_sectionOfObj eR' eR fV _ _
    _ = PresheafOfCategories.sectionOfObj eR
          ((SelfIntersection.composition B S hS (schemeStack.{u, w} B S hS U).val 𝒳.val
            x.hom.hom).toFunctor.obj yb) (SelfIntersection.composition_obj_over rfl) :=
        PresheafOfCategories.sectionOfObj_eq_of_hom eR _ _ θ (IsHomLift.map (p := (rel x).val.p) θ)
    _ = (SelfIntersection.compositionLaw eU eR hset).app (op y.base)
          ⟨(PresheafOfCategories.sectionOfObj eR yb.x yb.hx,
            PresheafOfCategories.sectionOfObj eR yb.y yb.hy),
            SelfIntersection.composable_sectionOfObj_compatible eU eR yb⟩ :=
        (SelfIntersection.compositionLaw_app_sectionOfObj eU eR hset yb).symm
    _ = _ := by
        congr 1
        exact Subtype.ext (Prod.ext (representingMap_app_sectionOfObj eR' eR fV y.x _).symm
          (representingMap_app_sectionOfObj eR' eR fV y.y _).symm)

end ChartBaseChange

end AlgebraicGeometry.Stack

end
