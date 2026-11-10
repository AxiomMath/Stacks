module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackLiftAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackChartCover
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.CategoryTheory.DottedArrows.Defs
public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered

/-!
# Lifting a point of a smooth algebraic stack across a first-order thickening

Let `T ⟶ T'` be a first-order thickening of affine schemes, `𝒳` an algebraic stack with a smooth
1-morphism `f : 𝒳 ⟶ T'`, and `x : T ⟶ 𝒳` a morphism over `T'`. Then `x` extends to a morphism
`x' : T' ⟶ 𝒳` over `T'` with `x'|_T ≅ x`, compatibly with the maps to `T'` (Stacks 0DNZ,
`AlgebraicGeometry.Stack.exists_dottedArrow_of_isSmooth_of_isFirstOrderThickening`).

The object `x_T` of `𝒳` over `T` given by `x` comes, on an affine étale cover of `T`, from an
affine étale piece `U₁` of a smooth chart `U₀ ⟶ 𝒳` of the algebraic stack
(`AlgebraicGeometry.Stack.GroupoidLift.exists_affine_etale_chart_cover`); the underlying morphism
`U₀ ⟶ T'` of the composite chart is smooth (Stacks 075V), and the chart is formally smooth on
objects. The lifting step `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_affine_chart`
extends `x_T` along `T ⟶ T'` to an object with image the identity of `T'`, and the 2-Yoneda lemma
turns that extension into the dotted arrow.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_isSmooth_of_isAlgebraicStack`.
* `AlgebraicGeometry.Stack.exists_dottedArrow_of_isSmooth_of_isFirstOrderThickening`.

## References

* [Stacks Project, Tag 0DNZ](https://stacks.math.columbia.edu/tag/0DNZ)
-/

@[expose] public section

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Stack

universe w u

namespace GroupoidLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **An object of a smooth algebraic stack over an affine `T'` lying over a square-zero
thickening `T ⟶ T'` of affines extends over `T'`**, to an object with image the identity. -/
theorem exists_lift_of_isSmooth_of_isAlgebraicStack (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeFibredCategory B S hS T')
    (hf : HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ g => Space.IsSmooth B S hS g) f)
    {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (i : T ⟶ T')
    (hi : Space.IsSquareZeroClosedImmersion B S hS i) (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x = T) (hfx : imageOf f x hx = i) :
    ∃ (z : 𝒳.val.obj) (hz : 𝒳.val.p.obj z = T') (φ : x ⟶ z),
      𝒳.val.p.IsHomLift i φ ∧ imageOf f z hz = 𝟙 T' := by
  obtain ⟨hXfib, -, -, U₀, atlas, hrep, hprop⟩ := id h𝒳
  let a : schemeFibredCategory B S hS U₀ ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom atlas
  have hUstack := isDeligneMumfordStack_schemeFibredCategory.{u, w} B S hS U₀
  let Psm : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun {_ _} q => Space.IsSmooth B S hS q
  let _ : (spaceProperty B S hS Psm).IsStableUnderBaseChange := by
    simpa [Psm, spaceProperty] using Space.isSmooth_isStableUnderBaseChange B S hS
  let _ : (spaceProperty B S hS Psm).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) := by
    change (Space.smoothMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)
    exact Space.smooth_isLocalAtTarget_fppf B S hS
  have ha : HasPropertyOnSomeSmoothDiagram B S hS Psm a :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative B S hS Psm
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) hUstack.1 h𝒳 a hrep).2
      (fun V y hy F hF hEquiv => (hprop V y hy F hF hEquiv).2)
  have hafs := isFormallySmoothOnObjects_of_isSmooth_unconditional B S hS hUstack.1 h𝒳 a hrep ha
  let 𝒳' : AlgebraicStacks.{u, w} B S hS := ⟨𝒳, h𝒳⟩
  let a' : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳' := Bicategory.InducedBicategory.mkHom a
  let f' : 𝒳' ⟶ schemeStack.{u, w} B S hS T' := Bicategory.InducedBicategory.mkHom f
  have hsm : Smooth ((BigFppfOver.toScheme B S hS).map
      (schemeMapOfFunctor B S hS (a ≫ f).hom)) :=
    smooth_siteMap_of_isSmooth B S hS (a' ≫ f')
      (AlgebraicStacks.isSmooth_comp B S hS a' f' ha hf)
  obtain ⟨c, W, g, s, m, θ, hc, hW, hgs, hge, hse, hθ⟩ :=
    exists_affine_etale_chart_cover a hrep hprop hT x hx
  have hm : m ≫ s ≫ schemeMapOfFunctor B S hS (a ≫ f).hom = g ≫ i := by
    rw [← Category.assoc]
    exact (schemeMapOfFunctor_naturality B S hS (a ≫ f).hom (Over.mk (m ≫ s))).symm.trans
      ((relPair_hom_eq f.hom.toFunctor f.hom.w g θ
        (BasedFunctor.w_obj a.hom (Over.mk (m ≫ s))) hx).trans (congrArg (g ≫ ·) hfx))
  exact exists_lift_of_affine_chart h𝒳
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS f' hf) a hafs hsm s hse i hi g
    hgs hge m hm x hx θ hθ

end GroupoidLift

section DottedArrow

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Any two based natural transformations between based functors into the category
`Over T`, based over `C` via `Over.forget T`, are equal. -/
theorem basedNatTrans_eq_of_over_forget
    {C : Type*} [Category C] (X : BasedCategory C) {T : C}
    {F G : X ⥤ᵇ BasedCategory.ofFunctor (Over.forget T)}
    (α β : F ⟶ G) : α = β := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext z
  apply Over.OverMorphism.ext
  have : (Over.forget T).IsHomLift (𝟙 (X.p.obj z)) (α.app z) := α.isHomLift' z
  have : (Over.forget T).IsHomLift (𝟙 (X.p.obj z)) (β.app z) := β.isHomLift' z
  exact (IsHomLift.fac' (Over.forget T) (𝟙 (X.p.obj z)) (α.app z)).trans
    (IsHomLift.fac' (Over.forget T) (𝟙 (X.p.obj z)) (β.app z)).symm

/-- If `p` is fibered in groupoids, then a morphism
`φ : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 U))` lying over `𝟙 U` yields a based natural
transformation `G ⟶ H`. -/
theorem exists_basedNatTrans_of_hom_mk_id
    {C : Type*} [Category C] {X : Type*} [Category X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C)
    (G H : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p)
    (φ : G.obj (Over.mk (𝟙 U)) ⟶ H.obj (Over.mk (𝟙 U)))
    (hφ : p.IsHomLift (𝟙 U) φ) : Nonempty (G ⟶ H) := by
  let E := Functor.twoYonedaEvaluation p U
  let : E.Full := Functor.twoYonedaEvaluation_full p hp U
  exact ⟨E.preimage (Functor.Fiber.homMk p U φ)⟩

/-- An object `Z` of `Over X` with `Z.left = Y` whose structure morphism, transported along this
equality, is `i : Y ⟶ X` equals `Over.mk i`. -/
theorem over_eq_mk_of_eqToHom_comp_eq {C : Type*} [Category C]
    {X Y : C} (i : Y ⟶ X) (Z : Over X)
    (hZ : Z.left = Y) (h : eqToHom hZ.symm ≫ Z.hom = i) :
    Z = Over.mk i := by
  cases Z with
  | mk A _ φ =>
    cases hZ
    simp only [eqToHom_refl, Category.id_comp] at h
    cases h
    rfl

/-- **A dotted arrow from an extension of the object over the thickening.** -/
theorem exists_dottedArrow_of_cartesian_lift
    {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (X : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : X ⟶ schemeFibredCategory B S hS T')
    (x : schemeFibredCategory B S hS T ⟶ X)
    (γ : ((Bicategory.InducedBicategory.mkHom { toFunctor := Over.map i, w := rfl } :
      schemeFibredCategory B S hS T ⟶ schemeFibredCategory B S hS T') ≫ 𝟙 _) ⟶ (x ≫ f))
    (z : X.val.obj) (hz : X.val.p.obj z = T')
    (hfz : f.hom.obj z = Over.mk (𝟙 T'))
    (φ : x.hom.obj (Over.mk (𝟙 T)) ⟶ z)
    (hφ : X.val.p.IsStronglyCartesian i φ) :
    Nonempty (DottedArrow x (Bicategory.InducedBicategory.mkHom
      { toFunctor := Over.map i, w := rfl }) f (𝟙 _) γ) := by
  set j' : schemeFibredCategory B S hS T ⟶ schemeFibredCategory B S hS T' :=
    Bicategory.InducedBicategory.mkHom { toFunctor := Over.map i, w := rfl }
  let E := Functor.twoYonedaEvaluation X.val.p T'
  let : E.IsEquivalence := Functor.twoYonedaEvaluation_isEquivalence X.val.p X.property T'
  let zF : X.val.p.Fiber T' := ⟨z, hz⟩
  let aB := E.objPreimage zF
  let e := E.objObjPreimageIso zF
  let a : schemeFibredCategory B S hS T' ⟶ X :=
    Bicategory.InducedBicategory.mkHom aB
  let ε : aB.obj (Over.mk (𝟙 T')) ⟶ z := e.hom.1
  have hε : X.val.p.IsHomLift (𝟙 T') ε := e.hom.2
  let t : j'.hom.obj (Over.mk (𝟙 T)) ⟶ Over.mk (𝟙 T') :=
    Over.mkIdTerminal.from _
  have hmap : X.val.p.IsHomLift i (aB.map t) := by
    simpa [t, j'] using Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal X.val.p T' aB
      (j'.hom.obj (Over.mk (𝟙 T)))
  have hc : X.val.p.IsHomLift i (aB.map t ≫ ε) :=
    @IsHomLift.comp_lift_id_right _ _ _ _ X.val.p _ _ _ _ _ i (aB.map t) hmap ε hε
  obtain ⟨α⟩ := exists_basedNatTrans_of_hom_mk_id X.val.p X.property T (j' ≫ a).hom x.hom _
    (@Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ X.val.p _ _ _ _ i φ _ _ _ _ _
      (Category.id_comp i).symm (aB.map t ≫ ε) hc)
  obtain ⟨ε', hε'def⟩ : ∃ e : f.hom.obj (aB.obj (Over.mk (𝟙 T'))) ⟶ Over.mk (𝟙 T'),
      e = f.hom.map ε ≫ eqToHom hfz := ⟨_, rfl⟩
  have hε'l : (Over.forget T').IsHomLift (𝟙 T') ε' := by
    have : (Over.forget T').IsHomLift (𝟙 T') (f.hom.map ε) :=
      BasedFunctor.preserves_isHomLift f.hom (𝟙 T') ε
    have : (Over.forget T').IsHomLift (𝟙 T') (eqToHom hfz) :=
      IsHomLift.eqToHom_codomain_lift_id hfz rfl
    rw [hε'def]
    exact IsHomLift.comp_lift_id_right (Over.forget T') (𝟙 T') (f.hom.map ε) (eqToHom hfz)
  have hiso : IsIso ε' := by
    have := (Functor.IsFiberedInGroupoids.over_forget T').isStronglyCartesian_homLift
      (𝟙 T') ε'
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (Over.forget T') (𝟙 T') ε'
  obtain ⟨β⟩ := exists_basedNatTrans_of_hom_mk_id (Over.forget T')
    (Functor.IsFiberedInGroupoids.over_forget T') T' (BasedFunctor.id _) (a ≫ f).hom
    (@inv _ _ _ _ ε' hiso)
    (@IsHomLift.lift_id_inv_isIso _ _ _ _ (Over.forget T') T' _ _ ε' hiso hε'l)
  exact ⟨⟨a, Bicategory.InducedBicategory.Hom₂.mk α, Bicategory.InducedBicategory.Hom₂.mk β,
    Bicategory.InducedBicategory.Hom₂.ext (basedNatTrans_eq_of_over_forget _ _ _)⟩⟩

/-- **Stacks 0DNZ.** Let `T ⟶ T'` be a first-order thickening of affine schemes, `𝒳` an algebraic
stack whose structure morphism `f : 𝒳 ⟶ T'` is smooth, and `x : T ⟶ 𝒳` a morphism over `T'`
(the 2-morphism `γ : j ⟶ x ≫ f`, with `j : T ⟶ T'` the morphism of represented categories
induced by the thickening). Then there is a morphism `x' : T' ⟶ 𝒳` over `T'` with `x'|_T ≅ x`:
a dotted arrow for the square `(x, j, f, 𝟙)`. -/
@[stacks 0DNZ]
theorem exists_dottedArrow_of_isSmooth_of_isFirstOrderThickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T T' : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (i : T ⟶ T')
    (hi : Stacks.Thickenings.IsFirstOrderThickening (B.inclusion.map i.left))
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (f : 𝒳 ⟶ schemeFibredCategory B S hS T')
    (hf : HasPropertyOnSomeSmoothDiagram B S hS
      (fun {X Y} (g : X ⟶ Y) => Space.IsSmooth B S hS g) f)
    (j : schemeFibredCategory B S hS T ⟶ schemeFibredCategory B S hS T')
    (hj : j.hom.toFunctor = Over.map i)
    (x : schemeFibredCategory B S hS T ⟶ 𝒳)
    (γ : (j ≫ 𝟙 _) ⟶ (x ≫ f)) :
    Nonempty (DottedArrow x j f (𝟙 _) γ) := by
  obtain rfl : j = (Bicategory.InducedBicategory.mkHom { toFunctor := Over.map i, w := rfl } :
      schemeFibredCategory B S hS T ⟶ schemeFibredCategory B S hS T') :=
    Bicategory.InducedBicategory.Hom.ext (BasedCategory.BasedFunctor.ext' hj)
  have hxT : 𝒳.val.p.obj (x.hom.obj (Over.mk (𝟙 T))) = T := BasedFunctor.w_obj x.hom _
  have hfx : GroupoidLift.imageOf f (x.hom.obj (Over.mk (𝟙 T))) hxT = i := by
    have hl : (Over.forget T').IsHomLift (𝟙 T) (γ.hom.app (Over.mk (𝟙 T))) :=
      γ.hom.isHomLift' (Over.mk (𝟙 T))
    have e2 := IsHomLift.fac' (Over.forget T') (𝟙 T) (γ.hom.app (Over.mk (𝟙 T)))
    change (γ.hom.app (Over.mk (𝟙 T))).left = _ at e2
    have e3 : GroupoidLift.imageOf f (x.hom.obj (Over.mk (𝟙 T))) hxT =
        (γ.hom.app (Over.mk (𝟙 T))).left ≫
          (f.hom.toFunctor.obj (x.hom.obj (Over.mk (𝟙 T)))).hom := by
      rw [e2]
      simp only [Category.id_comp, eqToHom_trans]
      rfl
    exact e3.trans ((Over.w (γ.hom.app (Over.mk (𝟙 T)))).trans (Category.id_comp i))
  obtain ⟨z, hz, φ, hφ, himg⟩ := GroupoidLift.exists_lift_of_isSmooth_of_isAlgebraicStack h𝒳 f hf
    hT i ⟨hi.1, hi.2⟩ _ hxT hfx
  have hfz : f.hom.obj z = Over.mk (𝟙 T') :=
    over_eq_mk_of_eqToHom_comp_eq (𝟙 T') _ ((relPair_left_eq f.hom.toFunctor f.hom.w z).trans hz)
      himg
  exact exists_dottedArrow_of_cartesian_lift i 𝒳 f x γ z hz hfz φ
    (𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift i φ)

end DottedArrow

end AlgebraicGeometry.Stack

end
