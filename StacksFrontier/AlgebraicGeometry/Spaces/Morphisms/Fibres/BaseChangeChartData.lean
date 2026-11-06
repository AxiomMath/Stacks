module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre

/-!
# Chart data for a base change of algebraic spaces

A pointed etale chart of a base change of algebraic spaces, together with the compatible charts
of the source and of the base that produce it, and the charts of the three morphisms it reads.

This is the shared input of every base-change argument for a property of morphisms of algebraic
spaces that is read off a single pointed chart of a fibre. The Cohen-Macaulay and the Gorenstein
base-change theorems both use it.

## Main definitions

* `AlgebraicGeometry.Space.BaseChangeChartData`: the bundle of charts.
* `AlgebraicGeometry.Space.BaseChangeChartData.chartPull`, `.chartSource`, `.chartBase`: the
  pointed charts of the base-changed morphism, of the original morphism and of the base.

## Main results

* `AlgebraicGeometry.Space.exists_baseChangeChartData`: such a bundle exists at every point.

## Tags

algebraic space, etale chart, base change, fibre
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] etale_isStableUnderComposition surjective_isStableUnderComposition

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_BaseChangeChartData :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_BaseChangeChartData
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_BaseChangeChartData B S hS).has_limit _

public structure BaseChangeChartData
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (x' : points B S hS (pullback f g)) where
  /-- The chart of the source. -/
  U : BigFppfOver B S hS
  /-- The chart of the target. -/
  V : BigFppfOver B S hS
  /-- The chart of the new target. -/
  V' : BigFppfOver B S hS
  /-- The chart morphism over `f`. -/
  p : U ⟶ V
  /-- The chart morphism over `g`. -/
  q : V' ⟶ V
  /-- The étale chart of the target. -/
  v : yoneda.obj V ⟶ Y
  /-- The étale chart of the source. -/
  aX : yoneda.obj U ⟶ X
  /-- The étale chart of the new target. -/
  d : yoneda.obj V' ⟶ Y'
  /-- The étale chart of the base change, on the fibre product of the charts. -/
  c : yoneda.obj (pullback p q) ⟶ pullback f g
  /-- A field-valued representative of the given point of the base-changed source. -/
  t : FieldValuedPoint B S hS (yoneda.obj (pullback p q))
  /-- The chart of the target is étale. -/
  vEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf v
  /-- The chart of the source is étale. -/
  aXEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf aX
  /-- The chart of the new target is étale. -/
  dEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf d
  /-- The chart of the base change is étale. -/
  cEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf c
  /-- The square over `f` commutes. -/
  commF : yoneda.map p ≫ v = aX ≫ f
  /-- The square over `g` commutes. -/
  commG : yoneda.map q ≫ v = d ≫ g
  /-- The chart of the base change lies over the chart of the source. -/
  cFst : c ≫ pullback.fst f g = yoneda.map (pullback.fst p q) ≫ aX
  /-- The chart of the base change lies over the chart of the new target. -/
  cSnd : c ≫ pullback.snd f g = yoneda.map (pullback.snd p q) ≫ d
  /-- The representative lies over the given point. -/
  tClass : pointsMap B S hS (yoneda.obj (pullback p q)) c
    (t.class B S hS (yoneda.obj (pullback p q))) = x'
  /-- The chart morphism over `f` has locally Noetherian fibres. -/
  pFiber : ∀ z, IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map p).fiber z)
  /-- The chart morphism over `g` is locally of finite type. -/
  qLft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q)

/-- A morphism of algebraic spaces with locally Noetherian fibres and a morphism locally of
finite type into its target admit compatible étale charts pointed over any point of the base
change. -/
public theorem exists_baseChangeChartData
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g)
    (x' : points B S hS (pullback f g)) :
    Nonempty (BaseChangeChartData B S hS f g x') := by
  obtain ⟨V, v, hvS, hvE⟩ := hY.exists_atlas
  obtain ⟨V', b₀, hb₀S, hb₀E⟩ :=
    (isAlgebraicSpace_pullback B S hS g v hY' (isAlgebraicSpace_yoneda B S hS V) hY).exists_atlas
  let d := b₀ ≫ pullback.fst g v
  let q := yoneda.preimage (b₀ ≫ pullback.snd g v)
  have hq : yoneda.map q = b₀ ≫ pullback.snd g v := yoneda.map_preimage _
  have hdS := presheafProperty_comp B S hS (@Surjective.{u}) b₀ _ hb₀S
    (presheafProperty_pullback_fst B S hS _ g v hvS)
  have hdE := presheafProperty_comp B S hS (@Etale.{u}) b₀ _ hb₀E
    (presheafProperty_pullback_fst B S hS _ g v hvE)
  have hcommG : yoneda.map q ≫ v = d ≫ g := by
    rw [hq]
    simp only [d, Category.assoc, pullback.condition]
  obtain ⟨U, a₀, ha₀S, ha₀E⟩ :=
    (isAlgebraicSpace_pullback B S hS f v hX (isAlgebraicSpace_yoneda B S hS V) hY).exists_atlas
  let aX := a₀ ≫ pullback.fst f v
  let p := yoneda.preimage (a₀ ≫ pullback.snd f v)
  have hp : yoneda.map p = a₀ ≫ pullback.snd f v := yoneda.map_preimage _
  have haXE := presheafProperty_comp B S hS (@Etale.{u}) a₀ _ ha₀E
    (presheafProperty_pullback_fst B S hS _ f v hvE)
  have hcommF : yoneda.map p ≫ v = aX ≫ f := by
    rw [hp]
    simp only [aX, Category.assoc, pullback.condition]
  let pU := pullback.fst p q
  let pV' := pullback.snd p q
  let k₁ : yoneda.obj (pullback p q) ⟶ pullback (pullback.snd f v) (yoneda.map q) :=
    pullback.lift (yoneda.map pU ≫ a₀) (yoneda.map pV') (by
      rw [Category.assoc, ← hp, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg yoneda.map pullback.condition)
  have hk₁ : IsPullback k₁ (yoneda.map pU)
      (pullback.fst (pullback.snd f v) (yoneda.map q)) a₀ := by
    apply IsPullback.of_right
      (t := (IsPullback.of_hasPullback (pullback.snd f v) (yoneda.map q)).flip)
    · simp only [k₁, pullback.lift_snd]
      simpa [hp] using ((IsPullback.of_hasPullback p q).map yoneda).flip
    · simp only [k₁, pullback.lift_fst]
  let k₂ : pullback (pullback.snd f v) (yoneda.map q) ⟶ pullback f g :=
    pullback.lift (pullback.fst (pullback.snd f v) (yoneda.map q) ≫ pullback.fst f v)
      (pullback.snd (pullback.snd f v) (yoneda.map q) ≫ d) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, hcommG, ← Category.assoc])
  have hk₂ : IsPullback k₂ (pullback.snd (pullback.snd f v) (yoneda.map q))
      (pullback.snd f g) d := by
    have hS12 := (IsPullback.of_hasPullback (pullback.snd f v) (yoneda.map q)).paste_horiz
      (IsPullback.of_hasPullback f v)
    rw [hcommG] at hS12
    refine IsPullback.of_right ?_ (by simp only [k₂, pullback.lift_snd])
      (IsPullback.of_hasPullback f g)
    simpa only [k₂, pullback.lift_fst] using hS12
  let c := k₁ ≫ k₂
  have hcE := presheafProperty_comp B S hS (@Etale.{u}) k₁ k₂
    (presheafProperty_of_isPullback B S hS _ hk₁ ha₀E)
    (presheafProperty_of_isPullback B S hS _ hk₂ hdE)
  have hcS := presheafProperty_comp B S hS (@Surjective.{u}) k₁ k₂
    (presheafProperty_of_isPullback B S hS _ hk₁ ha₀S)
    (presheafProperty_of_isPullback B S hS _ hk₂ hdS)
  have hcFst : c ≫ pullback.fst f g = yoneda.map pU ≫ aX := by
    simp only [c, k₂, k₁, aX, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
  have hcSnd : c ≫ pullback.snd f g = yoneda.map pV' ≫ d := by
    simp only [c, k₂, k₁, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd]
  obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS (pullback f g)
    (isAlgebraicSpace_pullback B S hS f g hX hY' hY) (pullback p q) c).mp hcS x'
  obtain ⟨t, rfl⟩ := Quot.exists_rep z
  exact ⟨{ U := U, V := V, V' := V', p := p, q := q, v := v, aX := aX, d := d, c := c
           t := t, vEtale := hvE, aXEtale := haXE, dEtale := hdE, cEtale := hcE
           commF := hcommF, commG := hcommG, cFst := hcFst, cSnd := hcSnd
           tClass := hz
           pFiber := locallyNoetherianFibers_of_etale_pullback_chart B S hS hX hY f hf V v
             hvE U a₀ p hp.symm ha₀E
           qLft := hg V' V d v q hdE hvE hcommG }⟩


/-! ### The three base-change statements -/

variable {B S hS}

/-- The pointed chart on the base change carried by base-change chart data. -/
public noncomputable def BaseChangeChartData.chartPull
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x') :
    EtaleChartAtPoint B S hS (pullback.snd f g) x' where
  U := pullback C.p C.q
  V := C.V'
  a := C.c
  b := C.d
  h := pullback.snd C.p C.q
  a_etale := C.cEtale
  b_etale := C.dEtale
  comm := C.cSnd.symm
  representative := C.t
  point := IsLocalRing.closedPoint C.t.carrier
  maps_to := C.tClass

/-- The pointed chart on the original morphism carried by base-change chart data. -/
public noncomputable def BaseChangeChartData.chartSource
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x') :
    EtaleChartAtPoint B S hS f (pointsMap B S hS (pullback f g) (pullback.fst f g) x') where
  U := C.U
  V := C.V
  a := C.aX
  b := C.v
  h := C.p
  a_etale := C.aXEtale
  b_etale := C.vEtale
  comm := C.commF
  representative := FieldValuedPoint.map B S hS (yoneda.obj (pullback C.p C.q))
    (yoneda.map (pullback.fst C.p C.q)) C.t
  point := IsLocalRing.closedPoint C.t.carrier
  maps_to := by
    change (pointsMap B S hS (yoneda.obj C.U) C.aX ∘
      pointsMap B S hS (yoneda.obj (pullback C.p C.q))
        (yoneda.map (pullback.fst C.p C.q)))
          (C.t.class B S hS (yoneda.obj (pullback C.p C.q))) = _
    rw [← pointsMap_comp B S hS (yoneda.obj (pullback C.p C.q))
      (yoneda.map (pullback.fst C.p C.q)) C.aX, ← C.cFst,
      pointsMap_comp B S hS (yoneda.obj (pullback C.p C.q)) C.c (pullback.fst f g)]
    simp only [Function.comp_apply, C.tClass]

/-- The pointed chart on the base morphism carried by base-change chart data. -/
public noncomputable def BaseChangeChartData.chartBase
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x') :
    EtaleChartAtPoint B S hS g (pointsMap B S hS (pullback f g) (pullback.snd f g) x') where
  U := C.V'
  V := C.V
  a := C.d
  b := C.v
  h := C.q
  a_etale := C.dEtale
  b_etale := C.vEtale
  comm := C.commG
  representative := FieldValuedPoint.map B S hS (yoneda.obj (pullback C.p C.q))
    (yoneda.map (pullback.snd C.p C.q)) C.t
  point := IsLocalRing.closedPoint C.t.carrier
  maps_to := by
    change (pointsMap B S hS (yoneda.obj C.V') C.d ∘
      pointsMap B S hS (yoneda.obj (pullback C.p C.q))
        (yoneda.map (pullback.snd C.p C.q)))
          (C.t.class B S hS (yoneda.obj (pullback C.p C.q))) = _
    rw [← pointsMap_comp B S hS (yoneda.obj (pullback C.p C.q))
      (yoneda.map (pullback.snd C.p C.q)) C.d, ← C.cSnd,
      pointsMap_comp B S hS (yoneda.obj (pullback C.p C.q)) C.c (pullback.snd f g)]
    simp only [Function.comp_apply, C.tClass]

/-- The chart point of the original morphism is the image of the chart point of the base
change. -/
public theorem BaseChangeChartData.sourcePoint_chartSource
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x') :
    C.chartSource.sourcePoint B S hS =
      (BigFppfOver.toScheme B S hS).map (pullback.fst C.p C.q)
        (C.chartPull.sourcePoint B S hS) := by
  show (BigFppfOver.toScheme B S hS).map (C.t.value ≫ pullback.fst C.p C.q) _ = _
  rw [Functor.map_comp]
  rfl

/-- The chart point of the base morphism is the image of the chart point of the base
change. -/
public theorem BaseChangeChartData.sourcePoint_chartBase
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x') :
    C.chartBase.sourcePoint B S hS =
      (BigFppfOver.toScheme B S hS).map (pullback.snd C.p C.q)
        (C.chartPull.sourcePoint B S hS) := by
  show (BigFppfOver.toScheme B S hS).map (C.t.value ≫ pullback.snd C.p C.q) _ = _
  rw [Functor.map_comp]
  rfl


section Statements

/-- The morphism of schemes underlying the chart of the base change is the base change of the
chart morphisms, up to the canonical isomorphism of the chart of the fibre product with the
fibre product of the charts. -/
public theorem toScheme_map_snd_of_chartData
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x') :
    (BigFppfOver.toScheme B S hS).map (pullback.snd C.p C.q) =
      (PreservesPullback.iso (BigFppfOver.toScheme B S hS) C.p C.q).hom ≫
        pullback.snd ((BigFppfOver.toScheme B S hS).map C.p)
          ((BigFppfOver.toScheme B S hS).map C.q) :=
  (PreservesPullback.iso_hom_snd _ _ _).symm

public theorem pullFiber_of_chartData
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {x' : points B S hS (pullback f g)} (C : BaseChangeChartData B S hS f g x')
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map C.q)] :
    ∀ y, IsLocallyNoetherian
      (((BigFppfOver.toScheme B S hS).map (pullback.snd C.p C.q)).fiber y) := by
  rw [toScheme_map_snd_of_chartData C]
  exact isLocallyNoetherian_fiber_iso_comp _ _
    (fun y' => isLocallyNoetherian_fiber_pullback _ _ C.pFiber y')

end Statements

end Space

end AlgebraicGeometry

end
