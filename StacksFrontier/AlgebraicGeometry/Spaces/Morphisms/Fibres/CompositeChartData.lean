module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Chart data for a composition of morphisms of algebraic spaces

A compatible triple of pointed etale scheme charts for a pair of composable morphisms of
algebraic spaces, together with the local Noetherianity of the fibres of each chart morphism
inherited from the corresponding morphism of spaces, and the three pointed charts it reads.

This is the shared input of every argument that proves a property of morphisms of algebraic
spaces stable under composition by reading the property off a single pointed chart. The
Cohen-Macaulay and the Gorenstein composition theorems both use it, along with the pointwise form
of flatness it needs.

## Main definitions

* `AlgebraicGeometry.Space.CompositeChartData`: the bundle of charts.
* `AlgebraicGeometry.Space.CompositeChartData.chartF`, `.chartG`, `.chartComp`: the pointed
  charts of the two morphisms and of their composite.

## Main results

* `AlgebraicGeometry.Space.isFlatAt_of_isFlat`: a flat morphism is flat at each point of its
  source.
* `AlgebraicGeometry.Space.exists_compositeChartData`: such a bundle exists at every point.

## Tags

algebraic space, etale chart, composition, fibre
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Flatness of a morphism of algebraic spaces implies flatness at each point of its source. -/
public theorem isFlatAt_of_isFlat
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (x : points B S hS X) : IsFlatAt B S hS f x := by
  intro c
  have := hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  exact (MorphismOfGerms.isFlat_ofSchemeHom_iff _ _).mpr (Flat.stalkMap _ _)

attribute [local instance] etale_isStableUnderComposition surjective_isStableUnderComposition

/-- The data of a compatible triple of etale scheme charts for a pair of composable morphisms
of algebraic spaces, pointed over a point of the source, together with the local Noetherianity
of the fibres of each chart morphism inherited from the corresponding morphism of spaces. -/
public structure CompositeChartData
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : points B S hS X) where
  /-- The chart of the source. -/
  U : BigFppfOver B S hS
  /-- The chart of the middle space. -/
  V : BigFppfOver B S hS
  /-- The chart of the target. -/
  W : BigFppfOver B S hS
  /-- The étale morphism presenting the source. -/
  a : yoneda.obj U ⟶ X
  /-- The étale morphism presenting the middle space. -/
  b : yoneda.obj V ⟶ Y
  /-- The étale morphism presenting the target. -/
  c : yoneda.obj W ⟶ Z
  /-- The chart morphism over `f`. -/
  α : U ⟶ V
  /-- The chart morphism over `g`. -/
  β : V ⟶ W
  /-- A field-valued representative of the chosen point of the source chart. -/
  p : FieldValuedPoint B S hS (yoneda.obj U)
  /-- A point of the spectrum of the representing field. -/
  point : Spec (.of p.carrier)
  /-- The chart of the source is étale. -/
  aEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf a
  /-- The chart of the middle space is étale. -/
  bEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf b
  /-- The chart of the target is étale. -/
  cEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf c
  /-- The square over `f` commutes. -/
  commF : yoneda.map α ≫ b = a ≫ f
  /-- The square over `g` commutes. -/
  commG : yoneda.map β ≫ c = b ≫ g
  /-- The representative lies over the specified point. -/
  mapsTo : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x
  /-- Local Noetherianity of the fibres of `f` passes to the chart morphism over `f`. -/
  noethF : HasLocallyNoetherianFibersAtPoints B S hS f →
    ∀ y, IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map α).fiber y)
  /-- Local Noetherianity of the fibres of `g` passes to the chart morphism over `g`. -/
  noethG : HasLocallyNoetherianFibersAtPoints B S hS g →
    ∀ z, IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map β).fiber z)
  /-- Local Noetherianity of the fibres of `f ≫ g` passes to the composite chart morphism. -/
  noethComp : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g) →
    ∀ z, IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map (α ≫ β)).fiber z)

variable {B S hS}

/-- The pointed chart on `f` carried by composite chart data. -/
public noncomputable def CompositeChartData.chartF
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y ⟶ Z}
    {x : points B S hS X} (d : CompositeChartData B S hS f g x) :
    EtaleChartAtPoint B S hS f x where
  U := d.U
  V := d.V
  a := d.a
  b := d.b
  h := d.α
  a_etale := d.aEtale
  b_etale := d.bEtale
  comm := d.commF
  representative := d.p
  point := d.point
  maps_to := d.mapsTo

/-- The pointed chart on `g` carried by composite chart data. -/
public noncomputable def CompositeChartData.chartG
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y ⟶ Z}
    {x : points B S hS X} (d : CompositeChartData B S hS f g x) :
    EtaleChartAtPoint B S hS g (pointsMap B S hS X f x) where
  U := d.V
  V := d.W
  a := d.b
  b := d.c
  h := d.β
  a_etale := d.bEtale
  b_etale := d.cEtale
  comm := d.commG
  representative := FieldValuedPoint.map B S hS (yoneda.obj d.U) (yoneda.map d.α) d.p
  point := d.point
  maps_to := by
    change (pointsMap B S hS (yoneda.obj d.V) d.b ∘
      pointsMap B S hS (yoneda.obj d.U) (yoneda.map d.α))
        (d.p.class B S hS (yoneda.obj d.U)) = _
    rw [← pointsMap_comp B S hS (yoneda.obj d.U) (yoneda.map d.α) d.b, d.commF,
      pointsMap_comp B S hS (yoneda.obj d.U) d.a f]
    simp only [Function.comp_apply, d.mapsTo]

/-- The pointed chart on `f ≫ g` carried by composite chart data. -/
public noncomputable def CompositeChartData.chartComp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : Y ⟶ Z}
    {x : points B S hS X} (d : CompositeChartData B S hS f g x) :
    EtaleChartAtPoint B S hS (f ≫ g) x where
  U := d.U
  V := d.W
  a := d.a
  b := d.c
  h := d.α ≫ d.β
  a_etale := d.aEtale
  b_etale := d.cEtale
  comm := by simp [d.commG, reassoc_of% d.commF]
  representative := d.p
  point := d.point
  maps_to := d.mapsTo

variable (B S hS)

/-- Pullbacks of presheaves on the big fppf site, supplied directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  (Limits.functorCategoryHasLimitsOfShape (J := WalkingCospan)).has_limit _

/-- An étale atlas of the fibre product of `f` with a surjective étale chart `b` whose first
projection is again a surjective étale chart. -/
private theorem exists_etale_atlas_pullback_fst
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (b : yoneda.obj V ⟶ Y)
    (hbS : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hbE : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ (U : BigFppfOver B S hS) (a₀ : yoneda.obj U ⟶ Limits.pullback f b),
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a₀ ∧
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (a₀ ≫ pullback.fst f b) ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (a₀ ≫ pullback.fst f b) := by
  obtain ⟨U, a₀, ha₀S, ha₀E⟩ :=
    (isAlgebraicSpace_pullback B S hS f b hX (isAlgebraicSpace_yoneda B S hS V) hY).exists_atlas
  exact ⟨U, a₀, ha₀E,
    presheafProperty_comp B S hS (@Surjective.{u}) a₀ _ ha₀S
      (presheafProperty_pullback_fst B S hS _ f b hbS),
    presheafProperty_comp B S hS (@Etale.{u}) a₀ _ ha₀E
      (presheafProperty_pullback_fst B S hS _ f b hbE)⟩

/-- A pair of composable morphisms of algebraic spaces admits a compatible triple of étale
scheme charts pointed over any point of the source. -/
public theorem exists_compositeChartData
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : points B S hS X) : Nonempty (CompositeChartData B S hS f g x) := by
  obtain ⟨W, c, hcS, hcE⟩ := hZ.exists_atlas
  obtain ⟨V, b₀, hb₀E, hbS, hbE⟩ := exists_etale_atlas_pullback_fst B S hS hY hZ g c hcS hcE
  let b := b₀ ≫ pullback.fst g c
  let β := yoneda.preimage (b₀ ≫ pullback.snd g c)
  have hβ : yoneda.map β = b₀ ≫ pullback.snd g c := yoneda.map_preimage _
  obtain ⟨U, a₀, ha₀E, haS, haE⟩ := exists_etale_atlas_pullback_fst B S hS hX hY f b hbS hbE
  let a := a₀ ≫ pullback.fst f b
  let α := yoneda.preimage (a₀ ≫ pullback.snd f b)
  have hα : yoneda.map α = a₀ ≫ pullback.snd f b := yoneda.map_preimage _
  let m : Limits.pullback f b ⟶ Limits.pullback f (pullback.fst g c) :=
    pullback.lift (f := f) (g := pullback.fst g c) (pullback.fst f b)
      (pullback.snd f b ≫ b₀) (by simp only [Category.assoc]; exact pullback.condition)
  have hm : IsPullback m (pullback.snd f b) (pullback.snd f (pullback.fst g c)) b₀ := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback f (pullback.fst g c))
    · simp only [m, pullback.lift_fst]
      simpa [b] using IsPullback.of_hasPullback f b
    · simp only [m, pullback.lift_snd]
  let e := pullbackRightPullbackFstIso g c f
  let ac := a₀ ≫ m ≫ e.hom
  have hacE : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ac := by
    dsimp only [ac]
    rw [← Category.assoc]
    exact (MorphismProperty.cancel_right_of_respectsIso
      (P := (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) (a₀ ≫ m) e.hom).mpr
      (presheafProperty_comp B S hS _ a₀ m ha₀E (presheafProperty_of_isPullback B S hS _ hm hb₀E))
  have hac : ac ≫ pullback.snd (f ≫ g) c = yoneda.map (α ≫ β) := by
    simp [ac, e, m, hα, hβ, Functor.map_comp, Category.assoc,
      pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd_assoc]
  obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haS x
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  refine ⟨{ U := U, V := V, W := W, a := a, b := b, c := c, α := α, β := β
            p := p, point := IsLocalRing.closedPoint p.carrier
            aEtale := haE, bEtale := hbE, cEtale := hcE
            commF := ?_, commG := ?_, mapsTo := hz
            noethF := ?_, noethG := ?_, noethComp := ?_ }⟩
  · rw [hα]
    simp only [a, Category.assoc, pullback.condition]
  · rw [hβ]
    simp only [b, Category.assoc, pullback.condition]
  · exact fun hf ↦ locallyNoetherianFibers_of_etale_pullback_chart B S hS hX hY f hf V b hbE
      U a₀ α hα.symm ha₀E
  · exact fun hg ↦ locallyNoetherianFibers_of_etale_pullback_chart B S hS hY hZ g hg W c hcE
      V b₀ β hβ.symm hb₀E
  · exact fun hgf ↦ locallyNoetherianFibers_of_etale_pullback_chart B S hS hX hZ (f ≫ g) hgf
      W c hcE U ac (α ≫ β) hac hacE

/-! ### The composition statements -/

end Space

end AlgebraicGeometry

end
