module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemEtalePresentation

/-!
# The limit of the chart system is a surjective étale chart of the limit

Let `A` be a limit situation with limit algebraic space `X` and chosen stage `X₀`, and let
`U₀ ⟶ X₀` be a morphism from an affine scheme. The limit `U = lim Uᵢ` of the chart system with
stages `Uᵢ = Xᵢ ×_{X₀} U₀` is the fibre product `X ×_{X₀} U₀` along the limit projection
`X ⟶ X₀`. Hence `U ⟶ X` is an étale chart of `X` when `U₀ ⟶ X₀` is an étale chart of `X₀`, and
it is surjective on points when `U₀ ⟶ X₀` is.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.limitIso`: the comparison isomorphism between the
  categorical limit of the system of a limit situation and the presheaf the situation is attached
  to.
* `AlgebraicGeometry.Space.LimitSituation.limitChartToSpace`: the morphism from the limit of a
  chart system to the limit algebraic space.
* `AlgebraicGeometry.Space.LimitSituation.chartLimitToSpace`: the same morphism for the chart
  system of the limit situation at an affine scheme-valued point of the chosen stage.
* `AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.inducedPresheafMap` and `.inducedMap`:
  the map of limit charts induced by a morphism of the two scheme-valued points.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.isPullback_limitChartToSpace`: the limit of a chart
  system is the fibre product `X ×_{X₀} U₀`.
* `AlgebraicGeometry.Space.LimitSituation.isEtaleChart_limitChartToSpace` and
  `.isEtaleChart_chartLimitToSpace`: the limit of a chart system is an étale chart of the limit.
* `AlgebraicGeometry.Space.LimitSituation.isSurjective_limitChartToSpace` and
  `.isSurjective_chartLimitToSpace`: the limit of a chart system is surjective on points.
* `AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.isPullback_inducedPresheafMap`: the
  limit of the relation system is the self fibre product of the limit of the chart system.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The map of limit charts induced by a morphism of the two scheme-valued points -/

section Induced

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶ D.obj i₀}
  {τ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {C : AffineChartSystem B S hS i₀ D U₀ f₀} {E : AffineChartSystem B S hS i₀ D R₀ g₀}

namespace AffineChartSystem.LimitBridge

variable (LC : AffineChartSystem.LimitBridge C) (LE : AffineChartSystem.LimitBridge E)

/-- The map of limit charts induced by a morphism `τ : yoneda R₀ ⟶ yoneda U₀` over `D i₀`, as a
map of presheaves: `lim Rᵢ = limit D ×_{D i₀} R₀` maps to `lim Uᵢ = limit D ×_{D i₀} U₀` by the
identity on the first factor and by `τ` on the second. -/
noncomputable def inducedPresheafMap (hτ : τ ≫ f₀ = g₀) :
    yoneda.obj LE.cone.pt ⟶ yoneda.obj LC.cone.pt :=
  LC.isPullback.lift LE.toLimit (LE.toBase ≫ τ) <| by
    rw [Category.assoc, hτ]; exact LE.isPullback.w

/-- The induced map of limit charts, followed by the projection to the limit of the system, is
the projection to the limit of the system. -/
@[simp]
theorem inducedPresheafMap_comp_toLimit (hτ : τ ≫ f₀ = g₀) :
    inducedPresheafMap LC LE hτ ≫ LC.toLimit = LE.toLimit :=
  LC.isPullback.lift_fst _ _ _

/-- The induced map of limit charts, followed by the projection to `U₀`, is the projection to
`R₀` followed by the morphism of points. -/
@[simp]
theorem inducedPresheafMap_comp_toBase (hτ : τ ≫ f₀ = g₀) :
    inducedPresheafMap LC LE hτ ≫ LC.toBase = LE.toBase ≫ τ :=
  LC.isPullback.lift_snd _ _ _

/-- The induced map of limit charts is compatible with the projections to the stagewise
charts. -/
theorem inducedPresheafMap_comp_π (hτ : τ ≫ f₀ = g₀) (j : Over i₀) :
    inducedPresheafMap LC LE hτ ≫ yoneda.map (LC.cone.π.app j)
      = yoneda.map (LE.cone.π.app j) ≫ C.inducedPresheafMap E hτ j := by
  refine (C.isPullback j).hom_ext ?_ ?_
  · rw [Category.assoc, ← LC.toLimit_comp_limitπ j, ← Category.assoc,
      inducedPresheafMap_comp_toLimit LC LE hτ, LE.toLimit_comp_limitπ j, Category.assoc,
      C.inducedPresheafMap_comp_stageMap E hτ j]
  · rw [Category.assoc, LC.baseMap_comp j, inducedPresheafMap_comp_toBase LC LE hτ,
      Category.assoc, C.inducedPresheafMap_comp_baseMap E hτ j, ← Category.assoc,
      LE.baseMap_comp j]

/-- The limit of the relation system is the self fibre product of the limit of the chart
system, as a cartesian square of presheaves over the limit of the system. -/
theorem isPullback_inducedPresheafMap (ht : τ ≫ f₀ = g₀)
    {υ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
      yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)} (hu : υ ≫ f₀ = g₀)
    (hpb : IsPullback τ υ f₀ f₀) :
    IsPullback (inducedPresheafMap LC LE ht) (inducedPresheafMap LC LE hu)
      LC.toLimit LC.toLimit := by
  have h1 : IsPullback LE.toBase (inducedPresheafMap LC LE ht) τ LC.toBase := by
    refine IsPullback.of_bot ?_ (inducedPresheafMap_comp_toBase LC LE ht).symm
      LC.isPullback.flip
    rw [inducedPresheafMap_comp_toLimit LC LE ht, ht]
    exact LE.isPullback.flip
  have h2 := h1.paste_horiz hpb.flip
  refine (IsPullback.of_right ?_ ?_ LC.isPullback.flip).flip
  · rwa [inducedPresheafMap_comp_toBase LC LE hu, LC.isPullback.w]
  · rw [inducedPresheafMap_comp_toLimit LC LE hu, inducedPresheafMap_comp_toLimit LC LE ht]

/-- The map of limit charts induced by a morphism of the two scheme-valued points, as a
morphism of the big fppf site of `S`. -/
noncomputable def inducedMap (hτ : τ ≫ f₀ = g₀) : LE.cone.pt ⟶ LC.cone.pt :=
  Yoneda.fullyFaithful.preimage (inducedPresheafMap LC LE hτ)

/-- The induced morphism of the site represents the induced map of presheaves. -/
@[simp]
theorem yoneda_map_inducedMap (hτ : τ ≫ f₀ = g₀) :
    yoneda.map (inducedMap LC LE hτ) = inducedPresheafMap LC LE hτ :=
  Yoneda.fullyFaithful.map_preimage _

/-- The induced morphism of the site is compatible with the projections to the stagewise
charts. -/
theorem inducedMap_comp_π (hτ : τ ≫ f₀ = g₀) (j : Over i₀) :
    inducedMap LC LE hτ ≫ LC.cone.π.app j
      = LE.cone.π.app j ≫ C.inducedMap E hτ j :=
  yoneda.map_injective <| by
    rw [yoneda.map_comp, yoneda.map_comp, yoneda_map_inducedMap LC LE hτ,
      C.yoneda_map_inducedMap E hτ j, inducedPresheafMap_comp_π LC LE hτ j]

/-- The square of
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.isPullback_inducedPresheafMap`, with its
two parallel maps the images under Yoneda of morphisms of the site. -/
theorem isPullback_yoneda_inducedMap (ht : τ ≫ f₀ = g₀)
    {υ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
      yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)} (hu : υ ≫ f₀ = g₀)
    (hpb : IsPullback τ υ f₀ f₀) :
    IsPullback (yoneda.map (inducedMap LC LE ht)) (yoneda.map (inducedMap LC LE hu))
      LC.toLimit LC.toLimit := by
  simpa only [yoneda_map_inducedMap] using isPullback_inducedPresheafMap LC LE ht hu hpb

end AffineChartSystem.LimitBridge

end Induced

/-! ### The limit of a chart system as a chart of the limit space -/

namespace LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)

/-- The categorical limit of the system of a limit situation is the presheaf the situation is
attached to. -/
noncomputable def limitIso : limit A.system ≅ X :=
  (limit.isLimit A.system).conePointUniqueUpToIso A.isLimitCone

/-- The comparison isomorphism is compatible with the projections to the stages. -/
theorem limitIso_hom_comp_π (i : A.Iᵒᵖ) :
    A.limitIso.hom ≫ A.π.app i = limit.π A.system i :=
  (limit.isLimit A.system).conePointUniqueUpToIso_hom_comp A.isLimitCone i

section Chart

variable {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (L : AffineChartSystem.LimitBridge C)

/-- The morphism from the limit of a chart system to the limit algebraic space. -/
noncomputable def limitChartToSpace : yoneda.obj L.cone.pt ⟶ X :=
  L.toLimit ≫ A.limitIso.hom

/-- The limit of a chart system is the fibre product `X ×_{X₀} U₀` of the limit algebraic space
with the chosen scheme-valued point over the chosen stage. -/
theorem isPullback_limitChartToSpace :
    IsPullback (A.limitChartToSpace C L) L.toBase (A.π.app (op A.base)) f₀ :=
  L.isPullback.of_iso' (Iso.refl _) A.limitIso.symm (Iso.refl _) (Iso.refl _)
    (by simp [limitChartToSpace]) (by simp)
    (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_comp_eq,
      A.limitIso_hom_comp_π]) (by simp)

/-- The limit of a chart system is an étale chart of the limit algebraic space, as soon as the
scheme-valued point the chart system is built from is an étale chart of the chosen stage. -/
theorem isEtaleChart_limitChartToSpace
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀)) :
    IsEtaleChart B S hS X (CostructuredArrow.mk (A.limitChartToSpace C L)) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (A.isPullback_limitChartToSpace C L).flip hf₀

/-- The limit of a chart system is surjective on points, as soon as the scheme-valued point the
chart system is built from is. -/
theorem isSurjective_limitChartToSpace (hsurj : IsSurjective B S hS f₀) :
    IsSurjective B S hS (A.limitChartToSpace C L) := by
  intro z
  obtain ⟨x, hx⟩ := hsurj (pointsMap B S hS X (A.π.app (op A.base)) z)
  obtain ⟨w, hw, -⟩ :=
    exists_point_of_isPullback_presheaf B S hS (A.isPullback_limitChartToSpace C L) z x hx.symm
  exact ⟨w, hw⟩

end Chart

/-! ### The same, at the chart system of the limit situation itself -/

section ChartSystem

variable (V : BigAffineFppf B S hS)
  (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ A.system.obj (op A.base))

/-- The morphism `U = lim Uᵢ ⟶ X` from the limit of the chart system of a limit situation at an
affine scheme-valued point of the chosen stage. -/
noncomputable abbrev chartLimitToSpace (hI : #A.I < B.cutoff.ord.cof) :
    yoneda.obj (A.chartLimitBridge V g hI).cone.pt ⟶ X :=
  A.limitChartToSpace (A.chartSystem V g) (A.chartLimitBridge V g hI)

/-- The limit of the chart system of a limit situation at an étale chart of the chosen stage is
an étale chart of the limit algebraic space. -/
theorem isEtaleChart_chartLimitToSpace
    (hg : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g))
    (hI : #A.I < B.cutoff.ord.cof) :
    IsEtaleChart B S hS X (CostructuredArrow.mk (A.chartLimitToSpace V g hI)) :=
  A.isEtaleChart_limitChartToSpace _ _ hg

/-- The limit of the chart system of a limit situation at a surjective scheme-valued point of
the chosen stage is surjective on points. -/
theorem isSurjective_chartLimitToSpace (hsurj : IsSurjective B S hS g)
    (hI : #A.I < B.cutoff.ord.cof) :
    IsSurjective B S hS (A.chartLimitToSpace V g hI) :=
  A.isSurjective_limitChartToSpace _ _ hsurj

end ChartSystem

end LimitSituation

end AlgebraicGeometry.Space

end
