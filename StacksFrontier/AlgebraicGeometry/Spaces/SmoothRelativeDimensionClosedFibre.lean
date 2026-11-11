module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.RelativeDimensionLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Smoothness of relative dimension `n` spreads out from the closed fibre

Let `f : Y ⟶ h_T` be a flat, universally closed morphism, locally of finite presentation, from
an algebraic space to a scheme `T`, and let `t` be a point of `T` which is a specialization of
every point of `T` (the closed point of a local scheme). If the closed fibre
`Y ×_T Spec κ(t) ⟶ Spec κ(t)` is smooth of relative dimension `n`, then so is `f`.

## The argument

Write `P` for smoothness of relative dimension `n`, a property of morphisms of schemes which is
étale local on the source and target. By Stacks 04RF, `P` holds on every étale chart of `f`
exactly when the induced germ property holds at every point of `|Y|`, and the set `N` of
points where the germ property holds is open.

* A point `x` of `|Y|` lying over `t` is in `N`: on a pointed étale chart `U ⟶ Y` whose target
  chart is `𝟙 h_T`, the scheme morphism `φ : U ⟶ T` is flat and locally of finite presentation,
  and its base change along `Spec κ(t) ⟶ T` is a chart of the closed fibre, so the fibre of `φ`
  over `t` is smooth of relative dimension `n`. The fibrewise criterion
  `AlgebraicGeometry.exists_smoothOfRelativeDimension_nbhd_of_fiber` makes `φ` smooth of
  relative dimension `n` near the chart point.
* Every point `y` of `|Y|` specializes to such an `x`: `|f|` is a closed map, so the image of
  the closure of `y` is a closed subset of `|T|` containing the image of `y`, hence containing
  `t`. As `N` is open and contains `x`, it contains `y`.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_smoothOfRelativeDimension_of_closedFibre`:
  the germ of `f` is smooth of relative dimension `n` at every point over `t`.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_smoothOfRelativeDimension_of_closedFibre`:
  `f` is smooth of relative dimension `n` on every étale chart.

## References

* [Stacks Project, Tag 04RF](https://stacks.math.columbia.edu/tag/04RF)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SmoothRelativeDimensionClosedFibre :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_SmoothRelativeDimensionClosedFibre
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_SmoothRelativeDimensionClosedFibre B S hS).has_limit _

/-- **The closed-fibre point case.** Under the hypotheses of
`holdsOnEveryEtaleChart_smoothOfRelativeDimension_of_closedFibre`, the germ of `f` is smooth of
relative dimension `n` at every point `x` of `Y` lying over `t`.

Take a pointed étale chart of `f` at `x` and replace its target chart by `𝟙 h_T`; the
resulting scheme morphism `φ : U ⟶ T` is flat and locally of finite presentation. Its base
change along `t₀` is a chart of the closed fibre of `f`, so the fibre of `φ` over `t` is smooth of
relative dimension `n`, and the fibrewise criterion
`exists_smoothOfRelativeDimension_nbhd_of_fiber` spreads this to an open neighbourhood of the
chart point. -/
theorem holdsOnEveryEtaleChartAtPoint_smoothOfRelativeDimension_of_closedFibre
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {T : BigFppfOver B S hS} (f : Y ⟶ yoneda.obj T)
    (hlfp : IsLocallyOfFinitePresentation B S hS f) (hflat : IsFlat B S hS f)
    (t : (BigFppfOver.toScheme B S hS).obj T)
    (T₀ : BigFppfOver B S hS) (t₀ : T₀ ⟶ T)
    (e : (BigFppfOver.toScheme B S hS).obj T₀ ≅
      Spec (((BigFppfOver.toScheme B S hS).obj T).residueField t))
    (he : e.hom ≫ ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField t =
      (BigFppfOver.toScheme B S hS).map t₀)
    (n : ℕ)
    (hfib : HoldsOnEveryEtaleChart B S hS (@SmoothOfRelativeDimension n)
      (pullback.snd f (yoneda.map t₀)))
    (x : points B S hS Y) (hx : pointsToScheme B S hS T (pointsMap B S hS Y f x) = t) :
    HoldsOnEveryEtaleChartAtPoint B S hS
      (MorphismOfGerms.HasRepresentativeWithProperty (@SmoothOfRelativeDimension n)) f x := by
  let P : MorphismProperty Scheme.{u} := @SmoothOfRelativeDimension n
  have hP : IsEtaleLocalOnSourceAndTarget P :=
    isEtaleLocalOnSourceAndTarget_smoothOfRelativeDimension n
  have hQ := MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget P hP
  let TT := BigFppfOver.toScheme B S hS
  have he' : e.hom ≫ (TT.obj T).fromSpecResidueField t = TT.map t₀ := he
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hY (isAlgebraicSpace_yoneda B S hS T) f x
  -- Replace the target chart of `c` by the identity of `h_T`.
  let β : c.V ⟶ T := yoneda.preimage c.b
  let h' : c.U ⟶ T := c.h ≫ β
  have hcomm : yoneda.map h' ≫ 𝟙 (yoneda.obj T) = c.a ≫ f := by
    simp only [h', β, Functor.map_comp, Functor.map_preimage, Category.comp_id, c.comm]
  have hid := presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj T))
  let c' : EtaleChartAtPoint B S hS f x :=
    { U := c.U
      V := T
      a := c.a
      b := 𝟙 _
      h := h'
      a_etale := c.a_etale
      b_etale := hid
      comm := hcomm
      representative := c.representative
      point := c.point
      maps_to := c.maps_to }
  refine (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _ hQ f x c').2 ?_
  let φ : TT.obj c.U ⟶ TT.obj T := TT.map h'
  have : Flat φ := hflat c.U T c.a (𝟙 _) h' c.a_etale hid hcomm
  have : LocallyOfFinitePresentation φ := hlfp c.U T c.a (𝟙 _) h' c.a_etale hid hcomm
  -- The chart point lies over `t`.
  have hv : φ (c'.sourcePoint B S hS) = t := by
    have hsp : c'.sourcePoint B S hS =
        pointsToScheme B S hS c.U (c.representative.class B S hS (yoneda.obj c.U)) := by
      change TT.map c.representative.value c.point =
        TT.map c.representative.value (IsLocalRing.closedPoint c.representative.carrier)
      rw [Subsingleton.elim c.point (IsLocalRing.closedPoint c.representative.carrier)]
    have hpt : pointsMap B S hS (yoneda.obj c.U) (yoneda.map h')
        (c.representative.class B S hS (yoneda.obj c.U)) = pointsMap B S hS Y f x := by
      rw [← Category.comp_id (yoneda.map h'), hcomm, pointsMap_comp_apply, c.maps_to]
    rw [hsp, ← pointsToScheme_pointsMap_yoneda, hpt, hx]
  -- The base change of the chart along `t₀` is a chart of the closed fibre.
  let p₁ : Limits.pullback h' t₀ ⟶ c.U := pullback.fst h' t₀
  let p₂ : Limits.pullback h' t₀ ⟶ T₀ := pullback.snd h' t₀
  have hpbW : IsPullback (yoneda.map p₁) (yoneda.map p₂) (yoneda.map h') (yoneda.map t₀) :=
    (IsPullback.of_hasPullback h' t₀).map yoneda
  have hcomm' : c.a ≫ f = yoneda.map h' := by rw [← hcomm, Category.comp_id]
  let a₀ : yoneda.obj (Limits.pullback h' t₀) ⟶ pullback f (yoneda.map t₀) :=
    pullback.lift (yoneda.map p₁ ≫ c.a) (yoneda.map p₂)
      (by rw [Category.assoc, hcomm', hpbW.w])
  have ha₀fst : a₀ ≫ pullback.fst f (yoneda.map t₀) = yoneda.map p₁ ≫ c.a :=
    pullback.lift_fst _ _ _
  have ha₀snd : a₀ ≫ pullback.snd f (yoneda.map t₀) = yoneda.map p₂ :=
    pullback.lift_snd _ _ _
  have hsq : IsPullback a₀ (yoneda.map p₁) (pullback.fst f (yoneda.map t₀)) c.a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd f (yoneda.map t₀))
      (v₁₃ := yoneda.map t₀) (h₂₂ := f) ?_ ha₀fst (IsPullback.of_hasPullback _ _).flip
    rw [ha₀snd, hcomm']
    exact hpbW.flip
  have ha₀ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      TT).presheaf a₀ := presheaf_of_isPullback B S hS hsq.flip c.a_etale
  have hPp₂ : P (TT.map p₂) :=
    hfib _ T₀ a₀ (𝟙 _) p₂ ha₀ (presheaf_etale_of_iso B S hS (Iso.refl _))
      (by rw [Category.comp_id, ha₀snd])
  -- Identify `TT.map p₂` with the fibre of `φ` over `t`.
  have hpbS : IsPullback (TT.map p₁) (TT.map p₂) φ (TT.map t₀) :=
    (IsPullback.of_hasPullback h' t₀).map TT
  have hF : IsPullback (φ.fiberι t) (φ.fiberToSpecResidueField t ≫ e.inv) φ (TT.map t₀) :=
    (IsPullback.of_hasPullback φ ((TT.obj T).fromSpecResidueField t)).of_iso
      (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) (Category.id_comp _).symm
      (Category.id_comp _).symm (by simp)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← he', Iso.inv_hom_id_assoc])
  have hfac : φ.fiberToSpecResidueField t =
      (hF.isoIsPullback _ _ hpbS).hom ≫ TT.map p₂ ≫ e.hom := by
    rw [← Category.assoc, IsPullback.isoIsPullback_hom_snd, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have : SmoothOfRelativeDimension n (φ.fiberToSpecResidueField t) := by
    rw [hfac]
    exact MorphismProperty.RespectsIso.precomp P _ _
      (MorphismProperty.RespectsIso.postcomp P _ _ hPp₂)
  obtain ⟨W, hvW, hPW⟩ :=
    exists_smoothOfRelativeDimension_nbhd_of_fiber (n := n) φ t (c'.sourcePoint B S hS) hv
  refine ⟨⟨W, hvW, W.ι ≫ φ, rfl⟩, MorphismOfGerms.mk_eq_mk_iff.mpr
    ⟨W, hvW, le_rfl, le_top, ?_⟩, hPW⟩
  simp
  rfl

/-- Let `f : Y ⟶ h_T` be flat, locally of finite presentation and universally closed, and let
`t` be a point of `T` which is a specialization of every point (the closed point of a local
scheme). If the closed fibre `Y ×_T Spec κ(t) ⟶ Spec κ(t)` is smooth of relative dimension `n`,
then so is `f`. -/
theorem holdsOnEveryEtaleChart_smoothOfRelativeDimension_of_closedFibre
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {T : BigFppfOver B S hS} (f : Y ⟶ yoneda.obj T)
    (hlfp : IsLocallyOfFinitePresentation B S hS f) (hflat : IsFlat B S hS f)
    (huc : UniversallyClosed B S hS f)
    (t : (BigFppfOver.toScheme B S hS).obj T) (ht : ∀ s, s ⤳ t)
    (T₀ : BigFppfOver B S hS) (t₀ : T₀ ⟶ T)
    (e : (BigFppfOver.toScheme B S hS).obj T₀ ≅
      Spec (((BigFppfOver.toScheme B S hS).obj T).residueField t))
    (he : e.hom ≫ ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField t =
      (BigFppfOver.toScheme B S hS).map t₀)
    (n : ℕ)
    (hfib : HoldsOnEveryEtaleChart B S hS (@SmoothOfRelativeDimension n)
      (pullback.snd f (yoneda.map t₀))) :
    HoldsOnEveryEtaleChart B S hS (@SmoothOfRelativeDimension n) f := by
  let P : MorphismProperty Scheme.{u} := @SmoothOfRelativeDimension n
  have hP : IsEtaleLocalOnSourceAndTarget P :=
    isEtaleLocalOnSourceAndTarget_smoothOfRelativeDimension n
  have hT := isAlgebraicSpace_yoneda B S hS T
  refine (holdsOnEveryEtaleChart_iff_forall_atPoint B S hS P hP hY hT f).2 ?_
  -- The locus where the germ property holds is open.
  let N : Set (points B S hS Y) :=
    {x | HoldsOnEveryEtaleChartAtPoint B S hS
      (MorphismOfGerms.HasRepresentativeWithProperty P) f x}
  have hN : IsOpen N := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨V, hV, hxV, hVP⟩ :=
      (holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS P hP hY hT f x).1 hx
    refine ⟨_, fun z hz => (holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS P hP hY hT f
      z).2 ⟨V, hV, hz, hVP⟩, ?_, hxV⟩
    exact openSubspacesOrderIso_apply B S hS Y hY ⟨V, hV⟩ ▸
      (openSubspacesOrderIso B S hS Y hY ⟨V, hV⟩).2
  -- Every point specializes to a point over `t`, which lies in the open locus.
  have hclosed : IsClosedMap (pointsMap B S hS Y f) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS f (huc _ hT (𝟙 _))
  intro y
  by_contra hy
  have hcl : closure {y} ⊆ Nᶜ :=
    closure_minimal (Set.singleton_subset_iff.2 hy) hN.isClosed_compl
  let τ := schemePointsHomeomorph B S hS T
  have hC : IsClosed (τ '' (pointsMap B S hS Y f '' closure {y})) :=
    τ.isClosedMap _ (hclosed _ isClosed_closure)
  have ht' : t ∈ τ '' (pointsMap B S hS Y f '' closure {y}) := by
    have hs := specializes_iff_mem_closure.1 (ht (τ (pointsMap B S hS Y f y)))
    have hmem : τ (pointsMap B S hS Y f y) ∈ τ '' (pointsMap B S hS Y f '' closure {y}) :=
      ⟨_, ⟨y, subset_closure rfl, rfl⟩, rfl⟩
    exact closure_minimal (Set.singleton_subset_iff.2 hmem) hC hs
  obtain ⟨_, ⟨x, hx, rfl⟩, hxt⟩ := ht'
  exact hcl hx (holdsOnEveryEtaleChartAtPoint_smoothOfRelativeDimension_of_closedFibre B S hS
    hY f hlfp hflat t T₀ t₀ e he n hfib x hxt)

end AlgebraicGeometry.Space

end
