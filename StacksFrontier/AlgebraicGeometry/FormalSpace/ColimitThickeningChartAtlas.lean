module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitThickeningCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOfAffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSetTheoreticConditionRefined

/-!
# The transported charts of a system of thickenings: affineness and covering

Let `E : Λ ⥤ FppfSheaf B S hS` be a diagram of algebraic spaces over `S`, indexed by a preorder
with least element `o`, whose transitions are representable thickenings, and let
`u₀ : h_{U₀} ⟶ E o` be an étale chart with `U₀` affine. In the proof of **Stacks 0AIU** the
chart is transported to every stage (`AlgebraicGeometry.FormalSpace.thickeningChart`), and the
proof needs, of the transported charts:

* that the colimit of each of them is an affine formal algebraic space, by **Stacks 0GVM**:
  each stage is an affine scheme (Stacks 07VT, thickening case), the transitions are base
  changes of those of `E`, hence representable thickenings, and the set-theoretic condition of
  **Stacks 0AIS** comes from the colimit of `E` along the chart morphism;
* that the transported charts of a family of charts of `E o` which is jointly surjective on
  points cover every stage.

This file proves both, together with the existence of such a family of affine charts for an
algebraic space.

## Main results

* `AlgebraicGeometry.FormalSpace.surjective_pointsMapULift_presheaf_of_relative_surjective`: a
  morphism of presheaves representable by objects of the site and surjective after every
  represented base change is surjective on points.
* `AlgebraicGeometry.FormalSpace.exists_affine_etale_charts_of_isAlgebraicSpaceULift`: an
  algebraic space has a family of étale charts by affine objects of the site which is jointly
  surjective on points.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_thickeningChart_obj`: each stage
  of a transported affine chart is an affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.relative_isThickening_thickeningChart_map`: the transitions of
  a transported chart are representable thickenings.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit_thickeningChart`: the
  colimit of a transported affine chart is an affine formal algebraic space as soon as it maps
  to a sheaf satisfying the set-theoretic condition by a morphism representable by algebraic
  spaces.
* `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_thickeningChartπ_app`: the
  transported charts of a family of affine étale charts of `E o` which is jointly surjective on
  points cover every stage.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of presheaves which is representable by objects of the site and surjective
after every represented base change is surjective on points.** A point of the target is a
section over the spectrum `A` of a field of the site; the base change along it is a surjective
morphism `W ⟶ A` of the site, and a point of `W` maps to the given point. This is
`AlgebraicGeometry.FormalSpace.surjective_pointsMapULift_of_relative_surjective` for an
arbitrary source. -/
theorem surjective_pointsMapULift_presheaf_of_relative_surjective
    {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : F' ⟶ F)
    (ha : (Space.surjectiveOnSite B S hS).relative (uliftYoneda.{u + 1}) a) :
    Function.Surjective (Space.pointsMapULift.{u + 1} B S hS _ a) := by
  intro xr
  obtain ⟨pt, rfl⟩ := Quot.exists_rep xr
  let A : BigFppfOver B S hS := pt.siteObject B S hS F
  let ξ : uliftYoneda.{u + 1}.obj A ⟶ F := uliftYonedaEquiv.{u + 1}.symm pt.value
  let q₀ : Space.FieldValuedPointULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj A) :=
    ⟨pt.carrier, pt.contained, pt.toBase, ULift.up (𝟙 A)⟩
  obtain ⟨y, hy⟩ := surjective_pointsMapULift_of_relative_surjective B S hS
    (uliftYoneda.{u + 1}.map (ha.rep.snd ξ)) (Space.relative_uliftYoneda_map B S hS _ _
      (ha.property_snd ξ)) (q₀.class B S hS _)
  have hξpt : Space.pointsMapULift B S hS (uliftYoneda.{u + 1}.obj A) ξ (q₀.class B S hS _)
      = pt.class B S hS F := by
    refine Quot.sound ⟨pt, ⟨𝟙 _, ?_⟩, ⟨𝟙 _, by simp⟩⟩
    show F.map (𝟙 A).op (ξ.app (Opposite.op A) (ULift.up (𝟙 A))) = pt.value
    simp [ξ]
  refine ⟨Space.pointsMapULift B S hS _ (ha.rep.fst ξ) y, ?_⟩
  calc Space.pointsMapULift B S hS _ a (Space.pointsMapULift B S hS _ (ha.rep.fst ξ) y)
      = Space.pointsMapULift B S hS _ (ha.rep.fst ξ ≫ a) y := by
        rw [Space.pointsMapULift_comp]; rfl
    _ = Space.pointsMapULift B S hS _ (uliftYoneda.{u + 1}.map (ha.rep.snd ξ) ≫ ξ) y := by
        rw [(ha.rep.isPullback ξ).w]
    _ = Space.pointsMapULift B S hS _ ξ
          (Space.pointsMapULift B S hS _ (uliftYoneda.{u + 1}.map (ha.rep.snd ξ)) y) := by
        rw [Space.pointsMapULift_comp]; rfl
    _ = pt.class B S hS F := by rw [hy, hξpt]

/-- **An algebraic space has a family of étale charts by affine objects of the site which is
jointly surjective on points**: the members of an affine open covering of the scheme of an
étale atlas, composed with the atlas. -/
theorem exists_affine_etale_charts_of_isAlgebraicSpaceULift
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hX : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X) :
    ∃ (I : Type (u + 1)) (U₀ : I → BigFppfOver B S hS)
      (u₀ : ∀ k, uliftYoneda.{u + 1}.obj (U₀ k) ⟶ X),
      (∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (U₀ k))) ∧
      (∀ k, Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) (u₀ k)) ∧
      ∀ x : Space.pointsULift.{u + 1} B S hS X,
        ∃ (k : I) (z : Space.pointsULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj (U₀ k))),
          Space.pointsMapULift B S hS _ (u₀ k) z = x := by
  obtain ⟨U, f, hfs, hfe⟩ := hX.exists_atlas
  let c := ((BigFppfOver.toScheme B S hS).obj U).affineCover
  have hc (i : c.I₀) : B.Contains (c.X i) :=
    Scheme.size_lt_of_isOpenImmersion (c.f i) U.left.property
  let V (i : c.I₀) : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (c.f i ≫ B.inclusion.map U.hom) : B.obj (hc i) ⟶ B.obj hS)
  let π (i : c.I₀) : V i ⟶ U := Over.homMk (ObjectProperty.homMk (c.f i)) rfl
  have hπet (i : c.I₀) : Etale ((BigFppfOver.toScheme B S hS).map (π i)) :=
    inferInstanceAs (Etale (c.f i))
  refine ⟨ULift.{u + 1} c.I₀, fun k ↦ V k.down, fun k ↦ uliftYoneda.{u + 1}.map (π k.down) ≫ f,
    fun k ↦ inferInstanceAs (IsAffine (c.X k.down)), fun k ↦ ?_, fun x ↦ ?_⟩
  · exact MorphismProperty.comp_mem _ _ _
      (Space.relative_uliftYoneda_map B S hS _ _ (hπet k.down)) hfe
  · obtain ⟨pU, hpU⟩ := surjective_pointsMapULift_of_relative_surjective B S hS f hfs x
    let y := Space.pointsEquivSchemeULift.{u + 1} B S hS U pU
    obtain ⟨w, hw⟩ := c.covers y
    let pV : Space.pointsULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj (V (c.idx y))) :=
      (Space.pointsEquivSchemeULift.{u + 1} B S hS (V (c.idx y))).symm w
    have hqV : Space.pointsMapULift B S hS _ (uliftYoneda.{u + 1}.map (π (c.idx y))) pV = pU := by
      refine (Space.pointsEquivSchemeULift.{u + 1} B S hS U).injective ?_
      rwa [Space.pointsEquivSchemeULift_naturality B S hS (π (c.idx y)) pV,
        Equiv.apply_symm_apply]
    refine ⟨ULift.up (c.idx y), pV, ?_⟩
    rw [Space.pointsMapULift_comp, Function.comp_apply, hqV, hpU]

variable {Λ : Type*} [Preorder Λ] (E : Λ ⥤ FppfSheaf B S hS)
  (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
  (o : Λ) (ho : ∀ j, o ≤ j)
  (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)

/-- **Each stage of a transported affine chart is an affine formal algebraic space**: it is
represented by an affine object of the site
(`AlgebraicGeometry.FormalSpace.exists_isAffine_iso_thickeningChart_obj`). -/
theorem isAffineFormalAlgebraicSpace_thickeningChart_obj
    {U₀ : BigFppfOver B S hS} (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (u₀ : uliftYoneda.{u + 1}.obj U₀ ⟶ (E.obj o).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) (j : Λ) :
    IsAffineFormalAlgebraicSpace B S hS
      ((thickeningChart B S hS E hthick o ho u₀ halg hu₀).obj j) := by
  obtain ⟨T, hT, ⟨e⟩⟩ :=
    exists_isAffine_iso_thickeningChart_obj B S hS E hthick o ho halg hU₀ u₀ hu₀ j
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := sheafToPresheaf J (Type (u + 1))
  let e' : (thickeningChart B S hS E hthick o ho u₀ halg hu₀).obj j ≅ J.uliftYoneda.obj T :=
    (Functor.FullyFaithful.ofFullyFaithful F).preimageIso
      (e ≪≫ (J.uliftYonedaCompSheafToPresheaf.{u + 1}.app T).symm)
  exact isAffineFormalAlgebraicSpace_of_iso B S hS e'.symm
    (isAffineFormalAlgebraicSpace_uliftYoneda B S hS ⟨T, hT⟩)

/-- **The transitions of a transported chart are representable thickenings**: each is a base
change of the corresponding transition of `E` (the transported charts are equifibered over
`E`), read along the sheafified Yoneda embedding as Stacks 0GVM asks. -/
theorem relative_isThickening_thickeningChart_map
    {C₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (u₀ : C₀ ⟶ (E.obj o).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀) ⦃i j : Λ⦄ (g : i ⟶ j) :
    MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
      ((thickeningChart B S hS E hthick o ho u₀ halg hu₀).map g) := by
  let J := BigFppfOver.topology B S hS
  let F := sheafToPresheaf J (Type (u + 1))
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS))
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have h1 : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
      (F.map ((thickeningChart B S hS E hthick o ho u₀ halg hu₀).map g)) :=
    MorphismProperty.of_isPullback
      ((thickeningChartπ_equifibered B S hS E hthick o ho u₀ halg hu₀ g).map F).flip (hthick g)
  exact (Space.relative_comp_map_iff (Sheaf.sheafifiedYoneda J) F _ _).mp
    (relative_of_natIso (sheafifiedYonedaPresheafIso B S hS).symm _ _ h1)

include hthick in
/-- **The transported charts of a family of affine étale charts of `E o` which is jointly
surjective on points cover every stage.** A point of a stage `E j` comes from a point of `E o`,
the transition `E o ⟶ E j` being a representable thickening, hence surjective on points; that
point comes from a point of some chart `U₀ k`, and the unit `h_{U₀ k} ⟶ (E o ⟶ E j)_* h_{U₀ k}`
carries it to a point of the transported chart over the point of `E j`. The covering criterion
for representable étale families
(`AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_jointly_surjective_points`)
concludes. -/
theorem isLocallySurjective_sigmaDesc_thickeningChartπ_app
    {I : Type (u + 1)} (U₀ : I → BigFppfOver B S hS)
    (hU₀ : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (U₀ k)))
    (u₀ : ∀ k, uliftYoneda.{u + 1}.obj (U₀ k) ⟶ (E.obj o).obj)
    (hu₀ : ∀ k, Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) (u₀ k))
    (hpts : ∀ x : Space.pointsULift.{u + 1} B S hS (E.obj o).obj,
      ∃ (k : I) (z : Space.pointsULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj (U₀ k))),
        Space.pointsMapULift B S hS _ (u₀ k) z = x)
    (j : Λ) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective
      (Sigma.desc fun k ↦ (thickeningChartπ B S hS E hthick o ho (u₀ k) halg (hu₀ k)).app j) := by
  refine isLocallySurjective_sigmaDesc_of_jointly_surjective_points B S hS _
    (fun k ↦ isAffineFormalAlgebraicSpace_thickeningChart_obj B S hS E hthick o ho halg
      (hU₀ k) (u₀ k) (hu₀ k) j)
    (fun k ↦ isRepresentableEtale_of_relative_etale B S hS _
      (hasSchemePropertyULift_etale_thickeningChartπ_app B S hS E hthick o ho (u₀ k) halg
        (hu₀ k) j)) fun x ↦ ?_
  have hsurj : (Space.surjectiveOnSite B S hS).relative uliftYoneda.{u + 1}
      (E.map (homOfLE (ho j))).hom :=
    MorphismProperty.relative_monotone (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS))
      (P := MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (fun _ _ _ hf ↦ ⟨hf.2⟩) _ (hthick _)
  obtain ⟨x₀, hx₀⟩ := surjective_pointsMapULift_presheaf_of_relative_surjective B S hS _ hsurj x
  obtain ⟨k, z, hz⟩ := hpts x₀
  refine ⟨k, Space.pointsMapULift B S hS _ (monoPushforward.unit _ (u₀ k)) z, ?_⟩
  calc Space.pointsMapULift B S hS _
          ((thickeningChartπ B S hS E hthick o ho (u₀ k) halg (hu₀ k)).app j).hom
          (Space.pointsMapULift B S hS _ (monoPushforward.unit _ (u₀ k)) z)
      = Space.pointsMapULift B S hS _ (monoPushforward.unit _ (u₀ k) ≫
          monoPushforward.π (E.map (homOfLE (ho j))).hom (u₀ k)) z := by
        rw [Space.pointsMapULift_comp, thickeningChartπ_app_hom]; rfl
    _ = Space.pointsMapULift B S hS _ (E.map (homOfLE (ho j))).hom
          (Space.pointsMapULift B S hS _ (u₀ k) z) := by
        rw [monoPushforward.unit_π, Space.pointsMapULift_comp]; rfl
    _ = x := by rw [hz, hx₀]

section Colimit

variable {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
  (E : Λ ⥤ FppfSheaf B S hS)
  (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
  (o : Λ) (ho : ∀ j, o ≤ j)
  (halg : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj)

/-- **The colimit of a transported affine chart is an affine formal algebraic space** (Stacks
0GVM), as soon as it maps to a sheaf satisfying the set-theoretic condition of Stacks 0AIS by a
morphism representable by algebraic spaces. -/
theorem isAffineFormalAlgebraicSpace_colimit_thickeningChart
    {U₀ : BigFppfOver B S hS} (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (u₀ : uliftYoneda.{u + 1}.obj U₀ ⟶ (E.obj o).obj)
    (hu₀ : Space.HasSchemePropertyULift.{u + 1} B S hS (@Etale) u₀)
    {Z : FppfSheaf B S hS} (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (Φ : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      colimit (thickeningChart B S hS E hthick o ho u₀ halg hu₀) ⟶ Z)
    (hΦ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS Φ.hom) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsAffineFormalAlgebraicSpace B S hS
      (colimit (thickeningChart B S hS E hthick o ho u₀ halg hu₀)) :=
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  isAffineFormalAlgebraicSpace_colimit B S hS _
    (fun j ↦ isAffineFormalAlgebraicSpace_thickeningChart_obj B S hS E hthick o ho halg hU₀ u₀
      hu₀ j)
    (fun _ _ g ↦ relative_isThickening_thickeningChart_map B S hS E hthick o ho halg u₀ hu₀ g)
    _ (Iso.refl _)
    (satisfiesSetTheoreticCondition_source_of_isRepresentableByAlgebraicSpacesULift B S hS Φ hΦ
      hZset)

end Colimit

end AlgebraicGeometry.FormalSpace

end
