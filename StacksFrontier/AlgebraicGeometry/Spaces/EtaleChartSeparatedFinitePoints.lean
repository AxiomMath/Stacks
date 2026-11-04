module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# Finitely many points have finite preimage in an affine étale chart

Stacks 03IJ, available as
`AlgebraicGeometry.Space.finite_fiber_pointsMap_of_etale_presentation`, says that an étale
morphism `φ : h_T ⟶ X` of presheaves on the big fppf site of `S` out of a representable
presheaf has finite fibres on points *provided* the two projections of its self-fibre product
are quasi-compact in the sense of Stacks 03HE. The proof of Stacks 082H uses the tag in the
situation it has arranged by then — `X` separated over an affine scheme and `T` affine, which
is what the source means by "cf. Decent Spaces, Section 68.6" — and there the hypothesis on
the projections is automatic. This file discharges it and draws the conclusion for a finite
set of points.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Spaces.isPullback_selfPullback_diagonal`: in any category with fibre products, the
  self-fibre product of `φ : T ⟶ X` over `X` is the fibre product of the *relative* diagonal
  of `f : X ⟶ Y` with the self-fibre product of `φ ≫ f` over `Y`.
* `AlgebraicGeometry.Space.exists_compactSpace_selfPullback_of_isSeparated_to_affine`: for `X`
  separated over an affine object of the site and `T` affine, the self-fibre product of a
  chart `h_T ⟶ X` is represented by an object of the site with quasi-compact underlying
  scheme.
* `AlgebraicGeometry.Space.isQuasiCompact_selfPullback_of_isSeparated_to_affine`: both
  projections of that self-fibre product are then quasi-compact, which is the hypothesis of
  Stacks 03IJ.
* `AlgebraicGeometry.Space.finite_preimage_pointsMap_of_affine_etale_chart`: a finite set of
  points of such an `X` has finite preimage in an affine étale chart of it.

## Implementation notes

The source argument is that the relation `R = T ×_X T` is a *closed* subscheme of `T ×_Y T`,
which is affine, so `R` is affine and in particular quasi-compact. Here that is the
observation that `R` is the fibre product of the relative diagonal of `f : X ⟶ Y` with
`T ×_Y T ⟶ X ×_Y X`, which is `Stacks.Spaces.isPullback_selfPullback_diagonal`, stated for an
arbitrary category with fibre products. Separatedness of `f` is by definition the statement
that the relative diagonal is representable with closed-immersion represented base changes
(Stacks 03HL), so applying it to the test morphism out of `h_{T ×_Y T}` yields an object of
the site, with a closed immersion into `T ×_Y T`, which represents `R`; closed immersions are
affine and the source of an affine morphism with affine target is affine.

The test morphism must come out of a *representable* presheaf, and `T ×_Y T` is computed in
the presheaf category; the comparison with the fibre product taken in the site is
`CategoryTheory.Limits.PreservesPullback.iso` for the Yoneda embedding, which preserves fibre
products, and the resulting change of the bottom leg of the cartesian square is
`Stacks.Spaces.isPullback_of_iso_right`.

Quasi-compactness of the two projections is then obtained through the representation: each
projection becomes, after the representing isomorphism, the Yoneda image of a morphism of the
site out of a quasi-compact scheme into an affine one, and such a morphism of schemes is
quasi-compact (`AlgebraicGeometry.quasiCompact_of_compactSpace_of_isAffine`); the passage from
that to quasi-compactness in the sense of Stacks 03HE is part (1) implies part (2) of Stacks
03HD, `AlgebraicGeometry.Space.isQuasiCompact_of_presheaf_quasiCompact`.

Étaleness of the chart is used only in the last statement, through Stacks 03IJ. The first
three results hold for an arbitrary morphism `h_T ⟶ X`.

Nothing here carries a Stacks tag: Stacks 03IJ is carried by
`AlgebraicGeometry.Space.finite_fiber_pointsMap_of_etale_presentation`, and the verification of
its hypothesis in the situation of Stacks 082H is a step inside that proof rather than a
result of either tag.

## References

* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03IJ](https://stacks.math.columbia.edu/tag/03IJ)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.Spaces

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- **The relation of a chart is a base change of the relative diagonal.** Let `f : X ⟶ Y` and
`φ : T ⟶ X` be morphisms in a category with fibre products and let `t = φ ≫ f`. Then
`T ×_X T` is the fibre product of the relative diagonal `X ⟶ X ×_Y X` with the canonical
morphism `T ×_Y T ⟶ X ×_Y X`.

This is the step of the proof of Stacks 082H which makes the relation of an affine chart a
*closed* subscheme of an affine scheme: `T ×_Y T` is affine when `T` and `Y` are, and
separatedness of `f` makes the left-hand leg of this square a closed immersion. -/
theorem isPullback_selfPullback_diagonal {X Y T : C} (f : X ⟶ Y) (φ : T ⟶ X) {t : T ⟶ Y}
    (ht : φ ≫ f = t) :
    IsPullback (pullback.fst φ φ ≫ φ)
      (pullback.lift (pullback.fst φ φ) (pullback.snd φ φ)
        (by rw [← ht, ← Category.assoc, ← Category.assoc, pullback.condition]) :
        pullback φ φ ⟶ pullback t t)
      (pullback.diagonal f)
      (pullback.lift (pullback.fst t t ≫ φ) (pullback.snd t t ≫ φ)
        (by rw [Category.assoc, Category.assoc, ht, pullback.condition])) := by
  subst ht
  set q : T ⟶ Y := φ ≫ f
  set b : pullback φ φ ⟶ pullback q q :=
    pullback.lift (pullback.fst φ φ) (pullback.snd φ φ)
      (by rw [← Category.assoc, ← Category.assoc, pullback.condition])
  set h : pullback q q ⟶ pullback f f :=
    pullback.lift (pullback.fst q q ≫ φ) (pullback.snd q q ≫ φ)
      (by rw [Category.assoc, Category.assoc, pullback.condition])
  have hbfst : b ≫ pullback.fst q q = pullback.fst φ φ := pullback.lift_fst _ _ _
  have hbsnd : b ≫ pullback.snd q q = pullback.snd φ φ := pullback.lift_snd _ _ _
  have hhfst : h ≫ pullback.fst f f = pullback.fst q q ≫ φ := pullback.lift_fst _ _ _
  have hhsnd : h ≫ pullback.snd f f = pullback.snd q q ≫ φ := pullback.lift_snd _ _ _
  have w : CommSq (pullback.fst φ φ ≫ φ) b (pullback.diagonal f) h := by
    refine ⟨pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, hhfst,
        ← Category.assoc, hbfst]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, hhsnd,
        ← Category.assoc, hbsnd, pullback.condition]
  have key₁ (s : PullbackCone (pullback.diagonal f) h) :
      (s.snd ≫ pullback.fst q q) ≫ φ = s.fst := by
    simpa [hhfst] using (s.condition =≫ pullback.fst f f).symm
  have key₂ (s : PullbackCone (pullback.diagonal f) h) :
      (s.snd ≫ pullback.snd q q) ≫ φ = s.fst := by
    simpa [hhsnd] using (s.condition =≫ pullback.snd f f).symm
  refine IsPullback.of_isLimit' w (PullbackCone.IsLimit.mk w.w
    (fun s => pullback.lift (s.snd ≫ pullback.fst q q) (s.snd ≫ pullback.snd q q) ?_) ?_ ?_ ?_)
  · rw [key₁, key₂]
  · intro s
    rw [← Category.assoc, pullback.lift_fst, key₁]
  · intro s
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hbfst, pullback.lift_fst]
    · rw [Category.assoc, hbsnd, pullback.lift_snd]
  · intro s m hm₁ hm₂
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, ← hbfst, ← Category.assoc, hm₂]
    · rw [pullback.lift_snd, ← hbsnd, ← Category.assoc, hm₂]

end Stacks.Spaces

namespace AlgebraicGeometry.Space

open Stacks.Spaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relation of a chart of a space separated over an affine scheme is quasi-compact.**
Let `X` be separated over an object `Y₀` of the big fppf site of `S` with affine underlying
scheme and let `φ : h_T ⟶ X` be any morphism from a representable presheaf with `T` affine.
Then the self-fibre product `h_T ×_X h_T` is represented by an object of the site whose
underlying scheme is quasi-compact.

Neither étaleness of `φ` nor algebraicity of `X` is used. The representing object is a closed
subscheme of `T ×_{Y₀} T`, which is affine, by `Stacks.Spaces.isPullback_selfPullback_diagonal`
and the definition of separatedness. -/
theorem exists_compactSpace_selfPullback_of_isSeparated_to_affine
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {f : X ⟶ yoneda.obj Y₀} (hf : IsSeparated B S hS f) (φ : yoneda.obj T ⟶ X) :
    ∃ (Q : BigFppfOver B S hS) (_ : pullback φ φ ≅ yoneda.obj Q),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj Q) := by
  have _ := hY₀
  have _ := hT
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨t, ht⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective (φ ≫ f)
  have sq1 := isPullback_selfPullback_diagonal f φ ht.symm
  set isoP := PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) t t
  have hgc : (pullback.fst (yoneda.map t) (yoneda.map t) ≫ φ) ≫ f =
      (pullback.snd (yoneda.map t) (yoneda.map t) ≫ φ) ≫ f := by
    rw [Category.assoc, Category.assoc, ← ht, pullback.condition]
  set g : yoneda.obj (pullback t t) ⟶ pullback f f :=
    isoP.hom ≫ pullback.lift (pullback.fst (yoneda.map t) (yoneda.map t) ≫ φ)
      (pullback.snd (yoneda.map t) (yoneda.map t) ≫ φ) hgc with hg
  have sq2 : IsPullback (pullback.fst φ φ ≫ φ)
      (pullback.lift (pullback.fst φ φ) (pullback.snd φ φ)
        (by rw [ht, ← Category.assoc, ← Category.assoc, pullback.condition]) ≫ isoP.inv)
      (pullback.diagonal f) g :=
    isPullback_of_iso_right (by simpa [hg] using sq1)
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd g)) := hf.property_snd g
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback t t)) :=
    IsAffine.of_isPullback ((IsPullback.of_hasPullback t t).map (BigFppfOver.toScheme B S hS))
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.rep.pullback g)) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hf.rep.snd g))
  exact ⟨hf.rep.pullback g, sq2.isoIsPullback _ _ (hf.rep.isPullback g), inferInstance⟩

/-- A morphism to a representable presheaf with affine underlying scheme, out of a presheaf
isomorphic to a representable one with quasi-compact underlying scheme, is quasi-compact in
the sense of Stacks 03HE.

Through the isomorphism the morphism is the Yoneda image of a morphism of the site, which is
quasi-compact on underlying schemes because its source is quasi-compact and its target
affine; part (1) implies part (2) of Stacks 03HD then gives quasi-compactness of the morphism
of presheaves. -/
private theorem isQuasiCompact_of_iso_yoneda_of_compactSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T Q : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hQ : CompactSpace ((BigFppfOver.toScheme B S hS).obj Q))
    (e : F ≅ yoneda.obj Q) (p : F ⟶ yoneda.obj T) :
    IsQuasiCompact B S hS p := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  obtain ⟨m, hm⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective (e.inv ≫ p)
  have hrel := (MorphismProperty.relative_map_iff
    (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)).2
    (quasiCompact_of_compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).map m) hT hQ)
  refine isQuasiCompact_of_presheaf_quasiCompact B S hS ?_
  rw [show p = e.hom ≫ yoneda.map m by rw [hm, Iso.hom_inv_id_assoc]]
  exact MorphismProperty.RespectsIso.precomp _ e.hom _ hrel

/-- **The projections of the relation of a chart of a space separated over an affine scheme
are quasi-compact.** This is the hypothesis of Stacks 03IJ, discharged in the situation the
proof of Stacks 082H has arranged: the target has been replaced by an affine scheme, the
morphism is separated, and the chart is affine. -/
theorem isQuasiCompact_selfPullback_of_isSeparated_to_affine
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {f : X ⟶ yoneda.obj Y₀} (hf : IsSeparated B S hS f) (φ : yoneda.obj T ⟶ X) :
    IsQuasiCompact B S hS (pullback.fst φ φ) ∧ IsQuasiCompact B S hS (pullback.snd φ φ) := by
  obtain ⟨Q, e, hQ⟩ :=
    exists_compactSpace_selfPullback_of_isSeparated_to_affine B S hS hY₀ hT hf φ
  constructor <;> exact isQuasiCompact_of_iso_yoneda_of_compactSpace B S hS hT hQ e _

/-- **Finitely many points have finite preimage in an affine étale chart of a space separated
over an affine scheme.** This is Stacks 03IJ applied in the situation of the proof of
Stacks 082H, where it produces the finite set `{z₁, …, z_m}` of points of the chart lying over
the prescribed points `x₁, …, x_n` of the space. -/
theorem finite_preimage_pointsMap_of_affine_etale_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y₀ T : BigFppfOver B S hS}
    (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    {f : X ⟶ yoneda.obj Y₀} (hf : IsSeparated B S hS f)
    (φ : yoneda.obj T ⟶ X) (hφ : IsEtale B S hS φ)
    {s : Set (points B S hS X)} (hs : s.Finite) :
    (pointsMap B S hS (yoneda.obj T) φ ⁻¹' s).Finite := by
  obtain ⟨hqc1, hqc2⟩ :=
    isQuasiCompact_selfPullback_of_isSeparated_to_affine B S hS hY₀ hT hf φ
  exact hs.preimage' fun a _ =>
    finite_fiber_pointsMap_of_etale_presentation B S hS X T φ hφ hqc1 hqc2 a

end AlgebraicGeometry.Space

end
