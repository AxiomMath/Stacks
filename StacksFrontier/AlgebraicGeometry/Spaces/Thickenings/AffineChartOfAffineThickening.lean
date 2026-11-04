module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.CartesianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Affine charts of a thickening of an affine algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`G ⊆ X` be a thickening whose underlying algebraic space is affine.  This file records three
consequences, none of which needs `X` to be separated or even quasi-separated.

* `X` has an affine surjective étale chart `φ : h_V ⟶ X`.  The point space of `X` is the image
  of that of `G`, which is quasi-compact, so the affine chart of Stacks 03FX over a
  quasi-compact set of points may be taken over all points.
* For any chart `φ : h_V ⟶ X` with `V` affine, the scheme `R = V ×_X V` is affine.  The
  closed subscheme `G ×_X R ⊆ R` is a thickening of schemes, and it is
  `(G ×_X V) ×_G (G ×_X V)`, a fibre product of affine schemes over an affine scheme; so
  Stacks 06AD for schemes applies.
* Consequently such a chart is a quasi-compact morphism: its base change along itself is the
  morphism `R ⟶ V` of affine schemes, and quasi-compactness is local on the target in the étale
  topology (Stacks 03KG).

## Main results

* `AlgebraicGeometry.Space.exists_affine_surjective_etale_chart_of_isThickening`: an affine
  surjective étale chart of `X`.
* `AlgebraicGeometry.Space.isAffine_of_isPullback_of_isThickening`: the kernel pair of an affine
  étale chart of `X` is affine.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isPullback_of_isAffine`: a surjective étale chart
  with affine source and affine kernel pair is quasi-compact.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology preservesLimitsOfShape_walkingCospan_toScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A thickening of an affine algebraic space has an affine surjective étale chart.** The
points of `X` are the image of the points of `G`, which form a quasi-compact space because `G`
is represented by an affine scheme, so the affine étale chart of Stacks 03FX over a
quasi-compact set of points may be taken over all of them. -/
theorem exists_affine_surjective_etale_chart_of_isThickening
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsThickening B S hS X G)
    (hGaff : IsAffineSpace B S hS G.toFunctor) :
    ∃ (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ X.1),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hGaff
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := inferInstance
  have : CompactSpace (points B S hS G.toFunctor) :=
    ((pointsHomeomorphOfIso B S hS e).trans (schemePointsHomeomorph B S hS T)).symm.compactSpace
  have huniv : IsCompact (Set.univ : Set (points B S hS X.1)) := by
    rw [← hG.2.range_eq, ← Set.image_univ]
    exact isCompact_univ.image (continuous_pointsMap B S hS G.ι)
  obtain ⟨V, φ, hV, hφ, hrange⟩ :=
    exists_affine_etale_chart_of_isCompact B S hS X.1 X.2 huniv
  refine ⟨V, φ, hV, ?_, hφ⟩
  exact (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 V φ).2
    fun x => hrange (Set.mem_univ x)

/-- **The kernel pair of an affine chart of a thickening of an affine algebraic space is
affine.** Let `G ⊆ X` be a thickening with `G` affine, let `φ : h_V ⟶ X` be a morphism from an
object of the site with affine underlying scheme, and let `R` with `t s : R ⟶ V` represent
`V ×_X V`.  Then the underlying scheme of `R` is affine.

The base change `G ×_X R ⟶ R` is a thickening of schemes, and pasting cartesian squares
identifies `G ×_X R` with `(G ×_X V) ×_G (G ×_X V)`, a fibre product of affine schemes over
the affine scheme representing `G`.  Stacks 06AD for schemes then makes `R` affine. -/
theorem isAffine_of_isPullback_of_isThickening
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsThickening B S hS X G)
    (hGaff : IsAffineSpace B S hS G.toFunctor) {V R : BigFppfOver B S hS}
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (φ : yoneda.obj V ⟶ X.1)
    (t s : R ⟶ V) (hpb : IsPullback (yoneda.map t) (yoneda.map s) φ φ) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj R) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hGaff
  obtain ⟨U₀, j, p, hA, hj⟩ := exists_thickening_chart_pullback_subfunctor B S hS hG V φ
  obtain ⟨R₁, q, p₁, hP, hq⟩ :=
    exists_thickening_chart_pullback_subfunctor B S hS hG R (yoneda.map t ≫ φ)
  have hw₁ : p₁ ≫ G.ι = (yoneda.map q ≫ yoneda.map t) ≫ φ := by
    rw [hP.w, Category.assoc]
  have lift_exists : ∀ (u : R ⟶ V), yoneda.map t ≫ φ = yoneda.map u ≫ φ →
      ∃ m, yoneda.map m ≫ p = p₁ ∧ yoneda.map m ≫ yoneda.map j = yoneda.map q ≫ yoneda.map u :=
    fun u hu => by
      obtain ⟨m, hm⟩ := yoneda.map_surjective (hA.lift p₁ (yoneda.map q ≫ yoneda.map u)
        (by rw [hw₁, Category.assoc, Category.assoc, hu]))
      exact ⟨m, by rw [hm, IsPullback.lift_fst], by rw [hm, IsPullback.lift_snd]⟩
  obtain ⟨m₁, hm₁p, hm₁j⟩ := lift_exists t rfl
  obtain ⟨m₂, hm₂p, hm₂j⟩ := lift_exists s hpb.w
  -- `R₁ = U₀ ×_{V, s} R`.
  have hQ : IsPullback (yoneda.map m₂) (yoneda.map q) (yoneda.map j) (yoneda.map s) := by
    refine IsPullback.of_right ?_ hm₂j hA
    rw [hm₂p, ← hpb.w]
    exact hP
  -- `R₁ = U₀ ×_X V`, along `j ≫ φ` and `φ`.
  have hO : IsPullback (yoneda.map m₂) (yoneda.map m₁ ≫ yoneda.map j) (p ≫ G.ι) φ := by
    rw [hm₁j, hA.w]
    exact hQ.paste_vert hpb.flip
  -- `R₁ = U₀ ×_G U₀`.
  have hG₀ : IsPullback (yoneda.map m₂) (yoneda.map m₁) p p :=
    IsPullback.of_bot hO (by rw [hm₁p, hm₂p]) hA
  obtain ⟨a, ha⟩ := yoneda.map_surjective (p ≫ e.hom)
  have hT₀ : IsPullback (yoneda.map m₂) (yoneda.map m₁) (yoneda.map a) (yoneda.map a) := by
    refine hG₀.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_ <;> simp [ha]
  have hsq := (IsPullback.of_map_of_faithful yoneda hT₀).map (BigFppfOver.toScheme B S hS)
  have := hj.1
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map j)
  have : IsAffine (pullback ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map a)) := inferInstance
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj R₁) := .of_isIso hsq.isoPullback.hom
  exact Stacks.Thickenings.isAffine_of_isThickening hq

/-- **A surjective étale chart with affine source and affine kernel pair is quasi-compact.**
Its base change along itself is, up to the identification of `V ×_X V` with `R`, the morphism
`s : R ⟶ V` of affine schemes, which is quasi-compact; quasi-compactness descends along the
surjective étale chart (Stacks 03KG). -/
theorem isQuasiCompact_of_isPullback_of_isAffine {X : AlgebraicSpaces B S hS}
    {V R : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hR : IsAffine ((BigFppfOver.toScheme B S hS).obj R)) (φ : yoneda.obj V ⟶ X.1)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (t s : R ⟶ V) (hpb : IsPullback (yoneda.map t) (yoneda.map s) φ φ) :
    IsQuasiCompact B S hS φ := by
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  refine isQuasiCompact_of_surjectiveEtale_atlas B S hS φ (isAlgebraicSpace_yoneda B S hS V)
    X.2 V φ (isSurjective_of_presheafSurjective B S hS φ hs)
    (isEtale_of_presheaf_etale B S hS he) ?_
  have heq : pullback.snd φ φ = hpb.isoPullback.inv ≫ yoneda.map s := by simp
  rw [heq]
  refine isQuasiCompact_of_presheaf_quasiCompact B S hS ?_
  have hqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map s) :=
    have : CompactSpace ((BigFppfOver.toScheme B S hS).obj R) := inferInstance
    quasiCompact_of_compactSpace_of_isAffine _ hV inferInstance
  exact MorphismProperty.RespectsIso.precomp _ hpb.isoPullback.inv _
    ((MorphismProperty.relative_map_iff
      (P := MorphismProperty.inverseImage
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) (F := yoneda)).2 hqc)

end AlgebraicGeometry.Space

end
