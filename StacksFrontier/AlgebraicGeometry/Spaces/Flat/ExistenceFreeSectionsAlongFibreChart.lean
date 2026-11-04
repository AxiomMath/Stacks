module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ExistenceFreeSectionsAlongFibre

/-!
# Free sections along a fibre for an algebraic space, read on the chart

`AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre` (in
`StacksFrontier.AlgebraicGeometry.Spaces.Flat.ExistenceFreeSectionsAlongFibre`) states the
reduction of Stacks 0CVW to an affine étale chart of the target with the covering clause of the
conclusion of Stacks 05L1 read on the point space of `X`. This file states the same reduction
with that covering clause kept on the scheme of the chart.

## Main results

* `AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre_chartFibre`: Stacks 0CVW
  at an affine étale chart of the target, with the covering clause of Stacks 05L1 on the chart,
  the induced morphism into the base change surjective and étale, and the identification of the
  set-theoretic fibre `f^{-1}({y}) ⊆ |X|` with the image of the fibre of the chart as a separate
  conjunct.

## References

* [Stacks Project, Tag 0CVW](https://stacks.math.columbia.edu/tag/0CVW)
* [Stacks Project, Tag 05L1](https://stacks.math.columbia.edu/tag/05L1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 0CVW** at an affine étale chart of the target, with the covering
clause of Stacks 05L1 kept on the chart.

This is `AlgebraicGeometry.Space.exists_affineChart_hasFreeSectionsAlongFibre` before its covering
clause is pushed to the point space of `X`. The conclusion of Stacks 05L1 is stated with the
covering clause read on the scheme of the chart `U` itself, where it says that the fibre of
`U ⟶ Y₁` over `w` is the image of the fibre over the closed point of the affine scheme that
Stacks 05L1 produces. The identification of the set-theoretic fibre `f^{-1}({y}) ⊆ |X|` with the
image of that fibre of `U` is a separate conjunct. -/
theorem exists_affineChart_hasFreeSectionsAlongFibre_chartFibre {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (hFt : IsFiniteTypeOnCharts B S hS X.2 F) (y : points B S hS Y.1)
    (hflat : ∀ x : points B S hS X.1, pointsMap B S hS X.1 f.hom x = y →
      x ∈ flatLocus B S hS X.2 f.hom F) :
    ∃ (Y₁ : BigFppfOver B S hS) (q : yoneda.obj Y₁ ⟶ Y.1) (U : SmallEtale B S hS X.1)
      (ĝ : U.obj.left ⟶ Y₁) (hsq : yoneda.map ĝ ≫ q = U.obj.hom ≫ f.hom)
      (w : points B S hS (yoneda.obj Y₁)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) ∧
      IsAffine (etaleChartScheme B S hS U) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      pointsMap B S hS (yoneda.obj Y₁) q w = y ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (pullback.lift (yoneda.map ĝ) U.obj.hom hsq) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (pullback.lift (yoneda.map ĝ) U.obj.hom hsq) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ĝ) ∧
      QuasiCompact ((BigFppfOver.toScheme B S hS).map ĝ) ∧
      (pointsMap B S hS X.1 f.hom ⁻¹' {y} : Set (points B S hS X.1)) =
        pointOfEtaleChart B S hS U ''
          ((BigFppfOver.toScheme B S hS).map ĝ ⁻¹' {pointsToScheme B S hS Y₁ w}) ∧
      HasFreeSectionsAlongFibreOver ((BigFppfOver.toScheme B S hS).map ĝ)
        (chartModule B S hS X.2 F U) (pointsToScheme B S hS Y₁ w) id
        ((BigFppfOver.toScheme B S hS).map ĝ ⁻¹' {pointsToScheme B S hS Y₁ w}) := by
  classical
  obtain ⟨Y₁, q, hY₁aff, hqet, w, hw⟩ := exists_affine_etale_chart_at_point B S hS Y.1 Y.2 y
  have hY₁alg : IsAlgebraicSpace B S hS (yoneda.obj Y₁) := isAlgebraicSpace_yoneda B S hS Y₁
  have hPalg : IsAlgebraicSpace B S hS (pullback q f.hom) :=
    isAlgebraicSpace_pullback B S hS q f.hom hY₁alg X.2 Y.2
  have hPqc : IsQuasiCompactSpace B S hS (pullback q f.hom) :=
    hf.2 (yoneda.obj Y₁) hY₁alg
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS Y₁ hY₁aff) q
  obtain ⟨X', c, hX'aff, hcsurj, hcet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (pullback q f.hom) hPalg).mp hPqc
  have hPiso : ∀ ⦃A C : BigFppfOver B S hS⦄ (m : A ⟶ C), IsIso m →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) m := by
    intro A C m _
    show Etale ((BigFppfOver.toScheme B S hS).map m)
    infer_instance
  have hcP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c := by
    have h₁ := hcet X' (𝟙 (yoneda.obj X')) (presheaf_id_of_iso B S hS _ hPiso X')
    rwa [Category.id_comp] at h₁
  have hsndP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd q f.hom) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback q f.hom) hqet
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have hcomp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hφP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ pullback.snd q f.hom) :=
    hcomp.comp_mem _ _ hcP hsndP
  set U : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (c ≫ pullback.snd q f.hom), hφP⟩ with hU
  set ĝ : U.obj.left ⟶ Y₁ := yoneda.preimage (c ≫ pullback.fst q f.hom) with hĝ
  have hĝmap : yoneda.map ĝ = c ≫ pullback.fst q f.hom := yoneda.map_preimage _
  have hsq : yoneda.map ĝ ≫ q = U.obj.hom ≫ f.hom := by
    rw [hĝmap]
    show (c ≫ pullback.fst q f.hom) ≫ q = (c ≫ pullback.snd q f.hom) ≫ f.hom
    rw [Category.assoc, Category.assoc, pullback.condition]
  set V : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk q, hqet⟩ with hV
  set d : ChartDiagram B S hS X.1 Y.1 f.hom := { U := U, V := V, g := ĝ, comm := hsq.symm }
    with hd
  set τ := (BigFppfOver.toScheme B S hS).map ĝ with hτ
  set w₀ := pointsToScheme B S hS Y₁ w with hw₀def
  have hw₀ : pointOfEtaleChart B S hS V w₀ = y := by
    show pointsMap B S hS (yoneda.obj Y₁) q
      ((pointsEquivScheme B S hS Y₁).symm w₀) = y
    rw [show (pointsEquivScheme B S hS Y₁).symm w₀ = w from
      (pointsEquivScheme B S hS Y₁).symm_apply_apply w]
    exact hw
  have hcompat : ∀ u : etaleChartScheme B S hS U,
      pointsMap B S hS X.1 f.hom (pointOfEtaleChart B S hS U u) =
        pointOfEtaleChart B S hS V (τ u) := by
    intro u
    show pointsMap B S hS X.1 f.hom (pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
      ((pointsEquivScheme B S hS U.obj.left).symm u)) = _
    rw [← pointsMap_comp_apply, ← hsq, pointsMap_comp_apply,
      pointsMap_yoneda_map_symm B S hS ĝ u]
    rfl
  have hlocft : LocallyOfFiniteType τ := hf.1 U.obj.left Y₁ U.obj.hom q ĝ hφP hqet hsq
  have hY₁affI : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) := hY₁aff
  have hUaffI : IsAffine (etaleChartScheme B S hS U) := hX'aff
  have hqcτ : QuasiCompact τ := inferInstance
  have hlift : pullback.lift (yoneda.map ĝ) U.obj.hom hsq = c :=
    pullback.hom_ext (by rw [pullback.lift_fst, hĝmap]) (pullback.lift_snd _ _ _)
  refine ⟨Y₁, q, U, ĝ, hsq, w, hY₁aff, hX'aff, hqet, hw, hlift ▸ hcsurj, hlift ▸ hcP, hlocft,
    hqcτ, ?_⟩
  · have hfibU : ∀ u : etaleChartScheme B S hS U, τ u = w₀ →
        pointsMap B S hS X.1 f.hom (pointOfEtaleChart B S hS U u) = y := fun u hu => by
      rw [hcompat u, hu, hw₀]
    have hfibEq : (pointsMap B S hS X.1 f.hom ⁻¹' {y} : Set (points B S hS X.1)) =
        pointOfEtaleChart B S hS U '' (τ ⁻¹' {w₀}) := by
      refine Set.Subset.antisymm ?_ ?_
      · intro x hx
        have hxy : pointsMap B S hS X.1 f.hom x = y := hx
        obtain ⟨z, hz₁, hz₂⟩ := exists_points_of_isPullback B S hS
          (IsPullback.of_hasPullback q f.hom) w x (hw.trans hxy.symm)
        obtain ⟨uu, huu⟩ := (surjective_iff_surjective_pointsMap B S hS
          (pullback q f.hom) hPalg X' c).mp hcsurj z
        refine ⟨pointsEquivScheme B S hS X' uu, ?_, ?_⟩
        · show τ (pointsEquivScheme B S hS X' uu) ∈ ({w₀} : Set _)
          have h : pointsToScheme B S hS Y₁
              (pointsMap B S hS (yoneda.obj X') (yoneda.map ĝ) uu) =
              τ (pointsToScheme B S hS X' uu) :=
            pointsToScheme_pointsMap_yoneda B S hS ĝ uu
          rw [hĝmap, pointsMap_comp_apply, huu, hz₁] at h
          exact h.symm
        · show pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom
            ((pointsEquivScheme B S hS X').symm (pointsEquivScheme B S hS X' uu)) = x
          rw [(pointsEquivScheme B S hS X').symm_apply_apply]
          show pointsMap B S hS (yoneda.obj X') (c ≫ pullback.snd q f.hom) uu = x
          rw [pointsMap_comp_apply, huu, hz₂]
      · rintro x ⟨u, hu, rfl⟩
        exact hfibU u hu
    have hflatChart : ∀ u : etaleChartScheme B S hS U, τ u = w₀ →
        IsFlatOverAt τ.toLRSHom.toShHom (chartModule B S hS X.2 F U) u := by
      intro u hu
      exact (mem_chartFlatLocus_iff_isFlatOverAtOnChartDiagram B S hS F d u).2
        ((isFlatOverAtOnChartDiagram_iff_mem_flatLocus B S hS f F d u).2
          (hflat _ (hfibU u hu)))
    have _ : (chartModule B S hS X.2 F U).IsQuasicoherent :=
      isQuasicoherent_restrictToChart B S hS X F ‹_› U
    have _ : (chartModule B S hS X.2 F U).IsFiniteType := hFt U
    exact ⟨hfibEq, hasFreeSectionsAlongFibreOver τ (chartModule B S hS X.2 F U) w₀
      id _ (Set.image_id _).symm hflatChart⟩

end AlgebraicGeometry.Space

end
