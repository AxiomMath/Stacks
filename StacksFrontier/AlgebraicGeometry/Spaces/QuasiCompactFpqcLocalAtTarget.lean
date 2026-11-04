module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Quasi-compactness of morphisms of algebraic spaces is fpqc local on the base

Quasi-compactness of a morphism of algebraic spaces over a scheme `S` (Stacks 03HE) is
local on the base for the fpqc topology of Stacks 03YH. Working with
`AlgebraicGeometry.Space.quasiCompactProperty`, the packaging of it as a
`CategoryTheory.MorphismProperty` on the category of algebraic spaces over `S`, this file
records that it is stable under base change and proves the locality.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_finite_jointly_surjective`: a finite family
  of quasi-compact algebraic spaces whose images cover the points of an algebraic space makes
  that space quasi-compact. This is the finite-index form of part (1) of Stacks 040W.
* `AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine`:
  quasi-compactness of a morphism may be checked on the fibre products with the represented
  presheaves of the affine objects of the site.
* `AlgebraicGeometry.Space.quasiCompactMorphismProperty_pullback_snd_iff`: the packaged
  property at the chosen fibre product of algebraic spaces is quasi-compactness of the second
  projection of the fibre product of presheaves.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_yoneda_of_isAffine`: a represented presheaf
  whose scheme is affine is a quasi-compact algebraic space.
* `AlgebraicGeometry.Space.quasiCompact_isLocalAtTarget_fpqc`: Stacks 041L, at
  `AlgebraicGeometry.Space.quasiCompactProperty`, with
  `AlgebraicGeometry.Space.isQuasiCompact_isLocalAtTarget_fppf` its fppf form.

## Implementation notes

The topology on points is the one of Stacks 03BX, installed as a local instance where needed.

## References

* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compactness from a finite cover on points -/

section Points

attribute [local instance] pointTopology

/-- A finite family of quasi-compact algebraic spaces over `S` whose images cover the points of
an algebraic space `G` makes `G` quasi-compact. -/
theorem isQuasiCompactSpace_of_finite_jointly_surjective {I : Type w} [Finite I]
    {Fi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hFi : ∀ i, IsAlgebraicSpace B S hS (Fi i)) (hG : IsAlgebraicSpace B S hS G)
    (f : ∀ i, Fi i ⟶ G) (hf : IsJointlySurjective B S hS Fi f)
    (hFiqc : ∀ i, IsQuasiCompactSpace B S hS (Fi i)) :
    IsQuasiCompactSpace B S hS G := by
  have _ (i : I) : CompactSpace (points B S hS (Fi i)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (Fi i) (hFi i)).mp (hFiqc i)
  refine (isQuasiCompactSpace_iff_compactSpace_points B S hS G hG).mpr ⟨?_⟩
  rw [← hf]
  exact isCompact_iUnion fun i ↦ isCompact_range (continuous_pointsMap B S hS (f i))

/-- A represented presheaf on the big fppf site over `S` whose scheme is affine is a
quasi-compact algebraic space. -/
theorem isQuasiCompactSpace_yoneda_of_isAffine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiCompactSpace B S hS (yoneda.obj T) := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  exact (isQuasiCompactSpace_iff_compactSpace_points B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)).mpr (compactSpace_points_yoneda B S hS T)

end Points

/-! ### Invariance under isomorphisms of the source -/

/-- Precomposing a quasi-compact morphism of algebraic spaces over `S` with an isomorphism
leaves it quasi-compact. -/
theorem isQuasiCompact_isIso_comp {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ F')
    [IsIso e] {f : F' ⟶ G} (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS (e ≫ f) :=
  isQuasiCompact_of_isPullback B S hS
    (IsPullback.of_horiz_isIso (fst := e) (snd := e ≫ f) (f := f) (g := 𝟙 G) ⟨by simp⟩) hf

/-- The converse of `AlgebraicGeometry.Space.isQuasiCompact_isIso_comp`: an isomorphism may be
cancelled from the source of a quasi-compact morphism. -/
theorem isQuasiCompact_of_isIso_comp {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ F')
    [IsIso e] {f : F' ⟶ G} (hf : IsQuasiCompact B S hS (e ≫ f)) :
    IsQuasiCompact B S hS f := by
  simpa using isQuasiCompact_isIso_comp B S hS (inv e) hf

/-! ### Quasi-compactness as a morphism property -/

/-- Quasi-compactness, as a morphism property of algebraic spaces over `S`, is stable under base
change (Stacks 03HF). -/
instance quasiCompactMorphismProperty_isStableUnderBaseChange :
    (quasiCompactProperty B S hS).IsStableUnderBaseChange where
  of_isPullback {X Y Y' Z f g f' g'} sq hg := by
    change IsQuasiCompact B S hS g'.hom
    have he : (sq.isoIsPullback _ _
        (AlgebraicSpaces.isPullback_fiberProduct B S hS g f)).hom.hom ≫
          pullback.snd g.hom f.hom = g'.hom :=
      congrArg (fun k : Y' ⟶ X ↦ k.hom)
        (sq.isoIsPullback_hom_snd _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS g f))
    let e := sq.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS g f)
    have _ : IsIso e.hom.hom := (ObjectProperty.ι _).map_isIso e.hom
    rw [← he]
    exact isQuasiCompact_isIso_comp B S hS e.hom.hom
      (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g.hom f.hom) hg)

/-- The second projection of the chosen fibre product in the category of algebraic spaces over
`S` carries the packaged property exactly when the second projection of the fibre product of
presheaves is quasi-compact. -/
theorem quasiCompactMorphismProperty_pullback_snd_iff {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    quasiCompactProperty B S hS (pullback.snd f g) ↔
      IsQuasiCompact B S hS (pullback.snd f.hom g.hom) := by
  have he : ((IsPullback.of_hasPullback f g).isoIsPullback _ _
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g)).hom.hom ≫
        pullback.snd f.hom g.hom = (pullback.snd f g).hom :=
    congrArg (fun k : pullback f g ⟶ Y ↦ k.hom)
      ((IsPullback.of_hasPullback f g).isoIsPullback_hom_snd _ _
        (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  let e := (IsPullback.of_hasPullback f g).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f g)
  have _ : IsIso e.hom.hom := (ObjectProperty.ι _).map_isIso e.hom
  refine ⟨fun h ↦ isQuasiCompact_of_isIso_comp B S hS e.hom.hom (he ▸ h), fun h ↦ ?_⟩
  show IsQuasiCompact B S hS (pullback.snd f g).hom
  rw [← he]
  exact isQuasiCompact_isIso_comp B S hS e.hom.hom h

/-- Quasi-compactness of the second projection of a fibre product of presheaves, from
quasi-compactness of the first projection of the symmetric fibre product. -/
theorem isQuasiCompact_pullback_snd_of_fst {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H)
    (g : G ⟶ H) (h : IsQuasiCompact B S hS (pullback.fst g f)) :
    IsQuasiCompact B S hS (pullback.snd f g) := by
  rw [← pullbackSymmetry_hom_comp_fst]
  exact isQuasiCompact_isIso_comp B S hS _ h

/-- Quasi-compactness of the first projection of a fibre product of presheaves, from
quasi-compactness of the second projection of the symmetric fibre product. -/
theorem isQuasiCompact_pullback_fst_of_snd {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H)
    (g : G ⟶ H) (h : IsQuasiCompact B S hS (pullback.snd f g)) :
    IsQuasiCompact B S hS (pullback.fst g f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  exact isQuasiCompact_isIso_comp B S hS _ h

/-! ### Reduction to affine test objects -/

/-- Quasi-compactness of a morphism of algebraic spaces over `S` may be tested on the
represented presheaves of the affine objects of the site: if every such fibre product is a
quasi-compact algebraic space, then the morphism is quasi-compact. -/
theorem isQuasiCompact_of_isQuasiCompactSpace_pullback_affine
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ g : yoneda.obj T ⟶ G, IsQuasiCompactSpace B S hS (pullback g f)) :
    IsQuasiCompact B S hS f := by
  intro Z hZ hZqc k
  obtain ⟨U, a, haffine, hasurj, -⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z hZ).mp hZqc
  have hQ : IsAlgebraicSpace B S hS (pullback k f) :=
    isAlgebraicSpace_pullback B S hS k f hZ hF hG
  refine isQuasiCompactSpace_of_finite_jointly_surjective B S hS
    (I := PUnit.{1}) (Fi := fun _ ↦ pullback a (pullback.fst k f))
    (fun _ ↦ isAlgebraicSpace_pullback B S hS a (pullback.fst k f)
      (isAlgebraicSpace_yoneda B S hS U) hQ hZ)
    hQ (fun _ ↦ pullback.snd a (pullback.fst k f)) ?_ fun _ ↦
      isQuasiCompactSpace_of_iso B S hS
        (pullbackRightPullbackFstIso k f a).symm (hf U haffine (a ≫ k))
  rw [isJointlySurjective_const_iff]
  exact surjective_pointsMap_of_isPullback B S hS
    (IsPullback.of_hasPullback a (pullback.fst k f))
    ((surjective_iff_surjective_pointsMap B S hS Z hZ U a).mp hasurj)

/-! ### Joint surjectivity transported from the underlying schemes -/

/-- A family of morphisms of the big fppf site over `S` which is jointly surjective on the
points of the underlying schemes is jointly surjective on the points of the represented
presheaves. -/
theorem exists_pointsMap_yonedaMap_eq_of_jointly_surjective {I : Type w}
    {T : BigFppfOver B S hS} {U : I → BigFppfOver B S hS} (g : ∀ i, U i ⟶ T)
    (hg : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, ∃ y, (BigFppfOver.toScheme B S hS).map (g i) y = x)
    (x : points B S hS (yoneda.obj T)) :
    ∃ i, ∃ y : points B S hS (yoneda.obj (U i)),
      pointsMap B S hS (yoneda.obj (U i)) (yoneda.map (g i)) y = x := by
  obtain ⟨i, y, hy⟩ := hg (pointsToScheme B S hS T x)
  exact ⟨i, (pointsEquivScheme B S hS (U i)).symm y,
    injective_pointsToScheme B S hS T (by
      rw [pointsToScheme_pointsMap]
      exact congrArg ((BigFppfOver.toScheme B S hS).map (g i))
        ((pointsEquivScheme B S hS (U i)).apply_symm_apply y) |>.trans hy)⟩

/-! ### Stacks 041L -/

/-- Quasi-compactness of morphisms of algebraic spaces over `S` is local on
the base for the fpqc topology. -/
@[stacks 041L, sga "4 IV 8.5.5" "more general"]
instance quasiCompact_isLocalAtTarget_fpqc :
    (quasiCompactProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  classical
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff
    (P := quasiCompactProperty B S hS)
    (K := Topology.precoverage.{u, v} .fpqc B S hS) fun X Y f R hR ↦
      ⟨fun hf U g _ _ ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f g) hf, fun hlocal ↦ ?_⟩
  obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
  have hlocal' (i : I) : IsQuasiCompact B S hS (pullback.snd f.hom (gi i).hom) :=
    (quasiCompactMorphismProperty_pullback_snd_iff B S hS f (gi i)).mp
      (hlocal (gi i) (.mk i))
  refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS X.property Y.property
    f.hom fun T hT h ↦ ?_
  obtain ⟨U, hfinite, hU, hfactor⟩ := hcover.2.2.2 ⟨T, hT⟩ h
  have _ : Finite U.I₀ := hfinite
  let inc := BigAffineFppf.inclusion B S hS
  let uj (j : U.I₀) : yoneda.obj (inc.obj (U.X j)) ⟶ yoneda.obj T :=
    yoneda.map (inc.map (U.f j))
  have hTalg : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hQ : IsAlgebraicSpace B S hS (pullback h f.hom) :=
    isAlgebraicSpace_pullback B S hS h f.hom hTalg X.property Y.property
  have hQj (j : U.I₀) :
      IsQuasiCompactSpace B S hS (pullback (uj j) (pullback.fst h f.hom)) := by
    obtain ⟨i, a, ha⟩ := hfactor j
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (inc.obj (U.X j))) :=
      (U.X j).property
    refine isQuasiCompactSpace_of_iso B S hS
      (pullback.congrHom ha rfl ≪≫ (pullbackRightPullbackFstIso h f.hom (uj j)).symm)
      (isQuasiCompactSpace_of_iso B S hS
        (pullbackSymmetry a (pullback.snd f.hom (gi i).hom) ≪≫
          pullbackLeftPullbackSndIso f.hom (gi i).hom a ≪≫
          pullbackSymmetry f.hom (a ≫ (gi i).hom)) ?_)
    exact hlocal' i (yoneda.obj (inc.obj (U.X j)))
      (isAlgebraicSpace_yoneda B S hS _)
      ((isQuasiCompactSpace_iff_compactSpace_points B S hS _
        (isAlgebraicSpace_yoneda B S hS _)).mpr
        (compactSpace_points_yoneda B S hS (inc.obj (U.X j)))) a
  have hschemes : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ j, ∃ y, (BigFppfOver.toScheme B S hS).map (inc.map (U.f j)) y = x := by
    have hmap : Presieve.map (BigAffineFppf.toScheme B S hS) U.presieve₀ =
        Presieve.ofArrows (fun j ↦ (BigAffineFppf.toScheme B S hS).obj (U.X j))
          fun j ↦ (BigAffineFppf.toScheme B S hS).map (U.f j) := by
      simp [PreZeroHypercover.presieve₀]
    change Presieve.map (BigAffineFppf.toScheme B S hS) U.presieve₀ ∈
        Scheme.qcPrecoverage _ ∧
      Presieve.map (BigAffineFppf.toScheme B S hS) U.presieve₀ ∈
        Scheme.precoverage @Flat _ at hU
    rw [hmap] at hU
    have hflat := hU.2
    change Presieve.ofArrows
        (fun j ↦ (BigAffineFppf.toScheme B S hS).obj (U.X j))
        (fun j ↦ (BigAffineFppf.toScheme B S hS).map (U.f j)) ∈
      Scheme.jointlySurjectivePrecoverage
        ((BigAffineFppf.toScheme B S hS).obj ⟨T, hT⟩) ∧ _ at hflat
    exact (Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).mp
      hflat.1
  refine isQuasiCompactSpace_of_finite_jointly_surjective B S hS
    (fun j ↦ isAlgebraicSpace_pullback B S hS (uj j) (pullback.fst h f.hom)
      (isAlgebraicSpace_yoneda B S hS _) hQ hTalg)
    hQ (fun j ↦ pullback.snd (uj j) (pullback.fst h f.hom)) ?_ hQj
  rw [isJointlySurjective_iff]
  intro z
  obtain ⟨j, y, hy⟩ := exists_pointsMap_yonedaMap_eq_of_jointly_surjective B S hS
    (fun j ↦ inc.map (U.f j)) hschemes
    (pointsMap B S hS (pullback h f.hom) (pullback.fst h f.hom) z)
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback (uj j) (pullback.fst h f.hom)) y z hy
  exact ⟨j, w, hw⟩

/-- Quasi-compactness of morphisms of algebraic spaces over `S` is local on the base for the
fpqc topology: `AlgebraicGeometry.Space.quasiCompact_isLocalAtTarget_fpqc` under a second name. -/
instance isQuasiCompact_isLocalAtTarget_fpqc :
    (quasiCompactProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  quasiCompact_isLocalAtTarget_fpqc B S hS

/-- Quasi-compactness of a morphism of algebraic spaces over `S` is local at the target for the
fppf topology. -/
@[sga "4 IV 8.5.5" "special case"]
instance isQuasiCompact_isLocalAtTarget_fppf :
    (quasiCompactProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fppf B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
