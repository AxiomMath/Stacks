module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionFunctorDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionRepresentedLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFlattening
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.TestSchemeFpqcSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent

/-!
# The flat-dimension functor of a pure module is an algebraic space

**Stacks 0CX1.** In Situation 0CWU, assume moreover that `f` is of finite presentation, that `F`
is an `𝒪_X`-module of finite presentation, and that `F` is pure relative to `Y`. Then `F_n` is an
algebraic space and `F_n ⟶ Y` is a monomorphism of finite presentation.

## Main definitions

* `AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionSubfunctor`: the functor `F_n` of
  equation 0CWV on the big fppf site of `S`, as the subfunctor of `Y` whose points are the maps to
  `Y` along which the base change of `F` is flat in dimensions `≥ n`.

## Main results

* `AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionSubfunctor_zero`: for `n = 0` it is
  the flatness locus `F_flat` of Stacks 0CWX.
* `AlgebraicGeometry.Space.FlatDimensionSituation.isSheaf_flatDimensionSubfunctor`: it is an fppf
  sheaf, by Stacks 0CWW.
* `AlgebraicGeometry.Space.FlatDimensionSituation.exists_isPullback_flatDimensionSubfunctor`: over
  a test scheme whose structure morphism is locally quasi-finite, `F_n` is represented by a
  monomorphism of finite presentation of schemes.
* `AlgebraicGeometry.Space.FlatDimensionSituation.isAlgebraicSpace_flatDimensionSubfunctor`:
  **Stacks 0CX1**.

## The proof

The source's proof: the functor `F_n` is a sheaf (Stacks 0CWW) and its map to `Y` is a
monomorphism; the question of representing it is étale local on `Y`, so `Y` may be taken to be a
scheme, then an affine one; over an affine base the fibre dimensions are bounded, and a
descending induction on `n` reduces to the case in which `F` is flat in dimensions `≥ n + 1`,
where the dévissage of Stacks 0CWJ, purity and Stacks 05UF conclude.

The descent and the induction are made in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatDimensionRepresentedLocus.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/FlatDimensionKeyCase.lean`, for the scheme-level functor
which a surjective étale chart of `X_T` presents over a test scheme `T`
(`AlgebraicGeometry.Space.FlatDimensionSituation.Presented`): it does not depend on the chart, so
it is defined on all schemes over `T`, and the scheme-level tools of Stacks 05UG apply to it.
Over an étale chart `W ⟶ Y` this gives a monomorphism of finite presentation `Z ⟶ W` which is the
base change of `F_n ⟶ Y`; so `Z ⟶ F_n` is a surjective étale chart and `F_n` is an algebraic
space (Stacks 0BGR); and local finite presentation, quasi-compactness and quasi-separatedness of
`F_n ⟶ Y` are read off étale charts of `Y` (Stacks 03MJ, 03KG, 03KM).

## Implementation notes

"Is an algebraic space" is `AlgebraicGeometry.IsAlgebraicSpace`, a predicate on presheaves on the
big fppf site of `S`, whereas `F_n` is displayed on the test schemes over `Y`. They are matched as
for `F_flat` in `StacksFrontier/AlgebraicGeometry/Spaces/UniversalFlattening.lean`: `F_n` is a
subterminal functor over `Y`, so the corresponding presheaf is the subfunctor of `Y` whose
`T`-points are the maps `T ⟶ Y` along which the condition holds.

Purity relative to `Y` is `AlgebraicGeometry.Space.IsPureAbove` at every point of `Y`, Stacks
0CVD part (5) unfolded, for the situation of Stacks 0CV6 that `f` and `F` determine. That
situation asks `f` to be of finite type and decent, which finite presentation gives.

## References

* [Stacks Project, Tag 0CX1](https://stacks.math.columbia.edu/tag/0CX1)
* [Stacks Project, Tag 0CWU](https://stacks.math.columbia.edu/tag/0CWU)
* [Stacks Project, Tag 0CWV](https://stacks.math.columbia.edu/tag/0CWV)
* [Stacks Project, Tag 0CWW](https://stacks.math.columbia.edu/tag/0CWW)
* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 05UG](https://stacks.math.columbia.edu/tag/05UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Flatness

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace FlatDimensionSituation

variable (D : FlatDimensionSituation.{u} B S hS)

/-- **The functor `F_n` of equation 0CWV on the big fppf site of `S`**: the subfunctor of `Y`
whose points are the maps to `Y` along which the base change of `F` is flat in dimensions
`≥ n`. -/
def flatDimensionSubfunctor (n : ℕ) : Subfunctor D.Y.obj where
  obj _ := {a | D.IsFlatInDimensionsGEAfterBaseChange (pointSchemeOver D.Y a) n}
  map i a ha := D.isFlatInDimensionsGEAfterBaseChange_of_hom (pointSchemeOverMap D.Y i a) n ha

/-- A point of `Y` is a section of `F_n` exactly when the base change of `F` to the test scheme
it determines is flat in dimensions `≥ n`. -/
theorem mem_flatDimensionSubfunctor_iff (n : ℕ) {T : (BigFppfOver B S hS)ᵒᵖ}
    (a : D.Y.obj.obj T) :
    a ∈ (D.flatDimensionSubfunctor n).obj T ↔
      D.IsFlatInDimensionsGEAfterBaseChange (pointSchemeOver D.Y a) n :=
  Iff.rfl

/-- The sections of `F_n` over a scheme of the site are the points of `Y` at whose test scheme the
functor `F_n` of equation 0CWV is nonempty. -/
theorem mem_flatDimensionSubfunctor_iff_nonempty (n : ℕ) {T : (BigFppfOver B S hS)ᵒᵖ}
    (a : D.Y.obj.obj T) :
    a ∈ (D.flatDimensionSubfunctor n).obj T ↔
      Nonempty ((D.flatDimensionFunctor n).obj (op (pointSchemeOver D.Y a))) :=
  (D.nonempty_flatDimensionFunctor_obj_iff n _).symm

/-! ### Dimension zero -/

/-- Flatness in dimensions `≥ 0` of the base change is flatness of the base change: on every
square of charts, the non-flat locus of each fibre has dimension `< 0` exactly when it is empty. -/
theorem isFlatInDimensionsGEAfterBaseChange_zero_iff (T : SchemesOver D.Y) :
    D.IsFlatInDimensionsGEAfterBaseChange T 0 ↔ D.toFlatnessSituation.IsFlatAfterBaseChange T := by
  have hqc := D.isQuasicoherentOnSite_baseChangeModule B S hS T
  have hqcC := isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS (baseChangeSpace D.f T)
    (D.toFlatnessSituation.baseChangeModule T) hqc
  have hftC := isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS (baseChangeSpace D.f T)
    (D.toFlatnessSituation.baseChangeModule T) hqc (D.isFiniteTypeOnSite_baseChangeModule T)
  refine forall_congr' fun d => ?_
  rw [isFlatOverInDimensionsGEOnChartDiagram_iff B S hS _ _
    (D.isLocallyOfFiniteType_baseChangeInclusion T) hqcC hftC d 0]
  have := locallyOfFiniteType_chartDiagram B S hS (D.isLocallyOfFiniteType_baseChangeInclusion T) d
  have := hqcC d.U
  have := hftC d.U
  exact (_root_.AlgebraicGeometry.isFlatOver_iff_isFlatOverInDimensionsGE_zero _ _).symm

/-- **For `n = 0`, `F_n` is the flatness locus `F_flat` of Stacks 0CWX.** -/
theorem flatDimensionSubfunctor_zero :
    D.flatDimensionSubfunctor 0 =
      D.toFlatnessSituation.flatSubfunctor D.toFlatnessSituation.isFlatStableUnderBaseChange := by
  ext T a
  exact D.isFlatInDimensionsGEAfterBaseChange_zero_iff (pointSchemeOver D.Y a)

/-! ### The sheaf property -/

/-- **`F_n` is a sheaf for the big fppf topology.** The target `Y` is a sheaf, so the subfunctor
is a sheaf exactly when membership in it is local; an fppf covering sieve of a scheme of the site
contains a flat, locally finitely presented, jointly surjective family, which is an fpqc covering
of the test scheme, and the condition is fpqc local by Stacks 0CWW. -/
theorem isSheaf_flatDimensionSubfunctor (n : ℕ) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (D.flatDimensionSubfunctor n).toFunctor := by
  have hY := (isSheaf_iff_isSheaf_of_type _ _).1 D.Y.2.isSheaf
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _ hY]
  intro U s hs
  classical
  choose c q hq hflat hlfp hx using fun x : (BigFppfOver.toScheme B S hS).obj U.unop =>
    BigFppfOver.exists_mem_of_mem_topology B S hS hs x
  set T : SchemesOver D.Y := pointSchemeOver D.Y s with hT
  set T' : (BigFppfOver.toScheme B S hS).obj U.unop → SchemesOver D.Y :=
    fun x => pointSchemeOver D.Y (D.Y.obj.map (q x).op s) with hT'
  set g : ∀ x, T' x ⟶ T := fun x => pointSchemeOverMap D.Y (q x).op s with hg
  have hpre : Presieve.ofArrows T' g ∈
      (Scheme.fpqcPrecoverage.comap (testSchemeFunctor D.Y)).coverings T := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    refine Scheme.fppfPrecoverage_le_fpqcPrecoverage _ ?_
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x => ⟨x, hx x⟩, fun x => ⟨hflat x, hlfp x⟩⟩
  have hsieve : Sieve.generate (Presieve.ofArrows T' g) ∈ fpqcTopology D.Y T :=
    Precoverage.generate_mem_toGrothendieck hpre
  refine D.isFlatInDimensionsGEAfterBaseChange_of_mem_fpqcTopology n hsieve ?_
  rintro T'' k ⟨Z, k₁, k₂, ⟨x⟩, rfl⟩
  exact D.isFlatInDimensionsGEAfterBaseChange_of_hom k₁ n (hq x)

/-! ### Representation over a quasi-finite test scheme -/

/-- The test scheme determined by a morphism from a scheme of the site to a test scheme. -/
theorem pointSchemeOver_app_eq (T : SchemesOver D.Y) {T' : BigFppfOver B S hS}
    (t : T' ⟶ T.left) :
    pointSchemeOver D.Y (T.hom.hom.app (op T') t) =
      CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) := by
  unfold pointSchemeOver
  congr 1
  apply ObjectProperty.hom_ext
  show yonedaEquiv.symm (T.hom.hom.app (op T') t) = yoneda.map t ≫ T.hom.hom
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  show _ = T.hom.hom.app (op T') (𝟙 T' ≫ t)
  rw [Category.id_comp]

/-- **`F_n` over a quasi-finite test scheme is represented by a monomorphism of finite
presentation of schemes.** Let `T` be a test scheme whose structure morphism to `Y` is locally
quasi-finite. Then there are a scheme `Z` of the site and a monomorphism of finite presentation
`z : Z ⟶ T` such that the square `Z ⟶ F_n`, `Z ⟶ T` over `F_n ⟶ Y`, `T ⟶ Y` is cartesian. -/
theorem exists_isPullback_flatDimensionSubfunctor (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hpure : ∀ y, IsPureAbove (D.fpPrePureSituation hf y)) (n : ℕ) (T : SchemesOver D.Y)
    (hqf : IsLocallyQuasiFinite B S hS T.hom.hom) :
    ∃ (Zs : BigFppfOver B S hS) (z : Zs ⟶ T.left)
      (j : yoneda.obj Zs ⟶ (D.flatDimensionSubfunctor n).toFunctor),
      FinitePresentation ((BigFppfOver.toScheme B S hS).map z) ∧
        Mono ((BigFppfOver.toScheme B S hS).map z) ∧
        IsPullback j (yoneda.map z) (D.flatDimensionSubfunctor n).ι T.hom.hom := by
  obtain ⟨Z, hZm, hZfp, hZ⟩ := D.isRepresentedOver hf hF hpure n T hqf
  obtain ⟨h1, h2, h3⟩ := hZfp
  have hZc : B.Contains Z.left :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact Z.hom).trans_lt T.left.left.2
  let Zs := BigFppfOver.siteObjectOver B S hS T.left hZc Z.hom
  let z : Zs ⟶ T.left := BigFppfOver.siteMapOver B S hS T.left hZc Z.hom
  have hzmono : Mono z := (BigFppfOver.toScheme B S hS).mono_of_mono_map hZm
  -- the preimage of `F_n` in `T` is the range of `z`
  have hpre :
      (D.flatDimensionSubfunctor n).preimage T.hom.hom = Subfunctor.range (yoneda.map z) := by
    ext T' t
    obtain ⟨T'⟩ := T'
    show D.IsFlatInDimensionsGEAfterBaseChange
      (pointSchemeOver D.Y (T.hom.hom.app (op T') t)) n ↔ t ∈ Set.range ((yoneda.map z).app (op T'))
    rw [D.pointSchemeOver_app_eq T t]
    let β : (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map t ≫ T.hom) : SchemesOver D.Y) ⟶
        T := CostructuredArrow.homMk t rfl
    rw [D.isFlatInDimensionsGEAfterBaseChange_iff_presented n β, hZ]
    constructor
    · rintro ⟨k⟩
      refine ⟨Over.homMk (ObjectProperty.homMk k.left) ?_, ?_⟩
      · apply ObjectProperty.hom_ext
        show k.left ≫ Z.hom ≫ T.left.hom.hom = T'.hom.hom
        rw [← Category.assoc, Over.w k]
        exact congrArg (fun m => m.hom) (Over.w t)
      · apply (BigFppfOver.toScheme B S hS).map_injective
        show k.left ≫ Z.hom = (BigFppfOver.toScheme B S hS).map t
        exact Over.w k
    · rintro ⟨k, rfl⟩
      exact ⟨Over.homMk ((BigFppfOver.toScheme B S hS).map k) rfl⟩
  -- the cartesian square
  let e : (D.flatDimensionSubfunctor n).preimage T.hom.hom ≅ Subfunctor.range (yoneda.map z) :=
    eqToIso hpre
  have he : ∀ (P Q : Subfunctor (yoneda.obj T.left)) (h : P = Q),
      (eqToHom (congrArg Subfunctor.toFunctor h)) ≫ Q.ι = P.ι := by
    intro P Q h
    subst h
    simp
  let eR : yoneda.obj Zs ≅ (Subfunctor.range (yoneda.map z)).toFunctor :=
    asIso (Subfunctor.toRange (yoneda.map z))
  let eP : yoneda.obj Zs ≅ ((D.flatDimensionSubfunctor n).preimage T.hom.hom).toFunctor :=
    eR ≪≫ eqToIso (congrArg Subfunctor.toFunctor hpre.symm)
  have heP : eP.hom ≫ ((D.flatDimensionSubfunctor n).preimage T.hom.hom).ι = yoneda.map z := by
    show (Subfunctor.toRange (yoneda.map z) ≫
      eqToHom (congrArg Subfunctor.toFunctor hpre.symm)) ≫ _ = _
    exact (Category.assoc _ _ _).trans ((congrArg (Subfunctor.toRange (yoneda.map z) ≫ ·)
      (he _ _ hpre.symm)).trans (Subfunctor.toRange_ι _))
  refine ⟨Zs, z, eP.hom ≫ (D.flatDimensionSubfunctor n).fromPreimage T.hom.hom,
    ⟨h1, h2, h3⟩, hZm, ?_⟩
  have hsq := Subfunctor.isPullback_preimage T.hom.hom (D.flatDimensionSubfunctor n)
  exact hsq.of_iso eP.symm (Iso.refl (D.flatDimensionSubfunctor n).toFunctor)
    (Iso.refl (yoneda.obj T.left)) (Iso.refl D.Y.obj)
    ((Category.comp_id _).trans (eP.inv_hom_id_assoc _).symm)
    ((Category.comp_id _).trans ((eP.inv_hom_id_assoc _).symm.trans
      (congrArg (eP.inv ≫ ·) heP)))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **Stacks Project, Tag 0CX1.** In Situation 0CWU, assume moreover that `f` is of finite
presentation, that `F` is an `𝒪_X`-module of finite presentation, and that `F` is pure relative
to `Y`. Then `F_n` is an algebraic space and `F_n ⟶ Y` is a monomorphism of finite presentation.

`F_n` is `AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionSubfunctor`, the functor of
equation 0CWV read on the big fppf site of `S` as a subfunctor of `Y`. Purity of `F` relative to
`Y` is purity above every point of `Y`, Stacks 0CVD part (5), for the situation of Stacks 0CV6
which `f` and `F` determine; that situation is formed from the hypotheses of the theorem, since a
morphism of finite presentation is of finite type and decent. -/
@[stacks 0CX1 "the full statement under exactly the source's hypotheses, nothing granted or \
assumed: F_n is the subfunctor of Y of the maps T ⟶ Y along which F_T is flat in dimensions ≥ n \
(equation 0CWV); purity relative to Y is purity above every point of Y (Stacks 0CVD (5)); \
finite presentation of f is local finite presentation, quasi-compactness and \
quasi-separatedness (Stacks 03XP (3))"]
theorem isAlgebraicSpace_flatDimensionSubfunctor (n : ℕ)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hpure : ∀ y, IsPureAbove (D.fpPrePureSituation hf y)) :
    IsAlgebraicSpace B S hS (D.flatDimensionSubfunctor n).toFunctor ∧
      Mono (D.flatDimensionSubfunctor n).ι ∧
      IsFinitePresentation B S hS (D.flatDimensionSubfunctor n).ι := by
  have hex := fun {W : BigFppfOver B S hS} (a : yoneda.obj W ⟶ D.Y.obj) (h : IsEtale B S hS a) =>
    D.exists_isPullback_flatDimensionSubfunctor hf hF hpure n
      (CostructuredArrow.mk (ObjectProperty.homMk a : (schemeSpaceFunctor B S hS).obj W ⟶ D.Y))
      (isLocallyQuasiFinite_of_isEtale' B S hS h)
  obtain ⟨W, a, has, hae⟩ := D.Y.2.exists_atlas
  have haet : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).2 hae
  obtain ⟨Zs, z, j, hzfp, -, hsq⟩ := hex a haet
  -- `F_n` is an algebraic space: `Z ⟶ F_n` is a surjective étale chart
  have hjs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip has
  have hje : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip hae
  have halg : IsAlgebraicSpace B S hS (D.flatDimensionSubfunctor n).toFunctor :=
    isAlgebraicSpace_of_relativelyRepresentable_surjective_etale B S hS
      (isAlgebraicSpace_yoneda B S hS Zs) (D.isSheaf_flatDimensionSubfunctor n) j hjs hje
  refine ⟨halg, inferInstance, ?_⟩
  -- the base change of `F_n ⟶ Y` along the atlas is of finite presentation
  have hpbfp : IsFinitePresentation B S hS (pullback.snd (D.flatDimensionSubfunctor n).ι a) := by
    have hsq' : IsPullback hsq.isoPullback.inv (pullback.snd (D.flatDimensionSubfunctor n).ι a)
        (yoneda.map z) (𝟙 _) :=
      IsPullback.of_horiz_isIso
        ⟨((Iso.inv_comp_eq _).2 hsq.isoPullback_hom_snd.symm).trans (Category.comp_id _).symm⟩
    exact isFinitePresentation_of_isPullback B S hS
      (isAlgebraicSpace_pullback B S hS (D.flatDimensionSubfunctor n).ι a halg
        (isAlgebraicSpace_yoneda B S hS W) D.Y.2)
      (isAlgebraicSpace_yoneda B S hS Zs) (isAlgebraicSpace_yoneda B S hS W)
      (isAlgebraicSpace_yoneda B S hS W) hsq'
      (isFinitePresentation_yoneda_map B S hS z hzfp)
  refine ⟨?_, isQuasiCompact_of_surjectiveEtale_atlas B S hS (D.flatDimensionSubfunctor n).ι halg
      D.Y.2 W a ((presheafSurjective_iff_isSurjective_yoneda B S hS D.Y.1 D.Y.2 W a).1 has) haet
      hpbfp.2.1, isQuasiSeparated_of_etaleChart B S hS halg has hae hpbfp.2.2⟩
  -- local finite presentation, on étale charts of the target
  intro U V u v α hu hv hcomm
  obtain ⟨ZV, zV, jV, hzVfp, -, hsqV⟩ := hex v ((isEtale_iff_presheaf_of_yoneda B S hS v).2 hv)
  have hjVe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf jV :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsqV.flip hv
  let k : yoneda.obj U ⟶ yoneda.obj ZV := hsqV.lift u (yoneda.map α) hcomm.symm
  let k' : U ⟶ ZV := yoneda.preimage k
  have hk' : yoneda.map k' = k := yoneda.map_preimage k
  have hk'j : yoneda.map k' ≫ jV = u := by rw [hk']; exact hsqV.lift_fst _ _ _
  have hk'z : k' ≫ zV = α :=
    yoneda.map_injective (by rw [yoneda.map_comp, hk']; exact hsqV.lift_snd _ _ _)
  have hk'et : Etale ((BigFppfOver.toScheme B S hS).map k') :=
    etale_of_etale_charts B S hS u jV hu hjVe k' hk'j
  rw [← hk'z, Functor.map_comp]
  have := hzVfp.locallyOfFinitePresentation
  infer_instance

end FlatDimensionSituation

end AlgebraicGeometry.Space

end
