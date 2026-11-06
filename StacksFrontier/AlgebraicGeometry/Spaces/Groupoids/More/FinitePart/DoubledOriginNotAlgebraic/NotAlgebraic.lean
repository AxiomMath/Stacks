module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.DoubledOriginNotAlgebraic.PairsOnSchemes

/-!
# The finite part of the doubled origin is not étale and not an algebraic space

The fourth point `{0₁, 0₂}` of the finite part does not extend off the origin
(`exists_opens_forall_notMem_of_surjective`); hence the finite part, if it is an algebraic space,
is not étale over `Y` (`not_isEtale_baseMap_doubledOriginFinitePart`), and in fact it is not an
algebraic space (`not_isAlgebraicSpace_doubledOriginFinitePart`), using the infinitesimal
neighbourhoods `Spec k[t]/(t^(N+1))` of the origin.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) AlgebraicGeometry.Space.hasPullbacks_presheaf_notAlgebraic
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) AlgebraicGeometry.Space.hasPullback_presheaf_notAlgebraic
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (AlgebraicGeometry.Space.hasPullbacks_presheaf_notAlgebraic B S hS).has_limit _

namespace AlgebraicGeometry.Space

/-! ### The fourth point does not extend off the origin -/

section NotExtend

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  Space.preservesLimitsOfShape_walkingCospan_toScheme

variable {B : BigFppfSite.{u}} {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {n : ℕ}

/-- The `i`-th chart section of the pullback `U ×_Y X` of the site along `b : U ⟶ Y`. -/
noncomputable def siteChartSection {U : BigFppfOver B (Spec (.of k)) hk}
    (b : U ⟶ affineSpaceObj B k hk n) (i : Fin 2) : U ⟶ pullback b (doubledCoordHom B k hk n) :=
  pullback.lift (𝟙 U) (b ≫ chartHom B k hk n i) (by
    rw [Category.id_comp, Category.assoc, chartHom_doubledCoordHom, Category.comp_id])

/-- The first projection of `siteChartSection b i` is the identity. -/
@[reassoc (attr := simp)]
theorem siteChartSection_fst {U : BigFppfOver B (Spec (.of k)) hk}
    (b : U ⟶ affineSpaceObj B k hk n) (i : Fin 2) :
    siteChartSection b i ≫ pullback.fst _ _ = 𝟙 U :=
  pullback.lift_fst _ _ _

/-- The second projection of `siteChartSection b i` is `b` followed by the `i`-th chart. -/
@[reassoc (attr := simp)]
theorem siteChartSection_snd {U : BigFppfOver B (Spec (.of k)) hk}
    (b : U ⟶ affineSpaceObj B k hk n) (i : Fin 2) :
    siteChartSection b i ≫ pullback.snd _ _ = b ≫ chartHom B k hk n i :=
  pullback.lift_snd _ _ _

/-- The chart sections of the ambient fibre product of a pair are the Yoneda images of the chart
sections of the pullback of the site. -/
theorem chartSection_eq {U : BigFppfOver B (Spec (.of k)) hk}
    (z : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace U))
    (b : U ⟶ affineSpaceObj B k hk n) (hz : z.toBase = schemeSpaceMap b) (i : Fin 2) :
    chartSection z i = (schemeSpaceMap (siteChartSection b i)).hom ≫
      (ambientIso (doubledCoordHom B k hk n) b hz).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [chartSection_fst, Category.assoc, ambientIso_hom_fst, schemeSpaceMap_hom_comp,
      siteChartSection_fst, schemeSpaceMap_hom_id]
  · rw [chartSection_snd, Category.assoc, ambientIso_hom_snd, schemeSpaceMap_hom_comp,
      siteChartSection_snd, hz, schemeSpaceMap_hom_comp]

/-- The image under the functor to schemes of the pullback square of the site defining
`U ×_Y X` is a pullback square over the coordinate morphism. -/
theorem isPullback_toScheme_pullback_doubledCoordHom {U : BigFppfOver B (Spec (.of k)) hk}
    (b : U ⟶ affineSpaceObj B k hk n) :
    IsPullback ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (pullback.fst b
        (doubledCoordHom B k hk n)))
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (pullback.snd b (doubledCoordHom B k hk n)))
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map b) (coordinateMorphism k n) :=
  (IsPullback.of_hasPullback b (doubledCoordHom B k hk n)).map _

/-- The chart sections of the image of the pullback square of the site are the images of the
chart sections of the site. -/
theorem chartSectionOfIsPullback_toScheme {U : BigFppfOver B (Spec (.of k)) hk}
    (b : U ⟶ affineSpaceObj B k hk n) (i : Fin 2) :
    chartSectionOfIsPullback (isPullback_toScheme_pullback_doubledCoordHom b) i =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (siteChartSection b i) := by
  have h1 : 𝟙 _ = (BigFppfOver.toScheme B (Spec (.of k)) hk).map (siteChartSection b i) ≫
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (pullback.fst b (doubledCoordHom B k hk n)) := by
    rw [← CategoryTheory.Functor.map_comp, siteChartSection_fst, CategoryTheory.Functor.map_id]
  have h2 : (BigFppfOver.toScheme B (Spec (.of k)) hk).map b ≫
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (chartHom B k hk n i) =
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map (siteChartSection b i) ≫
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (pullback.snd b (doubledCoordHom B k hk n)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, siteChartSection_snd]
  exact (isPullback_toScheme_pullback_doubledCoordHom b).hom_ext
    ((chartSectionOfIsPullback_fst (isPullback_toScheme_pullback_doubledCoordHom b) i).trans h1)
    ((chartSectionOfIsPullback_snd (isPullback_toScheme_pullback_doubledCoordHom b) i).trans h2)

/-- **The fourth point does not extend off the origin, over an affine base.** Let `z` be a pair
of Stacks 04PC over an affine object `U` for the coordinate morphism, with morphism `b` to `Y`,
and let `x : E ⟶ U` and a point `e` of `E` be such that both chart sections of `z`, pulled back
along `x`, lie in the open subspace of `z`, and `b` maps `x e` off the complement of the origin.
Then a whole neighbourhood of `x e` is mapped off the complement of the origin. -/
theorem exists_opens_forall_notMem_of_isAffine {U E : BigFppfOver B (Spec (.of k)) hk}
    (hU : IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U))
    (b : U ⟶ affineSpaceObj B k hk n)
    (z : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace U))
    (hz : z.toBase = schemeSpaceMap b) (x : E ⟶ U)
    (hmem : ∀ i, ∃ l, l ≫ z.subspace.ι = (schemeSpaceMap x).hom ≫ chartSection z i)
    (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj E)
    (hu : (BigFppfOver.toScheme B (Spec (.of k)) hk).map b
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map x pt) ∉ puncturedAffineSpace k n) :
    ∃ O : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).Opens,
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map x pt ∈ O ∧
        ∀ y ∈ O, (BigFppfOver.toScheme B (Spec (.of k)) hk).map b y ∉ puncturedAffineSpace k n := by
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  obtain ⟨W, j, hj, hzj, hfin⟩ := z.exists_eq_range _ b hz
  have hfin := hfin hU
  have : Mono j := q.mono_of_mono_map inferInstance
  have hmem' : ∀ i, chartSectionOfIsPullback (isPullback_toScheme_pullback_doubledCoordHom b) i
      (q.map x pt) ∈ (q.map j).opensRange := by
    intro i
    have h := hmem i
    rw [chartSection_eq z b hz i, ← Category.assoc, schemeSpaceMap_hom_comp] at h
    obtain ⟨g, hg⟩ := FiniteOpenSubspace.exists_comp_eq_of_exists _ hz hzj _ h
    rw [chartSectionOfIsPullback_toScheme, ← Scheme.Hom.comp_apply,
      ← CategoryTheory.Functor.map_comp, ← hg, CategoryTheory.Functor.map_comp,
      Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hfinW : _root_.AlgebraicGeometry.IsFinite
      ((q.map j).opensRange.ι ≫ q.map (pullback.fst b (doubledCoordHom B k hk n))) := by
    rw [CategoryTheory.Functor.map_comp] at hfin
    have h' : _root_.AlgebraicGeometry.IsFinite
        ((q.map j).isoOpensRange.inv ≫ (q.map j ≫ q.map (pullback.fst b _))) := inferInstance
    simpa only [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using h'
  exact exists_opens_forall_notMem_puncturedAffineSpace
    (isPullback_toScheme_pullback_doubledCoordHom b) _ hfinW (q.map x pt) hu (hmem' 0) (hmem' 1)


/-- **The fourth point does not extend off the origin.** Let `z` be a pair of Stacks 04PC over an
object `U` for the coordinate morphism, with morphism `b` to `Y`, and let `x : E ⟶ U` and a point
`pt` of `E` be such that both chart sections of `z`, pulled back along `x`, lie in the open
subspace of `z`, and `b` maps `x pt` off the complement of the origin. Then a whole neighbourhood
of `x pt` is mapped off the complement of the origin. The case of an affine `U` is
`exists_opens_forall_notMem_of_isAffine`; the general case restricts to an affine open
neighbourhood of `x pt`. -/
theorem exists_opens_forall_notMem {U E : BigFppfOver B (Spec (.of k)) hk}
    (b : U ⟶ affineSpaceObj B k hk n)
    (z : FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace U))
    (hz : z.toBase = schemeSpaceMap b) (x : E ⟶ U)
    (hmem : ∀ i, ∃ l, l ≫ z.subspace.ι = (schemeSpaceMap x).hom ≫ chartSection z i)
    (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj E)
    (hu : (BigFppfOver.toScheme B (Spec (.of k)) hk).map b
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map x pt) ∉ puncturedAffineSpace k n) :
    ∃ O : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).Opens,
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map x pt ∈ O ∧
        ∀ y ∈ O, (BigFppfOver.toScheme B (Spec (.of k)) hk).map b y ∉ puncturedAffineSpace k n := by
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  obtain ⟨_, ⟨A₀, hA, rfl⟩, huA, -⟩ := (q.obj U).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (q.map x pt)) isOpen_univ
  let A : (q.obj U).Opens := A₀
  let U' := Stacks.SeparationLocal.openObj B (Spec (.of k)) hk U A.ι
  let ι : U' ⟶ U := Stacks.SeparationLocal.openObjHom B (Spec (.of k)) hk U A.ι
  let z' := restrictFinitePair B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n)) ι z
  have hzz' := restrictFinitePair_isBaseChange B (Spec (.of k)) hk
    (schemeSpaceMap (doubledCoordHom B k hk n)) ι z
  have hz' : z'.toBase = schemeSpaceMap (ι ≫ b) :=
    ObjectProperty.hom_ext _ (by rw [hzz'.toBase_hom_eq, hz, schemeSpaceMap_hom_comp])
  obtain ⟨a, ha⟩ : q.map x pt ∈ Set.range A.ι := by rwa [Scheme.Opens.range_ι]
  have hsq := (IsPullback.of_hasPullback x ι).map q
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := q.map x) (g := q.map ι)
    pt a ha.symm
  let pt' := hsq.isoPullback.inv w
  have hpt1 : q.map (pullback.fst x ι) pt' = pt := by
    rw [← hw1, ← hsq.isoPullback_inv_fst, Scheme.Hom.comp_apply]
  have hpt2 : q.map (pullback.snd x ι) pt' = a := by
    rw [← hw2, ← hsq.isoPullback_inv_snd, Scheme.Hom.comp_apply]
  have hmem' : ∀ i, ∃ l, l ≫ z'.subspace.ι =
      (schemeSpaceMap (pullback.snd x ι)).hom ≫ chartSection z' i := by
    intro i
    rw [hzz'.exists_comp_ι_eq_iff, Category.assoc, hzz'.chartSection_ambientMap,
      ← Category.assoc, schemeSpaceMap_hom_comp, ← pullback.condition, ← schemeSpaceMap_hom_comp,
      Category.assoc]
    obtain ⟨l, hl⟩ := hmem i
    exact ⟨(schemeSpaceMap (pullback.fst x ι)).hom ≫ l, by rw [Category.assoc, hl]⟩
  have hxa : q.map x pt = q.map ι (q.map (pullback.snd x ι) pt') := by
    rw [hpt2]
    exact ha.symm
  have hu' : q.map (ι ≫ b) (q.map (pullback.snd x ι) pt') ∉ puncturedAffineSpace k n := by
    rwa [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_apply, ← hxa]
  obtain ⟨O, hO, hOb⟩ := exists_opens_forall_notMem_of_isAffine (U := U') hA (ι ≫ b) z' hz'
    (pullback.snd x ι) hmem' pt' hu'
  refine ⟨A.ι ''ᵁ O, ?_, ?_⟩
  · rw [hxa]
    exact ⟨_, hO, rfl⟩
  · rintro y ⟨y', hy', rfl⟩
    have := hOb y' hy'
    rw [CategoryTheory.Functor.map_comp] at this
    exact this

/-- Both chart sections of a pair lie in its open subspace after any base change along which the
pair becomes the pair of another pair with open subspace everything. -/
theorem exists_comp_ι_eq_chartSection_of_map_eq {U E T : BigFppfOver B (Spec (.of k)) hk}
    (τ : (doubledOriginFinitePart B k hk n).toFunctor.obj (op U))
    (σ : (doubledOriginFinitePart B k hk n).toFunctor.obj (op T))
    (hσ : ((doubledOriginFinitePart B k hk n).sections T σ).subspace = ⊤)
    (x : E ⟶ U) (g : E ⟶ T)
    (hxg : (doubledOriginFinitePart B k hk n).toFunctor.map x.op τ =
      (doubledOriginFinitePart B k hk n).toFunctor.map g.op σ) (i : Fin 2) :
    ∃ l, l ≫ ((doubledOriginFinitePart B k hk n).sections U τ).subspace.ι =
      (schemeSpaceMap x).hom ≫
        chartSection ((doubledOriginFinitePart B k hk n).sections U τ) i := by
  have h1 := (doubledOriginFinitePart B k hk n).map_isBaseChange x τ
  have h2 := (doubledOriginFinitePart B k hk n).map_isBaseChange g σ
  rw [← hxg] at h2
  have htop := h2.subspace_eq_top hσ
  rw [← h1.chartSection_ambientMap]
  exact (h1.exists_comp_ι_eq_iff _).mp
    ⟨Subfunctor.lift _ (by rw [htop]; exact le_top), Subfunctor.lift_ι _ _⟩


end NotExtend


/-! ### The finite part is not étale over `Y` -/

section NotEtale

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  Space.preservesLimitsOfShape_walkingCospan_toScheme

variable {B : BigFppfSite.{u}} {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {n : ℕ}

/-- The projection of the finite part to `Y`, precomposed with a section over a scheme, is the
morphism to `Y` of the corresponding pair of Stacks 04PC. -/
theorem _root_.AlgebraicGeometry.Space.FinitePartPresheaf.comp_baseMap {S : Scheme.{u}}
    {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    (P : FinitePartPresheaf B S hS f) {U : BigFppfOver B S hS}
    (φ : yoneda.obj U ⟶ P.toFunctor) :
    φ ≫ P.baseMap = (P.sections U (yonedaEquiv φ)).toBase.hom :=
  yonedaEquiv.injective ((yonedaEquiv_comp _ _).trans
    ((Equiv.apply_symm_apply yonedaEquiv _).symm.trans
      (congrArg yonedaEquiv (P.baseMap_spec U (yonedaEquiv φ)))))

/-- Morphisms into a representable are compared through a presheaf over it: if
`φ ≫ β = yoneda.map b`, `σ ≫ β = yoneda.map a` and `yoneda.map x ≫ φ = yoneda.map g ≫ σ`, then
`x ≫ b = g ≫ a`. -/
theorem comp_eq_comp_of_yoneda_map {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type _}
    {U T E Y : C} {φ : yoneda.obj U ⟶ F} {σ : yoneda.obj T ⟶ F} {β : F ⟶ yoneda.obj Y}
    {b : U ⟶ Y} {a : T ⟶ Y} {x : E ⟶ U} {g : E ⟶ T} (hb : φ ≫ β = yoneda.map b)
    (ha : σ ≫ β = yoneda.map a) (hw : yoneda.map x ≫ φ = yoneda.map g ≫ σ) : x ≫ b = g ≫ a :=
  yoneda.map_injective <| (yoneda.map_comp _ _).trans <|
    (congrArg (yoneda.map x ≫ ·) hb.symm).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ β) hw).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (yoneda.map g ≫ ·) ha).trans (yoneda.map_comp _ _).symm

/-- The pair of Stacks 04PC over `T` with morphism `a` to `Y` and with open subspace the whole of
`T ×_Y X`, for an `a` mapping every point to the origin. Over the origin `a : Spec k ⟶ Y` it is
the fourth point `{0₁, 0₂}` of the finite part over the origin. -/
noncomputable def wholePair {T : BigFppfOver B (Spec (.of k)) hk} (a : T ⟶ affineSpaceObj B k hk n)
    (ha : ∀ y, (BigFppfOver.toScheme B (Spec (.of k)) hk).map a y ∉ puncturedAffineSpace k n) :
    FiniteOpenSubspace B (Spec (.of k)) hk (schemeSpaceMap (doubledCoordHom B k hk n))
      (schemeSpace T) :=
  wholeFiniteOpenSubspace (doubledCoordHom B k hk n) a
    (isFinite_of_isPullback_of_forall_notMem (isPullback_toScheme_pullback_doubledCoordHom a) ha)

/-- The section of the finite part given by `wholePair a ha` has projection `a` to `Y`. -/
private theorem wholePair_comp_baseMap {T : BigFppfOver B (Spec (.of k)) hk}
    (a : T ⟶ affineSpaceObj B k hk n)
    (ha : ∀ y, (BigFppfOver.toScheme B (Spec (.of k)) hk).map a y ∉ puncturedAffineSpace k n) :
    yonedaEquiv.symm (((doubledOriginFinitePart B k hk n).sections T).symm (wholePair a ha)) ≫
      (doubledOriginFinitePart B k hk n).baseMap = yoneda.map a := by
  rw [FinitePartPresheaf.comp_baseMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- **The fourth point does not lift through a chart off the origin.** Let `φ : U ⟶ (X/Y)_fin` be
a morphism from a scheme, with composite `b : U ⟶ Y` with the projection, and let
`x : E ⟶ U`, `g : E ⟶ T` exhibit `φ ∘ x` as the pullback along `g` of the pair over `T` with
whole open subspace, for some `a : T ⟶ Y` mapping everything to the origin. Then every point
`x pt` of `U` has an open neighbourhood mapped by `b` entirely to the origin. -/
theorem exists_opens_forall_notMem_of_comp_eq {U T E : BigFppfOver B (Spec (.of k)) hk}
    (φ : yoneda.obj U ⟶ (doubledOriginFinitePart B k hk n).toFunctor)
    (a : T ⟶ affineSpaceObj B k hk n)
    (ha : ∀ y, (BigFppfOver.toScheme B (Spec (.of k)) hk).map a y ∉ puncturedAffineSpace k n)
    (x : E ⟶ U) (g : E ⟶ T)
    (hw : yoneda.map x ≫ φ = yoneda.map g ≫
      yonedaEquiv.symm (((doubledOriginFinitePart B k hk n).sections T).symm (wholePair a ha)))
    (pt : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj E) :
    ∃ O : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).Opens,
      (BigFppfOver.toScheme B (Spec (.of k)) hk).map x pt ∈ O ∧
      ∀ y ∈ O, (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (yoneda.preimage (φ ≫ (doubledOriginFinitePart B k hk n).baseMap)) y ∉
          puncturedAffineSpace k n := by
  let F := doubledOriginFinitePart B k hk n
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  let σ := (F.sections T).symm (wholePair a ha)
  have hσ : F.sections T σ = wholePair a ha := Equiv.apply_symm_apply _ _
  let σm : yoneda.obj T ⟶ F.toFunctor := yonedaEquiv.symm σ
  let τ := yonedaEquiv φ
  let z := F.sections U τ
  set b : U ⟶ affineSpaceObj B k hk n := yoneda.preimage (φ ≫ F.baseMap)
  have hφb : φ ≫ F.baseMap = yoneda.map b := (yoneda.map_preimage _).symm
  have hz : z.toBase = schemeSpaceMap b :=
    ObjectProperty.hom_ext _ ((F.comp_baseMap φ).symm.trans hφb)
  have hxg : F.toFunctor.map x.op τ = F.toFunctor.map g.op σ := by
    have h1 := yonedaEquiv_naturality φ x
    have h2 := yonedaEquiv_naturality σm g
    rw [Equiv.apply_symm_apply] at h2
    rw [h1, h2, hw]
  have hmem := exists_comp_ι_eq_chartSection_of_map_eq τ σ (by rw [hσ]; rfl) x g hxg
  have hxb : x ≫ b = g ≫ a := comp_eq_comp_of_yoneda_map hφb (wholePair_comp_baseMap a ha) hw
  have hu : q.map b (q.map x pt) ∉ puncturedAffineSpace k n := by
    rw [← Scheme.Hom.comp_apply, ← CategoryTheory.Functor.map_comp, hxb,
      CategoryTheory.Functor.map_comp, Scheme.Hom.comp_apply]
    exact ha _
  exact exists_opens_forall_notMem b z hz x hmem pt hu

/-- **The fourth point lifts to every surjective chart.** For a surjective representable morphism
`φ : U ⟶ (X/Y)_fin` from a scheme, the fourth point `{0₁, 0₂}` of the finite part over the
origin lifts to a point `x pt` of `U`, and comes with a pullback square exhibiting the lift. -/
theorem exists_lift_wholePair {U T : BigFppfOver B (Spec (.of k)) hk}
    (φ : yoneda.obj U ⟶ (doubledOriginFinitePart B k hk n).toFunctor)
    (hφ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf φ)
    (σm : yoneda.obj T ⟶ (doubledOriginFinitePart B k hk n).toFunctor)
    [Nonempty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T)] :
    ∃ (E : BigFppfOver B (Spec (.of k)) hk) (x : E ⟶ U) (g : E ⟶ T),
      yoneda.map x ≫ φ = yoneda.map g ≫ σm ∧
      Nonempty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj E) := by
  have hgs : Surjective ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (hφ.rep.snd σm)) :=
    hφ.property_snd σm
  obtain ⟨pt, -⟩ := ((BigFppfOver.toScheme B (Spec (.of k)) hk).map (hφ.rep.snd σm)).surjective
    (Nonempty.some inferInstance)
  exact ⟨_, hφ.rep.fst' σm, hφ.rep.snd σm, (hφ.rep.isPullback' σm).w, ⟨pt⟩⟩

/-- `Spec k` has a point. -/
instance : Nonempty ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (pointObj B k hk)) :=
  ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)⟩

/-- **The fourth point does not lift through an étale chart.** Let `φ : U ⟶ (X/Y)_fin` be a
morphism from a scheme which is surjective and representable, and let `b : U ⟶ Y` be its
composite with the projection to `Y`. Then some point of `U` above the origin has an open
neighbourhood mapped by `b` entirely to the origin: the fourth point `{0₁, 0₂}` lifts to `U`,
and over that lift both chart sections lie in the open subspace of the pair carried by `φ`. -/
theorem exists_opens_forall_notMem_of_surjective {U : BigFppfOver B (Spec (.of k)) hk}
    (φ : yoneda.obj U ⟶ (doubledOriginFinitePart B k hk n).toFunctor)
    (hφ : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of k)) hk)).presheaf φ) :
    ∃ (u : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj U)
      (O : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).Opens), u ∈ O ∧
      ∀ y ∈ O, (BigFppfOver.toScheme B (Spec (.of k)) hk).map
        (yoneda.preimage (φ ≫ (doubledOriginFinitePart B k hk n).baseMap)) y ∉
          puncturedAffineSpace k n := by
  obtain ⟨E, x, g, hw, ⟨pt⟩⟩ := exists_lift_wholePair φ hφ (yonedaEquiv.symm
    (((doubledOriginFinitePart B k hk n).sections (pointObj B k hk)).symm
      (wholePair (originHom B k hk n) (originHom_notMem_puncturedAffineSpace B k hk n))))
  obtain ⟨O, huO, hO⟩ := exists_opens_forall_notMem_of_comp_eq φ _ _ x g hw pt
  exact ⟨_, O, huO, hO⟩

/-- **Non-étaleness, part (4) of Stacks 04QI.** If the finite part `(X/Y)_fin` of the coordinate
morphism of affine space with doubled origin, in positive dimension, is an algebraic space, then
its projection to `Y` is not étale. Were it étale, the composite `b : U ⟶ Y` of an étale atlas with
the projection would be étale, hence open, so no point of `U` would have an open neighbourhood
mapped entirely to the origin, contradicting
`AlgebraicGeometry.Space.exists_opens_forall_notMem_of_surjective`: the fourth point
`{0₁, 0₂}` of the finite part over the origin does not lift to an open subscheme of `U ×_Y X`
finite over `U` for an étale `U ⟶ Y`. -/
theorem not_isEtale_baseMap_doubledOriginFinitePart (hn : 0 < n)
    (hF : IsAlgebraicSpace B (Spec (.of k)) hk (doubledOriginFinitePart B k hk n).toFunctor) :
    ¬ IsEtale B (Spec (.of k)) hk (doubledOriginFinitePart B k hk n).baseMap := by
  intro hE
  obtain ⟨U, φ, hsurj, het⟩ := hF.exists_atlas
  obtain ⟨u, O, huO, hO⟩ := exists_opens_forall_notMem_of_surjective φ hsurj
  have hb : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (yoneda.preimage (φ ≫ (doubledOriginFinitePart B k hk n).baseMap))) := by
    rw [← presheaf_yoneda_map_etale_iff, yoneda.map_preimage]
    exact hE U φ het
  have hbo : _root_.AlgebraicGeometry.UniversallyOpen
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (yoneda.preimage (φ ≫ (doubledOriginFinitePart B k hk n).baseMap))) := inferInstance
  obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp (@mem_closure_preimage_puncturedAffineSpace k _ n hn _
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (yoneda.preimage (φ ≫ (doubledOriginFinitePart B k hk n).baseMap))) hbo u) O O.2 huO
  exact hO y hyO hy

end NotEtale


/-! ### The finite part is not an algebraic space -/

section NotAlgebraic

attribute [local instance] BigFppfSite.hasPullbacks_schemes
  Space.preservesLimitsOfShape_walkingCospan_toScheme

variable {B : BigFppfSite.{u}} {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {n : ℕ}

/-- No nonempty affine open subscheme of a scheme étale over `Spec k[t]/(t^(m+1))` kills `t ^ m`:
the ring of sections would be a flat `k[t]/(t^(m+1))`-algebra killing `t ^ m`, hence zero. -/
theorem false_of_etale_of_pow_eq_zero {m : ℕ} {E : Scheme.{u}}
    (g : E ⟶ Spec (.of (thickeningRing k m))) [_root_.AlgebraicGeometry.Etale g]
    (V : E.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (h : E.presheaf.map (homOfLE le_top : V ⟶ ⊤).op
      (g.appTop ((Scheme.ΓSpecIso _).inv (thickeningParameter k m))) ^ m = 0) :
    False := by
  have hflat : (g.appLE ⊤ V le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat g inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have hφ : ((g.appLE ⊤ V le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (thickeningRing k m))).inv.hom).Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective
      (Scheme.ΓSpecIso
        (CommRingCat.of (thickeningRing k m))).symm.commRingCatIsoToRingEquiv.bijective)
      hflat
  have := hφ.subsingleton_of_map_pow_eq_zero (isNilpotent_thickeningParameter m)
    (exists_eq_thickeningParameter_mul m) h
  exact false_of_nontrivial_of_subsingleton Γ(E, V)

/-- The restriction to an open `V` of the pullback of a global section along `f` is the pullback
along `f` of its restriction to any open containing the image of `V`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.map_appTop_eq_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (s : Γ(Y, ⊤)) :
    X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (f.appTop s) =
      f.appLE U V e (Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

/-- No nonempty affine open of a scheme étale over `Spec k[t]/(t^(m+1))` maps, compatibly with
the morphism to `𝔸ⁿ` sending every coordinate to `t`, into an open on which the pullback of the
first coordinate has vanishing `m`-th power. -/
theorem false_of_etale_of_comp_eq (hn : 0 < n) {m : ℕ} {X E : Scheme.{u}} (x : E ⟶ X)
    (b : X ⟶ Spec (.of (MvPolynomial (Fin n) k)))
    (g : E ⟶ Spec (.of (thickeningRing k m))) [_root_.AlgebraicGeometry.Etale g]
    (hxb : x ≫ b =
      g ≫ Spec.map (CommRingCat.ofHom (thickeningCoordinates (k := k) n m).toRingHom))
    (U₁ : X.Opens) (E₁ : E.Opens) (hE₁ : IsAffineOpen E₁) [Nonempty E₁] (hE₁U : E₁ ≤ x ⁻¹ᵁ U₁)
    (hN : X.presheaf.map (homOfLE le_top : U₁ ⟶ ⊤).op (b.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) k))).inv
        (MvPolynomial.X ⟨0, hn⟩))) ^ m = 0) :
    False := by
  refine false_of_etale_of_pow_eq_zero g E₁ hE₁ ?_
  have ht : (Scheme.ΓSpecIso (CommRingCat.of (thickeningRing k m))).inv (thickeningParameter k m) =
      (Spec.map (CommRingCat.ofHom (thickeningCoordinates (k := k) n m).toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) k))).inv
          (MvPolynomial.X ⟨0, hn⟩)) := by
    rw [show thickeningParameter k m =
      (thickeningCoordinates (k := k) n m) (MvPolynomial.X ⟨0, hn⟩) by simp]
    exact congrArg (fun f => f (MvPolynomial.X ⟨0, hn⟩))
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (thickeningCoordinates (k := k) n m).toRingHom))
  have hcomp : g.appTop ((Spec.map (CommRingCat.ofHom
      (thickeningCoordinates (k := k) n m).toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) k))).inv
          (MvPolynomial.X ⟨0, hn⟩))) = x.appTop (b.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) k))).inv
          (MvPolynomial.X ⟨0, hn⟩))) :=
    (congrArg (fun f => Scheme.Hom.appTop f
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) k))).inv
        (MvPolynomial.X ⟨0, hn⟩))) hxb).symm
  rw [ht, hcomp, Scheme.Hom.map_appTop_eq_appLE x U₁ E₁ hE₁U, ← map_pow, hN, map_zero]

/-- The pair over `Spec k[t]/(t^(N+1))` with whole open subspace, at the morphism sending every
coordinate to `t`, restricts at the rational point to the pair with whole open subspace at the
origin. -/
theorem yoneda_map_thickeningInclusion_comp_wholePair (N : ℕ) :
    yoneda.map (thickeningInclusion B k hk N) ≫
      yonedaEquiv.symm (((doubledOriginFinitePart B k hk n).sections _).symm
        (wholePair (thickeningHom B k hk n N)
          (thickeningHom_notMem_puncturedAffineSpace B k hk n N))) =
      yonedaEquiv.symm (((doubledOriginFinitePart B k hk n).sections _).symm
        (wholePair (originHom B k hk n) (originHom_notMem_puncturedAffineSpace B k hk n))) := by
  let F := doubledOriginFinitePart B k hk n
  refine yonedaEquiv.injective ?_
  rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine (F.sections _).injective ?_
  rw [Equiv.apply_symm_apply]
  have hbc := F.map_isBaseChange (thickeningInclusion B k hk N)
    ((F.sections _).symm (wholePair (thickeningHom B k hk n N)
      (thickeningHom_notMem_puncturedAffineSpace B k hk n N)))
  rw [Equiv.apply_symm_apply] at hbc
  refine FiniteOpenSubspace.ext_of_subspace_eq_top ?_ (hbc.subspace_eq_top rfl) rfl
  refine ObjectProperty.hom_ext _ ?_
  rw [hbc.toBase_hom_eq]
  exact (schemeSpaceMap_hom_comp _ _).trans (congrArg (fun f => (schemeSpaceMap f).hom)
    (thickeningInclusion_thickeningHom B k hk n N))

/-- **Not an algebraic space, part (5) of Stacks 04QI.** In positive dimension the finite part
`(X/Y)_fin` of the coordinate morphism of affine space with doubled origin is not an algebraic
space. This is the final assertion of the remark, whose details the source omits.

Suppose it were, with surjective étale atlas `φ : U ⟶ (X/Y)_fin`, and let `b : U ⟶ Y` be the
composite with the projection. The fourth point `{0₁, 0₂}` over the origin lifts to a point `v`
of `U`, and by `AlgebraicGeometry.Space.exists_opens_forall_notMem_of_comp_eq` an affine open
neighbourhood `U₁` of `v` is mapped by `b` to the origin, so a coordinate pulls back to a
nilpotent section of `U₁`, say with `N`-th power zero. On the other hand the pair over
`T = Spec k[t]/(t^(N+1))` with whole open subspace, at the morphism `T ⟶ Y` sending every
coordinate to `t`, restricts to the fourth point at the closed point; so its pullback `E` along
`φ` is étale over `T` and contains a point over `v`, and the image of `t` in the sections of an
affine open neighbourhood of that point inside the preimage of `U₁` has vanishing `N`-th power.
This is impossible for a nonempty scheme étale over `T`, by
`AlgebraicGeometry.Space.false_of_etale_of_pow_eq_zero`. -/
theorem not_isAlgebraicSpace_doubledOriginFinitePart (hn : 0 < n) :
    ¬ IsAlgebraicSpace B (Spec (.of k)) hk (doubledOriginFinitePart B k hk n).toFunctor := by
  intro hF
  let F := doubledOriginFinitePart B k hk n
  let q := BigFppfOver.toScheme B (Spec (.of k)) hk
  obtain ⟨U, φ, hsurj, het⟩ := hF.exists_atlas
  set b : U ⟶ affineSpaceObj B k hk n := yoneda.preimage (φ ≫ F.baseMap)
  have hφb : φ ≫ F.baseMap = yoneda.map b := (yoneda.map_preimage _).symm
  let σ₀ : yoneda.obj (pointObj B k hk) ⟶ F.toFunctor := yonedaEquiv.symm ((F.sections _).symm
    (wholePair (originHom B k hk n) (originHom_notMem_puncturedAffineSpace B k hk n)))
  obtain ⟨E₀, x₀, g₀, hw₀, ⟨pt⟩⟩ := exists_lift_wholePair φ hsurj σ₀
  obtain ⟨O, hO, hOb⟩ := exists_opens_forall_notMem_of_comp_eq φ _ _ x₀ g₀ hw₀ pt
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hvU₁, hU₁O⟩ :=
    (q.obj U).isBasis_affineOpens.exists_subset_of_mem_open hO O.2
  let bS : q.obj U ⟶ Spec (.of (MvPolynomial (Fin n) k)) := q.map b
  let r : Γ(Spec (.of (MvPolynomial (Fin n) k)), ⊤) :=
    (Scheme.ΓSpecIso _).inv (MvPolynomial.X ⟨0, hn⟩)
  obtain ⟨N, hN⟩ : IsNilpotent ((q.obj U).presheaf.map (homOfLE le_top : U₁ ⟶ ⊤).op
      (bS.appTop r)) := by
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact (IsAffineOpen.isCompact hU₁),
      Scheme.basicOpen_res, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    exact eq_bot_iff.mpr fun y hy => hOb y (hU₁O hy.1) (Opens.mem_iSup.mpr ⟨⟨0, hn⟩, hy.2⟩)
  let σN : yoneda.obj (thickeningObj B k hk N) ⟶ F.toFunctor := yonedaEquiv.symm
    ((F.sections _).symm (wholePair (thickeningHom B k hk n N)
      (thickeningHom_notMem_puncturedAffineSpace B k hk n N)))
  have hres : yoneda.map (thickeningInclusion B k hk N) ≫ σN = σ₀ :=
    yoneda_map_thickeningInclusion_comp_wholePair N
  let xN : hsurj.rep.pullback σN ⟶ U := hsurj.rep.fst' σN
  let gN : hsurj.rep.pullback σN ⟶ thickeningObj B k hk N := hsurj.rep.snd σN
  have hwN : yoneda.map xN ≫ φ = yoneda.map gN ≫ σN := (hsurj.rep.isPullback' σN).w
  let gS : q.obj (hsurj.rep.pullback σN) ⟶ Spec (.of (thickeningRing k N)) := q.map gN
  have hgN : _root_.AlgebraicGeometry.Etale gS := het.property_snd σN
  let ρ : E₀ ⟶ hsurj.rep.pullback σN :=
    hsurj.rep.lift' x₀ (g₀ ≫ thickeningInclusion B k hk N) (by
      rw [hw₀, CategoryTheory.Functor.map_comp, Category.assoc, hres])
  have hρ : ρ ≫ xN = x₀ := hsurj.rep.lift'_fst _ _ _
  have he : q.map ρ pt ∈ q.map xN ⁻¹ᵁ U₁ := by
    rwa [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← CategoryTheory.Functor.map_comp, hρ]
  obtain ⟨_, ⟨E₁, hE₁, rfl⟩, heE₁, hE₁U⟩ :=
    (q.obj (hsurj.rep.pullback σN)).isBasis_affineOpens.exists_subset_of_mem_open he
      (q.map xN ⁻¹ᵁ U₁).2
  have : Nonempty E₁ := ⟨⟨_, heE₁⟩⟩
  exact false_of_etale_of_comp_eq hn (q.map xN) bS gS ((q.map_comp _ _).symm.trans
    ((congrArg q.map (comp_eq_comp_of_yoneda_map hφb (wholePair_comp_baseMap _ _) hwN)).trans
      (q.map_comp _ _)))
    U₁ E₁ hE₁ hE₁U hN

end NotAlgebraic

end AlgebraicGeometry.Space

end
