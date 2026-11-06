module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionSquaringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.MinimalDegreeFibreBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceUniqueness
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsResidualSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SeparatedFromElementarySquare
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalHomeomorphismEtaleFailure
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# A counterexample to Stacks 0F45 as published

Stacks 0F45 asserts: let `g : X ⟶ Y` be a morphism of algebraic spaces over `S` and let
`(U ⊆ X, f : V ⟶ X)` be an elementary distinguished square such that `U ⟶ Y` and `V ⟶ Y` are
separated and `U ×_X V ⟶ U ×_Y V` is closed; then `g` is separated. This is false. The proof in
the source covers `X ×_Y X` by the four products of `U` and `V` over `Y` and asserts that the
diagonal of `g` pulls back to `V` over `V ×_Y V`; it pulls back to `V ×_X V`, which is `V` only
when `f` is a monomorphism, and nothing in the hypotheses controls `V ×_X V ⟶ V ×_Y V`.

Here is a counterexample. Let `k` be a field in which `2` is invertible and let `X` be the
quotient of the affine line `𝐀¹_k` by the étale equivalence relation identifying `x` with `-x`
for `x ≠ 0` (Stacks 02Z1), with its chart `f : 𝐀¹_k ⟶ X`. Squaring the coordinate descends to
`g : X ⟶ 𝐀¹_k`, which is not separated (Stacks 05VS). Let `U ⊆ X` be the open subspace over the
punctured line `𝐀¹_k ∖ {0}`.

* `(U ⊆ X, f)` is an elementary distinguished square: the complement of `U` is the single point
  over the origin, it is the image of the origin of `𝐀¹_k`, and the chart is étale and carries
  the origin isomorphically onto it, since no other point of `𝐀¹_k` lies over it.
* `U ⟶ 𝐀¹_k` is a monomorphism, because `g` is an isomorphism over the punctured line, hence it
  is separated; and `V = 𝐀¹_k ⟶ 𝐀¹_k` is separated because `𝐀¹_k` is a separated scheme.
* `U ×_X V ⟶ U ×_Y V` is an isomorphism, hence closed: `U` is the full preimage of the punctured
  line and `U ⟶ Y` is a monomorphism, so two points of `U` and of `V` with the same image in
  `Y` have the same image in `X`.

The fourth piece, `V ×_X V ⟶ V ×_Y V`, is the relation `𝐀¹_k ⨿ (𝐀¹_k ∖ {0}) ⟶ 𝐀¹_k ×_{𝐀¹_k} 𝐀¹_k`,
which is not a closed immersion; this is exactly why `g` fails to be separated.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.exists_isElementaryDistinguishedSquare_not_isSeparated`:
  over every field in which `2` is invertible and in every big fppf site containing its
  spectrum, the data above satisfy all the hypotheses of Stacks 0F45 and `g` is not separated.
* `AlgebraicGeometry.Space.not_forall_isSeparated_of_isElementaryDistinguishedSquare`: the
  statement of Stacks 0F45, quantified over all big fppf sites, base schemes and data, is false.
* `CategoryTheory.Limits.isIso_pullback_mapDesc_of_isPullback`: for `U ⟶ X` the preimage of a
  subobject `W ⟶ Y` along `X ⟶ Y` with `U ⟶ W` a monomorphism, the comparison
  `U ×_X V ⟶ U ×_Y V` is an isomorphism.

## Implementation notes

The statement with the additional hypothesis that `V ×_X V ⟶ V ×_Y V` is closed holds, and is
`AlgebraicGeometry.Space.isSeparated_of_elementaryDistinguishedSquare`.

The open subspace `U` is the preimage under `g` of the subfunctor of the restricted functor of
points of `𝐀¹_k` cut out by the punctured line, so that `U ⟶ Y` is a monomorphism by
`AlgebraicGeometry.AffineLineInvolution.isIso_squaringMap_pullback_puncturedAffineLine`. The
reduced closed subspace on the complement of `U` is identified with the image of the origin of
`𝐀¹_k` by the uniqueness of residual spaces (Stacks 06QZ), both being residual spaces of `X`
at its origin.

## References

* [Stacks Project, Tag 0F45](https://stacks.math.columbia.edu/tag/0F45)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 05VS](https://stacks.math.columbia.edu/tag/05VS)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- Pullbacks of presheaves on the big fppf site, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high)
    AlgebraicGeometry.hasPullbacks_presheaf_SeparatedFromElementarySquareCounterexample
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high)
    AlgebraicGeometry.hasPullback_presheaf_SeparatedFromElementarySquareCounterexample
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : AlgebraicGeometry.Scheme.{u})
    (hS : B.Contains S) {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (AlgebraicGeometry.hasPullbacks_presheaf_SeparatedFromElementarySquareCounterexample
    B S hS).has_limit _

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

/-- Let `i : U ⟶ X` be the base change of `j : W ⟶ Y` along `g : X ⟶ Y`, and suppose the base
change `e : U ⟶ W` of `g` is a monomorphism. Then for every `f : V ⟶ X` the comparison map
`U ×_X V ⟶ U ×_Y V` is an isomorphism: a pair of points of `U` and `V` with the same image in
`Y` already has the same image in `X`. -/
theorem isIso_pullback_mapDesc_of_isPullback {U X Y W V : C} {e : U ⟶ W} {i : U ⟶ X}
    {j : W ⟶ Y} {g : X ⟶ Y} (h : IsPullback e i j g) [Mono e] (f : V ⟶ X)
    [HasPullback i f] [HasPullback (i ≫ g) (f ≫ g)] :
    IsIso (pullback.mapDesc i f g) := by
  have hc : (pullback.fst (i ≫ g) (f ≫ g) ≫ e) ≫ j =
      (pullback.snd (i ≫ g) (f ≫ g) ≫ f) ≫ g := by
    simpa only [Category.assoc, h.w] using pullback.condition
  have hab : pullback.fst (i ≫ g) (f ≫ g) ≫ i = pullback.snd (i ≫ g) (f ≫ g) ≫ f := by
    rw [← (cancel_mono e).1 (h.lift_fst _ _ hc), h.lift_snd]
  refine ⟨pullback.lift _ _ hab, ?_, ?_⟩ <;> apply pullback.hom_ext <;>
    simp only [pullback.mapDesc, pullback.map, Category.assoc, pullback.lift_fst,
      pullback.lift_snd, Category.comp_id, Category.id_comp]

end CategoryTheory.Limits

namespace CategoryTheory.Subfunctor

/-- A morphism between subfunctors compatible with the two inclusions gives an inequality. -/
private theorem le_of_comp_ι_eq {C : Type*} [Category C] {F : C ⥤ Type*} {G H : Subfunctor F}
    (φ : G.toFunctor ⟶ H.toFunctor) (h : φ ≫ H.ι = G.ι) : G ≤ H := fun T x hx => by
  have h' : ((φ.app T ⟨x, hx⟩ : H.toFunctor.obj T) : F.obj T) = x :=
    congrArg (fun a => a ⟨x, hx⟩) (congr_app h T)
  rw [← h']
  exact (φ.app T ⟨x, hx⟩).2

/-- Two subfunctors of the same functor are equal as soon as an isomorphism between them is
compatible with the two inclusions. -/
theorem eq_of_iso {C : Type*} [Category C] {F : C ⥤ Type*} {G H : Subfunctor F}
    (e : G.toFunctor ≅ H.toFunctor) (he : e.hom ≫ H.ι = G.ι) : G = H :=
  le_antisymm (le_of_comp_ι_eq e.hom he)
    (le_of_comp_ι_eq e.inv (by rw [← he, Iso.inv_hom_id_assoc]))

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- The inclusion of the punctured affine line into the restricted functor of points of the
affine line. -/
noncomputable abbrev puncturedPointsInclusion :
    Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (puncturedAffineLine k) ⟶
      Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k) :=
  (Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
    (yoneda.map (puncturedAffineLineInclusion k))

/-- The inclusion of the punctured affine line is a monomorphism of schemes over `k`. -/
instance : Mono (puncturedAffineLineInclusion k) := by
  have : Mono (puncturedAffineLineInclusion k).left := by
    rw [puncturedAffineLineInclusion_left]
    infer_instance
  exact Over.mono_of_mono_left _

/-- The inclusion of the punctured line into the points of the affine line is a monomorphism. -/
theorem mono_puncturedPointsInclusion : Mono (puncturedPointsInclusion k B hk) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  exact (mono_iff_injective _).2 fun x y hxy => (cancel_mono (puncturedAffineLineInclusion k)).1 hxy

/-- The punctured line is isomorphic to its image in the points of the affine line. -/
theorem isIso_toRange_puncturedPointsInclusion :
    IsIso (Subfunctor.toRange (puncturedPointsInclusion k B hk)) := by
  have := mono_puncturedPointsInclusion k B hk
  infer_instance

/-- The punctured affine line, as a subfunctor of the restricted functor of points of the
affine line. -/
noncomputable abbrev puncturedSubfunctor :
    Subfunctor (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion)
      (affineLine k)) :=
  Subfunctor.range (puncturedPointsInclusion k B hk)

/-- The inclusion of the punctured line into the restricted functor of points of the affine line
is, up to the identifications of both with represented presheaves, the represented open
immersion of the punctured line. -/
theorem puncturedPointsInclusion_eq :
    puncturedPointsInclusion k B hk =
      (puncturedPointsIso k B hk).hom ≫
        yoneda.map (puncturedChartInclusion k B hk) ≫
        (affineLinePointsIso k B hk).inv :=
  (Iso.inv_comp_eq _).1 (Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post B.inclusion)
    (V := puncturedAffineLineChart k B hk) (W := affineLineChart k B hk)
    (puncturedAffineLineInclusion k))

/-- The punctured affine line is an open subspace of the affine line. -/
theorem isOpenSubspace_puncturedSubfunctor :
    Space.IsOpenSubspace B (Spec (.of k)) hk (puncturedSubfunctor k B hk) := by
  have hr := isIso_toRange_puncturedPointsInclusion k B hk
  refine ⟨(isAlgebraicSpace_yoneda B (Spec (.of k)) hk (puncturedAffineLineChart k B hk)).of_iso
    ((puncturedPointsIso k B hk).symm ≪≫
      @asIso _ _ _ _ (Subfunctor.toRange (puncturedPointsInclusion k B hk)) hr), ?_⟩
  have hfac : (puncturedSubfunctor k B hk).ι =
      inv (Subfunctor.toRange (puncturedPointsInclusion k B hk)) ≫
        puncturedPointsInclusion k B hk := by
    rw [IsIso.eq_inv_comp, Subfunctor.toRange_ι]
  have hopen : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of k)) hk).map
      (puncturedChartInclusion k B hk)) := by
    have h := congrArg Over.Hom.left ((Over.post (X := B.obj hk) B.inclusion).map_preimage
      (X := puncturedAffineLineChart k B hk) (Y := affineLineChart k B hk)
      (puncturedAffineLineInclusion k))
    show AlgebraicGeometry.IsOpenImmersion ((Over.post (X := B.obj hk) B.inclusion).map
      ((Over.post (X := B.obj hk) B.inclusion).preimage (X := puncturedAffineLineChart k B hk)
        (Y := affineLineChart k B hk) (puncturedAffineLineInclusion k))).left
    rw [h, puncturedAffineLineInclusion_left]
    exact Scheme.Opens.instIsOpenImmersionι _
  rw [hfac]
  refine Space.isOpenImmersion_comp B (Spec (.of k)) hk _ _ ?_ ?_
  · exact Space.isOpenImmersion_of_isIso B (Spec (.of k)) hk _
  rw [puncturedPointsInclusion_eq]
  refine Space.isOpenImmersion_comp B (Spec (.of k)) hk _ _ ?_ ?_
  · exact @Space.isOpenImmersion_of_isIso B (Spec (.of k)) hk _ _ _
      (Iso.isIso_hom (puncturedPointsIso k B hk))
  refine Space.isOpenImmersion_comp B (Spec (.of k)) hk _ _ ?_ ?_
  · exact Space.isOpenImmersion_yoneda_map B (Spec (.of k)) hk _ hopen
  · exact Space.isOpenImmersion_of_isIso B (Spec (.of k)) hk _

variable [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]

/-- The open subspace of the involution quotient lying over the punctured affine line under the
squaring map. -/
noncomputable abbrev puncturedQuotient : Subfunctor (involutionQuotient k B hk).obj :=
  (puncturedSubfunctor k B hk).preimage (squaringMap k B hk)

/-- Over a field in which `2` is invertible, the squaring map restricts to an isomorphism from
the part of the involution quotient over the punctured affine line onto the punctured line. -/
theorem isIso_fromPreimage_squaringMap (hchar : (2 : k) ≠ 0) :
    IsIso ((puncturedSubfunctor k B hk).fromPreimage (squaringMap k B hk)) := by
  have hiso := isIso_squaringMap_pullback_puncturedAffineLine k hchar B hk
  have hr := isIso_toRange_puncturedPointsInclusion k B hk
  have h1 := Subfunctor.isPullback_preimage (squaringMap k B hk) (puncturedSubfunctor k B hk)
  have h2 : IsPullback
      (pullback.snd (squaringMap k B hk) (puncturedPointsInclusion k B hk) ≫
        Subfunctor.toRange (puncturedPointsInclusion k B hk))
      (pullback.fst (squaringMap k B hk) (puncturedPointsInclusion k B hk))
      (puncturedSubfunctor k B hk).ι (squaringMap k B hk) :=
    (IsPullback.of_hasPullback (squaringMap k B hk) (puncturedPointsInclusion k B hk)).flip.of_iso
      (Iso.refl _) (@asIso _ _ _ _ (Subfunctor.toRange (puncturedPointsInclusion k B hk)) hr)
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  rw [← IsPullback.isoIsPullback_hom_fst _ _ h1 h2]
  infer_instance

/-- The squaring map is a monomorphism on the part of the involution quotient over the punctured
affine line. -/
theorem mono_puncturedQuotient_ι_comp_squaringMap (hchar : (2 : k) ≠ 0) :
    Mono ((puncturedQuotient k B hk).ι ≫ squaringMap k B hk) := by
  have := isIso_fromPreimage_squaringMap k B hk hchar
  rw [← Subfunctor.fromPreimage_ι]
  exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ this) _ inferInstance

/-- A point of the involution quotient lies in the part over the punctured affine line exactly
when its image under the squaring map is not the origin. -/
theorem mem_range_pointsMap_puncturedQuotient_iff
    (x : Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj) :
    x ∈ Set.range (Space.pointsMap B (Spec (.of k)) hk _ (puncturedQuotient k B hk).ι) ↔
      Space.pointsMap B (Spec (.of k)) hk _ (squaringMap k B hk) x ≠ originPoint k B hk := by
  rw [← mem_range_pointsMap_puncturedAffineLineInclusion_iff]
  have hsq := Subfunctor.isPullback_preimage (squaringMap k B hk) (puncturedSubfunctor k B hk)
  have hr := isIso_toRange_puncturedPointsInclusion k B hk
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := @Space.pointsMap_surjective_of_isIso B (Spec (.of k)) hk _ _
      (Subfunctor.toRange (puncturedPointsInclusion k B hk)) hr
      (Space.pointsMap B (Spec (.of k)) hk _
        ((puncturedSubfunctor k B hk).fromPreimage (squaringMap k B hk)) z)
    refine ⟨y, ?_⟩
    rw [← Space.pointsMap_comp_apply, ← hsq.w, Space.pointsMap_comp_apply, ← hy,
      ← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]
  · rintro ⟨y, hy⟩
    obtain ⟨w, -, hw⟩ := Space.exists_point_of_isPullback_presheaf B (Spec (.of k)) hk hsq
      (Space.pointsMap B (Spec (.of k)) hk _
        (Subfunctor.toRange (puncturedPointsInclusion k B hk)) y) x
      (by rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι, hy])
    exact ⟨w, hw⟩

/-- The origin of the affine line, as a field-valued point of its restricted functor of points:
the zero section over the ground field itself. -/
noncomputable def originFieldPoint : Space.FieldValuedPoint B (Spec (.of k)) hk
    (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k)) where
  carrier := k
  contained := hk
  toBase := 𝟙 (Spec (.of k))
  value := affineLineZero k _

/-- The object of the site carrying the origin: the ground field itself. -/
noncomputable abbrev originObject : BigFppfOver B (Spec (.of k)) hk :=
  (originFieldPoint k B hk).siteObject

/-- The origin of the affine line, as a morphism of the site from the ground field. -/
noncomputable def originChart : originObject k B hk ⟶ affineLineChart k B hk :=
  (Over.post (X := B.obj hk) B.inclusion).preimage (X := originObject k B hk)
    (Y := affineLineChart k B hk) (affineLineZero k _)

/-- The origin of the affine line, as a morphism into the presheaf represented by the affine
line. -/
noncomputable abbrev originChartPoint :
    yoneda.obj (originObject k B hk) ⟶ yoneda.obj (affineLineChart k B hk) :=
  yoneda.map (originChart k B hk)

/-- The unique point of the ground field, as a point of the presheaf it represents. -/
noncomputable def originObjectPoint :
    Space.points B (Spec (.of k)) hk (yoneda.obj (originObject k B hk)) :=
  Space.FieldValuedPoint.class B (Spec (.of k)) hk _
    { carrier := k
      contained := hk
      toBase := 𝟙 (Spec (.of k))
      value := 𝟙 _ }

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The point of the ground field is carried to the origin of the affine line. -/
theorem pointsMap_originChartPoint :
    Space.pointsMap B (Spec (.of k)) hk _
        (originChartPoint k B hk ≫ (affineLinePointsIso k B hk).inv)
        (originObjectPoint k B hk) = originPoint k B hk := by
  rw [originObjectPoint, Space.pointsMap_class]
  refine Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B (Spec (.of k)) hk _
    ⟨_, Space.FieldValuedPoint.dominates_refl B (Spec (.of k)) hk _ _, 𝟙 _, ?_⟩
  show (Over.post (X := B.obj hk) B.inclusion).map (𝟙 _) ≫ affineLineZero k _ =
    (Over.post (X := B.obj hk) B.inclusion).map (𝟙 _ ≫ originChart k B hk)
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, originChart]
  exact ((Over.post (X := B.obj hk) B.inclusion).map_preimage (X := originObject k B hk)
    (Y := affineLineChart k B hk) (affineLineZero k _)).symm

/-- The chart of the involution quotient followed by the squaring map is squaring the coordinate
on the restricted functor of points of the affine line. -/
theorem quotientChart_comp_squaringMap' :
    quotientChart k B hk ≫ squaringMap k B hk =
      (affineLinePointsIso k B hk).inv ≫ (Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
        (yoneda.map (affineLineSquare k)) := by
  rw [quotientChart_comp_squaringMap]
  exact (Space.pointsYonedaIso_inv_comp_whiskerLeft (Over.post B.inclusion)
    (V := affineLineChart k B hk) (W := affineLineChart k B hk) (affineLineSquare k)).symm

/-- The origin of the involution quotient lies over the origin of the affine line. -/
theorem pointsMap_squaringMap_origin :
    Space.pointsMap B (Spec (.of k)) hk _ (squaringMap k B hk)
        (Space.pointsMap B (Spec (.of k)) hk _ (originChartPoint k B hk ≫ quotientChart k B hk)
          (originObjectPoint k B hk)) = originPoint k B hk := by
  rw [← Space.pointsMap_comp_apply, Category.assoc, quotientChart_comp_squaringMap',
    ← Category.assoc, Space.pointsMap_comp_apply, pointsMap_originChartPoint,
    pointsMap_affineLineSquare_eq_originPoint_iff]

attribute [local instance] Space.pointTopology

/-- The origin of the involution quotient: the image of the origin of the affine line. -/
noncomputable abbrev quotientOrigin :
    Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj :=
  Space.pointsMap B (Spec (.of k)) hk _ (originChartPoint k B hk ≫ quotientChart k B hk)
    (originObjectPoint k B hk)

/-- The origin of the involution quotient is its only point over the origin of the affine
line. -/
theorem pointsMap_squaringMap_eq_originPoint_iff
    (x : Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj) :
    Space.pointsMap B (Spec (.of k)) hk _ (squaringMap k B hk) x = originPoint k B hk ↔
      x = quotientOrigin k B hk :=
  ⟨fun h => (existsUnique_pointsMap_squaringMap_eq_originPoint k B hk).unique h
      (pointsMap_squaringMap_origin k B hk),
    fun h => h ▸ pointsMap_squaringMap_origin k B hk⟩

/-- The complement of the part of the involution quotient over the punctured affine line is the
origin. -/
theorem compl_range_pointsMap_puncturedQuotient :
    (Set.range (Space.pointsMap B (Spec (.of k)) hk _ (puncturedQuotient k B hk).ι))ᶜ =
      {quotientOrigin k B hk} := by
  ext x
  rw [Set.mem_compl_iff, mem_range_pointsMap_puncturedQuotient_iff, not_not,
    pointsMap_squaringMap_eq_originPoint_iff, Set.mem_singleton_iff]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- Every morphism of the site into the ground field over itself is the structure morphism. -/
theorem hom_originObject_ext {T : BigFppfOver B (Spec (.of k)) hk}
    (a b : T ⟶ originObject k B hk) : a = b := by
  have ha : a.left.hom ≫ 𝟙 _ = T.hom.hom := congrArg (fun c => c.hom) (Over.w a)
  have hb : b.left.hom ≫ 𝟙 _ = T.hom.hom := congrArg (fun c => c.hom) (Over.w b)
  ext1
  apply ObjectProperty.hom_ext
  rw [← Category.comp_id a.left.hom, ← Category.comp_id b.left.hom, ha, hb]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The presheaf represented by the ground field has a single point. -/
theorem subsingleton_points_originObject :
    Subsingleton (Space.points B (Spec (.of k)) hk (yoneda.obj (originObject k B hk))) :=
  Space.subsingleton_points_yoneda_of_isoSpec_toScheme B (Spec (.of k)) hk _
    (Iso.refl (Spec (.of k)))

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- Every morphism out of the presheaf represented by the ground field is a monomorphism. -/
theorem mono_of_yoneda_originObject {G : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (φ : yoneda.obj (originObject k B hk) ⟶ G) : Mono φ :=
  ⟨fun a b _ => by
    ext T x
    exact hom_originObject_ext k B hk _ _⟩

/-- The involution quotient is locally Noetherian, its chart being the affine line. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_involutionQuotient (hchar : (2 : k) ≠ 0) :
    Space.HasEtaleLocalProperty B (Spec (.of k)) hk (involutionQuotient k B hk).obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  ⟨affineLineChart k B hk, quotientChart k B hk, presheafSurjective_quotientChart k B hk hchar,
    presheafEtale_quotientChart k B hk hchar, isLocallyNoetherian_affineLine k⟩

/-- The image of the origin of the affine line is a residual space of the involution quotient at
its origin. -/
theorem isResidualSpaceAt_range_quotientOrigin :
    Space.IsResidualSpaceAt B (Spec (.of k)) hk (involutionQuotient k B hk).obj
      (quotientOrigin k B hk)
      (Subfunctor.range (originChartPoint k B hk ≫ quotientChart k B hk)).ι := by
  have hm := mono_of_yoneda_originObject k B hk (originChartPoint k B hk ≫ quotientChart k B hk)
  have hr : IsIso (Subfunctor.toRange (originChartPoint k B hk ≫ quotientChart k B hk)) :=
    inferInstance
  let e := @asIso _ _ _ _ (Subfunctor.toRange (originChartPoint k B hk ≫ quotientChart k B hk)) hr
  have hsub := subsingleton_points_originObject k B hk
  refine ⟨(isAlgebraicSpace_yoneda B (Spec (.of k)) hk (originObject k B hk)).of_iso e,
    inferInstance,
    Space.hasEtaleLocalProperty_of_representable B (Spec (.of k)) hk _ _ (originObject k B hk)
      e.symm (inferInstanceAs (IsReduced (Spec (.of k)))),
    Space.hasEtaleLocalProperty_of_representable B (Spec (.of k)) hk _ _ (originObject k B hk)
      e.symm (inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))),
    ⟨Space.pointsMap B (Spec (.of k)) hk _ e.hom (originObjectPoint k B hk)⟩,
    (Space.pointsEquivOfIso B (Spec (.of k)) hk e).symm.injective.subsingleton, ?_⟩
  intro z
  obtain ⟨y, rfl⟩ := @Space.pointsMap_surjective_of_isIso B (Spec (.of k)) hk _ _ e.hom hr z
  rw [← Space.pointsMap_comp_apply]
  show Space.pointsMap B (Spec (.of k)) hk _
    (Subfunctor.toRange (originChartPoint k B hk ≫ quotientChart k B hk) ≫
      (Subfunctor.range (originChartPoint k B hk ≫ quotientChart k B hk)).ι) y = _
  rw [Subfunctor.toRange_ι, Subsingleton.elim y (originObjectPoint k B hk)]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] in
/-- The restricted functor of points of the affine line is an algebraic space. -/
theorem isAlgebraicSpace_affineLinePoints :
    IsAlgebraicSpace B (Spec (.of k)) hk
      (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k)) :=
  (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (affineLineChart k B hk)).of_iso
    (affineLinePointsIso k B hk).symm

/-- The part of the involution quotient over the punctured affine line is an open subspace. -/
theorem isOpenSubspace_puncturedQuotient (hchar : (2 : k) ≠ 0) :
    Space.IsOpenSubspace B (Spec (.of k)) hk (puncturedQuotient k B hk) :=
  Space.isOpenSubspace_preimage B (Spec (.of k)) hk (squaringMap k B hk)
    (puncturedSubfunctor k B hk) (isAlgebraicSpace_affineLinePoints k B hk)
    (isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar)
    (isOpenSubspace_puncturedSubfunctor k B hk)

/-- The part of the involution quotient over the punctured affine line, together with the chart
`𝐀¹_k ⟶ X`, is an elementary distinguished square: the complement of the open part is the
origin, and the chart carries the origin of the affine line isomorphically onto it. -/
theorem isElementaryDistinguishedSquare_puncturedQuotient (hchar : (2 : k) ≠ 0) :
    Space.IsElementaryDistinguishedSquare B (Spec (.of k)) hk
      (isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar)
      (puncturedQuotient k B hk) (quotientChart k B hk) := by
  have hX := isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar
  have hU := isOpenSubspace_puncturedQuotient k B hk hchar
  have hq : Space.IsEtale B (Spec (.of k)) hk (quotientChart k B hk) :=
    (Space.isEtale_iff_presheaf_of_yoneda B (Spec (.of k)) hk _).2
      (presheafEtale_quotientChart k B hk hchar)
  have hc : IsClosed
      (Set.range (Space.pointsMap B (Spec (.of k)) hk _ (puncturedQuotient k B hk).ι))ᶜ :=
    (Space.isOpen_range_pointsMap_of_isOpenImmersion B (Spec (.of k)) hk _ hU.2).isClosed_compl
  refine ⟨isAlgebraicSpace_yoneda B (Spec (.of k)) hk _, hU, hq, hc, ?_⟩
  have h0 : IsClosed ({quotientOrigin k B hk} :
      Set (Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj)) :=
    compl_range_pointsMap_puncturedQuotient k B hk ▸ hc
  have key : ∀ (s t : Set (Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj))
      (_ : s = t) (hs : IsClosed s) (ht : IsClosed t),
      Space.reducedClosedSubspace B (Spec (.of k)) hk _ hX s hs =
        Space.reducedClosedSubspace B (Spec (.of k)) hk _ hX t ht := by
    rintro s _ rfl _ _
    rfl
  rw [key _ _ (compl_range_pointsMap_puncturedQuotient k B hk) hc h0]
  obtain ⟨e, he, -⟩ := Space.existsUnique_iso_of_isResidualSpaceAt B (Spec (.of k)) hk hX
    (Space.reducedClosedSubspace B (Spec (.of k)) hk _ hX {quotientOrigin k B hk} h0).ι
    (Subfunctor.range (originChartPoint k B hk ≫ quotientChart k B hk)).ι
    (Space.isResidualSpaceAt_ι_reducedClosedSubspace B (Spec (.of k)) hk hX
      (hasEtaleLocalProperty_isLocallyNoetherian_involutionQuotient k B hk hchar) _ h0)
    (isResidualSpaceAt_range_quotientOrigin k B hk)
  rw [← Subfunctor.eq_of_iso e he]
  refine Space.isIso_fromPreimage_range_of_isEtale B (Spec (.of k)) hk
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk _) hX _ hq
    (inferInstanceAs (IsReduced (Spec (.of k))))
    (inferInstanceAs (IsLocallyNoetherian (Spec (.of k))))
    (subsingleton_points_originObject k B hk) ⟨originObjectPoint k B hk⟩
    (originChartPoint k B hk) (mono_of_yoneda_originObject k B hk _) (fun w z hwz => ?_)
  have hsub := subsingleton_points_originObject k B hk
  rw [Subsingleton.elim z (originObjectPoint k B hk)] at hwz ⊢
  have h1 : Space.pointsMap B (Spec (.of k)) hk _ (affineLinePointsIso k B hk).inv w =
      originPoint k B hk := by
    rw [← pointsMap_affineLineSquare_eq_originPoint_iff, ← Space.pointsMap_comp_apply,
      ← quotientChart_comp_squaringMap', Space.pointsMap_comp_apply, hwz]
    exact pointsMap_squaringMap_origin k B hk
  have h2 := pointsMap_originChartPoint k B hk
  rw [Space.pointsMap_comp_apply] at h2
  exact (Space.pointsEquivOfIso B (Spec (.of k)) hk (affineLinePointsIso k B hk).symm).injective
    (h1.trans h2.symm)

/-- **The hypotheses of Stacks 0F45 as published do not imply separatedness.** Over a field in
which `2` is invertible, let `X` be the quotient of the affine line by the punctured graph of
negation and let `g : X ⟶ 𝐀¹_k` be the squaring map. With `U ⊆ X` the part over the punctured
line and `f : 𝐀¹_k ⟶ X` the chart, `(U ⊆ X, f)` is an elementary distinguished square, `U ⟶ 𝐀¹_k`
and `𝐀¹_k ⟶ 𝐀¹_k` are separated and `U ×_X 𝐀¹_k ⟶ U ×_{𝐀¹_k} 𝐀¹_k` is closed, yet `g` is not
separated. -/
theorem exists_isElementaryDistinguishedSquare_not_isSeparated (hchar : (2 : k) ≠ 0) :
    ∃ (X V Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (_ : IsAlgebraicSpace B (Spec (.of k)) hk Y)
      (g : X ⟶ Y) (U : Subfunctor X) (f : V ⟶ X),
      Space.IsElementaryDistinguishedSquare B (Spec (.of k)) hk hX U f ∧
      Space.IsSeparated B (Spec (.of k)) hk (U.ι ≫ g) ∧
      Space.IsSeparated B (Spec (.of k)) hk (f ≫ g) ∧
      Space.IsClosedMorphism B (Spec (.of k)) hk (pullback.mapDesc U.ι f g) ∧
      ¬ Space.IsSeparated B (Spec (.of k)) hk g := by
  have hiso := isIso_fromPreimage_squaringMap k B hk hchar
  have : Mono ((puncturedSubfunctor k B hk).fromPreimage (squaringMap k B hk)) :=
    @IsIso.mono_of_iso _ _ _ _ _ hiso
  have hmd := isIso_pullback_mapDesc_of_isPullback
    (Subfunctor.isPullback_preimage (squaringMap k B hk) (puncturedSubfunctor k B hk))
    (quotientChart k B hk)
  refine ⟨_, _, _, isAlgebraicSpace_involutionQuotient_of_isAffineHom k B hk hchar,
    isAlgebraicSpace_affineLinePoints k B hk, squaringMap k B hk, puncturedQuotient k B hk,
    quotientChart k B hk, isElementaryDistinguishedSquare_puncturedQuotient k B hk hchar,
    Space.isSeparated_of_mono B (Spec (.of k)) hk _
      (mono_puncturedQuotient_ι_comp_squaringMap k B hk hchar),
    Space.isSeparated_of_scheme_isSeparated B (Spec (.of k)) hk
      (inferInstanceAs (Scheme.IsSeparated (affineLine k).left)) _,
    @Space.isClosedMorphism_of_isIso B (Spec (.of k)) hk _ _ _ hmd,
    not_isSeparated_squaringMap k B hk hchar⟩

end AlgebraicGeometry.AffineLineInvolution

namespace AlgebraicGeometry.Space

/-- **Stacks 0F45 as published is false.** It is not true that a morphism `g : X ⟶ Y` of
algebraic spaces over `S` is separated as soon as an elementary distinguished square
`(U ⊆ X, f : V ⟶ X)` has `U ⟶ Y` and `V ⟶ Y` separated and `U ×_X V ⟶ U ×_Y V` closed. The
counterexample is
`AlgebraicGeometry.AffineLineInvolution.exists_isElementaryDistinguishedSquare_not_isSeparated`,
over the field `ℚ`. The statement with the further hypothesis that `V ×_X V ⟶ V ×_Y V` is closed
is `AlgebraicGeometry.Space.isSeparated_of_elementaryDistinguishedSquare`. -/
@[stacks 0F45 "counterexample: the statement as published is false; the corrected statement, \
with V ×_X V ⟶ V ×_Y V also closed, is isSeparated_of_elementaryDistinguishedSquare"]
theorem not_forall_isSeparated_of_isElementaryDistinguishedSquare :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      {X V Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
      (_hY : IsAlgebraicSpace B S hS Y) (g : X ⟶ Y) (U : Subfunctor X) (f : V ⟶ X),
      IsElementaryDistinguishedSquare B S hS hX U f →
      IsSeparated B S hS (U.ι ≫ g) → IsSeparated B S hS (f ≫ g) →
      IsClosedMorphism B S hS (pullback.mapDesc U.ι f g) → IsSeparated B S hS g := by
  intro h
  obtain ⟨B, hB⟩ := BigFppfSite.exists_contains (Spec (.of (ULift.{u} ℚ)))
  have := BigFppfOver.hasSheafify_type B _ hB
  have hchar : (2 : ULift.{u} ℚ) ≠ 0 := fun h2 => by
    have := congrArg ULift.down h2
    norm_num at this
  obtain ⟨X, V, Y, hX, hY, g, U, f, hsq, hU, hV, hUV, hg⟩ :=
    AffineLineInvolution.exists_isElementaryDistinguishedSquare_not_isSeparated
      (ULift.{u} ℚ) B hB hchar
  exact hg (h B _ hB hX hY g U f hsq hU hV hUV)

end AlgebraicGeometry.Space

end
