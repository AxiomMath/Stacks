module

public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SchemeOfAffineCase
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.FiniteOrderStep

/-!
# Deformations of a curve as a family of curves have a scheme as total space

Let `T` be an affine scheme, `T₀ → T` a finite-order thickening, and `G` an algebraic space over
`T` whose base change `F = G ×_T T₀` is a scheme. Then `G` is a scheme. Every point of `G` is
the image of a point of an affine open `V` of `F`; since `F → G` is a closed immersion which is
bijective on points, the image of `V` is an open subspace `W` of `G` with `W ×_T T₀ ≅ V`, and an
algebraic space over `T` whose base change to `T₀` is affine is affine. So `G` is covered by
affine open subspaces.

Applied to a deformation of the point `x₀ : Spec k → Curves` classifying a proper scheme `X` of
dimension at most one over `k`, over an object `A` of `𝒞_Λ`, this says that the total space of
the deformation is a scheme: it is an algebraic space over `Spec A` whose base change to the
closed point `Spec k → Spec A`, a finite-order thickening, is `X`. Hence the comparison functor
`Def_X ⥤ 𝓕_{Curves, k, x₀}` of
`StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison` is essentially
surjective, so it is an equivalence over `𝒞_Λ`, and `Def_X` is unobstructed if and only if
`𝓕_{Curves, k, x₀}` is. This is the equality `Def_X = 𝓕_{Λ-Curves, k, x₀}` in the proof of
Stacks 0DZU.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isPullback_isFiniteOrderThickening`: an algebraic
  space over an affine scheme whose base change along a finite-order thickening of the base is a
  scheme is a scheme.
* `Deformation.Examples.exists_iso_schemeSpace_total`: the total space of every deformation of
  `x₀` is a scheme.
* `Deformation.Examples.schemeDeformationToCurves_isEquivalence`: `Def_X ≌ 𝓕_{Curves, k, x₀}`.
* `Deformation.Examples.isSmooth_schemeDeformationToCurvesBased`: the comparison functor is a
  smooth morphism of categories over `𝒞_Λ`.
* `Deformation.Examples.isSmooth_baseProjection_schemeDeformation_iff_curves`: `Def_X` is
  unobstructed if and only if `𝓕_{Curves, k, x₀}` is.

## Implementation notes

The source deduces that the total space `Y` of a deformation of `x₀` over an Artinian base is a
scheme from Stacks 0ADD, an algebraic space being a scheme near any point whose local ring has
dimension at most one. Here the same conclusion is drawn from the thickening `X → Y`: it is the
base change of the finite-order thickening `Spec k → Spec A`, and Stacks 05ZR in the form above,
for a thickening pulled back from a finite-order thickening of an affine base, makes `Y` a
scheme. The affine case it needs is
`AlgebraicGeometry.Space.isAffineSpace_of_isFiniteOrderThickening_pullback`, so no dimension
theory of algebraic spaces enters.

## References

* [Stacks Project, Tag 0DZU](https://stacks.math.columbia.edu/tag/0DZU)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every point of a representable presheaf lies in the image of an affine open chart. -/
theorem exists_isAffine_isOpenImmersion_mem_range_pointsMap
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [F.IsRepresentable] (x : points B S hS F) :
    ∃ (V : BigFppfOver B S hS) (α : yoneda.obj V ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧ IsOpenImmersion B S hS α ∧
        x ∈ Set.range (pointsMap B S hS (yoneda.obj V) α) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨i, q, hq⟩ := exists_affineChart_pointsMap_eq B S hS (Functor.reprX F)
    (Functor.reprW F) p
  refine ⟨affineChart B S hS (Functor.reprX F) i,
    yoneda.map (affineChartι B S hS (Functor.reprX F) i) ≫ (Functor.reprW F).hom,
    isAffine_affineChart B S hS (Functor.reprX F) i, ?_, ⟨_, hq⟩⟩
  refine MorphismProperty.RespectsIso.postcomp _ (Functor.reprW F).hom _ ?_
  exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.IsOpenImmersion.{u}) _).2
    (isOpenImmersion_toScheme_map_affineChartι B S hS (Functor.reprX F) i)

/-- If `f : F ⟶ G` is injective on points and the subfunctor `W` of `G` has as points the image
of those of `α : P ⟶ F`, then the base change of `W` along `f` has the same points as `α`. -/
theorem range_pointsMap_pullback_fst_eq {F G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (W : Subfunctor G) (α : P ⟶ F) (hinj : Function.Injective (pointsMap B S hS F f))
    (hWpts : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      pointsMap B S hS F f '' Set.range (pointsMap B S hS P α)) :
    Set.range (pointsMap B S hS (pullback f W.ι) (pullback.fst f W.ι)) =
      Set.range (pointsMap B S hS P α) := by
  refine subset_antisymm ?_ ?_
  · rintro z ⟨w, rfl⟩
    have hmem : pointsMap B S hS F f (pointsMap B S hS (pullback f W.ι)
        (pullback.fst f W.ι) w) ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
      rw [pointsMap_apply_comm B S hS pullback.condition w]
      exact ⟨_, rfl⟩
    rw [hWpts] at hmem
    obtain ⟨z', hz', hfz'⟩ := hmem
    exact hinj hfz' ▸ hz'
  · rintro z ⟨w, rfl⟩
    have hmem : pointsMap B S hS F f (pointsMap B S hS P α w) ∈
        Set.range (pointsMap B S hS W.toFunctor W.ι) := by
      rw [hWpts]
      exact ⟨_, ⟨w, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨c, hc, -⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback f W.ι) _ b hb.symm
    exact ⟨c, hc⟩

/-- An open immersion into `F` with the same points as an open immersion from an affine
object has affine source. -/
theorem isAffineSpace_of_range_pointsMap_eq {F Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : BigFppfOver B S hS} (α : yoneda.obj V ⟶ F) (β : Q ⟶ F)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) (hα : IsOpenImmersion B S hS α)
    (hQ : IsAlgebraicSpace B S hS Q) (hβ : IsOpenImmersion B S hS β)
    (h : Set.range (pointsMap B S hS Q β) = Set.range (pointsMap B S hS (yoneda.obj V) α)) :
    IsAffineSpace B S hS Q := by
  have _ : Mono α := mono_of_presheaf_isOpenImmersion hα
  have _ : Mono β := mono_of_presheaf_isOpenImmersion hβ
  have hrange : Subfunctor.range β = Subfunctor.range α := by
    have hP := range_pointsMap_ι_range B S hS β
    have hA := range_pointsMap_ι_range B S hS α
    refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_range_of_isOpenImmersion V α hα) ?_)
      (le_of_range_pointsMap_ι_subset B S hS
        (isOpenSubspace_range_of_isAlgebraicSpace B S hS hQ _ hβ) ?_) <;>
      rw [hP, hA, h]
  refine ⟨V, hVaff, ⟨rangeIsoOfMono B S hS β ≪≫ ?_⟩⟩
  rw [hrange]
  exact (rangeIsoOfMono B S hS α).symm

/-- **An algebraic space over an affine scheme whose base change along a finite-order thickening
of the base is a scheme is a scheme.** Let `π : G ⟶ T` be an algebraic space over an affine
object `T` of the site, `k : T₀ ⟶ T` a finite-order thickening, and `f : F ⟶ G` the base change of
`k` along `π`, a closed immersion bijective on points. If `F` is representable, so is `G`.

Every point of `G` is the image of a point of an affine open `V` of `F`; the image of `|V|` is
open, `|f|` being a closed bijection, and the open subspace `W` of `G` it cuts out has
`W ×_T T₀ ≅ V`, so `W` is affine and the point lies in the schematic locus (Stacks 03JH). -/
theorem isRepresentable_of_isPullback_isFiniteOrderThickening
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) {T₀ T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map k))
    (f : F ⟶ G) (g : F ⟶ yoneda.obj T₀) (π : G ⟶ yoneda.obj T)
    (sq : IsPullback f g π (yoneda.map k)) (hf : IsClosedImmersion B S hS f)
    (hbij : Function.Bijective (pointsMap B S hS F f)) (hFrep : F.IsRepresentable) :
    G.IsRepresentable := by
  classical
  let _ : F.IsRepresentable := hFrep
  have hclosedmap : IsClosedMap (pointsMap B S hS F f) :=
    isClosed_of_universallyClosed B S hS hG f
      ((isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hF hG f).1
        (isIntegralHom_of_isClosedImmersion B S hS f hf)).2
  refine isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hG fun y => ?_
  obtain ⟨x, hx⟩ := hbij.2 y
  obtain ⟨V, α, hVaff, hαopen, v, hv⟩ :=
    exists_isAffine_isOpenImmersion_mem_range_pointsMap B S hS x
  have himage : IsOpen (pointsMap B S hS F f ''
      Set.range (pointsMap B S hS (yoneda.obj V) α)) := by
    rw [← isClosed_compl_iff, ← Set.image_compl_eq hbij]
    exact hclosedmap _
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS α hαopen).isClosed_compl
  set W : Subfunctor G := openSubspaceOfPoints B S hS G
    (pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α))
  have hW : IsOpenSubspace B S hS W :=
    isOpenSubspace_openSubspaceOfPoints B S hS hG _ himage
  have hWpts : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      pointsMap B S hS F f '' Set.range (pointsMap B S hS (yoneda.obj V) α) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hyW : y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
    rw [hWpts]
    exact ⟨x, ⟨v, hv⟩, hx⟩
  have hfstopen : IsOpenImmersion B S hS (pullback.fst f W.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback f W.ι).flip hW.2
  have hQaff := isAffineSpace_of_range_pointsMap_eq B S hS α (pullback.fst f W.ι) hVaff hαopen
    (isAlgebraicSpace_pullback B S hS f W.ι hF hW.1 hG) hfstopen
    (range_pointsMap_pullback_fst_eq B S hS f W α hbij.1 hWpts)
  have hpaste : IsPullback (pullback.snd f W.ι) (pullback.fst f W.ι ≫ g) (W.ι ≫ π)
      (yoneda.map k) :=
    (IsPullback.of_hasPullback f W.ι).flip.paste_vert sq
  have hW₀aff : IsAffineSpace B S hS (pullback (W.ι ≫ π) (yoneda.map k)) := by
    obtain ⟨V', hV', ⟨e⟩⟩ := hQaff
    exact ⟨V', hV', ⟨hpaste.isoPullback.symm ≪≫ e⟩⟩
  obtain ⟨T', -, ⟨eT⟩⟩ :=
    isAffineSpace_of_isFiniteOrderThickening_pullback B S hS hW.1 k hk (W.ι ≫ π) hW₀aff
  exact (mem_range_pointsMap_schematicLocus_iff B S hS G y).2
    ⟨W, hW, isRepresentable_of_natIso _ eT.symm, hyW⟩

end AlgebraicGeometry.Space

namespace Deformation.Examples

open Deformation.Artin

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
variable (X : Over (Spec (.of k))) [IsProper X.hom] (hk : B.Contains (Spec (.of k)))
  (hdim : topologicalKrullDim X.left ≤ 1) (iΛ : Spec (.of Λ) ⟶ integerBase)

/-- **The total space of a deformation of `x₀` is a scheme.** The identification of the special
fibre exhibits `X` as the base change of the total space along the closed point
`Spec k ⟶ Spec A`, a finite-order thickening, and `X` is a scheme. -/
theorem exists_iso_schemeSpace_total
    (y : DeformationObject iΛ (curvesToSchemesOver B hZ) (curveFamilyOfScheme X B hZ hk hdim)
      (curvesToSchemesOver_obj_curveFamilyOfScheme X B hZ hk hdim iΛ)) :
    ∃ T : BigFppfOver B integerBase hZ, Nonempty (y.point.total ≅ schemeSpace T) := by
  obtain ⟨A, ⟨⟨⟨S, hS⟩, ⟨⟨⟩⟩, sHom⟩, total, toBase, hflat, hproper, hfp, hrd⟩, arrow, hbase,
    harrow⟩ := y
  obtain rfl : S = Spec (.of A) := congrArg Over.left hbase
  obtain rfl : sHom = ObjectProperty.homMk (specULiftZIsTerminal.from _) :=
    ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _)
  have hA : B.Contains (baseSpec A) := hS
  have hb : arrow.baseMap = integerSiteMap B hZ hk hA (residueSpecMap A) := by
    change 𝟙 _ ≫ (BigFppfOver.toScheme B integerBase hZ).map arrow.baseMap ≫ 𝟙 _ = _ at harrow
    rw [Category.id_comp, Category.comp_id] at harrow
    rw [← integerSiteMap_toScheme_map arrow.baseMap]
    exact congrArg _ harrow
  have hci : Space.IsClosedImmersion B integerBase hZ (schemeSpaceMap arrow.baseMap).hom := by
    rw [hb]
    exact Space.presheaf_yoneda_map_of_inverseImage B integerBase hZ
      (P := @AlgebraicGeometry.IsClosedImmersion) inferInstance _
      (residueSpecMap_isClosedImmersion A)
  have hsurj : Space.IsSurjective B integerBase hZ (schemeSpaceMap arrow.baseMap).hom := by
    rw [hb]
    exact Space.isSurjective_yoneda_map B integerBase hZ _ ⟨residueSpecMap_surjective A⟩
  have hi : Space.IsThickeningHom B integerBase hZ arrow.totalMap :=
    (Space.isThickeningHom_iff_isClosedImmersion_and_isSurjective B integerBase hZ _).2
      ⟨Space.isClosedImmersion_of_isPullback B integerBase hZ arrow.cartesian.flip hci,
        Space.isSurjective_of_isPullback B integerBase hZ arrow.cartesian.flip hsurj⟩
  have hthick : Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B integerBase hZ).map arrow.baseMap) := by
    rw [hb]
    exact residueSpecMap_isFiniteOrderThickening A
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (integerSiteObject B hZ hA)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  have := hi.mono
  have hrep : total.1.IsRepresentable :=
    Space.isRepresentable_of_isPullback_isFiniteOrderThickening B integerBase hZ
      (T₀ := integerSiteObject B hZ hk) (T := integerSiteObject B hZ hA)
      (curveFamilyOfScheme X B hZ hk hdim).total.property total.property arrow.baseMap hthick
      arrow.totalMap.hom (curveFamilyOfScheme X B hZ hk hdim).toBase.hom toBase.hom
      (AlgebraicSpaces.isPullback_hom B integerBase hZ arrow.cartesian) hi.isClosedImmersion
      ⟨Space.pointsMap_injective_of_mono B integerBase hZ _, hi.surjective_pointsMap⟩
      (inferInstanceAs (yoneda.obj _).IsRepresentable)
  exact ⟨total.1.reprX,
    ⟨(ObjectProperty.fullyFaithfulι _).preimageIso total.1.reprW.symm⟩⟩

/-- **Every deformation of `x₀` comes from a deformation of `X`**: every object of
`𝓕_{Curves, k, x₀}` receives an isomorphism over `𝒞_Λ` from the image of a deformation of `X`,
its total space being a scheme. -/
theorem exists_iso_schemeDeformationToCurves_obj
    (y : (curvesPredeformation B hZ X hk hdim iΛ).carrier) :
    ∃ (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
      (φ : (schemeDeformationToCurves B hZ X hk hdim iΛ).obj P ≅ y),
      (curvesPredeformation B hZ X hk hdim iΛ).projection.IsHomLift
        (𝟙 ((curvesPredeformation B hZ X hk hdim iΛ).projection.obj y)) φ.hom := by
  obtain ⟨T, ⟨e⟩⟩ := exists_iso_schemeSpace_total B hZ X hk hdim iΛ y
  exact exists_iso_schemeDeformationToCurves_obj_of_iso_schemeSpace B hZ X hk hdim iΛ y T e

/-- The comparison functor is essentially surjective. -/
instance schemeDeformationToCurves_essSurj :
    (schemeDeformationToCurves B hZ X hk hdim iΛ).EssSurj where
  mem_essImage y := by
    obtain ⟨P, φ, -⟩ := exists_iso_schemeDeformationToCurves_obj B hZ X hk hdim iΛ y
    exact ⟨P, ⟨φ⟩⟩

/-- **`Def_X` is equivalent to `𝓕_{Curves, k, x₀}`**: the comparison functor is full, faithful
and essentially surjective. -/
instance schemeDeformationToCurves_isEquivalence :
    (schemeDeformationToCurves B hZ X hk hdim iΛ).IsEquivalence where

/-- **The comparison functor is a smooth morphism of categories over `𝒞_Λ`**: it is full, and
every object of `𝓕_{Curves, k, x₀}` receives a vertical arrow from the image of a deformation of
`X`. -/
theorem isSmooth_schemeDeformationToCurvesBased :
    IsSmooth (schemeDeformationToCurvesBased B hZ X hk hdim iΛ) := by
  have : (schemeDeformationToCurvesBased B hZ X hk hdim iΛ).toFunctor.Full :=
    inferInstanceAs (schemeDeformationToCurves B hZ X hk hdim iΛ).Full
  refine isSmooth_of_full_of_exists_vertical _ fun y => ?_
  obtain ⟨P, φ, hφ⟩ := exists_iso_schemeDeformationToCurves_obj B hZ X hk hdim iΛ y
  exact ⟨P, φ.hom, hφ⟩

/-- **`Def_X` is unobstructed if and only if `𝓕_{Curves, k, x₀}` is.** This is the equality
`Def_X = 𝓕_{Λ-Curves, k, x₀}` in the proof of Stacks 0DZU, read on unobstructedness: the
structure functor of `Def_X` is the comparison functor followed by that of
`𝓕_{Curves, k, x₀}`, the comparison functor is smooth, and it is essentially surjective with a
source cofibred in groupoids. -/
theorem isSmooth_baseProjection_schemeDeformation_iff_curves :
    IsSmooth (baseProjection (schemeDeformationCategoryProjection (Λ := Λ) X)) ↔
      IsSmooth (baseProjection (curvesPredeformation B hZ X hk hdim iΛ).projection) := by
  rw [← schemeDeformationToCurvesBased_comp_baseProjection B hZ X hk hdim iΛ]
  refine ⟨fun h => ?_,
    isSmooth_comp _ _ (isSmooth_schemeDeformationToCurvesBased B hZ X hk hdim iΛ)⟩
  have : (schemeDeformationToCurvesBased B hZ X hk hdim iΛ).toFunctor.EssSurj :=
    inferInstanceAs (schemeDeformationToCurves B hZ X hk hdim iΛ).EssSurj
  exact isSmooth_of_essSurj_comp (schemeDeformationToCurvesBased B hZ X hk hdim iΛ) _ h

end Deformation.Examples
