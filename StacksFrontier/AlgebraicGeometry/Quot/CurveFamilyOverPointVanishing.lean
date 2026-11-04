module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceTowerHypotheses
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.TerminalChartVanishingAboveTheDimension

/-!
# A family of curves over a one-point base is a curve, and its cohomology stops in degree one

Let `f : X ⟶ S` be a family of curves (Stacks 0D4Z) whose base `S` is an affine, locally
Noetherian scheme with at most one point, for instance the spectrum of a field. Then the total
space `X` is a scheme (Stacks 0ADD at every point), Noetherian and of dimension at most one, and
`H^q(X, 𝓜) = 0` for every quasi-coherent `𝒪_X`-module `𝓜` and every `q ≥ 2`. This is the input
"`X_s` is a `1`-dimensional Noetherian scheme, so `H^i(X_s, 𝒪_{X_s}) = 0` for `i ≥ 2`"
(Cohomology, Proposition 02UZ) of the proof of Stacks 0E1J.

## Main results

* `AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_dimensionAtPoint_eq_of_subsingleton`:
  over a one-point base, the relative dimension of Stacks 04NM at a point is the dimension of
  Stacks 04N5 of the space at that point.
* `AlgebraicGeometry.CurveFamily.dimension_total_le_one_of_subsingleton`: the total space of a
  family of curves over a one-point base has dimension at most one.
* `AlgebraicGeometry.CurveFamily.isRepresentable_total_of_subsingleton`: it is a scheme.
* `AlgebraicGeometry.CurveFamily.exists_isTerminal_chart_of_subsingleton`: it has a terminal
  étale chart whose scheme is a Noetherian space of dimension at most one.
* `AlgebraicGeometry.CurveFamily.isZero_rightDerived_globalSectionsFunctor_of_subsingleton`:
  `H^q(X, 𝓜) = 0` for `q ≥ 2` and `𝓜` quasi-coherent.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0A4R](https://stacks.math.columbia.edu/tag/0A4R)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k : BigFppfOver B S hS}

/-- **Over a one-point base the relative dimension is the absolute dimension.** For a morphism
`g : X ⟶ k` of algebraic spaces over `S` whose target is represented by a scheme with at most one
point, the relative dimension of Stacks 04NM at a point `x` is `e` exactly when the dimension of
Stacks 04N5 of `X` at `x` is `e`: both are read on one étale scheme chart at `x`, and the fibre of
the chart morphism is the whole chart. -/
theorem hasRelativeDimensionAt_iff_dimensionAtPoint_eq_of_subsingleton
    (hX : IsAlgebraicSpace B S hS X)
    (hk : Subsingleton ((BigFppfOver.toScheme B S hS).obj k)) (g : X ⟶ yoneda.obj k)
    (x : points B S hS X) (e : ℕ∞) :
    HasRelativeDimensionAt e B S hS g x ↔ dimensionAtPoint B S hS X hX x = (e : WithBot ℕ∞) := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS X hX x
  have := isMultiplicative_presheaf_etale B S hS
  have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj k)) :=
    MorphismProperty.id_mem _ _
  have hcomm : yoneda.map (yoneda.preimage (a ≫ g)) ≫ 𝟙 (yoneda.obj k) = a ≫ g := by
    rw [Category.comp_id, yoneda.map_preimage]
  have hcl : (pointsEquivScheme B S hS U).symm (schemePoint B S hS U p) =
      p.class B S hS (yoneda.obj U) :=
    (pointsEquivScheme B S hS U).symm_apply_eq.2 rfl
  have hx : x = pointsMap B S hS (yoneda.obj U) a
      ((pointsEquivScheme B S hS U).symm (schemePoint B S hS U p)) := by
    rw [hcl]
    exact hp.symm
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a ha p hp, hx,
    hasRelativeDimensionAt_pointsMap_iff B S hS e g U k a (𝟙 (yoneda.obj k))
      (yoneda.preimage (a ≫ g)) ha hb hcomm (schemePoint B S hS U p),
    topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton]

end Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

attribute [local instance] Space.pointTopology

variable (Y : CurveFamily B hZ)
  [hY : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj Y.base)]

include hY in
/-- **The total space of a family of curves over a one-point base has dimension at most one**:
at each point its dimension is the relative dimension of the family there, which is at most
one. -/
theorem dimension_total_le_one_of_subsingleton :
    Space.dimension B integerBase hZ Y.total.obj Y.total.property ≤ 1 := by
  refine iSup_le fun x => ?_
  obtain ⟨e, he, h⟩ := Y.relativeDimensionLE x
  rw [(Space.hasRelativeDimensionAt_iff_dimensionAtPoint_eq_of_subsingleton B integerBase hZ
    Y.total.property hY Y.toBase.hom x e).1 h]
  exact_mod_cast he

include hY in
/-- **The local rings of the total space of a family of curves over a one-point base have
dimension at most one** (Stacks 0BAN): their supremum is the dimension. -/
theorem localRingDimension_le_one_of_subsingleton (x : Space.points B integerBase hZ Y.total.obj) :
    Space.localRingDimension B integerBase hZ x ≤ 1 := by
  have h := (le_iSup (fun y : Space.points B integerBase hZ Y.total.obj =>
    (Space.localRingDimension B integerBase hZ y : WithBot ℕ∞)) x).trans
    ((Space.dimension_eq_iSup_localRingDimension B integerBase hZ Y.total.obj
      Y.total.property).symm.le.trans (Y.dimension_total_le_one_of_subsingleton))
  exact_mod_cast h

variable [hAff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y.base)]
  [hNoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj Y.base)]

include hY hAff hNoeth in
/-- **The total space of a family of curves over an affine locally Noetherian one-point base is a
scheme.** It is separated, since it is proper over an affine scheme, and locally Noetherian,
since it is of finite type over a locally Noetherian scheme; its local rings have dimension at
most one. So every point lies in an open subspace which is a scheme (Stacks 0ADD), and the
schematic locus is everything (Stacks 03JH). -/
theorem isRepresentable_total_of_subsingleton : Y.total.obj.IsRepresentable :=
  Space.isRepresentable_of_surjective_pointsMap_schematicLocus B integerBase hZ Y.total.property
    fun x => (Space.mem_range_pointsMap_schematicLocus_iff B integerBase hZ _ x).2
      (Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one B integerBase hZ
        Y.total.property
        (Space.isAbsolutelySeparated_of_isSeparated_to_affine B integerBase hZ B.contains_terminal
          Y.base hAff Y.toBase.hom Y.proper.1)
        (Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B integerBase hZ
          Y.total.property (isAlgebraicSpace_yoneda B integerBase hZ Y.base) Y.toBase.hom
          Y.proper.2.1.1
          (Space.hasEtaleLocalProperty_of_representable B integerBase hZ _ _ Y.base (Iso.refl _)
            hNoeth))
        x (Y.localRingDimension_le_one_of_subsingleton x))

include hY hAff hNoeth in
/-- **The total space of a family of curves over an affine locally Noetherian one-point base has a
terminal étale chart whose scheme is a Noetherian space of dimension at most one.** The chart is
the scheme representing the total space (`isRepresentable_total_of_subsingleton`). Its scheme is
proper and of finite presentation over the base, hence Noetherian, and each of its points has
local dimension at most one, the fibre over the single point of the base being the whole
scheme. -/
theorem exists_isTerminal_chart_of_subsingleton :
    ∃ A : Space.SmallEtale B integerBase hZ Y.total.1, Nonempty (IsTerminal A) ∧
      NoetherianSpace (Space.chartScheme A) ∧
      topologicalKrullDim (Space.chartScheme A) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  have := Y.isRepresentable_total_of_subsingleton
  let e : yoneda.obj Y.total.obj.reprX ≅ Y.total.obj := Y.total.obj.reprW
  let A : Space.SmallEtale B integerBase hZ Y.total.1 :=
    ⟨CostructuredArrow.mk e.hom, Space.presheaf_of_isIso B integerBase hZ inferInstance
      (fun U => by
        show Etale ((BigFppfOver.toScheme B integerBase hZ).map (𝟙 U))
        rw [CategoryTheory.Functor.map_id]
        infer_instance) e.hom⟩
  have hA : IsTerminal A := IsTerminal.ofUniqueHom
    (fun A' => ObjectProperty.homMk (CostructuredArrow.homMk
      (yoneda.preimage (A'.obj.hom ≫ e.inv)) (by simp [A])))
    (fun A' m => ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
      (yoneda.map_injective (by
        have hw := CostructuredArrow.w m.hom
        show _ = yoneda.map (yoneda.preimage (A'.obj.hom ≫ e.inv))
        rw [Functor.map_preimage, ← hw]
        simp [A]))))
  let q : Y.total.obj.reprX ⟶ Y.base := yoneda.preimage (e.hom ≫ Y.toBase.hom)
  have hid : schemeSpaceMap (𝟙 Y.base) = 𝟙 (schemeSpace Y.base) := by
    simp [schemeSpaceMap]
    rfl
  have : IsIso (schemeSpaceMap (𝟙 Y.base)) := by
    rw [hid]
    infer_instance
  let p : schemeSpace Y.total.obj.reprX ⟶ Y.total := ObjectProperty.homMk e.hom
  have : IsIso p := ⟨⟨ObjectProperty.homMk e.inv, InducedCategory.hom_ext e.hom_inv_id,
    InducedCategory.hom_ext e.inv_hom_id⟩⟩
  have sq : IsPullback p (schemeSpaceMap q) Y.toBase (schemeSpaceMap (𝟙 Y.base)) :=
    IsPullback.of_horiz_isIso ⟨InducedCategory.hom_ext (by
      simp only [ObjectProperty.FullSubcategory.comp_hom, schemeSpaceMap, Functor.map_preimage,
        CategoryTheory.Functor.map_id, p, q]
      exact (Category.comp_id _).symm)⟩
  let T := (BigFppfOver.toScheme B integerBase hZ).obj Y.total.obj.reprX
  have hprop := Y.isProper_toScheme_map_of_isPullback_schemeSpaceMap sq
  have hfp := Y.locallyOfFinitePresentation_toScheme_map_of_isPullback sq
  have : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B integerBase hZ).map q)
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).map q)
  have : IsNoetherian T := ⟨⟩
  refine ⟨A, ⟨hA⟩, inferInstanceAs (NoetherianSpace T), ?_⟩
  show topologicalKrullDim T ≤ _
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun t => ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim,
    ← topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton
      ((BigFppfOver.toScheme B integerBase hZ).map q) t]
  exact Y.topologicalKrullDimAt_fiber_toScheme_map_le_of_isPullback sq
    (by rw [CategoryTheory.Functor.map_id]; infer_instance) t

attribute [local instance 5000] SheafOfModules.instAbelian in
attribute [local instance] Space.hasInjectiveResolutions_modules Space.enoughInjectives_modules in
include hY hAff hNoeth in
/-- **The cohomology of a family of curves over an affine locally Noetherian one-point base stops
in degree one.** For a quasi-coherent module `𝓜` on the total space `X`, `H^q(X, 𝓜) = 0` for every
`q ≥ 2`: `X` is a Noetherian scheme of dimension at most one
(`exists_isTerminal_chart_of_subsingleton`), so this is vanishing above the dimension (Stacks
02UZ, read on the small étale site through Stacks 03DW). -/
theorem isZero_rightDerived_globalSectionsFunctor_of_subsingleton
    (M : Space.Modules.{u, u} B integerBase hZ Y.total.1 Y.total.2)
    (hM : M.IsQuasicoherentOnSite) {q : ℕ} (hq : 2 ≤ q) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Y.total.1 Y.total.2).O)).rightDerived
          q).obj M) := by
  obtain ⟨A, ⟨hA⟩, hN, hdim⟩ := Y.exists_isTerminal_chart_of_subsingleton
  exact Space.isZero_rightDerived_globalSectionsFunctor_of_isTerminal_of_dim_le B integerBase hZ
    Y.total hA M hM hdim (by omega)

end CurveFamily

end AlgebraicGeometry

end
