module

public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.LocalModel
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.ZeroSection

/-!
# The zero locus of a vector bundle over an affine chart

Let `W` be an algebraic space over a scheme `S` in a big fppf site, `ℰ` a finite locally free
`𝒪_W`-module with vector bundle `p : E ⟶ W`, zero section `o : W ⟶ E` and zero locus
`o(W) ⊆ E`. Over an affine étale chart `V` of `W` the fibre product `E ×_W V` is
`Spec Γ(V, Sym(ℰ))`, and the zero section restricts to the closed immersion
`V ⟶ Spec Γ(V, Sym(ℰ))` given by the augmentation `ε_V : Γ(V, Sym(ℰ)) ⟶ Γ(V, 𝒪)`. This file
proves that the inverse image of the zero locus in `E ×_W V` is exactly that closed subscheme.

## Main definitions

* `AlgebraicGeometry.Space.vectorBundleChartZeroSection`: the zero section `V ⟶ E ×_W V` over an
  affine chart.

## Main results

* `AlgebraicGeometry.Space.chartEval_augmentationPushforwardAlgebraHom`: the chart reading of the
  morphism of algebras given by `ε : 𝒜 ⟶ 𝒪_X` is `ε` followed by pullback of functions.
* `AlgebraicGeometry.Space.ΓSpecIso_inv_comp_appTop_vectorBundleChartZeroSection`: the chart zero
  section induces `ε_V` on global functions.
* `AlgebraicGeometry.Space.preimage_vectorBundleZeroLocus`: the inverse image of `o(W)` in
  `E ×_W V` is the range of the chart zero section.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart reading of the morphism of algebras given by `ε : 𝒜 ⟶ 𝒪_X`** is `ε` at the
chart followed by pullback of functions along `v : T ⟶ V`. -/
theorem chartEval_augmentationPushforwardAlgebraHom {X : AlgebraicSpaces B S hS}
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (ε : A ⟶ unitAlgebra B S hS X)
    (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (x : X.1.obj (op T)) (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom) :
    chartEval B S hS A V v x hxv
        (augmentationPushforwardAlgebraHom B S hS A ε (specPointOver B S hS T x)) =
      ε.right.hom.app (op V) ≫ ((BigFppfOver.toScheme B S hS).map v).appTop := by
  ext a
  exact chartEval_algebraMap B S hS (A := unitAlgebra B S hS X) V v x hxv
    (unitAlgebraHom B S hS X _) (ε.right.hom.app (op V) a)

variable (W : AlgebraicSpaces B S hS) (F : SheafOfModules.{u} (structureRingSheaf B S hS W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
  (V : SmallEtale B S hS W.1) [IsAffine (chartScheme V)]

/-- The augmentation `ε_V : Γ(V, Sym(ℰ)) ⟶ Γ(V, 𝒪)` on an étale chart. -/
abbrev chartAugmentation :
    (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V) ⟶ Γ(chartScheme V, ⊤) :=
  (vectorBundleAugmentation B S hS W F).right.hom.app (op V)

/-- The augmentation is a retraction of the structure map. -/
theorem chartAlgebraMap_comp_chartAugmentation :
    chartAlgebraMap B S hS (symmetricAlgebraSheaf B S hS W F) V ≫
      chartAugmentation B S hS W F V = 𝟙 _ := by
  ext r
  exact (vectorBundleAugmentation B S hS W F).comm (op V) r

/-- The composite of `V ≅ Spec Γ(V, 𝒪)`, the morphism `Spec ε_V` and the chart map
`Spec Γ(V, Sym(ℰ)) ⟶ V` is the identity of `V`. -/
theorem specChartMap_comp :
    ((chartScheme V).isoSpec.hom ≫ Spec.map (chartAugmentation B S hS W F V)) ≫
        specChartMap B S hS (symmetricAlgebraSheaf B S hS W F) V =
      (BigFppfOver.toScheme B S hS).map (𝟙 V.obj.left) := by
  rw [specChartMap, Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp,
    chartAlgebraMap_comp_chartAugmentation, Spec.map_id, Category.id_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **The zero section of the vector bundle over an affine chart**, `V ⟶ E ×_W V`, the morphism
of the site given by the augmentation `Γ(V, Sym(ℰ)) ⟶ Γ(V, 𝒪)`. -/
def vectorBundleChartZeroSection : V.obj.left ⟶ vectorBundleChart B S hS W F V :=
  affineChartSpecLift B S hS (symmetricAlgebraSheaf B S hS W F)
    (sectionsBelowCutoff_symmetricAlgebraSheaf B S hS W F
      (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)
      (_root_.SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
        (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree F
          inferInstance))) V (𝟙 V.obj.left)
    ((chartScheme V).isoSpec.hom ≫ Spec.map (chartAugmentation B S hS W F V))
    (specChartMap_comp B S hS W F V)

/-- The chart zero section, as a morphism of schemes, is `V ≅ Spec Γ(V, 𝒪)` followed by
`Spec ε_V`. -/
theorem toScheme_map_vectorBundleChartZeroSection :
    (BigFppfOver.toScheme B S hS).map (vectorBundleChartZeroSection B S hS W F V) =
      (chartScheme V).isoSpec.hom ≫ Spec.map (chartAugmentation B S hS W F V) :=
  toScheme_map_affineChartSpecLift B S hS _ _ V _ _ _

/-- The chart zero section is a section of the chart projection. -/
theorem vectorBundleChartZeroSection_comp_hom :
    vectorBundleChartZeroSection B S hS W F V ≫ vectorBundleChartHom B S hS W F V = 𝟙 _ := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, toScheme_map_vectorBundleChartZeroSection, toScheme_map_affineChartSpecHom]
  exact specChartMap_comp B S hS W F V

/-- **The chart zero section induces the augmentation on global functions.** -/
theorem ΓSpecIso_inv_comp_appTop_vectorBundleChartZeroSection :
    (Scheme.ΓSpecIso ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V))).inv ≫
        ((BigFppfOver.toScheme B S hS).map (vectorBundleChartZeroSection B S hS W F V)).appTop =
      chartAugmentation B S hS W F V := by
  have h' : (chartScheme V).isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(chartScheme V, ⊤)).inv := by
    rw [← Iso.comp_hom_eq_id, ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop,
      Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop]
  have h : (Scheme.ΓSpecIso Γ(chartScheme V, ⊤)).inv ≫ (chartScheme V).isoSpec.hom.appTop =
      𝟙 _ := by
    rw [← h', ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rw [toScheme_map_vectorBundleChartZeroSection, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, h, Category.comp_id]

/-- The point of `E` given by a point `t` of `E ×_W V`, read through the relative spectrum. -/
theorem relativeSpecPointsEquiv_vectorBundleChartToTotal_app {T : BigFppfOver B S hS}
    (t : T ⟶ vectorBundleChart B S hS W F V) :
    relativeSpecPointsEquiv B S hS (symmetricAlgebraSheaf B S hS W F) T
        ((vectorBundleChartToTotal B S hS W F V).app (op T) t) =
      (affineChartSpecPoint B S hS _ _ V
        (exists_chartEval_symmetricAlgebraSheaf_eq B S hS W F V)).map B S hS t :=
  relativeSpecPointsEquiv_affineChartSpecToPoints_app B S hS _ _ V _ t

/-- The point of `W` underlying the point of `E` given by `t : T ⟶ E ×_W V` is the image under
the chart of `t` followed by the chart projection `E ×_W V ⟶ V`. -/
private theorem map_affineChartSpecPoint_pt_eq {T : BigFppfOver B S hS}
    (t : T ⟶ vectorBundleChart B S hS W F V) :
    ((affineChartSpecPoint B S hS _ _ V
        (exists_chartEval_symmetricAlgebraSheaf_eq B S hS W F V)).map B S hS t).pt =
      V.obj.hom.app (op T) (t ≫ vectorBundleChartHom B S hS W F V) := by
  rw [RelativeSpecPoint.map_pt, affineChartSpecPoint_pt, map_affineChartSpecPt]

/-- The point of `W` underlying the point of `E` given by `t : T ⟶ E ×_W V` is `t` followed by
the chart projection `E ×_W V ⟶ V` and `V ⟶ W`. -/
theorem yonedaEquiv_symm_map_affineChartSpecPoint_pt {T : BigFppfOver B S hS}
    (t : T ⟶ vectorBundleChart B S hS W F V) :
    yonedaEquiv.symm ((affineChartSpecPoint B S hS _ _ V
        (exists_chartEval_symmetricAlgebraSheaf_eq B S hS W F V)).map B S hS t).pt =
      yoneda.map (t ≫ vectorBundleChartHom B S hS W F V) ≫ V.obj.hom := by
  rw [map_affineChartSpecPoint_pt_eq, chart_hom_app_eq, Equiv.symm_apply_apply]

/-- The point of `W` given by `s : T ⟶ V` corresponds to the composite `T ⟶ V ⟶ W`. -/
theorem yonedaEquiv_symm_hom_app {T : BigFppfOver B S hS} (s : T ⟶ V.obj.left) :
    yonedaEquiv.symm (V.obj.hom.app (op T) s) = yoneda.map s ≫ V.obj.hom := by
  rw [chart_hom_app_eq, Equiv.symm_apply_apply]

omit [SheafOfModules.IsFiniteLocallyFree F] in
/-- The chart reading of the point of `E` given by `s : T ⟶ V` and the zero section is the
augmentation followed by pullback of functions along `s`. -/
theorem chartEval_relativeSpecSectionPoint_vectorBundleAugmentation {T : BigFppfOver B S hS}
    (s : T ⟶ V.obj.left) :
    (relativeSpecSectionPoint B S hS (symmetricAlgebraSheaf B S hS W F)
        (vectorBundleAugmentation B S hS W F) T (V.obj.hom.app (op T) s)).chartEval B S hS V s
        (yonedaEquiv_symm_hom_app B S hS W V s) =
      chartAugmentation B S hS W F V ≫ ((BigFppfOver.toScheme B S hS).map s).appTop :=
  chartEval_augmentationPushforwardAlgebraHom B S hS _ (vectorBundleAugmentation B S hS W F) V s _ _

/-- The chart reading of the point of `E` given by `t : T ⟶ E ×_W V` is pullback of functions
along `t`. -/
theorem chartEval_map_affineChartSpecPoint_vectorBundleChart {T : BigFppfOver B S hS}
    (t : T ⟶ vectorBundleChart B S hS W F V) :
    ((affineChartSpecPoint B S hS _ _ V
        (exists_chartEval_symmetricAlgebraSheaf_eq B S hS W F V)).map B S hS t).chartEval B S hS V
        (t ≫ vectorBundleChartHom B S hS W F V)
        (yonedaEquiv_symm_map_affineChartSpecPoint_pt B S hS W F V t) =
      (Scheme.ΓSpecIso ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V))).inv ≫
        ((BigFppfOver.toScheme B S hS).map t).appTop :=
  affineChartSpecPoint_map_chartEval B S hS _ _ V _ t _

/-- The chart zero section composed with `s : T ⟶ V` induces the augmentation followed by pullback
of functions along `s`, on global functions. -/
private theorem ΓSpecIso_inv_comp_appTop_comp_vectorBundleChartZeroSection {T : BigFppfOver B S hS}
    (s : T ⟶ V.obj.left) :
    (Scheme.ΓSpecIso ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V))).inv ≫
        ((BigFppfOver.toScheme B S hS).map (s ≫ vectorBundleChartZeroSection B S hS W F V)).appTop =
      chartAugmentation B S hS W F V ≫ ((BigFppfOver.toScheme B S hS).map s).appTop := by
  rw [Functor.map_comp, Scheme.Hom.comp_appTop, ← Category.assoc,
    ΓSpecIso_inv_comp_appTop_vectorBundleChartZeroSection]

/-- A point of `E ×_W V` lying over the zero locus factors through the chart zero section. -/
theorem exists_comp_vectorBundleChartZeroSection_eq_of_mem {T : BigFppfOver B S hS}
    (t : T ⟶ vectorBundleChart B S hS W F V)
    (ht : (vectorBundleChartToTotal B S hS W F V).app (op T) t ∈
      (vectorBundleZeroLocus B S hS W F).1.obj (op T)) :
    ∃ s, s ≫ vectorBundleChartZeroSection B S hS W F V = t := by
  obtain ⟨w, hw⟩ := ht
  have hw' := congrArg (relativeSpecPointsEquiv B S hS (symmetricAlgebraSheaf B S hS W F) T) hw
  change relativeSpecPointsEquiv B S hS (symmetricAlgebraSheaf B S hS W F) T
      ((relativeSpecSection B S hS _ (vectorBundleAugmentation B S hS W F)).app (op T) w) = _
    at hw'
  rw [relativeSpecPointsEquiv_relativeSpecSection_app,
    relativeSpecPointsEquiv_vectorBundleChartToTotal_app] at hw'
  obtain rfl : w = V.obj.hom.app (op T) (t ≫ vectorBundleChartHom B S hS W F V) :=
    (congrArg RelativeSpecPoint.pt hw').trans (map_affineChartSpecPoint_pt_eq B S hS W F V t)
  refine ⟨t ≫ vectorBundleChartHom B S hS W F V,
    (BigFppfOver.toScheme B S hS).map_injective (Scheme.hom_ext_of_ΓSpecIso_inv ?_)⟩
  rw [ΓSpecIso_inv_comp_appTop_comp_vectorBundleChartZeroSection,
    ← chartEval_relativeSpecSectionPoint_vectorBundleAugmentation,
    ← chartEval_map_affineChartSpecPoint_vectorBundleChart]
  exact RelativeSpecPoint.chartEval_congr B S hS V rfl hw' _ _

/-- The chart zero section lands in the zero locus. -/
theorem vectorBundleChartToTotal_app_comp_vectorBundleChartZeroSection_mem
    {T : BigFppfOver B S hS} (s : T ⟶ V.obj.left) :
    (vectorBundleChartToTotal B S hS W F V).app (op T)
        (s ≫ vectorBundleChartZeroSection B S hS W F V) ∈
      (vectorBundleZeroLocus B S hS W F).1.obj (op T) := by
  set A := symmetricAlgebraSheaf B S hS W F
  set j := vectorBundleChartZeroSection B S hS W F V
  have hs : (s ≫ j) ≫ vectorBundleChartHom B S hS W F V = s := by
    rw [Category.assoc, vectorBundleChartZeroSection_comp_hom, Category.comp_id]
  refine ⟨V.obj.hom.app (op T) s, (relativeSpecPointsEquiv B S hS A T).injective ?_⟩
  show relativeSpecPointsEquiv B S hS A T
      ((relativeSpecSection B S hS A (vectorBundleAugmentation B S hS W F)).app (op T) _) = _
  rw [relativeSpecPointsEquiv_relativeSpecSection_app]
  rw [relativeSpecPointsEquiv_vectorBundleChartToTotal_app]
  have hpt : (relativeSpecSectionPoint B S hS A (vectorBundleAugmentation B S hS W F) T
      (V.obj.hom.app (op T) s)).pt = ((affineChartSpecPoint B S hS _ _ V
        (exists_chartEval_symmetricAlgebraSheaf_eq B S hS W F V)).map B S hS (s ≫ j)).pt := by
    show V.obj.hom.app (op T) s = _
    rw [map_affineChartSpecPoint_pt_eq, hs]
  refine RelativeSpecPoint.ext_of_chartEval B S hS A V
    (fun v x hxv => injective_chartEval_of_isAffine B S hS A
      (isQuasicoherent_symmetricAlgebraSheaf B S hS W F
        (SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent F)) V v x hxv) hpt s
    (yonedaEquiv_symm_hom_app B S hS W V s)
    (by rw [← hpt]; exact yonedaEquiv_symm_hom_app B S hS W V s) ?_
  rw [chartEval_relativeSpecSectionPoint_vectorBundleAugmentation]
  refine Eq.trans ?_ (RelativeSpecPoint.chartEval_congr B S hS V hs rfl
    (yonedaEquiv_symm_map_affineChartSpecPoint_pt B S hS W F V (s ≫ j)) _)
  rw [chartEval_map_affineChartSpecPoint_vectorBundleChart,
    ΓSpecIso_inv_comp_appTop_comp_vectorBundleChartZeroSection]

/-- **The inverse image of the zero locus over an affine chart.** The inverse image of
`o(W) ⊆ E` in `E ×_W V` is the closed subscheme cut out by the augmentation, the range of the
chart zero section `V ⟶ E ×_W V`. -/
theorem preimage_vectorBundleZeroLocus :
    (vectorBundleZeroLocus B S hS W F).1.preimage (vectorBundleChartToTotal B S hS W F V) =
      Subfunctor.range (yoneda.map (vectorBundleChartZeroSection B S hS W F V)) := by
  ext ⟨T⟩ t
  simp only [Subfunctor.preimage_obj, Set.mem_preimage, Subfunctor.range_obj, Set.mem_range]
  refine ⟨exists_comp_vectorBundleChartZeroSection_eq_of_mem B S hS W F V t, ?_⟩
  rintro ⟨s, rfl⟩
  exact vectorBundleChartToTotal_app_comp_vectorBundleChartZeroSection_mem B S hS W F V s

end AlgebraicGeometry.Space

end
