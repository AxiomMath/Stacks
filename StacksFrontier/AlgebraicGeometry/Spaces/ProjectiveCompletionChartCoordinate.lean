module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartQuotientReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsSchemeReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionAffinePartChartReading

/-!
# The coordinates of `U ×_X V ⟶ E ×_X V`

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module, `U` the affine part of the
projective completion `P = 𝐏(ℰ ⊕ 𝒪_X)`, `q : u^*ℰ ⟶ 𝒪_U` the map `m ↦ (m, 0)/s`, and `V` an affine
étale chart of `X` with a morphism `m` to the presenting chart, on which `ℰ` is free. The value of
`q` on the inverse image of a section `e` of `ℰ` over `V`, at the chart `A = U ×_X V` of `U`, is
the coordinate `λ(σ'(e))/λ(σ)` of the open immersion `A ⟶ 𝐏((ℰ ⊕ 𝒪)|_V)` of
`Stacks.RelativeProj.UnitSplitting.splitCoordVector` (Stacks 0ERW, proof).

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace AlgebraicGeometry.Space

/-! ### Values of a map to the structure sheaf at a chart, read on the scheme -/

section Values

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2)
  (hN : N.IsQuasicoherentOnSite) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
  (w : representedSpaceMap B S hS d.g ≫ chartToSpace B S hS Y d.V =
    chartToSpace B S hS X d.U ≫ f)


/-- A section of the reading of `f^*N`, in the spelling of the readings of morphisms. -/
abbrev readingSectionCast (z : Γ(schemeReading ((modulePullback B S hS f).obj N)
    (chartToSpace B S hS X d.U), ⊤)) :
    Γ((SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj (chartFppfObject B S hS X d.U))
            (chartFppfObject B S hS X d.U).left.property).obj
            ((representedSmallEtaleModuleEquivalence B S hS
                (chartFppfObject B S hS X d.U)).inverse.obj
              ((modulePullback B S hS (chartToSpace B S hS X d.U)).obj
                ((modulePullback B S hS f).obj N))), ⊤) := z

/-- Applying the reading of a morphism to two equal sections, one of them cast. -/
theorem reading_app_eq_of_eq {O' : Modules.{u, u} B S hS X.1 X.2}
    (φ : (modulePullback B S hS f).obj N ⟶ O')
    (x y : Γ(schemeReading ((modulePullback B S hS f).obj N) (chartToSpace B S hS X d.U), ⊤))
    (h : x = y) :
    ((SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj (chartFppfObject B S hS X d.U))
            (chartFppfObject B S hS X d.U).left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS
              (chartFppfObject B S hS X d.U)).inverse.map
            ((modulePullback B S hS (chartToSpace B S hS X d.U)).map φ))).app ⊤ x =
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj (chartFppfObject B S hS X d.U))
            (chartFppfObject B S hS X d.U).left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS
              (chartFppfObject B S hS X d.U)).inverse.map
            ((modulePullback B S hS (chartToSpace B S hS X d.U)).map φ))).app ⊤
        (readingSectionCast f N d y) := by
  subst h
  rfl

end Values

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

/-! ### The coordinates of `φ : U ×_X V ⟶ E ×_X V` on the generators of `Sym(ℰ)` -/

section Generators

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]
    {V : SmallEtale B S hS X.1} (m : V ⟶ bundleBaseChart X) [IsAffine (chartScheme V)]

/-- The chart reading of the point of the relative spectrum given by a point `t ∈ Y(T)`. -/
theorem relativeSpecLiftPoint_chartEval {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS} (y : Y ⟶ X)
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (β : A ⟶ pushforwardAlgebra B S hS (Over.mk y))
    (V : SmallEtale B S hS X.1) {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (t : Y.1.obj (Opposite.op T))
    (h : yonedaEquiv.symm (y.hom.app (Opposite.op T) t) = yoneda.map v ≫ V.obj.hom) :
    (relativeSpecLiftPoint B S hS y β T t).chartEval B S hS V v h =
      chartEval B S hS A V v (y.hom.app (Opposite.op T) t) h
        (compPushforwardAlgebraMap B S hS β (pointOverOfPoint B S hS y T t)) :=
  rfl

/-- The identity of an object of the site acts as the identity on global functions. -/
theorem toScheme_map_id_appTop_apply {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (T : BigFppfOver B S hS) (z : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (𝟙 T)).appTop z = z := by
  rw [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]
    [IsAffine (chartScheme V)] in
/-- The chart diagram `U_V ⟶ V` over `u : U ⟶ X`. -/
theorem affinePartChartOverChart_comm :
    (affinePartChartOverChart E hr m).1.hom ≫ (projectiveCompletionAffinePartProj E hr).hom =
      yoneda.map (projectiveCompletionAffinePartOverChartToChart E hr m) ≫ V.1.hom :=
  (isPullback_projectiveCompletionAffinePart_toChart E hr m).w

/-- **The coordinate of `φ` attached to a section `x` of `ℰ` over `V`** is the value of
`q : u^*ℰ ⟶ 𝒪_U` on the inverse image of `x` at the chart `U_V` of `U`. -/
theorem appTop_projectiveCompletionAffinePartChartToVectorBundleChart_gen
    (x : E.val.obj (Opposite.op V)) :
    ((Scheme.ΓSpecIso ((symmetricAlgebraSheaf B S hS X E).right.obj.obj (Opposite.op V))).inv ≫
      ((BigFppfOver.toScheme B S hS).map
        (projectiveCompletionAffinePartChartToVectorBundleChart E hr m)).appTop)
      ((symmetricAlgebra B S hS X E).ungradedIncl 1
        ((symmetricAlgebraGen B S hS X E).val.app (Opposite.op V) x)) =
      (projectiveCompletionAffinePartQuotient E hr
          (isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom E
            hr)).val.app (Opposite.op (affinePartChartOverChart E hr m))
        (modulePullbackChartSection B S hS (projectiveCompletionAffinePartProj E hr) E
          ⟨affinePartChartOverChart E hr m, V,
            projectiveCompletionAffinePartOverChartToChart E hr m,
            affinePartChartOverChart_comm E hr m⟩ x) := by
  set hs := isIso_modulePullback_projectiveCompletionAffinePartHom_projectiveCompletionSectionHom
    E hr with hs_def
  set φ₀ := projectiveCompletionAffinePartChartToVectorBundleChart E hr m with hφ₀
  set t : (projectiveCompletionAffinePart E hr).1.obj
      (Opposite.op (projectiveCompletionAffinePartOverChart E hr m)) :=
    (projectiveCompletionAffinePartOverChartToAffinePart E hr m).app _ (𝟙 _) with ht
  have hu : yonedaEquiv.symm t = yoneda.map (𝟙 (projectiveCompletionAffinePartOverChart E hr m)) ≫
      (affinePartChartOverChart E hr m).obj.hom := by
    refine (Equiv.symm_apply_apply yonedaEquiv
      (projectiveCompletionAffinePartOverChartToAffinePart E hr m)).trans ?_
    rw [CategoryTheory.Functor.map_id]
    exact (Category.id_comp _).symm
  have hBR := chartEval_projectiveCompletionAffinePartAlgebraMap_gen E hr hs t
    (Uc := affinePartChartOverChart E hr m) (𝟙 _)
    (projectiveCompletionAffinePartOverChartToChart E hr m) hu
    (affinePartChartOverChart_comm E hr m) x
  have htot : (vectorBundleChartToTotal B S hS X
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V).app _ φ₀ =
      (projectiveCompletionAffinePartToVectorBundle E hr hs).hom.app _ t := by
    have e := congrArg
      (fun k => k.app (Opposite.op (projectiveCompletionAffinePartOverChart E hr m)) (𝟙 _))
      (yoneda_map_projectiveCompletionAffinePartChartToVectorBundleChart_toTotal E hr m)
    simpa using e
  have hex := @exists_chartEval_symmetricAlgebraSheaf_eq B S hS X
    (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) _ V
  have hpt := (relativeSpecPointsEquiv_affineChartSpecToPoints_app B S hS _ _ V hex φ₀).symm.trans
    ((congrArg _ htot).trans
      (relativeSpecPointsEquiv_projectiveCompletionAffinePartToVectorBundle_app E hr hs t))
  have hv : φ₀ ≫ vectorBundleChartHom B S hS X
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V =
      𝟙 _ ≫ projectiveCompletionAffinePartOverChartToChart E hr m := by
    rw [Category.id_comp]
    exact projectiveCompletionAffinePartChartToVectorBundleChart_comp_hom E hr m
  have h1 := affineChartSpecPoint_map_chartEval B S hS _ _ V hex φ₀
  have h' := yonedaEquiv_symm_app_eq_of_chart B S hS (projectiveCompletionAffinePartProj E hr) t
    (Uc := affinePartChartOverChart E hr m) (V := V) (𝟙 _)
    (projectiveCompletionAffinePartOverChartToChart E hr m) hu
    (affinePartChartOverChart_comm E hr m)
  have hh : yonedaEquiv.symm ((affineChartSpecPoint B S hS _ _ V hex).map B S hS φ₀).pt =
      yoneda.map (φ₀ ≫ vectorBundleChartHom B S hS X
        (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V) ≫ V.obj.hom := by
    rw [hpt, hv]; exact h'
  have e1 := RelativeSpecPoint.chartEval_congr B S hS V hv hpt hh h'
  set z := (symmetricAlgebra B S hS X E).ungradedIncl 1
    ((symmetricAlgebraGen B S hS X E).val.app (Opposite.op V) x) with hz
  have e2 := congrArg (fun F => F z) ((h1 hh).symm.trans e1)
  have e3 := congrArg (fun F => F z)
    (relativeSpecLiftPoint_chartEval (projectiveCompletionAffinePartProj E hr)
      (projectiveCompletionAffinePartAlgebraMap E hr hs) V _ t h')
  refine e2.trans (e3.trans (hBR.trans ?_))
  exact toScheme_map_id_appTop_apply _ _

end Generators

end AlgebraicGeometry.Space

end
