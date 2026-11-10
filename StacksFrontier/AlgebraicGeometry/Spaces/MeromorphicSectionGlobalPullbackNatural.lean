module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafModuleMap

/-!
# The global pullback of meromorphic sections is natural in the module

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined. The global map

`Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))`

of `AlgebraicGeometry.Space.pullbackMeromorphicSection` is natural in `M`: for a morphism
`φ : M ⟶ N` of sheaves of `𝒪_Y`-modules the square

`Γ(Y, 𝒦_Y(M)) → Γ(Y, 𝒦_Y(N))`, `Γ(X, 𝒦_X(f^*M)) → Γ(X, 𝒦_X(f^*N))`

commutes, the horizontal maps being
`AlgebraicGeometry.Space.meromorphicSectionSheafMap` at `φ` and at `f^*φ`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackUnitSection_naturality_module` and
  `AlgebraicGeometry.Space.modulePullbackChartFMap_naturality_module`: the chart component of the
  unit of the adjunction `f^* ⊣ f_*` is natural in the module.
* `AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_meromorphicSectionModuleMap`:
  the chartwise pullback of meromorphic sections is natural in the module.
* `AlgebraicGeometry.Space.pullbackMeromorphicSection_sectionsMap`: the global pullback of
  meromorphic sections is natural in the module.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Unit

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2}

/-- The unit section of a module pullback is natural in the module. -/
theorem modulePullbackUnitSection_naturality_module (φ : M ⟶ N)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : M.val.obj (op d.V)) :
    modulePullbackUnitSection B S hS f N d ((φ.val.app (op d.V)).hom s) =
      ((modulePullback B S hS f).map φ).val.app (op d.U)
        (modulePullbackUnitSection B S hS f M d s) := by
  have hunit := congrArg
    (fun a : M ⟶ (modulePushforward B S hS f).obj ((modulePullback B S hS f).obj N) =>
      a.val.app (op d.V) s) ((modulePullbackAdjunction B S hS f).unit.naturality φ)
  exact (congrArg (modulePushforwardCounitApp B S hS f
      ((modulePullback B S hS f).obj N) d) hunit).trans
    (modulePushforwardCounitApp_map B S hS f ((modulePullback B S hS f).map φ) d _)

/-- The chart component of the unit of the adjunction `f^* ⊣ f_*` is natural in the module. -/
theorem modulePullbackChartFMap_naturality_module (φ : M ⟶ N)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : M.val.obj (op d.V)) :
    (modulePullbackChartFMap B S hS f N).app d ((φ.val.app (op d.V)).hom s) =
      (((modulePullback B S hS f).map φ).val.app (op d.U)).hom
        ((modulePullbackChartFMap B S hS f M).app d s) := by
  have h : ∀ (P : Modules.{u, u} B S hS Y.1 Y.2) (t : P.val.obj (op d.V)),
      (modulePullbackChartFMap B S hS f P).app d t =
        modulePullbackUnitSection B S hS f P d t :=
    fun P t => modulePullbackHomFMap_app B S hS f P _ (𝟙 _) d t
  rw [h, h]
  exact modulePullbackUnitSection_naturality_module B S hS f φ d s

end Unit

section ChartRule

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (hf : PullbacksMeromorphicSections B S hS f.hom)

/-- The chartwise rule `m ⊗ a ↦ (f^*m) ⊗ (f^♯a)` for pullback of meromorphic sections commutes
with extension of scalars along `𝒪 ⟶ 𝒦` applied to `φ : M ⟶ N` on the source and to `f^*φ` on
the target. -/
theorem chartPullbackMeromorphicSectionsSheaf_meromorphicSectionModuleMap (φ : M ⟶ N)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (t : (meromorphicSectionModule B S hS Y.1 Y.2 M).obj (op d.V)) :
    chartPullbackMeromorphicSectionsSheaf B S hS f N hf d
        (((meromorphicSectionModuleMap B S hS Y.1 Y.2 φ).app (op d.V)).hom t) =
      ((meromorphicSectionModuleMap B S hS X.1 X.2
          ((modulePullback B S hS f).map φ)).app (op d.U)).hom
        (chartPullbackMeromorphicSectionsSheaf B S hS f M hf d t) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((congrArg (chartPullbackMeromorphicSectionsSheaf B S hS f N hf d)
          (map_add ((meromorphicSectionModuleMap B S hS Y.1 Y.2 φ).app (op d.V)).hom x y)).trans
        (map_add (chartPullbackMeromorphicSectionsSheaf B S hS f N hf d) _ _)).trans
      (((congrArg₂ (· + ·) hx hy).trans
          (map_add ((meromorphicSectionModuleMap B S hS X.1 X.2
            ((modulePullback B S hS f).map φ)).app (op d.U)).hom _ _).symm).trans
        (congrArg ((meromorphicSectionModuleMap B S hS X.1 X.2
            ((modulePullback B S hS f).map φ)).app (op d.U)).hom
          (map_add (chartPullbackMeromorphicSectionsSheaf B S hS f M hf d) x y).symm))
  | tmul a m =>
    exact (congrArg (chartPullbackMeromorphicSectionsSheaf B S hS f N hf d)
        (meromorphicSectionModuleMap_tmul B S hS Y.1 Y.2 φ d.V a m)).trans
      ((chartPullbackMeromorphicSectionsSheaf_tmul B S hS f N hf d a _).trans
        ((congrArg
            (fun z => chartMeromorphicPullbackHom B S hS f hf d a ⊗ₜ[
                chartRing B S hS X.1 X.2 d.U] z)
            (modulePullbackChartFMap_naturality_module B S hS f φ d m)).trans
          ((meromorphicSectionModuleMap_tmul B S hS X.1 X.2
              ((modulePullback B S hS f).map φ) d.U _ _).symm.trans
            (congrArg ((meromorphicSectionModuleMap B S hS X.1 X.2
                ((modulePullback B S hS f).map φ)).app (op d.U)).hom
              (chartPullbackMeromorphicSectionsSheaf_tmul B S hS f M hf d a m).symm))))

end ChartRule

section Global

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (hf : PullbacksMeromorphicSections B S hS f.hom)

/-- The global pullback of meromorphic sections is natural in the module, evaluated on the chart
of `X` of an affine commuting square. -/
theorem pullbackMeromorphicSection_eval_sectionsMap_chartDiagram (φ : M ⟶ N)
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj d.U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj d.V))) :
    (pullbackMeromorphicSection B S hS f N hf
          (SheafOfModules.sectionsMap
            (meromorphicSectionSheafMap B S hS Y.1 Y.2 φ) s)).eval (op d.U) =
      ((meromorphicSectionSheafMap B S hS X.1 X.2
            ((modulePullback B S hS f).map φ)).val.app (op d.U)).hom
        ((pullbackMeromorphicSection B S hS f M hf s).eval (op d.U)) := by
  obtain ⟨Ts, hTs, hTsrep⟩ := exists_eval_toMeromorphicSectionSheaf_sieve_mem B S hS Y.1 Y.2 M
    d.V (s.eval (op d.V))
  obtain ⟨n, d', a, κ, -, -, hκ, -, hcov⟩ :=
    exists_affine_chartDiagram_cover_of_sieve B S hS f d hU hV hTs
  refine meromorphicSectionSheaf_eq_of_cover B S hS X.1 X.2
    ((modulePullback B S hS f).obj N) d.U (fun i ↦ (d' i).U) a hcov _ _ fun i ↦ ?_
  obtain ⟨ts, hts⟩ := hTsrep (κ i) (hκ i)
  have hsV : s.eval (op (d' i).V) =
      toMeromorphicSectionSheaf B S hS Y.1 Y.2 M (d' i).V ts :=
    (hts.trans (PresheafOfModules.sections_property s (κ i).op)).symm
  have htV : (SheafOfModules.sectionsMap
        (meromorphicSectionSheafMap B S hS Y.1 Y.2 φ) s).eval (op (d' i).V) =
      toMeromorphicSectionSheaf B S hS Y.1 Y.2 N (d' i).V
        (((meromorphicSectionModuleMap B S hS Y.1 Y.2 φ).app (op (d' i).V)).hom ts) := by
    rw [eval_sectionsMap_meromorphicSectionSheafMap, hsV,
      meromorphicSectionSheafMap_toMeromorphicSectionSheaf]
  have hresL : ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2
          ((modulePullback B S hS f).obj N)).val.map (a i).op).hom
        ((pullbackMeromorphicSection B S hS f N hf
          (SheafOfModules.sectionsMap
            (meromorphicSectionSheafMap B S hS Y.1 Y.2 φ) s)).eval (op d.U)) =
      (pullbackMeromorphicSection B S hS f N hf
        (SheafOfModules.sectionsMap
          (meromorphicSectionSheafMap B S hS Y.1 Y.2 φ) s)).eval (op (d' i).U) :=
    PresheafOfModules.sections_property _ (a i).op
  have hresR : ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2
          ((modulePullback B S hS f).obj M)).val.map (a i).op).hom
        ((pullbackMeromorphicSection B S hS f M hf s).eval (op d.U)) =
      (pullbackMeromorphicSection B S hS f M hf s).eval (op (d' i).U) :=
    PresheafOfModules.sections_property _ (a i).op
  rw [hresL, ← PresheafOfModules.naturality_apply, hresR,
    pullbackMeromorphicSection_eval_chartDiagram B S hS f N hf _ (d' i) _ htV,
    pullbackMeromorphicSection_eval_chartDiagram B S hS f M hf s (d' i) ts hsV,
    meromorphicSectionSheafMap_toMeromorphicSectionSheaf,
    chartPullbackMeromorphicSectionsSheaf_meromorphicSectionModuleMap]

/-- The global pullback of meromorphic sections is natural in the module: for a morphism
`φ : M ⟶ N` of sheaves of `𝒪_Y`-modules the pullback of the image of a meromorphic section of
`M` under `𝒦_Y(φ)` is the image of the pullback of that section under `𝒦_X(f^*φ)`. -/
@[stacks 0ENC "the algebra of the part (1) map, which its construction leaves unasserted: \
the global map on meromorphic sections is natural in the module, for the action of the sheaf of \
meromorphic sections on morphisms of modules"]
theorem pullbackMeromorphicSection_sectionsMap (φ : M ⟶ N)
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M) :
    pullbackMeromorphicSection B S hS f N hf
        (SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS Y.1 Y.2 φ) s) =
      SheafOfModules.sectionsMap
        (meromorphicSectionSheafMap B S hS X.1 X.2 ((modulePullback B S hS f).map φ))
        (pullbackMeromorphicSection B S hS f M hf s) := by
  have key : ∀ U : SmallEtale B S hS X.1,
      (pullbackMeromorphicSection B S hS f N hf
            (SheafOfModules.sectionsMap
              (meromorphicSectionSheafMap B S hS Y.1 Y.2 φ) s)).eval (op U) =
        ((meromorphicSectionSheafMap B S hS X.1 X.2
              ((modulePullback B S hS f).map φ)).val.app (op U)).hom
          ((pullbackMeromorphicSection B S hS f M hf s).eval (op U)) := by
    intro U
    obtain ⟨I, W, b, d, hdU, hUaff, hVaff, hcov⟩ := exists_affine_chartDiagram_ofArrows B S hS f U
    refine meromorphicSectionSheaf_eq_of_cover B S hS X.1 X.2
      ((modulePullback B S hS f).obj N) U W b hcov _ _ fun i ↦ ?_
    have hresL : ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2
            ((modulePullback B S hS f).obj N)).val.map (b i).op).hom
          ((pullbackMeromorphicSection B S hS f N hf
            (SheafOfModules.sectionsMap
              (meromorphicSectionSheafMap B S hS Y.1 Y.2 φ) s)).eval (op U)) =
        (pullbackMeromorphicSection B S hS f N hf
          (SheafOfModules.sectionsMap
            (meromorphicSectionSheafMap B S hS Y.1 Y.2 φ) s)).eval (op (W i)) :=
      PresheafOfModules.sections_property _ (b i).op
    have hresR : ((meromorphicSectionSheaf.{u, u} B S hS X.1 X.2
            ((modulePullback B S hS f).obj M)).val.map (b i).op).hom
          ((pullbackMeromorphicSection B S hS f M hf s).eval (op U)) =
        (pullbackMeromorphicSection B S hS f M hf s).eval (op (W i)) :=
      PresheafOfModules.sections_property _ (b i).op
    have hd := pullbackMeromorphicSection_eval_sectionsMap_chartDiagram B S hS f hf φ s (d i)
      (by rw [hdU i]; exact hUaff i) (hVaff i)
    rw [hdU i] at hd
    rw [hresL, ← PresheafOfModules.naturality_apply, hresR]
    exact hd
  exact Subtype.ext (funext fun ⟨U⟩ => key U)

end Global

end AlgebraicGeometry.Space

end
