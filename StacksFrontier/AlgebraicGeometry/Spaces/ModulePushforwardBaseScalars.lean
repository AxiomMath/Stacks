module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.BaseIdealMultiple
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear

/-!
# The direct image of modules commutes with multiplication by scalars of the base

Let `A` be a ring and `f : X ⟶ Y` a morphism of algebraic spaces over `Spec A`.  Every element
`a ∈ A` is a global function on `X` and on `Y`, by pulling it back along the structure morphisms
of the étale charts (`AlgebraicGeometry.Space.baseRingHom`), and so acts on every `𝒪_X`-module
and on every `𝒪_Y`-module.  The direct image `f_*` carries multiplication by `a` on an
`𝒪_X`-module `𝓕` to multiplication by `a` on `f_*𝓕`.

The sections of `f_*𝓕` over an étale chart `V` of `Y` are the limit of the sections of `𝓕` over
the étale charts of `X` above `X ×_Y V`, and the chart projections of that limit carry the scalar
action through the structure map `f♯` to the action of the pullbacks of functions on `V`.  The
pullback of `a` along a chart of `Y` and then along the induced morphism of charts is the pullback
of `a` along the composite, which is the structure morphism of the chart of `X`, all morphisms of
charts being morphisms over `Spec A`.

## Main results

* `AlgebraicGeometry.Space.moduleChartProjection_smul`: the chart projections of the sections of
  a direct image are semilinear over the pullback of functions along the induced morphism of
  charts.
* `AlgebraicGeometry.Space.chartPullback_baseRingHom`: the pullback along a morphism of charts of
  a scalar of the base, read on the target, is that scalar read on the source.
* `AlgebraicGeometry.Space.modulePushforward_map_globalSmul_baseRingHom`: `f_*` carries
  multiplication by `a ∈ A` to multiplication by `a`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The chart projections of a direct image are semilinear.**  For an étale chart `V` of `Y`
and an étale chart of `X` above `X ×_Y V`, the projection of the sections of `f_*𝓕` over `V` to
the sections of `𝓕` over that chart carries the action of a function `r` on `V` to the action of
its pullback along the induced morphism of charts. -/
theorem moduleChartProjection_smul (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op V))
    (x : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) (r • x) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
            j.right from chartPullbackRingHom B S hS f V j r) •
        (show F.val.obj j.right from
          (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) x) := by
  have hP : PreservesFiniteProducts (smallEtaleDirectImage B S hS f ⋙
      sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)) := inferInstance
  have hQ : PreservesFiniteProducts
      (sectionsFunctor.{u} (SmallEtale.topology B S hS X.1) j.right) := inferInstance
  have hR : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget RingCat.{u}) := inferInstance
  have hA : (SmallEtale.topology B S hS X.1).HasSheafCompose
      (forget AddCommGrpCat.{u}) := inferInstance
  refine Eq.trans (@moduleSMulObj_naturality _ _ _ hR hA
    (structureRingSheaf B S hS X) F _ hP _ hQ (moduleChartProjection B S hS f V j)
    (show ((smallEtaleDirectImage B S hS f ⋙
        sectionsFunctor.{u} (SmallEtale.topology B S hS Y.1) (op V)).obj
      (structureSetSheaf B S hS X)) from
      ((structureSharp B S hS f).hom.app (op V)).hom r) x) ?_
  rw [moduleChartProjection_app_structureSharp]
  exact sectionsFunctor_map_moduleSMulHom (structureRingSheaf B S hS X) F j.right
    (chartPullback B S hS f V j r)
    ((moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) x)

/-- The chart projections of a direct image are natural in the module. -/
theorem moduleChartProjection_modulePushforward_map (f : X ⟶ Y)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ F') (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    (moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F')
        (((modulePushforward B S hS f).map φ).val.app (op V) x) =
      φ.val.app j.right ((moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X F) x) :=
  Functor.natTrans_app_map_apply (moduleChartProjection B S hS f V j)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map φ) x

/-- **A pulled-back function pulls back to the pulled-back function.**  For `f : X ⟶ Y`,
`h : Y ⟶ T` with `T` an object of the site and `x` a function on `T`, pulling the function
`h^♯ x` on an étale chart `V` of `Y` back along the morphism of charts induced by an étale chart
of `X` above `X ×_Y V` gives `(f ≫ h)^♯ x` on that chart. -/
theorem chartPullback_pullbackToGlobalFunctions (f : X ⟶ Y) {T : BigFppfOver B S hS}
    (h : Y ⟶ schemeSpace T) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    chartPullback B S hS f V j ((pullbackToGlobalFunctions B S hS Y T h x).1 (op V)) =
      (pullbackToGlobalFunctions B S hS X T (f ≫ h) x).1 j.right := by
  have hcomm := (chartDiagramOfIndex B S hS f V j).comm
  have hg : chartBaseChangeMap B S hS f V j ≫ yoneda.preimage (V.1.hom ≫ h.hom) =
      yoneda.preimage (j.right.unop.1.hom ≫ (f ≫ h).hom) := by
    refine yoneda.map_injective ?_
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
    have hc : j.right.unop.1.hom ≫ f.hom =
        yoneda.map (chartBaseChangeMap B S hS f V j) ≫ V.1.hom := hcomm
    exact ((congrArg (· ≫ h.hom) hc).trans (Category.assoc _ _ _)).symm
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f V j)).op)
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (V.1.hom ≫ h.hom))).op) x) =
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (j.right.unop.1.hom ≫ (f ≫ h).hom))).op) x
  rw [← hg, Functor.map_comp, op_comp, Functor.map_comp]
  rfl

/-- The direct image carries multiplication by a global function `s` on `X` to multiplication by
a global function `t` on `Y`, once `t` pulls back to `s` along every morphism of charts. -/
private theorem modulePushforward_map_globalSmul_of_chartPullback (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (s : Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (t : Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (h : ∀ (V : SmallEtale B S hS Y.1)
      (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op),
      chartPullback B S hS f V j (t.1 (op V)) = s.1 j.right) :
    (modulePushforward B S hS f).map (Stacks.Cohomology.SiteModules.globalSmul _ s F) =
      Stacks.Cohomology.SiteModules.globalSmul _ t ((modulePushforward B S hS f).obj F) := by
  ext V y
  refine moduleChartProjection_ext B S hS f V.unop (moduleSetSheaf B S hS X F) (fun j => ?_)
  refine (moduleChartProjection_modulePushforward_map B S hS f _ V.unop j y).trans ?_
  refine Eq.trans ?_ (moduleChartProjection_smul B S hS f F V.unop j _ y).symm
  exact congrArg (fun r => HSMul.hSMul
    (α := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj j.right)
    (β := F.val.obj j.right) (γ := F.val.obj j.right) r
    ((moduleChartProjection B S hS f V.unop j).app (moduleSetSheaf B S hS X F) y))
    (h V.unop j).symm

/-- **The direct image commutes with multiplication by pulled-back functions.**  For
`f : X ⟶ Y`, `h : Y ⟶ T` with `T` an object of the site, an `𝒪_X`-module `𝓕` and a function `x`
on `T`, the direct image of multiplication by `(f ≫ h)^♯ x` on `𝓕` is multiplication by
`h^♯ x` on `f_*𝓕`. -/
theorem modulePushforward_map_globalSmul_pullbackToGlobalFunctions (f : X ⟶ Y)
    {T : BigFppfOver B S hS} (h : Y ⟶ schemeSpace T) (F : Modules.{u, u} B S hS X.1 X.2)
    (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (modulePushforward B S hS f).map
        (Stacks.Cohomology.SiteModules.globalSmul
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
          (pullbackToGlobalFunctions B S hS X T (f ≫ h) x) F) =
      Stacks.Cohomology.SiteModules.globalSmul
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
        (pullbackToGlobalFunctions B S hS Y T h x) ((modulePushforward B S hS f).obj F) := by
  exact modulePushforward_map_globalSmul_of_chartPullback B S hS f F _ _
    (fun V j => chartPullback_pullbackToGlobalFunctions B S hS f h V j x)

end General

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    {X Y : AlgebraicSpaces B (Spec (.of A)) hA}

/-- **A scalar of the base pulls back to itself.**  Pulling the function `a` on an étale chart `V`
of `Y` back along the morphism of charts induced by an étale chart of `X` above `X ×_Y V` gives
the function `a` on that chart, because the morphism of charts is a morphism over `Spec A`. -/
theorem chartPullback_baseRingHom (f : X ⟶ Y) (V : SmallEtale B (Spec (.of A)) hA Y.1)
    (j : StructuredArrow (op (chartBaseChange B (Spec (.of A)) hA f V))
      (comparisonFunctor B (Spec (.of A)) hA X).op) (a : A) :
    chartPullback B (Spec (.of A)) hA f V j ((baseRingHom A B hA Y.1 Y.2 a).1 (op V)) =
      (baseRingHom A B hA X.1 X.2 a).1 j.right := by
  have hw := Over.w (chartBaseChangeMap B (Spec (.of A)) hA f V j)
  show (Scheme.Γ.map (B.inclusion.map (chartBaseChangeMap B (Spec (.of A)) hA f V j).left).op)
      (((Scheme.ΓSpecIso (.of A)).inv ≫
        Scheme.Γ.map ((B.inclusion.map
          ((SmallEtale.toOver B (Spec (.of A)) hA Y.1).obj V).hom).op)).hom a) =
    ((Scheme.ΓSpecIso (.of A)).inv ≫ Scheme.Γ.map ((B.inclusion.map
      ((SmallEtale.toOver B (Spec (.of A)) hA X.1).obj j.right.unop).hom).op)).hom a
  rw [← hw, Functor.map_comp, op_comp, Functor.map_comp]
  rfl

/-- **The direct image commutes with multiplication by scalars of the base.**  For a morphism
`f : X ⟶ Y` of algebraic spaces over `Spec A`, an `𝒪_X`-module `𝓕` and `a ∈ A`, the direct image
of multiplication by `a` on `𝓕` is multiplication by `a` on `f_*𝓕`. -/
theorem modulePushforward_map_globalSmul_baseRingHom (f : X ⟶ Y)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (a : A) :
    (modulePushforward B (Spec (.of A)) hA f).map
        (Stacks.Cohomology.SiteModules.globalSmul
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O))
          (baseRingHom A B hA X.1 X.2 a) F) =
      Stacks.Cohomology.SiteModules.globalSmul
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA Y.1 Y.2).O))
        (baseRingHom A B hA Y.1 Y.2 a) ((modulePushforward B (Spec (.of A)) hA f).obj F) := by
  exact modulePushforward_map_globalSmul_of_chartPullback B (Spec (.of A)) hA f F _ _
    (fun V j => chartPullback_baseRingHom A B hA f V j a)

end AlgebraicGeometry.Space

end
