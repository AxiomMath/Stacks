module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartBaseChangeCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompCoherence

/-!
# The chart comparison of the direct image of modules is compatible with composition

`AlgebraicGeometry.Space.modulePushforwardChartIso` identifies, for a *representable* morphism
`f : X ⟶ Y` of algebraic spaces, the direct image of modules `f_*` of Stacks 03LU with the
concrete direct image `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` taken along base
change of étale scheme charts. These identifications compose: for representable `h : D ⟶ A` and
`g : A ⟶ C`, comparing the two direct images one factor at a time and then contracting the two
base-change direct images is the contraction `AlgebraicGeometry.Space.modulePushforwardCompIso` of
Stacks 03LU followed by the comparison below `h ≫ g`.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_chartModProj`: the comparison of
  the two direct images is `AlgebraicGeometry.Space.chartModProj` on sections.
* `AlgebraicGeometry.Space.modulePushforwardChartIso_comp`: **the chart comparisons of the
  direct image of modules compose**, as an equality of isomorphisms of functors.
* `AlgebraicGeometry.Space.modulePushforwardChartIso_comp_app`: the same at one module, as an
  equality of two composites of morphisms of sheaves of modules.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ChartPushforwardContraction

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {L : GrothendieckTopology E} {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.IsContinuous J K] [G.IsContinuous K L] [H.IsContinuous J L]
  [(F ⋙ G).IsContinuous J L]
  {R : Sheaf J RingCat.{w}} {R' : Sheaf K RingCat.{w}} {R'' : Sheaf L RingCat.{w}}

/-- **The contraction of an iterated direct image of sheaves of modules, on sections.** Let two
morphisms of ringed sites be composed and let `e` identify a third continuous functor with the
composite, compatibly with the structure maps. Then the contraction of the two direct images reads
a section over `W` as its restriction along the component of `e` at `W`. -/
theorem contraction_hom_app_val_app
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R')
    (ψ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{w} K L).obj R'')
    {χ : R ⟶ (H.sheafPushforwardContinuous RingCat.{w} J L).obj R''} (e : H ≅ F ⋙ G)
    (he : SheafOfModules.comparisonComp φ ψ ≫
      (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} J L).app R'' = χ)
    (M : SheafOfModules.{w} R'') (W : C) (s : M.val.obj (op (G.obj (F.obj W))))
    {c : H.obj W ⟶ G.obj (F.obj W)} (hc : e.hom.app W = c) :
    ((SheafOfModules.pushforwardComp.{w} φ ψ ≪≫
        SheafOfModules.pushforwardCongr₂.{w} _ e he).hom.app M).val.app (op W) s =
      M.val.map c.op s := by
  subst hc
  exact (Stacks.Sheaves.RingedToposModules.isoTrans_hom_app_val_app
      (SheafOfModules.pushforwardComp.{w} φ ψ)
      (SheafOfModules.pushforwardCongr₂.{w} _ e he) M (op W) s).trans
    ((Stacks.SectionsComponents.pushforwardCongr₂_hom_app_val_app _ e he M (op W) _).trans
      (congrArg (fun z => M.val.map (e.hom.app W).op z)
        (SheafOfModules.pushforwardComp_hom_app_val_app φ ψ M (op W) s)))

end Stacks.ChartPushforwardContraction

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison on sections, as a chart projection of modules -/

/-- **The chart comparison of the two direct images of modules is the chart projection of modules
on sections.** -/
theorem modulePushforwardChartIso_hom_app_chartModProj {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hrep : yoneda.relativelyRepresentable f.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (n : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    ((modulePushforwardChartIso B S hS f hrep).hom.app N).val.app (op V) n =
      chartModProj B S hS f hrep N V n :=
  (modulePushforwardChartIso_hom_app_chartSetProj B S hS f hrep N V n).trans
    (chartModProj_eq_chartSetProj B S hS f hrep N V n).symm

section Comp

variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite
  Stacks.SheafOfModules.Tensor.ringSheaf CategoryTheory.sheafCompose

/-! ### The contraction of the two base-change direct images -/

/-- **The contraction of the two base-change direct images.** Base change of charts along `g`
followed by base change along `h`, and base change along `h ≫ g`, give the same direct image of
modules: the two structure maps compose by
`AlgebraicGeometry.Space.smallBaseChangeSharp_comparisonComp` over the comparison
`AlgebraicGeometry.Space.smallBaseChangeChartCompIso` of the two base changes. -/
noncomputable abbrev smallBaseChangeChartPushforwardCompIso :
    smallBaseChangeModulePushforward.{u, u} B S hS h hreph ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS g hrepg ≅
      smallBaseChangeModulePushforward.{u, u} B S hS (h ≫ g) hrephg :=
  SheafOfModules.pushforwardComp.{u} (smallBaseChangeSharp B S hS g hrepg)
      (smallBaseChangeSharp B S hS h hreph) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _
      (smallBaseChangeChartCompIso B S hS h g hreph hrepg hrephg)
      (smallBaseChangeSharp_comparisonComp B S hS h g hreph hrepg hrephg)

/-! ### The composition coherence -/

/-- **The iterated chart projection, with the middle functor a variable.** Pushing a comparison `τ`
of the direct image along `h` forward along `g`, and then comparing the direct image along `g` with
base change, reads a section over an étale chart `V` of `C` as the value of `τ` on the chart
projection to `V ×_C A`. -/
theorem chartModProj_comp_chartIso (N : Modules.{u, u} B S hS D.1 D.2)
    (V : SmallEtale B S hS C.1)
    (x : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj N).val.obj (op V))
    {Φ : Modules.{u, u} B S hS D.1 D.2 ⥤ Modules.{u, u} B S hS A.1 A.2}
    (τ : modulePushforward B S hS h ≅ Φ)
    {s : (Φ.obj N).val.obj (op ((smallBaseChange B S hS g hrepg).obj V))}
    (hs : (τ.hom.app N).val.app (op ((smallBaseChange B S hS g hrepg).obj V))
        (chartModProj B S hS g hrepg ((modulePushforward B S hS h).obj N) V x) = s) :
    ((Functor.isoWhiskerLeft Φ (modulePushforwardChartIso B S hS g hrepg)).hom.app
          N).val.app (op V)
        (((Functor.isoWhiskerRight τ (modulePushforward B S hS g)).hom.app
          N).val.app (op V) x) = s :=
  ((modulePushforwardChartIso_hom_app_chartModProj B S hS g hrepg (Φ.obj N) V _).trans
    (chartModProj_map B S hS g hrepg (τ.hom.app N) V x)).trans hs

/-- **The route through the two chart comparisons, on sections.** Comparing the direct image along
`h`, then the direct image along `g`, and then contracting the two base-change direct images reads
a section over an étale chart `V` of `C` as its iterated chart projection, restricted along the
comparison `AlgebraicGeometry.Space.chartBaseChangeCompComparison` of `V ×_C D` with
`(V ×_C A) ×_A D`. -/
theorem chartIso_comp_contraction_val_app (N : Modules.{u, u} B S hS D.1 D.2)
    (V : SmallEtale B S hS C.1)
    (x : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj N).val.obj (op V)) :
    ((Functor.isoWhiskerRight (modulePushforwardChartIso B S hS h hreph)
              (modulePushforward B S hS g) ≪≫
            Functor.isoWhiskerLeft
              (smallBaseChangeModulePushforward.{u, u} B S hS h hreph)
              (modulePushforwardChartIso B S hS g hrepg) ≪≫
            smallBaseChangeChartPushforwardCompIso B S hS h g hreph hrepg hrephg).hom.app
        N).val.app (op V) x =
      N.val.map (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (chartModProj B S hS h hreph N ((smallBaseChange B S hS g hrepg).obj V)
          (chartModProj B S hS g hrepg ((modulePushforward B S hS h).obj N) V x)) := by
  have key := Stacks.ChartPushforwardContraction.contraction_hom_app_val_app
    (smallBaseChangeSharp B S hS g hrepg) (smallBaseChangeSharp B S hS h hreph)
    (smallBaseChangeChartCompIso B S hS h g hreph hrepg hrephg)
    (smallBaseChangeSharp_comparisonComp B S hS h g hreph hrepg hrephg)
    N V
    (chartModProj B S hS h hreph N ((smallBaseChange B S hS g hrepg).obj V)
      (chartModProj B S hS g hrepg ((modulePushforward B S hS h).obj N) V x))
    (smallBaseChangeChartCompIso_hom_app B S hS h g hreph hrepg hrephg V)
  have hs := chartModProj_comp_chartIso B S hS h g hrepg N V x
    (modulePushforwardChartIso B S hS h hreph)
    (modulePushforwardChartIso_hom_app_chartModProj B S hS h hreph N
      ((smallBaseChange B S hS g hrepg).obj V)
      (chartModProj B S hS g hrepg ((modulePushforward B S hS h).obj N) V x))
  rw [Stacks.Sheaves.RingedToposModules.isoTrans_hom_app_val_app,
    Stacks.Sheaves.RingedToposModules.isoTrans_hom_app_val_app, hs]
  exact key

/-- **The route through the contraction of Stacks 03LU, on sections.** Contracting the two direct
images of Stacks 03LU and then comparing with base change along `h ≫ g` reads a section over an
étale chart `V` of `C` as the same restricted iterated chart projection. -/
theorem modulePushforwardCompIso_comp_chartIso_val_app (N : Modules.{u, u} B S hS D.1 D.2)
    (V : SmallEtale B S hS C.1)
    (x : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj N).val.obj (op V)) :
    ((modulePushforwardCompIso B S hS h g ≪≫
          modulePushforwardChartIso B S hS (h ≫ g) hrephg).hom.app N).val.app (op V) x =
      N.val.map (chartBaseChangeCompComparison B S hS h g hreph hrepg hrephg V).op
        (chartModProj B S hS h hreph N ((smallBaseChange B S hS g hrepg).obj V)
          (chartModProj B S hS g hrepg ((modulePushforward B S hS h).obj N) V x)) :=
  (Stacks.Sheaves.RingedToposModules.isoTrans_hom_app_val_app
      (modulePushforwardCompIso B S hS h g)
      (modulePushforwardChartIso B S hS (h ≫ g) hrephg) N (op V) x).trans
    ((modulePushforwardChartIso_hom_app_chartModProj B S hS (h ≫ g) hrephg N V _).trans
      (chartModProj_modulePushforwardCompIso B S hS h g hreph hrepg hrephg N V x))

/-- **The chart comparisons of the direct images compose, on sections.** Both routes read a section
of the twice-pushed-forward module over an étale chart `V` of `C` as its iterated chart projection,
restricted along the comparison `AlgebraicGeometry.Space.chartBaseChangeCompComparison` of
`V ×_C D` with `(V ×_C A) ×_A D`. -/
theorem modulePushforwardChartIso_comp_val_app (N : Modules.{u, u} B S hS D.1 D.2)
    (V : SmallEtale B S hS C.1)
    (x : ((modulePushforward B S hS h ⋙ modulePushforward B S hS g).obj N).val.obj (op V)) :
    ((Functor.isoWhiskerRight (modulePushforwardChartIso B S hS h hreph)
              (modulePushforward B S hS g) ≪≫
            Functor.isoWhiskerLeft
              (smallBaseChangeModulePushforward.{u, u} B S hS h hreph)
              (modulePushforwardChartIso B S hS g hrepg) ≪≫
            smallBaseChangeChartPushforwardCompIso B S hS h g hreph hrepg hrephg).hom.app
        N).val.app (op V) x =
      ((modulePushforwardCompIso B S hS h g ≪≫
          modulePushforwardChartIso B S hS (h ≫ g) hrephg).hom.app N).val.app (op V) x :=
  (chartIso_comp_contraction_val_app B S hS h g hreph hrepg hrephg N V x).trans
    (modulePushforwardCompIso_comp_chartIso_val_app B S hS h g hreph hrepg hrephg N V x).symm

/-- **The chart comparison of the direct image of modules is compatible with composition.** For
representable morphisms `h : D ⟶ A` and `g : A ⟶ C` of algebraic spaces, comparing the direct image
of Stacks 03LU with the direct image along base change of étale scheme charts one factor at a time
and then contracting the two base-change direct images is the contraction
`AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU followed by the comparison below
`h ≫ g`. -/
theorem modulePushforwardChartIso_comp :
    Functor.isoWhiskerRight (modulePushforwardChartIso B S hS h hreph)
          (modulePushforward B S hS g) ≪≫
        Functor.isoWhiskerLeft (smallBaseChangeModulePushforward.{u, u} B S hS h hreph)
          (modulePushforwardChartIso B S hS g hrepg) ≪≫
        smallBaseChangeChartPushforwardCompIso B S hS h g hreph hrepg hrephg =
      modulePushforwardCompIso B S hS h g ≪≫
        modulePushforwardChartIso B S hS (h ≫ g) hrephg :=
  Iso.ext (NatTrans.ext (funext fun N =>
    Stacks.ChartUnitTransport.hom_ext_val_app_apply_unop fun V x =>
      modulePushforwardChartIso_comp_val_app B S hS h g hreph hrepg hrephg N V x))

/-- **The chart comparison of the direct image of modules is compatible with composition, at one
module.** The two composites of morphisms of sheaves of modules on the small étale site of `C`
agree at `N`. -/
theorem modulePushforwardChartIso_comp_app (N : Modules.{u, u} B S hS D.1 D.2) :
    (modulePushforward B S hS g).map
          ((modulePushforwardChartIso B S hS h hreph).hom.app N) ≫
        (modulePushforwardChartIso B S hS g hrepg).hom.app
          ((smallBaseChangeModulePushforward.{u, u} B S hS h hreph).obj N) ≫
        (smallBaseChangeChartPushforwardCompIso B S hS h g hreph hrepg hrephg).hom.app N =
      (modulePushforwardCompIso B S hS h g).hom.app N ≫
        (modulePushforwardChartIso B S hS (h ≫ g) hrephg).hom.app N :=
  NatTrans.congr_app (congrArg Iso.hom
    (modulePushforwardChartIso_comp B S hS h g hreph hrepg hrephg)) N

end Comp

end AlgebraicGeometry.Space

end
