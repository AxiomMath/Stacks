module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartProjectionSpellingAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCounitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutQuotientSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecLiftOfAlgebraHom

/-!
# Reading a morphism into a direct image at a represented point

Let `y : Y ⟶ X` be a morphism of algebraic spaces, `𝒜` a sheaf of `𝒪_X`-algebras and
`β : 𝒜 ⟶ y_* 𝒪_Y` a morphism of algebras; it gives the morphism `Y ⟶ \underline{Spec}_X(𝒜)` of
`AlgebraicGeometry.Space.relativeSpecLift`, whose value at a point `t ∈ Y(T)` is `β` followed by
the map of direct images `y_* 𝒪_Y ⟶ (y ∘ t)_* 𝒪_T` that `t` induces.  This file reads that point
at an étale chart `V` of `X` (`AlgebraicGeometry.Space.chartEval`), when `t` factors through an
étale chart `U` of `Y` along `u : T ⟶ U` and `U` lies over `V`: the reading is `β` at `V`, then the
chart projection of `y_* 𝒪_Y` to `U`, then pullback along `u`.  For `β` built from the adjunct
`ℰ ⟶ y_* 𝒪_Y` of a morphism `q : y^* ℰ ⟶ 𝒪_Y`, the chart projection of the value on a section `e`
of `ℰ` is `q` applied to the section of `y^* ℰ` over `U` that `e` gives
(`AlgebraicGeometry.Space.modulePullbackChartSection`): **the space-level adjunct, read at a
chart, is the scheme-level adjunct of the reading.**  No representability of `y` is assumed.

## Main results

* `AlgebraicGeometry.Space.chartEval_compPushforwardAlgebraMap_pointOverOfPoint_apply`: the chart
  reading of the point given by `β` at a represented point.
* `AlgebraicGeometry.Space.directImageChartProjection_homEquiv_comp_eqToHom`: the chart projection
  of the adjunct of `q`.
* `AlgebraicGeometry.Space.chartEval_compPushforwardAlgebraMap_pointOverOfPoint_of_homEquiv`: the
  two combined.

## Implementation notes

Two spellings are converted slowly by the unifier and the kernel, and the statements are arranged
so that each conversion happens once: the direct-image algebra `pushforwardAlgebra (Over.mk y)`
against `pushforwardCommRingFunctor … (smallEtaleRingedTopos Y).O`, and the field `d.V` of a chart
diagram written as `⟨U, V, g, hg⟩` against `V`.  In `drake --heartbeats` units (statement, proof
and kernel check counted together; Lean limits them separately) the heaviest declarations are
`directImageChartProjection_pushforwardRingMap_of_chart` (about 120% of the default
`maxHeartbeats`), `directImageChartProjection_homEquiv_comp_eqToHom` (about 93%) and
`modulePushforwardCounitApp_unit_val_app` (about 84%); all pass at the default limit.  Sections of
modules are indexed by objects of `(smallEtaleRingedSite …).C`, and the helper lemmas here take
their object of the site in that type: stated over `SmallEtale …` instead, their instances cost an
expensive conversion.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

attribute [local implicit_reducible] AlgebraicGeometry.Space.pushforwardAlgebra
  AlgebraicGeometry.Space.AlgebraSheaf.ofHom

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section PointChart

variable {X : AlgebraicSpaces B S hS}

/-- The commutativity of the chart diagram of a point `x ∈ X(T)` read at the identity chart of
`T`. -/
theorem idEtaleChart_hom_comp_specPointOver (V : SmallEtale B S hS X.1)
    {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom) :
    (idEtaleChart B S hS T).1.hom ≫ (specPointOver B S hS T x).hom.hom =
      yoneda.map v ≫ V.1.hom :=
  (Category.id_comp _).trans hxv

/-- The morphism of charts from the identity chart of `T` to the base-changed chart `T ×_X V`,
out of the initial index, is the graph of `v`. -/
theorem toOver_map_initial_to_eq_chartGraph (V : SmallEtale B S hS X.1)
    {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom) :
    ((smallBaseChangeIndex_isInitial B S hS (specPointOver B S hS T x).hom
        (relativelyRepresentable_specPointOver B S hS T x) V).to
      (indexOfChartDiagram B S hS (specPointOver B S hS T x).hom
        ⟨idEtaleChart B S hS T, V, v,
          idEtaleChart_hom_comp_specPointOver B S hS V v x hxv⟩)).right.unop.hom.left =
      chartGraph B S hS V v x hxv := by
  set φ := (smallBaseChangeIndex_isInitial B S hS (specPointOver B S hS T x).hom
      (relativelyRepresentable_specPointOver B S hS T x) V).to
    (indexOfChartDiagram B S hS (specPointOver B S hS T x).hom
      ⟨idEtaleChart B S hS T, V, v, idEtaleChart_hom_comp_specPointOver B S hS V v x hxv⟩)
  have hsnd : v = φ.right.unop.hom.left ≫
      (relativelyRepresentable_specPointOver B S hS T x).snd V.1.hom :=
    (chartBaseChangeMap_indexOfChartDiagram B S hS (specPointOver B S hS T x).hom
        ⟨idEtaleChart B S hS T, V, v,
          idEtaleChart_hom_comp_specPointOver B S hS V v x hxv⟩).symm.trans
      ((chartBaseChangeMap_comp B S hS (specPointOver B S hS T x).hom V φ).trans
        (congrArg (fun k => φ.right.unop.hom.left ≫ k)
          (chartBaseChangeMap_smallBaseChangeIndex B S hS (specPointOver B S hS T x).hom
            (relativelyRepresentable_specPointOver B S hS T x) V)))
  refine (relativelyRepresentable_specPointOver B S hS T x).hom_ext ?_ ?_
  · exact (CostructuredArrow.w φ.right.unop.hom).trans (chartGraph_fst B S hS V v x hxv).symm
  · exact hsnd.symm.trans (chartGraph_snd B S hS V v x hxv).symm

/-- `AlgebraicGeometry.Space.pointSectionsIso` is the chart projection of `x_* 𝒪_T` to the
base-changed chart `T ×_X V`. -/
theorem pointSectionsIso_hom_apply (T : BigFppfOver B S hS) (x : X.1.obj (op T))
    (V : SmallEtale B S hS X.1)
    (w : (pushforwardAlgebra B S hS (specPointOver B S hS T x)).right.obj.obj (op V)) :
    (pointSectionsIso B S hS T x V).hom w =
      (directImageChartProjection B S hS (specPointOver B S hS T x).hom V
          (chartBaseChangeArrow B S hS (specPointOver B S hS T x).hom
            (relativelyRepresentable_specPointOver B S hS T x) V)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS (specPointOver B S hS T x).left).O) w :=
  (Sheaf.hom_congr_app_apply (smallEtaleRingedToposHom_representableRing_forget B S hS
      (specPointOver B S hS T x).hom (relativelyRepresentable_specPointOver B S hS T x)
      (smallEtaleRingedTopos B S hS (specPointOver B S hS T x).left).O) (op V) w).trans
    (directImageChartProjection_smallEtaleRingedToposHom_representable B S hS
      (specPointOver B S hS T x).hom (relativelyRepresentable_specPointOver B S hS T x)
      ((sheafCompose _ (forget CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS (specPointOver B S hS T x).left).O) V w)

/-- The chart reading on a section: `α` at `V`, then `AlgebraicGeometry.Space.pointSectionsIso`,
then pullback along the graph. -/
theorem chartEval_apply (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    (α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)) (a : A.right.obj.obj (op V)) :
    chartEval B S hS A V v x hxv α a =
      ((BigFppfOver.toScheme B S hS).map (chartGraph B S hS V v x hxv)).appTop
        ((pointSectionsIso B S hS T x V).hom (α.right.hom.app (op V) a)) :=
  rfl

/-- The component of `compPushforwardAlgebraMap α f` at a chart, on a section. -/
theorem compPushforwardAlgebraMap_right_app_apply {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {P Q : Over X} (α : A ⟶ pushforwardAlgebra B S hS P) (f : Q ⟶ P)
    (V : SmallEtale B S hS X.1) (a : A.right.obj.obj (op V)) :
    (compPushforwardAlgebraMap B S hS α f).right.hom.app (op V) a =
      (pushforwardRingMap B S hS f).hom.app (op V) (α.right.hom.app (op V) a) := by
  rw [compPushforwardAlgebraMap_right_app, CommRingCat.comp_apply]

/-- **The sections of `x_* 𝒪_T` over `V`, read on `T` along the graph of `v`, are the chart
projection of the direct image at the chart diagram of `v`.** -/
theorem appTop_chartGraph_pointSectionsIso_hom_apply (V : SmallEtale B S hS X.1)
    {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    (w : (pushforwardAlgebra B S hS (specPointOver B S hS T x)).right.obj.obj (op V)) :
    ((BigFppfOver.toScheme B S hS).map (chartGraph B S hS V v x hxv)).appTop
        ((pointSectionsIso B S hS T x V).hom w) =
      (directImageChartProjection B S hS (specPointOver B S hS T x).hom V
          (indexOfChartDiagram B S hS (specPointOver B S hS T x).hom
            ⟨idEtaleChart B S hS T, V, v,
              idEtaleChart_hom_comp_specPointOver B S hS V v x hxv⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS (specPointOver B S hS T x).left).O) w := by
  rw [pointSectionsIso_hom_apply, ← toOver_map_initial_to_eq_chartGraph B S hS V v x hxv]
  exact (moduleChartProjection_indexOfChartDiagram_eq_map_chartSetProj B S hS
    (specPointOver B S hS T x).hom (relativelyRepresentable_specPointOver B S hS T x)
    ((sheafCompose _ (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS (specPointOver B S hS T x).left).O)
    ⟨idEtaleChart B S hS T, V, v, idEtaleChart_hom_comp_specPointOver B S hS V v x hxv⟩ w).symm

end PointChart

section RepresentedPoint

variable {X Y : AlgebraicSpaces B S hS} (y : Y ⟶ X) {T : BigFppfOver B S hS}
  (t : Y.1.obj (op T)) {Uc : SmallEtale B S hS Y.1} (u : T ⟶ Uc.obj.left)
  {V : SmallEtale B S hS X.1}
  (g : (SmallEtale.toOver B S hS Y.1).obj Uc ⟶ (SmallEtale.toOver B S hS X.1).obj V)

/-- The chart diagram of the morphism `T ⟶ Y` of a point `t` factoring through a chart. -/
theorem idEtaleChart_hom_comp_pointOverOfPoint_left
    (hu : yonedaEquiv.symm t = yoneda.map u ≫ Uc.obj.hom) :
    (idEtaleChart B S hS T).1.hom ≫ (pointOverOfPoint B S hS y T t).left.hom =
      yoneda.map u ≫ Uc.1.hom :=
  (Category.id_comp _).trans hu

/-- The point `y ∘ t` factors through the chart `V` along `u ≫ g`. -/
theorem yonedaEquiv_symm_app_eq_of_chart (hu : yonedaEquiv.symm t = yoneda.map u ≫ Uc.obj.hom)
    (hg : Uc.1.hom ≫ y.hom = yoneda.map g ≫ V.1.hom) :
    yonedaEquiv.symm (y.hom.app (op T) t) = yoneda.map (u ≫ g) ≫ V.obj.hom := by
  rw [← yonedaEquiv_symm_comp_hom B S hS y t, hu, Category.assoc, hg, ← Category.assoc,
    ← Functor.map_comp]

/-- The chart projection of the direct-image map `pushforwardAlgMap P y` followed by a transport
along `P ≫ y = q`, at a composite chart diagram, stated at variables so that the transport can be
eliminated. -/
theorem directImageChartProjection_pushforwardAlgMap_eqToHom {A : AlgebraicSpaces B S hS}
    (P : A ⟶ Y) (q : A ⟶ X) (hw : P ≫ y = q) {UA : SmallEtale B S hS A.1}
    (a : (SmallEtale.toOver B S hS A.1).obj UA ⟶ (SmallEtale.toOver B S hS Y.1).obj Uc)
    (ha : UA.1.hom ≫ P.hom = yoneda.map a ≫ Uc.1.hom)
    (hg : Uc.1.hom ≫ y.hom = yoneda.map g ≫ V.1.hom)
    (hc : UA.1.hom ≫ q.hom = yoneda.map (a ≫ g) ≫ V.1.hom)
    (z : ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).obj
      (smallEtaleRingedTopos B S hS Y).O).obj.obj (op V)) :
    (directImageChartProjection B S hS q V (indexOfChartDiagram B S hS q ⟨UA, V, a ≫ g, hc⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A).O)
        ((pushforwardAlgMap B S hS P y ≫ eqToHom (congrArg (fun q' : A ⟶ X =>
          (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q').toToposHom).obj
            (smallEtaleRingedTopos B S hS A).O) hw)).hom.app (op V) z) =
      ((BigFppfOver.toScheme B S hS).map a).appTop
        ((directImageChartProjection B S hS y V (indexOfChartDiagram B S hS y ⟨Uc, V, g, hg⟩)).app
          ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O)
            z) := by
  subst hw
  rw [eqToHom_refl, Category.comp_id]
  refine (eq_of_heq (directImageChartProjection_congr B S hS (P ≫ y) V
    (indexOfChartDiagram_chartDiagram_comp B S hS P y (U := UA) (V := Uc) (W := V) a g ha hg)
    _ _)).trans ?_
  refine (directImageChartProjection_pushforwardAlgMap B S hS P y V
    (indexOfChartDiagram B S hS y ⟨Uc, V, g, hg⟩)
    (indexOfChartDiagram B S hS P ⟨UA, Uc, a, ha⟩) z).trans ?_
  exact congrArg (fun m => (forget CommRingCat.{u}).map
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op)
      ((directImageChartProjection B S hS y V (indexOfChartDiagram B S hS y ⟨Uc, V, g, hg⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O) z))
    (chartBaseChangeMap_indexOfChartDiagram B S hS P ⟨UA, Uc, a, ha⟩)

/-- `AlgebraicGeometry.Space.directImageChartProjection_pushforwardAlgMap_eqToHom` for the
direct-image map `AlgebraicGeometry.Space.pushforwardRingMap` of a morphism over `X`, stated for
variable objects of `CategoryTheory.Over X`. -/
theorem directImageChartProjection_pushforwardRingMap_of_chart {Yo Zo : Over X} (f : Yo ⟶ Zo)
    {Uz : SmallEtale B S hS Zo.left.1} {UA : SmallEtale B S hS Yo.left.1}
    (a : (SmallEtale.toOver B S hS Yo.left.1).obj UA ⟶ (SmallEtale.toOver B S hS Zo.left.1).obj Uz)
    (gz : (SmallEtale.toOver B S hS Zo.left.1).obj Uz ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (ha : UA.1.hom ≫ f.left.hom = yoneda.map a ≫ Uz.1.hom)
    (hg : Uz.1.hom ≫ Zo.hom.hom = yoneda.map gz ≫ V.1.hom)
    (hc : UA.1.hom ≫ Yo.hom.hom = yoneda.map (a ≫ gz) ≫ V.1.hom)
    (z : (pushforwardAlgebra B S hS Zo).right.obj.obj (op V)) :
    (directImageChartProjection B S hS Yo.hom V
        (indexOfChartDiagram B S hS Yo.hom ⟨UA, V, a ≫ gz, hc⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Yo.left).O)
        ((pushforwardRingMap B S hS f).hom.app (op V) z) =
      ((BigFppfOver.toScheme B S hS).map a).appTop
        ((directImageChartProjection B S hS Zo.hom V
            (indexOfChartDiagram B S hS Zo.hom ⟨Uz, V, gz, hg⟩)).app
          ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Zo.left).O)
          z) :=
  (congrArg (fun m : (pushforwardAlgebra B S hS Zo).right ⟶ (pushforwardAlgebra B S hS Yo).right =>
      (directImageChartProjection B S hS Yo.hom V
        (indexOfChartDiagram B S hS Yo.hom ⟨UA, V, a ≫ gz, hc⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Yo.left).O)
        (m.hom.app (op V) z)) (pushforwardRingMap_eq B S hS f)).trans
    (directImageChartProjection_pushforwardAlgMap_eqToHom B S hS Zo.hom gz f.left Yo.hom
      (Over.w f) a ha hg hc z)

/-- **The direct-image map of a represented point, read at the chart diagram of the point.**
Let `t ∈ Y(T)` factor through an étale chart `U` of `Y` along `u : T ⟶ U`, and let `U` lie
over an étale chart `V` of `X` along `g`.  The map `y_* 𝒪_Y ⟶ (y ∘ t)_* 𝒪_T` induced by `t`,
followed by the chart projection to `T` itself, is the chart projection of `y_* 𝒪_Y` to `U`
followed by pullback of functions along `u`. -/
theorem directImageChartProjection_pushforwardRingMap_pointOverOfPoint
    (hu : yonedaEquiv.symm t = yoneda.map u ≫ Uc.obj.hom)
    (hg : Uc.1.hom ≫ y.hom = yoneda.map g ≫ V.1.hom)
    (z : (pushforwardAlgebra B S hS (Over.mk y)).right.obj.obj (op V)) :
    (directImageChartProjection B S hS
        (specPointOver B S hS T (y.hom.app (op T) t)).hom V
        (indexOfChartDiagram B S hS (specPointOver B S hS T (y.hom.app (op T) t)).hom
          ⟨idEtaleChart B S hS T, V, u ≫ g, idEtaleChart_hom_comp_specPointOver B S hS V
            (u ≫ g) _ (yonedaEquiv_symm_app_eq_of_chart B S hS y t u g hu hg)⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS (specPointOver B S hS T (y.hom.app (op T) t)).left).O)
        ((pushforwardRingMap B S hS (pointOverOfPoint B S hS y T t)).hom.app (op V) z) =
      ((BigFppfOver.toScheme B S hS).map u).appTop
        ((directImageChartProjection B S hS y V (indexOfChartDiagram B S hS y ⟨Uc, V, g, hg⟩)).app
          ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O) z) :=
  directImageChartProjection_pushforwardRingMap_of_chart B S hS
    (pointOverOfPoint B S hS y T t) (UA := idEtaleChart B S hS T) u g
    (idEtaleChart_hom_comp_pointOverOfPoint_left B S hS y t u hu) hg _ z

/-- **The chart reading of the point of `\underline{Spec}_X(𝒜)` given by `β : 𝒜 ⟶ y_* 𝒪_Y`
at a represented point `t ∈ Y(T)`.**  If `t` factors through an étale chart `U` of `Y` along
`u : T ⟶ U`, and `U` lies over an étale chart `V` of `X` along `g`, then reading
`β` followed by the map of direct images that `t` induces, at `V` along `u ≫ g`, is `β` at `V`,
followed by the chart projection of `y_* 𝒪_Y` to `U`, followed by pullback of functions along
`u`. -/
theorem chartEval_compPushforwardAlgebraMap_pointOverOfPoint_apply
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (β : A ⟶ pushforwardAlgebra B S hS (Over.mk y))
    (hu : yonedaEquiv.symm t = yoneda.map u ≫ Uc.obj.hom)
    (hg : Uc.1.hom ≫ y.hom = yoneda.map g ≫ V.1.hom)
    (a : A.right.obj.obj (op V)) :
    chartEval B S hS A V (u ≫ g) (y.hom.app (op T) t)
        (yonedaEquiv_symm_app_eq_of_chart B S hS y t u g hu hg)
        (compPushforwardAlgebraMap B S hS β (pointOverOfPoint B S hS y T t)) a =
      ((BigFppfOver.toScheme B S hS).map u).appTop
        ((directImageChartProjection B S hS y V (indexOfChartDiagram B S hS y ⟨Uc, V, g, hg⟩)).app
          ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O)
          (β.right.hom.app (op V) a)) := by
  rw [chartEval_apply, compPushforwardAlgebraMap_right_app_apply]
  exact (appTop_chartGraph_pointSectionsIso_hom_apply B S hS V (u ≫ g) (y.hom.app (op T) t)
      (yonedaEquiv_symm_app_eq_of_chart B S hS y t u g hu hg)
      ((pushforwardRingMap B S hS (pointOverOfPoint B S hS y T t)).hom.app (op V)
        (β.right.hom.app (op V) a))).trans
    (directImageChartProjection_pushforwardRingMap_pointOverOfPoint B S hS y t u g hu hg
      (β.right.hom.app (op V) a))

end RepresentedPoint

section Adjunct

/-- A transport `eqToHom` between equal modules is, on sections, heterogeneously the identity.
The object of the site is typed as an object of the small étale ringed site, which is how the
sections of `AlgebraicGeometry.Space.Modules` are indexed. -/
theorem modules_eqToHom_val_app_heq {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (h : M = N)
    (W : (smallEtaleRingedSite B S hS Z.1 Z.2).Cᵒᵖ) (m : M.val.obj W) :
    HEq ((eqToHom h).val.app W m) m := by
  subst h
  rfl

/-- A composite of morphisms of modules on a section, with the object of the site typed as an
object of the small étale ringed site. -/
theorem modules_comp_val_app_apply_of_ringedSite {Z : AlgebraicSpaces B S hS}
    {M₁ M₂ M₃ : Modules.{u, u} B S hS Z.1 Z.2} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃)
    (W : (smallEtaleRingedSite B S hS Z.1 Z.2).Cᵒᵖ) (w : M₁.val.obj W) :
    (a ≫ b).val.app W w = b.val.app W (a.val.app W w) :=
  rfl

variable {X Y : AlgebraicSpaces B S hS} (y : Y ⟶ X)

/-- The chart component of the direct image at a chart diagram, applied to the value of the unit
of `y^* ⊣ y_*`, is the chart section of the inverse image.  This is
`AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection` with the unit
section unfolded. -/
theorem modulePushforwardCounitApp_unit_val_app (E : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS Y.1 X.1 y.hom) (e : E.val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS y ((modulePullback B S hS y).obj E) d
        (((modulePullbackAdjunction B S hS y).unit.app E).val.app (op d.V) e) =
      modulePullbackChartSection B S hS y E d e :=
  modulePullbackUnitSection_eq_modulePullbackChartSection B S hS y E d e

/-- **The chart projection of `y_* 𝒪_Y`, read on a section of the module underlying the
direct-image algebra, is the chart component of the direct image of `𝒪_Y`**: the transport of
`AlgebraicGeometry.Space.underlyingModule_pushforwardAlgebra` is the identity on sections. -/
theorem directImageChartProjection_eqToHom_underlyingModule {Uc : SmallEtale B S hS Y.1}
    {V : SmallEtale B S hS X.1}
    (g : (SmallEtale.toOver B S hS Y.1).obj Uc ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (hg : Uc.1.hom ≫ y.hom = yoneda.map g ≫ V.1.hom)
    (w : ((modulePushforward B S hS y).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Y))).val.obj (op V)) :
    (directImageChartProjection B S hS y V (indexOfChartDiagram B S hS y ⟨Uc, V, g, hg⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O)
        ((eqToHom (underlyingModule_pushforwardAlgebra B S hS y).symm).val.app (op V) w) =
      modulePushforwardCounitApp B S hS y (SheafOfModules.unit (structureRingSheaf B S hS Y))
        ⟨Uc, V, g, hg⟩ w := by
  rw [eq_of_heq (modules_eqToHom_val_app_heq B S hS
    (underlyingModule_pushforwardAlgebra B S hS y).symm (op V) w)]
  rfl

/-- **The adjunct `ℰ ⟶ y_* 𝒪_Y` of `q : y^* ℰ ⟶ 𝒪_Y`, as a map into the direct-image algebra,
read at a chart diagram**: the chart projection of its value on a section `e` over the chart of
`X` is `q` applied to the chart section of `y^* ℰ` that `e` gives. -/
theorem directImageChartProjection_homEquiv_comp_eqToHom (E : Modules.{u, u} B S hS X.1 X.2)
    (q : (modulePullback B S hS y).obj E ⟶ SheafOfModules.unit (structureRingSheaf B S hS Y))
    {Uc : SmallEtale B S hS Y.1} {V : SmallEtale B S hS X.1}
    (g : (SmallEtale.toOver B S hS Y.1).obj Uc ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (hg : Uc.1.hom ≫ y.hom = yoneda.map g ≫ V.1.hom) (e : E.val.obj (op V)) :
    (directImageChartProjection B S hS y V (indexOfChartDiagram B S hS y ⟨Uc, V, g, hg⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Y).O)
        (((modulePullbackAdjunction B S hS y).homEquiv E _ q ≫
          eqToHom (underlyingModule_pushforwardAlgebra B S hS y).symm).val.app (op V) e) =
      q.val.app (op Uc) (modulePullbackChartSection B S hS y E ⟨Uc, V, g, hg⟩ e) := by
  rw [modules_comp_val_app_apply_of_ringedSite,
    directImageChartProjection_eqToHom_underlyingModule B S hS y g hg]
  exact modulePushforwardCounitApp_homEquiv y E _ q ⟨Uc, V, g, hg⟩ e

/-- **The space-level adjunct, read at a represented point, is the scheme-level adjunct of the
reading.**  Let `y : Y ⟶ X`, `q : y^* ℰ ⟶ 𝒪_Y`, and `β : 𝒜 ⟶ y_* 𝒪_Y` a morphism of algebras which
on a section `a` of `𝒜` over an étale chart `V` of `X` takes the value of the adjunct
`ℰ ⟶ y_* 𝒪_Y` of `q` on a section `e` of `ℰ` over `V`.  Let `t ∈ Y(T)` factor through an étale
chart `U` of `Y` along `u : T ⟶ U`, with `U` over `V` along `g`.  Then the point of
`\underline{Spec}_X(𝒜)` given by `β` at `t`, read at `V` along `u ≫ g`, sends `a` to the function
`q(e|_U)` pulled back along `u`, where `e|_U` is the section of `y^* ℰ` over `U` given by `e`. -/
theorem chartEval_compPushforwardAlgebraMap_pointOverOfPoint_of_homEquiv
    {T : BigFppfOver B S hS} (t : Y.1.obj (op T)) {Uc : SmallEtale B S hS Y.1}
    (u : T ⟶ Uc.obj.left) {V : SmallEtale B S hS X.1}
    (g : (SmallEtale.toOver B S hS Y.1).obj Uc ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (hu : yonedaEquiv.symm t = yoneda.map u ≫ Uc.obj.hom)
    (hg : Uc.1.hom ≫ y.hom = yoneda.map g ≫ V.1.hom)
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (β : A ⟶ pushforwardAlgebra B S hS (Over.mk y))
    (E : Modules.{u, u} B S hS X.1 X.2)
    (q : (modulePullback B S hS y).obj E ⟶ SheafOfModules.unit (structureRingSheaf B S hS Y))
    (a : A.right.obj.obj (op V)) (e : E.val.obj (op V))
    (hβ : β.right.hom.app (op V) a =
      ((modulePullbackAdjunction B S hS y).homEquiv E _ q ≫
        eqToHom (underlyingModule_pushforwardAlgebra B S hS y).symm).val.app (op V) e) :
    chartEval B S hS A V (u ≫ g) (y.hom.app (op T) t)
        (yonedaEquiv_symm_app_eq_of_chart B S hS y t u g hu hg)
        (compPushforwardAlgebraMap B S hS β (pointOverOfPoint B S hS y T t)) a =
      ((BigFppfOver.toScheme B S hS).map u).appTop
        (q.val.app (op Uc) (modulePullbackChartSection B S hS y E ⟨Uc, V, g, hg⟩ e)) := by
  rw [chartEval_compPushforwardAlgebraMap_pointOverOfPoint_apply B S hS y t u g β hu hg a, hβ]
  exact congrArg (fun r => ((BigFppfOver.toScheme B S hS).map u).appTop r)
    (directImageChartProjection_homEquiv_comp_eqToHom B S hS y E q g hg e)

end Adjunct

end AlgebraicGeometry.Space

end

