module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseOverlap
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartDiagramSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageCartesianChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCounitComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# Gluing modules on an algebraic space over a pushout along a thickening

In the situation `AlgebraicGeometry.Space.ThickeningPushoutSpaces`, given an `𝒪_V`-module `A`,
an `𝒪_{U'}`-module `B'` and an isomorphism `θ : c^*A ≅ d^*B'`, the glued module of Stacks 08KV is
the fibre product `a_*A ×_{(c ≫ a)_*c^*A} b_*B'`.  This file computes the two maps
`a_*A ⟶ (c ≫ a)_*c^*A` and `b_*B' ⟶ (c ≫ a)_*c^*A` on the charts: on the chart `W_Z` they are the
chart section of `c^*A`, and the chart section of `d^*B'` followed by `θ`.

## Main results

* `AlgebraicGeometry.Space.ThickeningPushoutSpaces.counitApp_glueLeft`,
  `AlgebraicGeometry.Space.ThickeningPushoutSpaces.counitApp_glueRight`.

## References

* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- The ambient-universe abelian structure on sheaves of modules would be selected ahead of
-- `SheafOfModules.instAbelian` for the `𝒪`-modules here, whose sections live in the universe of
-- the schemes.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ThickeningPushoutSpaces

/-- A composite of morphisms of modules acts on the sections over `op W` by composition, with
`op W` spelled as an object of the site of the sheaf of modules (the spelling that
`SheafOfModules.val` produces), so that it applies to such sections without unfolding the
ringed site. -/
theorem comp_val_app_op {X : AlgebraicSpaces B S hS} {F G H : Modules.{u, u} B S hS X.1 X.2}
    (f : F ⟶ G) (g : G ⟶ H) (W : SmallEtale B S hS X.1) (s : F.val.obj (op W)) :
    (f ≫ g).val.app (op W) s = g.val.app (op W) (f.val.app (op W) s) :=
  rfl

variable {Z Z' Y Y' : BigFppfOver B S hS} {i : Z ⟶ Z'} {f : Z ⟶ Y} {g : Z' ⟶ Y'} {h : Y ⟶ Y'}
  {P V U' U : AlgebraicSpaces B S hS} {p : P ⟶ (schemeSpaceFunctor B S hS).obj Y'}
  {pV : V ⟶ (schemeSpaceFunctor B S hS).obj Y} {pU' : U' ⟶ (schemeSpaceFunctor B S hS).obj Z'}
  {pU : U ⟶ (schemeSpaceFunctor B S hS).obj Z} {a : V ⟶ P} {b : U' ⟶ P} {c : U ⟶ V} {d : U ⟶ U'}

variable (E : ThickeningPushoutSpaces i f g h p pV pU' pU a b c d)
include E

/-! ### The two units -/

section Units

variable (A : Modules.{u, u} B S hS V.1 V.2) (B' : Modules.{u, u} B S hS U'.1 U'.2)

variable (c) in
/-- The unit `A ⟶ c_*c^*A`. -/
def unitC : A ⟶ (modulePushforward B S hS c).obj ((modulePullback B S hS c).obj A) :=
  (modulePullbackAdjunction B S hS c).unit.app A

variable (d) in
/-- The unit `B' ⟶ d_*d^*B'`. -/
def unitD : B' ⟶ (modulePushforward B S hS d).obj ((modulePullback B S hS d).obj B') :=
  (modulePullbackAdjunction B S hS d).unit.app B'

end Units

/-! ### The composite chart diagram over `U ⟶ P` -/

variable (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom)

/-- The chart diagram `W_Z ⟶ W` over `c ≫ a`. -/
abbrev dWZW : ChartDiagram B S hS U.1 P.1 (c ≫ a).hom :=
  ⟨(E.dWZ dT).U, dT.U, (E.dWZ dT).g ≫ (E.dWY dT).g,
    (ChartDiagram.comp B S hS c a (E.dWZ dT).g (E.dWY dT).g (E.dWZ dT).comm
      (E.dWY dT).comm).comm⟩

/-- The composite chart diagram `W_Z ⟶ W` is cartesian. -/
theorem isPullback_dWZW :
    IsPullback (E.dWZW dT).U.1.hom (yoneda.map (E.dWZW dT).g) (c ≫ a).hom dT.U.1.hom := by
  have h₁ := (E.rep_c.isPullback (E.WY dT).1.hom)
  have h₂ := (E.rep_a.isPullback dT.U.1.hom)
  have := h₁.paste_vert h₂
  have e : yoneda.map (E.dWZW dT).g =
      yoneda.map (E.rep_c.snd (E.WY dT).1.hom) ≫ yoneda.map (E.rep_a.snd dT.U.1.hom) :=
    yoneda.map_comp _ _
  exact e ▸ this

/-- The counit map of `(c ≫ a)_*` on the cartesian chart diagram `W_Z ⟶ W` is bijective. -/
theorem bijective_counitApp_dWZW (F : Modules.{u, u} B S hS U.1 U.2) :
    Function.Bijective (modulePushforwardCounitApp B S hS (c ≫ a) F (E.dWZW dT)) :=
  bijective_modulePushforwardCounitApp_of_isPullback B S hS _ F _ (E.isPullback_dWZW dT)

/-! ### The two halves of the glued module, read on the charts -/

section GlueCharts

variable (A : Modules.{u, u} B S hS V.1 V.2) (B' : Modules.{u, u} B S hS U'.1 U'.2)
  (θ : (modulePullback B S hS d).obj B' ⟶ (modulePullback B S hS c).obj A)

/-- **The left half of the glued module on the chart `W_Z`** is the chart section of `c^*A`. -/
theorem counitApp_glueLeft (x : ((modulePushforward B S hS a).obj A).val.obj (op dT.U)) :
    modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (((modulePushforward B S hS a).map (unitC c A) ≫
          (modulePushforwardCompIso B S hS c a).hom.app
            ((modulePullback B S hS c).obj A)).val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x) := by
  have h := modulePushforwardCounitApp_comp_compIso B S hS c a
    ((modulePullback B S hS c).obj A) ((modulePushforward B S hS a).map (unitC c A))
    (U := E.WZ dT) (V := E.WY dT) (W := dT.U) (E.dWZ dT).g (E.dWY dT).g (E.dWZ dT).comm
    (E.dWY dT).comm ((E.dWZ dT).g ≫ (E.dWY dT).g) (E.dWZW dT).comm rfl x
  exact h.trans (by
    rw [modulePushforwardCounitApp_map_mk]
    exact modulePullbackUnitSection_eq_modulePullbackChartSection B S hS c A (E.dWZ dT) _)

/-- The chart diagram `W_Z ⟶ W` over `d ≫ b`. -/
abbrev dWZW' : ChartDiagram B S hS U.1 P.1 (d ≫ b).hom :=
  ChartDiagram.comp B S hS d b (E.dWZZ' dT).g (E.dWZ' dT).g (E.dWZZ' dT).comm
    (E.dWZ' dT).comm

/-- The chart formula of `b_*B' ⟶ (d ≫ b)_*d^*B'` on the chart `W_Z`. -/
theorem counitApp_glueRight₀ (y : ((modulePushforward B S hS b).obj B').val.obj (op dT.U)) :
    modulePushforwardCounitApp B S hS (d ≫ b) ((modulePullback B S hS d).obj B')
        (E.dWZW' dT)
        (((modulePushforward B S hS b).map (unitD d B') ≫
            (modulePushforwardCompIso B S hS d b).hom.app
              ((modulePullback B S hS d).obj B')).val.app (op dT.U) y) =
      modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y) := by
  have h := modulePushforwardCounitApp_comp_compIso B S hS d b
    ((modulePullback B S hS d).obj B') ((modulePushforward B S hS b).map (unitD d B'))
    (U := E.WZ dT) (V := E.WZ' dT) (W := dT.U) (E.dWZZ' dT).g (E.dWZ' dT).g (E.dWZZ' dT).comm
    (E.dWZ' dT).comm ((E.dWZZ' dT).g ≫ (E.dWZ' dT).g) (E.dWZW' dT).comm rfl y
  exact (h.trans (congrArg (modulePushforwardCounitApp B S hS d
      ((modulePullback B S hS d).obj B') (E.dWZZ' dT))
    (modulePushforwardCounitApp_map_mk B S hS b (unitD d B')
      (U := E.WZ' dT) (V := dT.U) (E.dWZ' dT).g (E.dWZ' dT).comm y))).trans
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS d B' (E.dWZZ' dT) _)

/-- The chart formula of the transport `(d ≫ b)_*d^*B' ⟶ (c ≫ a)_*c^*A` through `θ`. -/
theorem counitApp_transport
    (s : ((modulePushforward B S hS (d ≫ b)).obj ((modulePullback B S hS d).obj B')).val.obj
      (op dT.U)) :
    modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT)
        (((eqToHom (congrArg (fun m => modulePushforward B S hS m) E.comm.symm)).app
            ((modulePullback B S hS d).obj B') ≫
          (modulePushforward B S hS (c ≫ a)).map θ).val.app (op dT.U) s) =
      θ.val.app (op (E.WZ dT))
        (modulePushforwardCounitApp B S hS (d ≫ b) ((modulePullback B S hS d).obj B')
          (E.dWZW' dT) s) := by
  have hg : (E.dWZZ' dT).g ≫ (E.dWZ' dT).g = (E.dWZ dT).g ≫ (E.dWY dT).g := E.mapWZ_snd dT
  have hc := modulePushforwardCounitApp_congr B S hS E.comm.symm
    ((modulePullback B S hS d).obj B') (U := E.WZ dT) (V := dT.U) hg (E.dWZW' dT).comm
    (E.dWZW dT).comm s
  exact (congrArg (modulePushforwardCounitApp B S hS (c ≫ a)
      ((modulePullback B S hS c).obj A) (E.dWZW dT))
      (comp_val_app_op _ _ dT.U s)).trans
    ((modulePushforwardCounitApp_map_mk B S hS (c ≫ a) θ (U := E.WZ dT) (V := dT.U)
      ((E.dWZ dT).g ≫ (E.dWY dT).g) (E.dWZW dT).comm _).trans
        (congrArg (θ.val.app (op (E.WZ dT))) hc))

/-- **The right half of the glued module on the chart `W_Z`** is the chart section of `d^*B'`,
followed by `θ`. -/
theorem counitApp_glueRight (y : ((modulePushforward B S hS b).obj B').val.obj (op dT.U)) :
    modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT)
        ((((modulePushforward B S hS b).map (unitD d B') ≫
            (modulePushforwardCompIso B S hS d b).hom.app
              ((modulePullback B S hS d).obj B')) ≫
          (eqToHom (congrArg (fun m => modulePushforward B S hS m) E.comm.symm)).app
            ((modulePullback B S hS d).obj B') ≫
          (modulePushforward B S hS (c ≫ a)).map θ).val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y)) :=
  (congrArg (modulePushforwardCounitApp B S hS (c ≫ a)
      ((modulePullback B S hS c).obj A) (E.dWZW dT)) (comp_val_app_op _ _ dT.U y)).trans
    ((E.counitApp_transport dT A B' θ _).trans
      (congrArg (θ.val.app (op (E.WZ dT))) (E.counitApp_glueRight₀ dT B' y)))

end GlueCharts

end ThickeningPushoutSpaces

end AlgebraicGeometry.Space

end
