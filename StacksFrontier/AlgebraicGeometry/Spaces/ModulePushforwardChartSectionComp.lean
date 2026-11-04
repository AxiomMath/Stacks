module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompMate

/-!
# The composition comparison for direct images of modules, on a chart section

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, and let `N` be an `𝒪_X`-module on the small étale site.  The comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso` of **Stacks 03LU** identifies `g_*(f_*N)` with
`(f ≫ g)_*N`, and `AlgebraicGeometry.Space.moduleChartProjection` projects the sections of a
direct image over an étale scheme chart of the target onto the sections over an étale scheme
chart of the source above the cartesian base change.  This file proves the **chart-level reading
of Stacks 03G2, part (3)**: the comparison carries an iterated chart projection to the chart
projection along the composite.

## Main results

* `AlgebraicGeometry.Space.moduleChartProjection_app_ranProj`: the chart projection of the direct
  image of sheaves of sets is the projection of the right Kan extension, after the comparison of
  the direct image with its Kan-extension form.
* `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_hom_comp_directImageRanIso`:
  `AlgebraicGeometry.Space.ranSpacesHom_comp_formula` with the Kan-extension comparison of the
  outer direct image transposed to the other side.
* `AlgebraicGeometry.Space.moduleChartProjection_comp_smallToposMorphismTypeU_comp_hom_app`: **the
  chart-level reading of Stacks 03G2, part (3), with an arbitrary morphism into the inner direct
  image precomposed.**
* `AlgebraicGeometry.Space.moduleChartProjection_smallToposMorphismTypeU_comp_hom_app`: **the
  chart-level reading of Stacks 03G2, part (3)** — the geometric comparison of the iterated
  direct image with the direct image of the composite carries an iterated chart projection to the
  chart projection along the composite, at the étale scheme chart of `X` above `X ×_Z W` which a
  chart `j` of `Y` above `Y ×_Z W` and a chart `k` of `X` above `X ×_Y j` determine.
* `AlgebraicGeometry.Space.moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_module` and
  `AlgebraicGeometry.Space.moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_module_val`:
  the same with the inner direct image, and then the section itself, spelled module-side
  through `AlgebraicGeometry.Space.modulePushforward`.
* `Space.moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_chartDiagram`:
  the same at a **composed chart diagram** `AlgebraicGeometry.Space.ChartDiagram.comp` — a chart
  `U` of `X` over a chart `V` of `Y` over a chart `W` of `Z` — with the two iterated projections
  on the right read as the chart sections `AlgebraicGeometry.Space.modulePushforwardCounitApp`.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app_apply` and
  `AlgebraicGeometry.Space.modulePushforwardCompIsoSection_apply`: **the comparison of Stacks 03LU
  on a section, with an arbitrary function applied to both sides**, the function's domain fixed
  at the geometric spelling of the sections of `(f ≫ g)_*N` in the first and at the module-side
  spelling in the second.
* `Space.moduleChartProjectionFun_smallToposMorphismTypeU_comp_hom_app_chartDiagram` and
  `Space.modulePushforwardCounitApp_smallToposMorphismTypeU_comp_hom_app_chartDiagram`:
  the chart-level reading of Stacks 03G2, part (3) at a composed chart diagram with the
  projection on the left read as the evaluated projection
  `AlgebraicGeometry.Space.moduleChartProjectionFun`, and then as the chart section
  `AlgebraicGeometry.Space.modulePushforwardCounitApp`.
* `Space.modulePushforwardCounitApp_modulePushforwardCompIsoSection_chartDiagram`:
  **the chart-level reading of Stacks 03LU at a composed chart diagram** — the comparison
  `g_*(f_*N) ≅ (f ≫ g)_*N` of Stacks 03LU carries a section over a chart `W` of `Z` to a section
  whose chart section over the composed chart diagram is the iterated chart section over the two
  diagrams it is composed from.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

namespace AlgebraicGeometry.Space

universe u

/-! ### Composites of morphisms of sheaves of sets on a section

Reading a composite of morphisms of sheaves of sets on a section, and transposing an
isomorphism across an equation, at a generic site or category.
-/

section Abstract

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- Transpose an isomorphism across an equation: the direction of `CategoryTheory.Iso.inv_comp_eq`
with the isomorphism applied on the other side. -/
private theorem eq_hom_comp_of_inv_comp {D : Type*} [Category D] {A A' T : D} (e : A ≅ A')
    {m : A ⟶ T} {n : A' ⟶ T} (h : e.inv ≫ m = n) : m = e.hom ≫ n := by
  rw [← h, Iso.hom_inv_id_assoc]

end Abstract

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The chart projection, carried abstractly -/

/-- **The chart projection of the direct image of sheaves of sets, in Kan-extension form.**  It
is the projection `AlgebraicGeometry.Space.ranProj` of the right Kan extension at the cartesian
chart `X ×_Y V`, applied after the comparison
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` of the direct image with its
Kan-extension form. -/
theorem moduleChartProjection_app_ranProj (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    (moduleChartProjection B S hS f V j).app P x =
      (ranProj B S hS X (chartBaseChange B S hS f V) j).app P
        (((smallEtaleDirectImageRanIso B S hS f).hom.app P).hom.app (op V) x) :=
  rfl

/-- Two equal indices give the same chart projection, up to `HEq` since the sections are taken
over `j.right`. -/
private theorem moduleChartProjection_app_congr (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {j j' : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (h : j = j') (x : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    HEq ((moduleChartProjection B S hS f V j).app P x)
      ((moduleChartProjection B S hS f V j').app P x) := by
  subst h
  rfl

/-! ### The comparison against the Kan-extension form -/

/-- **The composite of a morphism into the inner direct image with the geometric comparison of
Stacks 03G2, part (3), read against the Kan-extension forms.**

This is `AlgebraicGeometry.Space.ranSpacesHom_comp_formula` with the comparison
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` of the outer direct image transposed from
the source to the target of the equation. -/
theorem smallToposMorphismTypeU_comp_hom_comp_directImageRanIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ψ : Q ⟶ (smallEtaleDirectImage B S hS f).obj P) :
    (smallEtaleDirectImage B S hS g).map ψ ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app P ≫
        (smallEtaleDirectImageRanIso B S hS (f ≫ g)).hom.app P =
      (smallEtaleDirectImageRanIso B S hS g).hom.app Q ≫
        (smallEtaleComparisonRestriction B S hS Z).map
          ((spacesDirectImage B S hS g).map (ranSpacesHom B S hS f P Q ψ) ≫
            (spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
              ((smallEtaleComparisonRan B S hS X).obj P)) :=
  eq_hom_comp_of_inv_comp ((smallEtaleDirectImageRanIso B S hS g).app Q)
    (ranSpacesHom_comp_formula B S hS f g P Q ψ)

/-! ### The chart-level reading of Stacks 03G2, part (3) -/

/-- **The chart-level reading of Stacks 03G2, part (3), with a morphism into the inner direct
image precomposed.**  Let `W` be an étale scheme chart of `Z`, let `j` be an étale scheme chart
of `Y` above `Y ×_Z W` and let `k` be an étale scheme chart of `X` above `X ×_Y j`.  For a
morphism `ψ` into the direct image `f_*P` and a section `y` of `g_*Q` over `W`, the chart
projection along `f ≫ g` at the chart of `X` above `X ×_Z W` which `j` and `k` determine, of the
section obtained by pushing `y` forward along `ψ` and applying the geometric comparison, is the
iterated chart projection: project at `j`, apply `ψ`, project at `k`. -/
theorem moduleChartProjection_comp_smallToposMorphismTypeU_comp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (ψ : Q ⟶ (smallEtaleDirectImage B S hS f).obj P) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (y : ((smallEtaleDirectImage B S hS g).obj Q).obj.obj (op W)) :
    (moduleChartProjection B S hS (f ≫ g) W
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app P
        (((smallEtaleDirectImage B S hS g).map ψ ≫
          (smallToposMorphismTypeU_comp B S hS f g).hom.app P).hom.app (op W) y) =
      (moduleChartProjection B S hS f j.right.unop k).app P
        (ψ.hom.app (op j.right.unop) ((moduleChartProjection B S hS g W j).app Q y)) := by
  refine (moduleChartProjection_app_ranProj B S hS (f ≫ g) W
    (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom)) P _).trans ?_
  refine Eq.trans (congrArg (fun m ↦ (ranProj B S hS X (chartBaseChange B S hS (f ≫ g) W)
      (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app P
        (m.hom.app (op W) y))
    (smallToposMorphismTypeU_comp_hom_comp_directImageRanIso B S hS f g P Q ψ)) ?_
  exact (ranProj_ranSpacesHom_comp B S hS f g P Q ψ W j k _).trans
    (moduleChartProjection_app_ranProj B S hS f j.right.unop k P _).symm

/-- **The chart-level reading of Stacks 03G2, part (3).**  The geometric comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of the iterated direct image `g_*(f_*P)`
with the direct image `(f ≫ g)_*P` along the composite carries an iterated chart projection to
the chart projection along `f ≫ g`, at the étale scheme chart of `X` above `X ×_Z W` which a
chart `j` of `Y` above `Y ×_Z W` and a chart `k` of `X` above `X ×_Y j` determine. -/
theorem moduleChartProjection_smallToposMorphismTypeU_comp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (y : ((smallEtaleDirectImage B S hS g).obj
      ((smallEtaleDirectImage B S hS f).obj P)).obj.obj (op W)) :
    (moduleChartProjection B S hS (f ≫ g) W
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app P
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app P).hom.app (op W) y) =
      (moduleChartProjection B S hS f j.right.unop k).app P
        ((moduleChartProjection B S hS g W j).app
          ((smallEtaleDirectImage B S hS f).obj P) y) := by
  have h := moduleChartProjection_comp_smallToposMorphismTypeU_comp_hom_app B S hS f g
    P ((smallEtaleDirectImage B S hS f).obj P)
    (𝟙 ((smallEtaleDirectImage B S hS f).obj P)) W j k y
  rw [CategoryTheory.Functor.map_id] at h
  exact h

/-! ### Module-side spellings -/

/-- The previous statement with the inner direct image spelled module-side, at the underlying
sheaf of sets of `f_*N` rather than at the direct image of the underlying sheaf of sets of `N`. -/
theorem moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_module (f : X ⟶ Y)
    (g : Y ⟶ Z) (N : Modules.{u, u} B S hS X.1 X.2) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (y : ((smallEtaleDirectImage B S hS g).obj
      (moduleSetSheaf B S hS Y ((modulePushforward B S hS f).obj N))).obj.obj (op W)) :
    (moduleChartProjection B S hS (f ≫ g) W
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app
        (moduleSetSheaf B S hS X N)
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app
          (moduleSetSheaf B S hS X N)).hom.app (op W) y) =
      (moduleChartProjection B S hS f j.right.unop k).app (moduleSetSheaf B S hS X N)
        ((moduleChartProjection B S hS g W j).app
          (moduleSetSheaf B S hS Y ((modulePushforward B S hS f).obj N)) y) :=
  moduleChartProjection_smallToposMorphismTypeU_comp_hom_app B S hS f g
    (moduleSetSheaf B S hS X N) W j k y

/-- The previous statement with the section typed as a section of the iterated direct image of
modules. -/
theorem moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_module_val
    (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules.{u, u} B S hS X.1 X.2) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (y : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj N).val.obj (op W)) :
    (moduleChartProjection B S hS (f ≫ g) W
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom))).app
        (moduleSetSheaf B S hS X N)
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app
          (moduleSetSheaf B S hS X N)).hom.app (op W) y) =
      (moduleChartProjection B S hS f j.right.unop k).app (moduleSetSheaf B S hS X N)
        ((moduleChartProjection B S hS g W j).app
          (moduleSetSheaf B S hS Y ((modulePushforward B S hS f).obj N)) y) :=
  moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_module B S hS f g N W j k y



/-- **The chart-level reading of Stacks 03G2, part (3) at a composed chart diagram.**  The
geometric comparison carries a section of the iterated direct image over a chart `W` of `Z` to a
section whose chart section over the chart diagram
`AlgebraicGeometry.Space.ChartDiagram.comp` — a chart `U` of `X` over a chart `V` of `Y` over
`W` — is the iterated chart section over the two diagrams it is composed from. -/
theorem moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_chartDiagram
    (f : X ⟶ Y) (g : Y ⟶ Z) {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (y : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj N).val.obj (op W)) :
    (moduleChartProjection B S hS (f ≫ g) W
          (indexOfChartDiagram B S hS (f ≫ g)
            (ChartDiagram.comp B S hS f g a b ha hb))).app (moduleSetSheaf B S hS X N)
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app
          (moduleSetSheaf B S hS X N)).hom.app (op W) y) =
      modulePushforwardCounitApp B S hS f N ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f).obj N)
          ⟨V, W, b, hb⟩ y) := by
  refine Eq.trans (eq_of_heq (moduleChartProjection_app_congr B S hS (f ≫ g) W
    (moduleSetSheaf B S hS X N)
    (indexOfChartDiagram_chartDiagram_comp B S hS f g a b ha hb)
    (((smallToposMorphismTypeU_comp B S hS f g).hom.app
      (moduleSetSheaf B S hS X N)).hom.app (op W) y))) ?_
  exact moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_module_val B S hS f g N W
    (indexOfChartDiagram B S hS g ⟨V, W, b, hb⟩)
    (indexOfChartDiagram B S hS f ⟨U, V, a, ha⟩) y

/-! ### The comparison of Stacks 03LU on a section -/

/-- **The comparison of Stacks 03LU on a section, with an arbitrary function applied to both
sides.**  The comparison of Stacks 03LU acts on a section of `g_*(f_*N)` as the geometric
comparison of Stacks 03G2, part (3) does, after applying any function `Φ` out of the sections of
`(f ≫ g)_*N` in the geometric spelling. -/
theorem modulePushforwardCompIso_hom_app_val_app_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) (V : (SmallEtale B S hS Z.1)ᵒᵖ) {T : Type u}
    (Φ : ((smallEtaleDirectImage B S hS (f ≫ g)).obj
      (moduleSetSheaf B S hS X N)).obj.obj V → T)
    (t : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj N).val.obj V) :
    Φ (((modulePushforwardCompIso B S hS f g).hom.app N).val.app V t) =
      Φ (((smallToposMorphismTypeU_comp B S hS f g).hom.app
        (moduleSetSheaf B S hS X N)).hom.app V t) :=
  congrArg Φ (modulePushforwardCompIso_hom_app_val_app B S hS f g N V t)

/-- **The comparison of Stacks 03LU on a section, with an arbitrary function of the module-side
sections applied to both sides.**  This is
`AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app_apply` with the function's
domain at the *module-side* spelling of the sections of `(f ≫ g)_*N` instead of the geometric
one, and with the comparison's action on the section named by
`AlgebraicGeometry.Space.modulePushforwardCompIsoSection`. -/
theorem modulePushforwardCompIsoSection_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) (V : (SmallEtale B S hS Z.1)ᵒᵖ) {T : Type u}
    (Φ : ((modulePushforward B S hS (f ≫ g)).obj N).val.obj V → T)
    (t : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj N).val.obj V) :
    Φ (modulePushforwardCompIsoSection B S hS f g N V t) =
      Φ (((smallToposMorphismTypeU_comp B S hS f g).hom.app
        (moduleSetSheaf B S hS X N)).hom.app V t) :=
  congrArg Φ (modulePushforwardCompIso_hom_app_val_app B S hS f g N V t)

/-! ### Stacks 03G2, part (3) and Stacks 03LU on a chart section -/

/-- **The chart-level reading of Stacks 03G2, part (3) at a composed chart diagram, on the
evaluated chart projection.**  This is
`AlgebraicGeometry.Space.moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_chartDiagram`
with the projection on the left written as
`AlgebraicGeometry.Space.moduleChartProjectionFun`, whose domain is the sections of the direct
image in the geometric spelling. -/
theorem moduleChartProjectionFun_smallToposMorphismTypeU_comp_hom_app_chartDiagram
    (f : X ⟶ Y) (g : Y ⟶ Z) {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (y : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj N).val.obj (op W)) :
    moduleChartProjectionFun B S hS (f ≫ g) W
          (indexOfChartDiagram B S hS (f ≫ g) (ChartDiagram.comp B S hS f g a b ha hb))
          (moduleSetSheaf B S hS X N)
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app
          (moduleSetSheaf B S hS X N)).hom.app (op W) y) =
      modulePushforwardCounitApp B S hS f N ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f).obj N)
          ⟨V, W, b, hb⟩ y) :=
  Eq.trans
    (moduleChartProjectionFun_eq B S hS (f ≫ g) W
      (indexOfChartDiagram B S hS (f ≫ g) (ChartDiagram.comp B S hS f g a b ha hb))
      (moduleSetSheaf B S hS X N)
      (((smallToposMorphismTypeU_comp B S hS f g).hom.app
        (moduleSetSheaf B S hS X N)).hom.app (op W) y))
    (moduleChartProjection_smallToposMorphismTypeU_comp_hom_app_chartDiagram B S hS f g
      a b ha hb N y)

/-- **The chart-level reading of Stacks 03G2, part (3) at a composed chart diagram, on chart
sections.**  The geometric comparison of the iterated direct
image with the direct image of the composite carries a section over a chart `W` of `Z` to a
section whose chart section over the composed chart diagram
`AlgebraicGeometry.Space.ChartDiagram.comp` is the iterated chart section over the two diagrams
it is composed from. -/
theorem modulePushforwardCounitApp_smallToposMorphismTypeU_comp_hom_app_chartDiagram
    (f : X ⟶ Y) (g : Y ⟶ Z) {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (y : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj N).val.obj (op W)) :
    modulePushforwardCounitApp B S hS (f ≫ g) N (ChartDiagram.comp B S hS f g a b ha hb)
        (((smallToposMorphismTypeU_comp B S hS f g).hom.app
          (moduleSetSheaf B S hS X N)).hom.app (op W) y) =
      modulePushforwardCounitApp B S hS f N ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f).obj N)
          ⟨V, W, b, hb⟩ y) :=
  Eq.trans
    (modulePushforwardCounitApp_eq_fun B S hS (f ≫ g) N
      (ChartDiagram.comp B S hS f g a b ha hb)
      (((smallToposMorphismTypeU_comp B S hS f g).hom.app
        (moduleSetSheaf B S hS X N)).hom.app (op W) y))
    (moduleChartProjectionFun_smallToposMorphismTypeU_comp_hom_app_chartDiagram B S hS f g
      a b ha hb N y)

/-- **The chart-level reading of Stacks 03LU at a composed chart diagram.**  The comparison
`g_*(f_*N) ≅ (f ≫ g)_*N` of Stacks 03LU carries a section of the iterated direct image over a
chart `W` of `Z` to a section whose chart section over the composed chart diagram
`AlgebraicGeometry.Space.ChartDiagram.comp` — a chart `U` of `X` over a chart `V` of `Y` over
`W` — is the iterated chart section over the two diagrams it is composed from. The action of
the comparison on the section is `AlgebraicGeometry.Space.modulePushforwardCompIsoSection`. -/
theorem modulePushforwardCounitApp_modulePushforwardCompIsoSection_chartDiagram
    (f : X ⟶ Y) (g : Y ⟶ Z) {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (y : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj N).val.obj (op W)) :
    modulePushforwardCounitApp B S hS (f ≫ g) N (ChartDiagram.comp B S hS f g a b ha hb)
        (modulePushforwardCompIsoSection B S hS f g N (op W) y) =
      modulePushforwardCounitApp B S hS f N ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f).obj N)
          ⟨V, W, b, hb⟩ y) :=
  Eq.trans
    (modulePushforwardCompIsoSection_apply B S hS f g N (op W)
      (modulePushforwardCounitApp B S hS (f ≫ g) N (ChartDiagram.comp B S hS f g a b ha hb)) y)
    (modulePushforwardCounitApp_smallToposMorphismTypeU_comp_hom_app_chartDiagram B S hS f g
      a b ha hb N y)

end AlgebraicGeometry.Space

end
