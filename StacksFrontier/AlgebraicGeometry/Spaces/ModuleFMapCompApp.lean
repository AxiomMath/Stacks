module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartSectionComp

/-!
# The chart formula for the composite of two linear maps of sections

`AlgebraicGeometry.Space.ModuleFMap.comp` composes a linear map of sections along `f : X ⟶ Y`
with one along `g : Y ⟶ Z`, through the module chart correspondence of Stacks 03G4 and the
composition comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU.  This
file proves its chart formula: on a chart diagram over `f ≫ g` whose vertical morphism factors
through a chart of `Y`, the component of the composite is the composite of the two components.

## Main definitions

* `AlgebraicGeometry.Space.moduleSectionApp`: a morphism of `𝒪`-modules applied to a section,
  as a named function.

## Main results

* `AlgebraicGeometry.Space.ModuleFMap.comp_app_of_vertical`: the chart formula at an arbitrary
  chart diagram over `f ≫ g` together with a factorization of its vertical morphism.
* `AlgebraicGeometry.Space.ModuleFMap.comp_app`: the chart formula at a composed chart diagram
  `AlgebraicGeometry.Space.ChartDiagram.comp`.

## Implementation notes

The proof never compares the components of two composites: the composite morphism of modules is
read on a section at a free chart diagram, which is definitional; the vertical morphism is then
rewritten inside the chart section `AlgebraicGeometry.Space.modulePushforwardCounitApp`, an
ordinary definition, rather than inside a component of `AlgebraicGeometry.Space.ModuleFMap.comp`,
a projection; the comparison of Stacks 03LU is crossed by
`AlgebraicGeometry.Space.modulePushforwardCounitApp_modulePushforwardCompIsoSection_chartDiagram`;
and the two remaining chart sections are the two linear maps of sections, by
`AlgebraicGeometry.Space.modulePushforwardHomFMap_moduleFMapHom`.  Applications of morphisms of
modules to sections are written through `AlgebraicGeometry.Space.moduleSectionApp`, so that each
junction of the chain is syntactic.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The chart formula for the composite -/

/-- **A morphism of `𝒪`-modules applied to a section, named.**

Naming it is load-bearing and the reason is the one
`AlgebraicGeometry.Space.modulePushforwardCompIsoSection` records: the sections of a module are
an object of `ModuleCat`, so `p.val.app V t` goes through the concrete-category coercion, whose
implicit arguments are fixed from the *expected* type at the point of application.  Written bare
in the argument position of a named function — the chart section
`AlgebraicGeometry.Space.modulePushforwardCounitApp`, say — the application elaborates to a
different term than the same application written as that function's own body, the two are
definitionally equal, and comparing them forces
`AlgebraicGeometry.Space.modulePushforward` open.  With the application named, every junction of
the chart formula below is syntactic and nothing is forced open. -/
noncomputable def moduleSectionApp {T : AlgebraicSpaces B S hS}
    {A A' : Modules.{u, u} B S hS T.1 T.2} (p : A ⟶ A')
    (V : (SmallEtale B S hS T.1)ᵒᵖ) (t : A.val.obj V) : A'.val.obj V :=
  p.val.app V t

/-- The named action of the comparison of Stacks 03LU on a section is
`AlgebraicGeometry.Space.modulePushforwardCompIsoSection`: both are the comparison's component
applied to the section, so this holds by `Eq.refl`, and it is the one place where the two names
meet. -/
private theorem moduleSectionApp_modulePushforwardCompIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (y : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj F).val.obj V) :
    moduleSectionApp B S hS ((modulePushforwardCompIso B S hS f g).hom.app F) V y =
      modulePushforwardCompIsoSection B S hS f g F V y := rfl

/-- The linear map of sections attached to a morphism of modules that is a composite of three
factors, read on a chart diagram: the three factors are applied to the section in turn and the
chart section of the direct image is taken.  Every argument is a free variable, so this holds by
`Eq.refl`. -/
private theorem modulePushforwardHomFMap_comp_comp_app (k : X ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) {A A' A'' : Modules.{u, u} B S hS Z.1 Z.2}
    (m : A ⟶ A') (n : A' ⟶ A'') (p : A'' ⟶ (modulePushforward B S hS k).obj F)
    (d : ChartDiagram B S hS X.1 Z.1 k.hom) (s : A.val.obj (op d.V)) :
    (modulePushforwardHomFMap B S hS k F A (m ≫ n ≫ p)).app d s =
      modulePushforwardCounitApp B S hS k F d
        (moduleSectionApp B S hS p (op d.V)
          (moduleSectionApp B S hS n (op d.V) (moduleSectionApp B S hS m (op d.V) s))) := rfl

/-- Naturality of the chart section of a direct image, read with
`AlgebraicGeometry.Space.moduleSectionApp`.  This is
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`. -/
private theorem modulePushforwardCounitApp_moduleSectionApp_map (k : X ⟶ Y)
    {F F' : Modules.{u, u} B S hS X.1 X.2} (a : F ⟶ F')
    (d : ChartDiagram B S hS X.1 Y.1 k.hom)
    (x : ((modulePushforward B S hS k).obj F).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS k F' d
        (moduleSectionApp B S hS ((modulePushforward B S hS k).map a) (op d.V) x) =
      moduleSectionApp B S hS a (op d.U) (modulePushforwardCounitApp B S hS k F d x) :=
  modulePushforwardCounitApp_map B S hS k a d x

/-- The chart section of the direct image, applied to the image of a section under the morphism
of modules attached to a linear map of sections, is that linear map of sections.  This is the
module chart correspondence being a bijection,
`AlgebraicGeometry.Space.modulePushforwardHomFMap_moduleFMapHom`, read on a chart diagram. -/
private theorem modulePushforwardCounitApp_moduleSectionApp_moduleFMapHom (k : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (ζ : ModuleFMap B S hS k F G) (d : ChartDiagram B S hS X.1 Y.1 k.hom)
    (s : G.val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS k F d
        (moduleSectionApp B S hS (moduleFMapHom B S hS k F G ζ) (op d.V) s) = ζ.app d s :=
  congrArg (fun z : ModuleFMap B S hS k F G ↦ z.app d s)
    (modulePushforwardHomFMap_moduleFMapHom B S hS k F G ζ)

/-- The composite of two linear maps of sections is the linear map of sections of the composite
morphism of modules, written out.  This is the two definitions unfolded, at the level of linear
maps of sections and so at free charts.  The same unfolding on a component — with the chart
diagram and the section already supplied — would reduce the projection as well and leave a bare
`.val.app`, for the reason `AlgebraicGeometry.Space.moduleSectionApp` records. -/
private theorem ModuleFMap.comp_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G) :
    ModuleFMap.comp B S hS f g F G H ξ η =
      modulePushforwardHomFMap B S hS (f ≫ g) F H
        (moduleFMapHom B S hS g G H ξ ≫
          (show (modulePushforward B S hS g).obj G ⟶
              (modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj F from
            (modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η)) ≫
          (modulePushforwardCompIso B S hS f g).hom.app F) := rfl

/-- **The composite of two linear maps of sections, read on an arbitrary chart diagram.**  Its
value is the chart section of the direct image along `f ≫ g`, at the comparison of Stacks 03LU
applied to the section carried through the two morphisms of modules.

Nothing here is specific to a composed chart diagram: the chart diagram is a free variable,
which is the whole point.  The chart formula below is this statement instantiated at a composed
diagram together with the chart-level reading of Stacks 03LU, so that the reductions are
performed once, here, and never at a composed diagram. -/
private theorem ModuleFMap.comp_app_counit (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G)
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom) (s : H.val.obj (op d.V)) :
    (ModuleFMap.comp B S hS f g F G H ξ η).app d s =
      modulePushforwardCounitApp B S hS (f ≫ g) F d
        (modulePushforwardCompIsoSection B S hS f g F (op d.V)
          (moduleSectionApp B S hS
            (show (modulePushforward B S hS g).obj G ⟶
                (modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj F from
              (modulePushforward B S hS g).map (moduleFMapHom B S hS f F G η)) (op d.V)
            (moduleSectionApp B S hS (moduleFMapHom B S hS g G H ξ) (op d.V) s))) := by
  rw [ModuleFMap.comp_eq B S hS f g F G H ξ η]
  exact (modulePushforwardHomFMap_comp_comp_app B S hS (f ≫ g) F _ _ _ d s).trans
    (congrArg (modulePushforwardCounitApp B S hS (f ≫ g) F d)
      (moduleSectionApp_modulePushforwardCompIso_hom_app B S hS f g F (op d.V) _))

/-- Rewriting the vertical morphism of a chart diagram inside a chart section of a direct
image.  The commutation is a proposition, so only the vertical morphisms have to agree.

This congruence is where the passage from a given chart diagram to a composed one is made, and
it has to be made *here* rather than on a component of
`AlgebraicGeometry.Space.ModuleFMap.comp`.  The two chart diagrams of the chart formula below
are equal by `Eq.refl`, but between
`(ModuleFMap.comp …).app ⟨U, W, a ≫ b, hc⟩ s` and `(ModuleFMap.comp …).app (ChartDiagram.comp …)
s` that equality is not usable, for the reason
`AlgebraicGeometry.Space.moduleSectionApp` records:
`AlgebraicGeometry.Space.ModuleFMap.app` is a *projection*, so reducing it unfolds
`AlgebraicGeometry.Space.ModuleFMap.comp` and leaves two bare `.val.app`s to compare.  The chart
section `AlgebraicGeometry.Space.modulePushforwardCounitApp` is an ordinary definition, so here
the diagram stays in an argument, nothing is reduced, and two spellings of one diagram are
interchangeable. -/
private theorem modulePushforwardCounitApp_congr_vertical {k : X ⟶ Z}
    (F : Modules.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS X.1 Z.1 k.hom)
    {c : (SmallEtale.toOver B S hS X.1).obj d.U ⟶ (SmallEtale.toOver B S hS Z.1).obj d.V}
    (h : d.g = c) (hc : d.U.1.hom ≫ k.hom = yoneda.map c ≫ d.V.1.hom)
    (x : ((modulePushforward B S hS k).obj F).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS k F d x =
      modulePushforwardCounitApp B S hS k F ⟨d.U, d.V, c, hc⟩ x := by
  obtain ⟨dU, dV, dg, dcomm⟩ := d
  subst h
  rfl

/-- **The chart formula for the composite of two linear maps of sections, at a chart diagram
whose vertical morphism factors.**  Let `d` be a chart diagram over `f ≫ g` and let its vertical
morphism factor as `a ≫ b` through a chart `V` of `Y`, so that `a` and `b` are chart diagrams
over `f` and over `g`.  Then the composite's component at `d` is the composite of the two
components: apply the outer linear map of sections on the upper diagram, then the inner one on
the lower.

This is what `AlgebraicGeometry.Space.ModuleFMap.comp` was owed, and it is stated at an
arbitrary `d` rather than at `AlgebraicGeometry.Space.ChartDiagram.comp` because that is the form
a consumer holding a chart diagram of its own can use — there is no transport from one to the
other; see `AlgebraicGeometry.Space.modulePushforwardCounitApp_congr_vertical`.

The chain is five steps.  The composite morphism of modules of
`AlgebraicGeometry.Space.moduleFMapHomComp` is read on a section, which is `Eq.refl` at free
variables (`AlgebraicGeometry.Space.ModuleFMap.comp_app_counit`);  the vertical morphism is
rewritten to `a ≫ b` inside the chart section;  the comparison of Stacks 03LU is crossed by
`AlgebraicGeometry.Space.modulePushforwardCounitApp_modulePushforwardCompIsoSection_chartDiagram`,
the chart-level reading of Stacks 03LU at a composed chart diagram;  the direct image along `g`
of the inner morphism of modules is moved out by
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`, naturality of the chart section;  and
the two remaining chart sections are the two linear maps of sections themselves, by
`AlgebraicGeometry.Space.modulePushforwardHomFMap_moduleFMapHom`. -/
theorem ModuleFMap.comp_app_of_vertical (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G)
    (d : ChartDiagram B S hS X.1 Z.1 (f ≫ g).hom) {V : SmallEtale B S hS Y.1}
    (a : (SmallEtale.toOver B S hS X.1).obj d.U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj d.V)
    (ha : d.U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ d.V.1.hom)
    (hd : d.g = a ≫ b) (s : H.val.obj (op d.V)) :
    (ModuleFMap.comp B S hS f g F G H ξ η).app d s =
      η.app ⟨d.U, V, a, ha⟩ (ξ.app ⟨V, d.V, b, hb⟩ s) := by
  refine Eq.trans (ModuleFMap.comp_app_counit B S hS f g F G H ξ η d s) ?_
  refine Eq.trans (modulePushforwardCounitApp_congr_vertical B S hS F d hd
    (ChartDiagram.comp B S hS f g a b ha hb).comm _) ?_
  refine Eq.trans (modulePushforwardCounitApp_modulePushforwardCompIsoSection_chartDiagram
    B S hS f g a b ha hb F _) ?_
  refine Eq.trans (congrArg (modulePushforwardCounitApp B S hS f F ⟨d.U, V, a, ha⟩)
    (modulePushforwardCounitApp_moduleSectionApp_map B S hS g
      (moduleFMapHom B S hS f F G η) ⟨V, d.V, b, hb⟩ _)) ?_
  refine Eq.trans (modulePushforwardCounitApp_moduleSectionApp_moduleFMapHom
    B S hS f F G η ⟨d.U, V, a, ha⟩ _) ?_
  exact congrArg (η.app ⟨d.U, V, a, ha⟩)
    (modulePushforwardCounitApp_moduleSectionApp_moduleFMapHom B S hS g G H ξ
      ⟨V, d.V, b, hb⟩ s)

/-- **The chart formula for the composite of two linear maps of sections.**  On a chart diagram
over `f ≫ g` that is composed from a chart diagram over `f` and one over `g` — a chart `U` of
`X` over a chart `V` of `Y` over a chart `W` of `Z` — the composite is the composite of the two
components.

This is `AlgebraicGeometry.Space.ModuleFMap.comp_app_of_vertical` at
`AlgebraicGeometry.Space.ChartDiagram.comp`, whose vertical morphism is `a ≫ b` by `Eq.refl`. -/
theorem ModuleFMap.comp_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (H : Modules.{u, u} B S hS Z.1 Z.2)
    (ξ : ModuleFMap B S hS g G H) (η : ModuleFMap B S hS f F G)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (s : H.val.obj (op W)) :
    (ModuleFMap.comp B S hS f g F G H ξ η).app
        (ChartDiagram.comp B S hS f g a b ha hb) s =
      η.app ⟨U, V, a, ha⟩ (ξ.app ⟨V, W, b, hb⟩ s) :=
  ModuleFMap.comp_app_of_vertical B S hS f g F G H ξ η
    (ChartDiagram.comp B S hS f g a b ha hb) a b ha hb rfl s

end AlgebraicGeometry.Space

end
