module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointSectionReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartBaseChangeCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicDirectImageChartMap

/-!
# Sections of a direct image along a representable morphism, and the unit on them

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  For an étale scheme chart `V` of `Y`, the sections of the direct image
`f_*N` over `V` are the sections of `N` over the base-changed chart `V ×_Y X`: the chart
projection `AlgebraicGeometry.Space.chartModProj` is a bijection.  This file records that, the
value of the unit of `f^* ⊣ f_*` under the chart projection — the chart section
`AlgebraicGeometry.Space.modulePullbackChartSection` at the cartesian chart diagram of `V`,
whose base change is bijective for a quasi-coherent module over affine charts — and the value of
the counit on such a chart section.

These are the three computations on sections that the gluing of modules of Stacks 08KV rests
on: the glued module is a fibre product of direct images along representable morphisms, and
its unit and counit are made of units and counits of `f^* ⊣ f_*`.

The cartesian chart diagram of `V` is `AlgebraicGeometry.Space.baseChangeChartDiagram` of
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicFunctionsPushforward.lean`.

## Main results

* `AlgebraicGeometry.Space.bijective_chartModProj`: the chart projection of the direct image is
  bijective.
* `AlgebraicGeometry.Space.chartModProj_modulePullbackAdjunction_unit`: the unit of
  `f^* ⊣ f_*`, projected to the base-changed chart, is the chart section of the cartesian chart
  diagram.
* `AlgebraicGeometry.Space.modulePullbackAdjunction_counit_chartSection`: the counit of
  `f^* ⊣ f_*`, applied to the chart section of a section of a direct image, is that section's
  chart projection.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)

/-- **The chart projection of the direct image is bijective**: it is the projection of a limit
over a category with an initial object to that object, after a component of an isomorphism of
sheaves. -/
theorem bijective_chartModProj (N : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1) :
    Function.Bijective (chartModProj B S hS f hf N V) := by
  have h₁ : Function.Bijective (chartRanApp B S hS f hf
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N).obj V) := by
    rw [← chartRanAppIso_hom]
    exact (isIso_iff_bijective _).1 inferInstance
  have h₂ : Function.Bijective (((smallEtaleComparisonRanIso B S hS X).hom.app
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)).hom.app
        (op (chartBaseChange B S hS f V))) := by
    have : IsIso (((smallEtaleComparisonRanIso B S hS X).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N)).hom) :=
      Functor.map_isIso (sheafToPresheaf (SpacesEtale.topology B S hS X) (Type u))
        ((smallEtaleComparisonRanIso B S hS X).hom.app
          (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) N))
    exact (isIso_iff_bijective _).1 (NatIso.isIso_app_of_isIso _ _)
  exact h₁.comp h₂

/-- The chart projection of a direct image is the chart projection at the base-changed index of
`AlgebraicGeometry.Space.moduleChartProjection`. -/
theorem chartModProj_eq_moduleChartProjection (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartModProj B S hS f hf N V z =
      (moduleChartProjection B S hS f V (smallBaseChangeIndex B S hS f hf V)).app
        (moduleSetSheaf B S hS X N) z :=
  (moduleChartProjection_app B S hS f V _ _ z).symm

/-- Two chart projections at equal indices agree. -/
theorem moduleChartProjection_congr {V : SmallEtale B S hS Y.1}
    {j₁ j₂ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (h : j₁ = j₂) (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    HEq ((moduleChartProjection B S hS f V j₁).app P x)
      ((moduleChartProjection B S hS f V j₂).app P x) := by
  subst h
  rfl

/-- **The chart projection of a direct image is the canonical map of sections at the cartesian
chart diagram.** -/
theorem chartModProj_eq_modulePushforwardCounitApp (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartModProj B S hS f hf N V z =
      modulePushforwardCounitApp B S hS f N (baseChangeChartDiagram B S hS f hf V) z :=
  (chartModProj_eq_moduleChartProjection B S hS f hf N V z).trans
    (eq_of_heq (moduleChartProjection_congr B S hS f
      (indexOfChartDiagram_baseChangeChartDiagram B S hS f hf V).symm _ z))

/-- **The unit of `f^* ⊣ f_*` on the base-changed chart.**  Projected to the chart `V ×_Y X`, the
unit of the adjunction of Stacks 03LU at a section of `M` over `V` is the chart section
`AlgebraicGeometry.Space.modulePullbackChartSection` of the cartesian chart diagram. -/
theorem chartModProj_modulePullbackAdjunction_unit (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS Y.1) (m : M.val.obj (op V)) :
    chartModProj B S hS f hf ((modulePullback B S hS f).obj M) V
        (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) m) =
      modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf V) m :=
  (chartModProj_eq_modulePushforwardCounitApp B S hS f hf _ V _).trans
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS f M
      (baseChangeChartDiagram B S hS f hf V) m)

/-- The chart projection is natural in the module. -/
theorem chartModProj_naturality {N N' : Modules.{u, u} B S hS X.1 X.2} (φ : N ⟶ N')
    (V : SmallEtale B S hS Y.1) (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartModProj B S hS f hf N' V (((modulePushforward B S hS f).map φ).val.app (op V) z) =
      φ.val.app (op ((smallBaseChange B S hS f hf).obj V)) (chartModProj B S hS f hf N V z) :=
  chartModProj_map B S hS f hf φ V z

/-- **The counit of `f^* ⊣ f_*` on a chart section.**  For a section `z` of a direct image
`f_*N` over a chart `V`, the counit applied to the chart section of `z` over `V ×_Y X` is the
chart projection of `z`: this is the triangle identity, read through the chart projection. -/
theorem modulePullbackAdjunction_counit_chartSection (N : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    ((modulePullbackAdjunction B S hS f).counit.app N).val.app
        (op ((smallBaseChange B S hS f hf).obj V))
        (modulePullbackChartSection B S hS f ((modulePushforward B S hS f).obj N)
          (baseChangeChartDiagram B S hS f hf V) z) =
      chartModProj B S hS f hf N V z := by
  have h1 := chartModProj_modulePullbackAdjunction_unit B S hS f hf
    ((modulePushforward B S hS f).obj N) V z
  have h2 := chartModProj_naturality B S hS f hf
    ((modulePullbackAdjunction B S hS f).counit.app N) V
    (((modulePullbackAdjunction B S hS f).unit.app ((modulePushforward B S hS f).obj N)).val.app
      (op V) z)
  have h3 : ((modulePushforward B S hS f).map
      ((modulePullbackAdjunction B S hS f).counit.app N)).val.app (op V)
      (((modulePullbackAdjunction B S hS f).unit.app ((modulePushforward B S hS f).obj N)).val.app
        (op V) z) = z :=
    congrArg (fun φ : (modulePushforward B S hS f).obj N ⟶
        (modulePushforward B S hS f).obj N => φ.val.app (op V) z)
      ((modulePullbackAdjunction B S hS f).right_triangle_components N)
  rw [← h1]
  exact h2.symm.trans (congrArg (chartModProj B S hS f hf N V) h3)

/-! ### Chart sections along chart diagrams -/

/-- The restriction map of a presheaf of modules along an identity is the identity. -/
theorem presheafOfModules_map_id_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) (X : Cᵒᵖ) (s : M.obj X) : M.map (𝟙 X) s = s := by
  rw [M.map_id]
  rfl

variable {B S hS} in
/-- The chart diagram obtained by precomposing the chart of the source with a morphism of
charts. -/
@[simps]
def ChartDiagram.precompSource {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (d : ChartDiagram B S hS F G p) {U' : SmallEtale B S hS F} (κ : U' ⟶ d.U) :
    ChartDiagram B S hS F G p where
  U := U'
  V := d.V
  g := (SmallEtale.toOver B S hS F).map κ ≫ d.g
  comm := by
    rw [yoneda.map_comp, Category.assoc, ← d.comm, ← Category.assoc]
    exact congrArg (· ≫ p) (CostructuredArrow.w κ.hom).symm

/-- The chart section of a precomposed chart diagram is the restriction of the chart section. -/
theorem modulePullbackChartSection_precomp (M : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) {U' : SmallEtale B S hS X.1} (κ : U' ⟶ d.U)
    (s : M.val.obj (op d.V)) :
    modulePullbackChartSection B S hS f M (d.precompSource κ) s =
      ((modulePullback B S hS f).obj M).val.map κ.op
        (modulePullbackChartSection B S hS f M d s) := by
  have h := modulePullbackChartSection_naturality B S hS f M d (d.precompSource κ) κ (𝟙 _)
    (by simp [ChartDiagram.precompSource]) s
  exact (congrArg (modulePullbackChartSection B S hS f M (d.precompSource κ))
    (presheafOfModules_map_id_apply M.val (op d.V) s).symm).trans h

/-- **The chart projection of a transport of direct images along an equality of morphisms** is
the restriction along the corresponding equality of base-changed charts. -/
theorem chartModProj_eqToHom {f f' : X ⟶ Y} (h : f = f')
    (hf : yoneda.relativelyRepresentable f.hom) (hf' : yoneda.relativelyRepresentable f'.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1)
    (z : ((modulePushforward B S hS f).obj N).val.obj (op V)) :
    chartModProj B S hS f' hf' N V
        (((eqToHom (congrArg (fun k : X ⟶ Y => modulePushforward B S hS k) h)).app N).val.app
          (op V) z) =
      N.val.map (eqToHom (by subst h; rfl) :
          (smallBaseChange B S hS f' hf').obj V ⟶ (smallBaseChange B S hS f hf).obj V).op
        (chartModProj B S hS f hf N V z) := by
  subst h
  exact (presheafOfModules_map_id_apply N.val _ _).symm

/-! ### The composition comparison of direct images on sections -/

/-- An isomorphism of sheaves of modules followed by its inverse is the identity on sections. -/
theorem sheafOfModules_iso_inv_hom_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (e : M ≅ N) (X : Cᵒᵖ)
    (y : N.val.obj X) : e.hom.val.app X (e.inv.val.app X y) = y := by
  have h1 : (e.inv ≫ e.hom).val.app X y = y := by
    rw [e.inv_hom_id]
    rfl
  exact h1

/-- An isomorphism of sheaves of modules preceded by its inverse is the identity on sections. -/
theorem sheafOfModules_iso_hom_inv_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (e : M ≅ N) (X : Cᵒᵖ)
    (y : M.val.obj X) : e.inv.val.app X (e.hom.val.app X y) = y :=
  sheafOfModules_iso_inv_hom_apply e.symm X y

/-- A natural isomorphism into sheaves of modules, after its inverse, is the identity on
sections. -/
theorem sheafOfModules_natIso_inv_hom_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {E : Type*} [Category E]
    {F G : E ⥤ SheafOfModules.{u} R} (e : F ≅ G) (N : E) (X : Cᵒᵖ) (y : (G.obj N).val.obj X) :
    (e.hom.app N).val.app X ((e.inv.app N).val.app X y) = y :=
  sheafOfModules_iso_inv_hom_apply (e.app N) X y

/-- A natural isomorphism into sheaves of modules, before its inverse, is the identity on
sections. -/
theorem sheafOfModules_natIso_hom_inv_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {E : Type*} [Category E]
    {F G : E ⥤ SheafOfModules.{u} R} (e : F ≅ G) (N : E) (X : Cᵒᵖ) (y : (F.obj N).val.obj X) :
    (e.inv.app N).val.app X ((e.hom.app N).val.app X y) = y :=
  sheafOfModules_iso_hom_inv_apply (e.app N) X y

section Comp

variable {A C D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
    (hreph : yoneda.relativelyRepresentable h.hom)
    (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom)

end Comp

/-! ### Sections of a fibre product of modules -/

variable {B S hS} in
/-- **The sections of a fibre product of modules over a chart are the fibre product of the
sections**: the two projections are jointly injective on sections, and a compatible pair of
sections lifts. -/
theorem sections_of_isPullback {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {P A A' C : Modules.{u, u} B S hS F hF}
    {fst : P ⟶ A} {snd : P ⟶ A'} {r : A ⟶ C} {s : A' ⟶ C} (h : IsPullback fst snd r s)
    (W : SmallEtale B S hS F) :
    (∀ z z' : P.val.obj (op W), fst.val.app (op W) z = fst.val.app (op W) z' →
        snd.val.app (op W) z = snd.val.app (op W) z' → z = z') ∧
      ∀ (x : A.val.obj (op W)) (y : A'.val.obj (op W)),
        r.val.app (op W) x = s.val.app (op W) y →
          ∃ z : P.val.obj (op W), fst.val.app (op W) z = x ∧ snd.val.app (op W) z = y := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O
  let Φ : Modules.{u, u} B S hS F hF ⥤ Type u := SheafOfModules.forget R ⋙
    PresheafOfModules.evaluation R.obj (op W) ⋙ CategoryTheory.forget (ModuleCat.{u} _)
  have h' := h.map Φ
  obtain ⟨-, hinj, hex⟩ := (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).1 h'
  exact ⟨fun z z' h1 h2 => hinj z z' ⟨h1, h2⟩, fun x y hxy => hex x y hxy⟩

end AlgebraicGeometry.Space

end
