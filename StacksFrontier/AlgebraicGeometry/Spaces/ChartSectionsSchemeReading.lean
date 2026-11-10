module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeReadingModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompIsoChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictToChartSchemeSectionsTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections

/-!
# Étale chart sections and global sections of the scheme reading

For an étale chart `W` of an algebraic space `Y` and an `𝒪_Y`-module `N`, the sections `N(W)` of
`N` over `W` are identified with the global sections of the reading
`AlgebraicGeometry.Space.schemeReading N (chartToSpace W)` of `N` on the scheme of `W`:

`θ : N(W) ≃+ Γ(N_W, ⊤)`.

The identification is the chart section `AlgebraicGeometry.Space.modulePullbackChartSection` of the
inverse image along `chartToSpace W` at the chart of `yoneda.obj W` cut out by the top open, whose
sections are, definitionally, the global sections of the reading.  It is bijective because the
inverse image along an étale chart is the étale restriction (Stacks 03LW), which carries that chart
section back to the section it came from.

## Main definitions

* `AlgebraicGeometry.Space.chartSectionsReadingEquiv`: θ.
* `AlgebraicGeometry.Space.chartReadingSection`: the chart section of the reading along any
  represented point factoring through a chart.

## Main results

* `AlgebraicGeometry.Space.chartSectionsReadingEquiv_apply`: θ is the chart section.
* `AlgebraicGeometry.Space.chartSectionsReadingEquiv_naturality`: θ is natural in the module.
* `AlgebraicGeometry.Space.chartSectionsReadingEquiv_smul`: θ is linear over the functions on the
  chart.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The chart of `yoneda.obj T` cut out by the top open of the scheme underlying `T`, read through
the identification of the two small étale sites.  The global sections of the reading of a module
are, definitionally, its sections over this chart. -/
abbrev readingTopChart (T : BigFppfOver B S hS) : SmallEtale B S hS (yoneda.obj T) :=
  (selfOpensFunctor B S hS T).obj ⊤

/-- The morphism from `readingTopChart T` to the identity chart of `yoneda.obj T`. -/
def readingTopChartToIdChart (T : BigFppfOver B S hS) :
    readingTopChart T ⟶ idEtaleChart B S hS T :=
  ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage (readingTopChart T).obj.hom)
    ((Category.comp_id _).trans (yoneda.map_preimage _)))

/-- The morphism of the big site underlying `readingTopChartToIdChart`. -/
abbrev readingTopChartMap (T : BigFppfOver B S hS) :
    (SmallEtale.toOver B S hS (yoneda.obj T)).obj (readingTopChart T) ⟶ T :=
  (SmallEtale.toOver B S hS (yoneda.obj T)).map (readingTopChartToIdChart T)

variable {Y : AlgebraicSpaces B S hS}

/-- The square of `AlgebraicGeometry.Space.readingChartDiagram` commutes. -/
theorem readingChartDiagram_comm (V : SmallEtale B S hS Y.1) {T : BigFppfOver B S hS}
    (v : T ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    {ψ : representedAlgebraicSpace B S hS T ⟶ Y} (hψ : ψ.hom = yoneda.map v ≫ V.1.hom) :
    (readingTopChart T).1.hom ≫ ψ.hom =
      yoneda.map (readingTopChartMap T ≫ v) ≫ V.1.hom := by
  rw [hψ, Functor.map_comp, Category.assoc,
    show yoneda.map (readingTopChartMap T) = (readingTopChart T).1.hom from
      yoneda.map_preimage _]

/-- The morphism from the top chart to the identity chart is an isomorphism. -/
instance isIso_readingTopChartToIdChart (T : BigFppfOver B S hS) :
    IsIso (readingTopChartToIdChart T) := by
  have h : readingTopChartToIdChart T =
      (eqToIso (selfOpensFunctor_obj B S hS T ⊤) ≪≫
        openChartTopIso B S hS (yoneda.obj T) (idEtaleChart B S hS T)).hom :=
    (isTerminalIdEtaleChart B S hS T).hom_ext _ _
  rw [h]
  infer_instance

/-- The chart diagram of `v : T ⟶ V` over `ψ`. -/
def readingChartDiagram (V : SmallEtale B S hS Y.1) {T : BigFppfOver B S hS}
    (v : T ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    {ψ : representedAlgebraicSpace B S hS T ⟶ Y} (hψ : ψ.hom = yoneda.map v ≫ V.1.hom) :
    ChartDiagram B S hS (yoneda.obj T) Y.1 ψ.hom :=
  ⟨readingTopChart T, V, readingTopChartMap T ≫ v, readingChartDiagram_comm V v hψ⟩

/-- **The section of the reading attached to a section over a chart**: for a represented point
`ψ` of `Y` factoring through an étale chart `V` along `v`, the chart section of `ψ^*N` at the top
chart, which is a global section of the reading of `N` along `ψ`. -/
def chartReadingSection (N : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS Y.1)
    {T : BigFppfOver B S hS} (v : T ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    {ψ : representedAlgebraicSpace B S hS T ⟶ Y} (hψ : ψ.hom = yoneda.map v ≫ V.1.hom)
    (x : N.val.obj (op V)) : Γ(schemeReading N ψ, ⊤) :=
  modulePullbackChartSection B S hS ψ N (readingChartDiagram V v hψ) x

/-- The structure morphism of a chart, as the chart diagram of the identity. -/
theorem chartToSpace_hom_eq (W : SmallEtale B S hS Y.1) :
    (chartToSpace B S hS Y W).hom = yoneda.map (𝟙 _) ≫ W.1.hom := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]; rfl

/-- The chart morphism from the postcomposed top chart to `W`. -/
abbrev readingTopChartPostcomp (W : SmallEtale B S hS Y.1) :
    (smallEtalePostcomp B S hS (chartToSpace B S hS Y W) (isEtale_chartToSpace B S hS Y W)).obj
      (readingTopChart (chartFppfObject B S hS Y W)) ⟶ W :=
  (smallEtalePostcomp B S hS (chartToSpace B S hS Y W) (isEtale_chartToSpace B S hS Y W)).map
    (readingTopChartToIdChart (chartFppfObject B S hS Y W))

/-- The postcomposed top chart is isomorphic to the chart. -/
instance isIso_readingTopChartPostcomp (W : SmallEtale B S hS Y.1) :
    IsIso (readingTopChartPostcomp W) :=
  ((smallEtalePostcomp B S hS (chartToSpace B S hS Y W)
    (isEtale_chartToSpace B S hS Y W)).mapIso
      (@asIso _ _ _ _ (readingTopChartToIdChart (chartFppfObject B S hS Y W))
        (isIso_readingTopChartToIdChart (chartFppfObject B S hS Y W)))).isIso_hom

omit [B.Contains S] in
/-- The identity restriction map of a presheaf of modules on a section. -/
theorem chartReading_presheaf_map_id_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) (X : Cᵒᵖ) (m : M.obj X) : M.map (𝟙 X) m = m := by
  rw [M.map_id]; rfl

/-- A restriction map along an isomorphism, followed by the one along its inverse. -/
theorem chartReading_presheaf_map_inv_hom_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {X Y : C} (f : X ⟶ Y) (_ : IsIso f) (m : M.obj (op Y)) :
    M.map (inv f).op (M.map f.op m) = m := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
    chartReading_presheaf_map_id_apply]

/-- A restriction map along the inverse of an isomorphism, followed by the one along it. -/
theorem chartReading_presheaf_map_hom_inv_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {X Y : C} (f : X ⟶ Y) (_ : IsIso f) (m : M.obj (op X)) :
    M.map f.op (M.map (inv f).op m) = m := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, IsIso.hom_inv_id, op_id,
    chartReading_presheaf_map_id_apply]

/-- The two components of an isomorphism of modules are inverse on sections. -/
theorem chartReading_iso_inv_hom_val_app {Z : AlgebraicSpaces B S hS}
    {M₁ M₂ : Modules.{u, u} B S hS Z.1 Z.2} (e : M₁ ≅ M₂)
    (W : (smallEtaleRingedSite B S hS Z.1 Z.2).Cᵒᵖ) (z : M₂.val.obj W) :
    e.hom.val.app W (e.inv.val.app W z) = z :=
  (comp_val_app_apply B S hS e.inv e.hom W z).symm.trans
    (congrArg (fun m : M₂ ⟶ M₂ ↦ m.val.app W z) e.inv_hom_id)

/-- The inverse of an isomorphism of modules undoes it on sections. -/
theorem chartReading_iso_hom_inv_val_app {Z : AlgebraicSpaces B S hS}
    {M₁ M₂ : Modules.{u, u} B S hS Z.1 Z.2} (e : M₁ ≅ M₂)
    (W : (smallEtaleRingedSite B S hS Z.1 Z.2).Cᵒᵖ) (z : M₁.val.obj W) :
    e.inv.val.app W (e.hom.val.app W z) = z :=
  chartReading_iso_inv_hom_val_app e.symm W z

/-- The comparison of Stacks 03LW at a chart. -/
abbrev chartEtaleComparison (N : Modules.{u, u} B S hS Y.1 Y.2) (W : SmallEtale B S hS Y.1) :=
  (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Y W)
    (isEtale_chartToSpace B S hS Y W)).app N

/-- The section of the étale restriction over the top chart attached to a section over `W`. -/
abbrev chartEtaleTopSection (N : Modules.{u, u} B S hS Y.1 Y.2) (W : SmallEtale B S hS Y.1)
    (x : N.val.obj (op W)) :
    ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
      (isEtale_chartToSpace B S hS Y W)).obj N).val.obj
        (op (readingTopChart (chartFppfObject B S hS Y W))) :=
  N.val.map (readingTopChartPostcomp W).op x

/-- Restricting back along the inverse undoes `chartEtaleTopSection`. -/
theorem chartEtaleTopSection_inv (N : Modules.{u, u} B S hS Y.1 Y.2) (W : SmallEtale B S hS Y.1)
    (x : N.val.obj (op W)) :
    N.val.map (inv (readingTopChartPostcomp W)).op (chartEtaleTopSection N W x) = x :=
  chartReading_presheaf_map_inv_hom_apply N.val (readingTopChartPostcomp W)
    (isIso_readingTopChartPostcomp W) x

/-- `chartEtaleTopSection` undoes the restriction along the inverse. -/
theorem chartEtaleTopSection_inv' (N : Modules.{u, u} B S hS Y.1 Y.2) (W : SmallEtale B S hS Y.1)
    (z : ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
      (isEtale_chartToSpace B S hS Y W)).obj N).val.obj
        (op (readingTopChart (chartFppfObject B S hS Y W)))) :
    chartEtaleTopSection N W (N.val.map (inv (readingTopChartPostcomp W)).op z) = z :=
  chartReading_presheaf_map_hom_inv_apply N.val (readingTopChartPostcomp W)
    (isIso_readingTopChartPostcomp W) z

/-- **The global sections of the reading of a module on `yoneda.obj T` are its sections over
`readingTopChart T`.**  This is the identity of the underlying type; it is stated for a variable
module, so that the definitional unfolding is paid once here. -/
def readingTopSectionsAddEquiv (T : BigFppfOver B S hS)
    (P : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)) :
    P.val.obj (op (readingTopChart T)) ≃+ Γ(representedZariskiModule B S hS T P, ⊤) where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- `readingTopSectionsAddEquiv` is the identity on elements. -/
theorem readingTopSectionsAddEquiv_apply (T : BigFppfOver B S hS)
    (P : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (a : P.val.obj (op (readingTopChart T))) :
    readingTopSectionsAddEquiv T P a = a :=
  rfl

/-- `chartEtaleTopSection` is additive. -/
theorem chartEtaleTopSection_add (N : Modules.{u, u} B S hS Y.1 Y.2) (W : SmallEtale B S hS Y.1)
    (x y : N.val.obj (op W)) :
    chartEtaleTopSection N W (x + y) = chartEtaleTopSection N W x + chartEtaleTopSection N W y :=
  (N.val.map (readingTopChartPostcomp W).op).hom.map_add x y

/-- The inverse of the comparison of Stacks 03LW is additive on top sections. -/
theorem chartEtaleComparison_inv_add (N : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SmallEtale B S hS Y.1)
    (a b : ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
      (isEtale_chartToSpace B S hS Y W)).obj N).val.obj
        (op (readingTopChart (chartFppfObject B S hS Y W)))) :
    (chartEtaleComparison N W).inv.val.app (op (readingTopChart (chartFppfObject B S hS Y W)))
        (a + b) =
      (chartEtaleComparison N W).inv.val.app (op (readingTopChart (chartFppfObject B S hS Y W))) a
      + (chartEtaleComparison N W).inv.val.app
          (op (readingTopChart (chartFppfObject B S hS Y W))) b :=
  ((chartEtaleComparison N W).inv.val.app
    (op (readingTopChart (chartFppfObject B S hS Y W)))).hom.map_add a b

/-- A morphism of modules on `yoneda.obj T`, read on global sections, is its component at
`readingTopChart T`. -/
theorem readingTopSectionsAddEquiv_map (T : BigFppfOver B S hS)
    {P P' : SheafOfModules.{u} (representedStructureRingSheaf B S hS T)} (k : P ⟶ P')
    (a : P.val.obj (op (readingTopChart T))) :
    ((SmallEtale.restrictModule (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
        T.left.property).map ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map k)).app
        ⊤ a = k.val.app (op (readingTopChart T)) a :=
  rfl

/-- The sections over `W` are the sections of the inverse image over the top chart. -/
def chartTopSectionsAddEquiv (N : Modules.{u, u} B S hS Y.1 Y.2) (W : SmallEtale B S hS Y.1) :
    N.val.obj (op W) ≃+ ((modulePullback B S hS (chartToSpace B S hS Y W)).obj N).val.obj
      (op (readingTopChart (chartFppfObject B S hS Y W))) where
  toFun x := (chartEtaleComparison N W).inv.val.app
    (op (readingTopChart (chartFppfObject B S hS Y W))) (chartEtaleTopSection N W x)
  invFun y := N.val.map (inv (readingTopChartPostcomp W)).op
    ((chartEtaleComparison N W).hom.val.app
      (op (readingTopChart (chartFppfObject B S hS Y W))) y)
  left_inv x :=
    (congrArg (fun z ↦ N.val.map (inv (readingTopChartPostcomp W)).op z)
      (chartReading_iso_inv_hom_val_app (chartEtaleComparison N W)
        (op (readingTopChart (chartFppfObject B S hS Y W))) (chartEtaleTopSection N W x))).trans
      (chartEtaleTopSection_inv N W x)
  right_inv y :=
    (congrArg (fun z ↦ (chartEtaleComparison N W).inv.val.app
        (op (readingTopChart (chartFppfObject B S hS Y W))) z)
      (chartEtaleTopSection_inv' N W ((chartEtaleComparison N W).hom.val.app
        (op (readingTopChart (chartFppfObject B S hS Y W))) y))).trans
      (chartReading_iso_hom_inv_val_app (chartEtaleComparison N W)
        (op (readingTopChart (chartFppfObject B S hS Y W))) y)
  map_add' x y :=
    (congrArg (fun z ↦ (chartEtaleComparison N W).inv.val.app
        (op (readingTopChart (chartFppfObject B S hS Y W))) z)
      (chartEtaleTopSection_add N W x y)).trans
      (chartEtaleComparison_inv_add N W _ _)

/-- **The sections of a module over an étale chart are the global sections of its reading on
the scheme of the chart**, additively: the chart section at the top chart, through the comparison
of Stacks 03LW. -/
def chartSectionsReadingEquiv (N : Modules.{u, u} B S hS Y.1 Y.2) (W : SmallEtale B S hS Y.1) :
    N.val.obj (op W) ≃+ Γ(schemeReading N (chartToSpace B S hS Y W), ⊤) :=
  (chartTopSectionsAddEquiv N W).trans (readingTopSectionsAddEquiv (chartFppfObject B S hS Y W)
    ((modulePullback B S hS (chartToSpace B S hS Y W)).obj N))

/-- The chart section at the top chart, through the étale-unit diagram, is the chart section at
the reading diagram. -/
theorem modulePullbackChartSection_etaleUnit_readingTopChart (N : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SmallEtale B S hS Y.1) (x : N.val.obj (op W)) :
    modulePullbackChartSection B S hS (chartToSpace B S hS Y W) N
        (ChartDiagram.etaleUnit B S hS (chartToSpace B S hS Y W) (isEtale_chartToSpace B S hS Y W)
          (readingTopChart (chartFppfObject B S hS Y W)))
        (chartEtaleTopSection N W x) =
      chartReadingSection N W (𝟙 _) (chartToSpace_hom_eq W) x := by
  refine (modulePullbackChartSection_naturality B S hS (chartToSpace B S hS Y W) N
    (readingChartDiagram W (𝟙 _) (chartToSpace_hom_eq W))
    (ChartDiagram.etaleUnit B S hS (chartToSpace B S hS Y W) (isEtale_chartToSpace B S hS Y W)
      (readingTopChart (chartFppfObject B S hS Y W)))
    (𝟙 _) (readingTopChartPostcomp W) ?_ x).trans ?_
  · change 𝟙 _ ≫ (readingTopChartMap (chartFppfObject B S hS Y W) ≫ 𝟙 _) =
      𝟙 _ ≫ readingTopChartMap (chartFppfObject B S hS Y W)
    rw [Category.comp_id]
  · exact chartReading_presheaf_map_id_apply _ _ _

/-- **θ is the chart section at the top chart.** -/
theorem chartSectionsReadingEquiv_apply (N : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SmallEtale B S hS Y.1) (x : N.val.obj (op W)) :
    chartSectionsReadingEquiv N W x =
      chartReadingSection N W (𝟙 _) (chartToSpace_hom_eq W) x := by
  refine Eq.trans ?_ (modulePullbackChartSection_etaleUnit_readingTopChart N W x)
  refine Eq.trans ?_ (chartReading_iso_hom_inv_val_app (chartEtaleComparison N W)
    (op (readingTopChart (chartFppfObject B S hS Y W))) _)
  exact congrArg (fun z ↦ (chartEtaleComparison N W).inv.val.app
      (op (readingTopChart (chartFppfObject B S hS Y W))) z)
    (modulePullbackIsoEtaleModulePullback_hom_modulePullbackChartSection_etaleUnit B S hS
      (chartToSpace B S hS Y W) (isEtale_chartToSpace B S hS Y W) N
      (readingTopChart (chartFppfObject B S hS Y W)) (chartEtaleTopSection N W x)).symm

/-- **θ is natural in the module.** -/
theorem chartSectionsReadingEquiv_naturality {N N' : Modules.{u, u} B S hS Y.1 Y.2} (φ : N ⟶ N')
    (W : SmallEtale B S hS Y.1) (x : N.val.obj (op W)) :
    chartSectionsReadingEquiv N' W (φ.val.app (op W) x) =
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (chartFppfObject B S hS Y W))
          (chartFppfObject B S hS Y W).left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS Y W)).inverse.map
          ((modulePullback B S hS (chartToSpace B S hS Y W)).map φ))).app ⊤
        (chartSectionsReadingEquiv N W x) := by
  have h1 := modulePullbackChartSection_map B S hS (chartToSpace B S hS Y W) N φ
    (readingChartDiagram W (𝟙 _) (chartToSpace_hom_eq W)) x
  have h2 := readingTopSectionsAddEquiv_map (chartFppfObject B S hS Y W)
      ((modulePullback B S hS (chartToSpace B S hS Y W)).map φ)
      (modulePullbackChartSection B S hS (chartToSpace B S hS Y W) N
        (readingChartDiagram W (𝟙 _) (chartToSpace_hom_eq W)) x)
  rw [chartSectionsReadingEquiv_apply, chartSectionsReadingEquiv_apply]
  exact h1.symm.trans h2.symm

/-- The morphism to the identity chart factors through the open chart of the top open. -/
theorem readingTopChartToIdChart_eq_eqToHom (T : BigFppfOver B S hS) :
    readingTopChartToIdChart T = eqToHom (selfOpensFunctor_obj B S hS T ⊤) ≫
      (isTerminalIdEtaleChart B S hS T).from
        ((openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T)).obj ⊤) :=
  (isTerminalIdEtaleChart B S hS T).hom_ext _ _

/-- The morphism from the open chart of the top open to the identity chart is the inclusion. -/
theorem toOver_map_isTerminalIdEtaleChart_from_openChart (T : BigFppfOver B S hS) :
    (SmallEtale.toOver B S hS (yoneda.obj T)).map ((isTerminalIdEtaleChart B S hS T).from
        ((openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T)).obj ⊤)) =
      openSubHom T ⊤ := by
  apply yoneda.map_injective
  have h := CostructuredArrow.w ((isTerminalIdEtaleChart B S hS T).from
        ((openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T)).obj ⊤)).hom
  exact ((Category.comp_id _).symm.trans h).trans (Category.comp_id _)

/-- The scheme morphism underlying the top chart is the inclusion of the top open. -/
theorem toScheme_map_readingTopChartMap (T : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (readingTopChartMap T) =
      (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens).ι := by
  have h1 : (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (yoneda.obj T)).map
      ((isTerminalIdEtaleChart B S hS T).from
        ((openChartFunctor B S hS (yoneda.obj T) (idEtaleChart B S hS T)).obj ⊤))) =
      (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens).ι :=
    (congrArg (BigFppfOver.toScheme B S hS).map
      (toOver_map_isTerminalIdEtaleChart_from_openChart T)).trans
      (toScheme_map_openSubHom _ _ _ T ⊤)
  refine (congrArg (fun k => (BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS (yoneda.obj T)).map k))
    (readingTopChartToIdChart_eq_eqToHom T)).trans ?_
  refine (congrArg (BigFppfOver.toScheme B S hS).map (Functor.map_comp _ _ _)).trans ?_
  refine (Functor.map_comp _ _ _).trans ?_
  rw [h1, eqToHom_map, eqToHom_map]
  exact Category.id_comp _


/-- The structure map of the reading at the top open is pullback along the top chart. -/
theorem selfOpensStructureMap_top_apply (T : BigFppfOver B S hS)
    (c : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (show (representedStructureRingSheaf B S hS T).obj.obj (op (readingTopChart T)) from
      (selfOpensStructureMap B S hS T).hom.app (op ⊤) c) =
    (show (representedStructureRingSheaf B S hS T).obj.obj (op (readingTopChart T)) from
      ((BigFppfOver.toScheme B S hS).map (readingTopChartMap T)).appTop c) := by
  have h1 : (representedSmallEtaleEquivalence B S hS T).counit.app
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⊤) = 𝟙 _ :=
    @Subsingleton.elim _ (_root_.AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property _ ⊤)
      _ _
  change (representedSchemeStructureSheaf B S hS T).obj.map
      ((representedSmallEtaleEquivalence B S hS T).counit.app
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⊤)).op
      ((CategoryTheory.forget₂ CommRingCat RingCat.{u}).map (Scheme.Opens.topIso ⊤).inv c) = _
  have h2 : (representedSchemeStructureSheaf B S hS T).obj.map
      ((representedSmallEtaleEquivalence B S hS T).counit.app
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⊤)).op = 𝟙 _ :=
    (congrArg (fun k => (representedSchemeStructureSheaf B S hS T).obj.map
          (Quiver.Hom.op k)) h1).trans
      ((congrArg (representedSchemeStructureSheaf B S hS T).obj.map op_id).trans
        ((representedSchemeStructureSheaf B S hS T).obj.map_id _))
  refine (congrArg (fun k => RingCat.Hom.hom k
    (ConcreteCategory.hom ((CategoryTheory.forget₂ CommRingCat RingCat.{u}).map
      (Scheme.Opens.topIso ⊤).inv) c)) h2).trans ?_
  change (Scheme.Opens.topIso ⊤).inv c =
    ((BigFppfOver.toScheme B S hS).map (readingTopChartMap T)).appTop c
  rw [toScheme_map_readingTopChartMap, Scheme.Opens.ι_appTop]
  exact congrArg (fun k => ((BigFppfOver.toScheme B S hS).obj T).presheaf.map k c)
    (Subsingleton.elim _ _)

/-- The functions on the scheme of `T` act on the global sections of the reading through the
functions on the top chart. -/
theorem readingTopSectionsAddEquiv_smul (T : BigFppfOver B S hS)
    (P : SheafOfModules.{u} (representedStructureRingSheaf B S hS T))
    (c : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (a : P.val.obj (op (readingTopChart T))) :
    readingTopSectionsAddEquiv T P
        ((show (representedStructureRingSheaf B S hS T).obj.obj (op (readingTopChart T)) from
          ((BigFppfOver.toScheme B S hS).map (readingTopChartMap T)).appTop c) • a) =
      c • readingTopSectionsAddEquiv T P a :=
  (congrArg (fun r : (representedStructureRingSheaf B S hS T).obj.obj (op (readingTopChart T)) =>
    readingTopSectionsAddEquiv T P (r • a)) (selfOpensStructureMap_top_apply T c)).symm

/-- `chartTopSectionsAddEquiv` is semilinear over the functions on the chart. -/
theorem chartTopSectionsAddEquiv_smul (N : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SmallEtale B S hS Y.1) (c : Γ(chartScheme W, ⊤)) (x : N.val.obj (op W)) :
    chartTopSectionsAddEquiv N W (c • x) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (chartSpace B S hS Y W).1 (chartSpace B S hS Y W).2).O).obj.obj
          (op (readingTopChart (chartFppfObject B S hS Y W))) from
        ((BigFppfOver.toScheme B S hS).map
          (readingTopChartMap (chartFppfObject B S hS Y W))).appTop c) •
        chartTopSectionsAddEquiv N W x := by
  have h1 : chartEtaleTopSection N W (c • x) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (chartSpace B S hS Y W).1 (chartSpace B S hS Y W).2).O).obj.obj
          (op (readingTopChart (chartFppfObject B S hS Y W))) from
        ((BigFppfOver.toScheme B S hS).map
          (readingTopChartMap (chartFppfObject B S hS Y W))).appTop c) •
        chartEtaleTopSection N W x :=
    PresheafOfModules.map_smul N.val (readingTopChartPostcomp W).op c x
  exact (congrArg (fun z ↦ (chartEtaleComparison N W).inv.val.app
      (op (readingTopChart (chartFppfObject B S hS Y W))) z) h1).trans
    (((chartEtaleComparison N W).inv.val.app
      (op (readingTopChart (chartFppfObject B S hS Y W)))).hom.map_smul _ _)

/-- **θ is linear over the functions on the chart.** -/
theorem chartSectionsReadingEquiv_smul (N : Modules.{u, u} B S hS Y.1 Y.2)
    (W : SmallEtale B S hS Y.1) (c : Γ(chartScheme W, ⊤)) (x : N.val.obj (op W)) :
    chartSectionsReadingEquiv N W (c • x) = c • chartSectionsReadingEquiv N W x :=
  (congrArg (readingTopSectionsAddEquiv (chartFppfObject B S hS Y W)
      ((modulePullback B S hS (chartToSpace B S hS Y W)).obj N))
    (chartTopSectionsAddEquiv_smul N W c x)).trans
    (readingTopSectionsAddEquiv_smul (chartFppfObject B S hS Y W)
      ((modulePullback B S hS (chartToSpace B S hS Y W)).obj N) c _)

end AlgebraicGeometry.Space

end
