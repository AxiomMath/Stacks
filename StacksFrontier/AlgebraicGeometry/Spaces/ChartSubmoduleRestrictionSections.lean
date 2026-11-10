module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparisonIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GradedAlgebraChartSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionsMeromorphic

/-!
# Sections of the chart restriction of a submodule

Let `X` be an algebraic space, `M` an `𝒪_X`-module and `K ⊆ M` a submodule on the small étale
site.  `AlgebraicGeometry.Space.restrictSubmoduleToChart M K W` is the Zariski submodule of the
chart restriction `M|_W` cut out by `K`, defined as a local closure of a sectionwise range.  This
file identifies its sections: through
`AlgebraicGeometry.Space.chartSectionsToRestrict`, which reads the sections of `M` over the étale
chart cut out by a Zariski open `O` of `chartScheme W` as sections of `M|_W` over `O`, a section
lies in the chart restriction of `K` exactly when it lies in `K`.  Consequently the chart
restriction of submodules reflects inclusions.

## Main results

* `AlgebraicGeometry.Space.restrictToChartSchemeFunctor_map_chartSectionsToRestrict`: the reading
  of sections is natural in the module.
* `AlgebraicGeometry.Space.chartSectionsToRestrict_mem_restrictSubmoduleToChart_iff`: **a section
  of `M` over the chart cut out by `O` lies in `K` iff its reading lies in the chart restriction of
  `K`.**
* `AlgebraicGeometry.Space.le_of_forall_restrictSubmoduleToChart_le` and
  `AlgebraicGeometry.Space.restrictSubmoduleToChart_le_iff`: **the chart restriction of submodules
  reflects inclusions**: `K₁ ≤ K₂` iff `K₁|_W ≤ K₂|_W` for every étale chart `W`.

## Implementation notes

The reading of sections is bijective for every module (the restricted presheaf of a sheaf on the
small étale site is already a Zariski sheaf), in particular for `K` itself viewed as a module, and
the restriction of the inclusion `K ⟶ M` is computed on readings by naturality.  A section in the
chart restriction of `K` therefore lies in `K` after restriction to the members of a Zariski cover
of `O`; the corresponding charts cover the chart of `O` in the small étale site, and `K` is a sheaf
submodule.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X : AlgebraicSpaces B S hS)

/-- **The reading of chart sections is natural in the module**: the chart restriction of a
morphism `φ : M ⟶ M'` acts on readings as `φ` acts on sections. -/
theorem restrictToChartSchemeFunctor_map_chartSectionsToRestrict
    {M M' : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ M') (W : SmallEtale B S hS X.1)
    (O : (chartScheme W).Opens) (x : M.val.obj (op (openChart B S hS X.1 W O))) :
    ((restrictToChartSchemeFunctor B S hS X.1 X.2 W).map φ).val.app (op O)
        (chartSectionsToRestrict X M W O x) =
      chartSectionsToRestrict X M' W O (φ.val.app _ x) := by
  let : HasSheafify (Opens.grothendieckTopology (chartScheme W)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology (chartScheme W)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact (congrArg (fun f => (PresheafOfModules.Hom.app f (op O)).hom (ULift.up x))
    ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (chartScheme W).ringCatSheaf.obj)).unit_naturality
      ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS X.1 W)).map
        ((SheafOfModules.forget _).map
          (SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, u}.map φ)))))

/-- **The direct-image form of the chart comparison is natural in the module.**  Both sides are
determined by their values on readings of sections of `M`, where they are restriction of sections
along `AlgebraicGeometry.Space.openChartRestrict` followed or preceded by `φ`. -/
theorem restrictToChartSchemePushforwardComparison_naturality
    {M M' : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ M') {U V : SmallEtale B S hS X.1}
    (g : V ⟶ U) :
    (restrictToChartSchemeFunctor B S hS X.1 X.2 U).map φ ≫
        restrictToChartSchemePushforwardComparison B S hS X.1 X.2 M' g =
      restrictToChartSchemePushforwardComparison B S hS X.1 X.2 M g ≫
        (Scheme.Modules.pushforward (chartSchemeMap g)).map
          ((restrictToChartSchemeFunctor B S hS X.1 X.2 V).map φ) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun O => ?_)
  obtain ⟨O⟩ := O
  ext a
  obtain ⟨x, rfl⟩ := (bijective_chartSectionsToRestrict X M U O).2 a
  change (restrictToChartSchemePushforwardComparison B S hS X.1 X.2 M' g).val.app (op O)
      (((restrictToChartSchemeFunctor B S hS X.1 X.2 U).map φ).val.app (op O)
        (chartSectionsToRestrict X M U O x)) =
    ((restrictToChartSchemeFunctor B S hS X.1 X.2 V).map φ).val.app (op (chartSchemeMap g ⁻¹ᵁ O))
      ((restrictToChartSchemePushforwardComparison B S hS X.1 X.2 M g).val.app (op O)
        (chartSectionsToRestrict X M U O x))
  rw [restrictToChartSchemeFunctor_map_chartSectionsToRestrict,
    restrictToChartSchemePushforwardComparison_chartSectionsToRestrict,
    restrictToChartSchemePushforwardComparison_chartSectionsToRestrict]
  refine Eq.trans ?_ (restrictToChartSchemeFunctor_map_chartSectionsToRestrict X φ V _ _).symm
  exact congrArg (chartSectionsToRestrict X M' V (chartSchemeMap g ⁻¹ᵁ O))
    (PresheafOfModules.naturality_apply φ.val (openChartRestrict B S hS X.1 g O).op x).symm

/-- **The chart comparison is natural in the module**: for `φ : M ⟶ M'` the square formed by the
comparisons of `M` and `M'` along a morphism of charts `g : V ⟶ U` and the chart restrictions of
`φ` commutes. -/
theorem restrictToChartSchemePullbackComparison_naturality
    {M M' : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ M') {U V : SmallEtale B S hS X.1}
    (g : V ⟶ U) :
    (Scheme.Modules.pullback (chartSchemeMap g)).map
          ((restrictToChartSchemeFunctor B S hS X.1 X.2 U).map φ) ≫
        restrictToChartSchemePullbackComparison B S hS X.1 X.2 M' g =
      restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g ≫
        (restrictToChartSchemeFunctor B S hS X.1 X.2 V).map φ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (chartSchemeMap g)).homEquiv _ _).injective
  refine ((Scheme.Modules.pullbackPushforwardAdjunction (chartSchemeMap g)).homEquiv_naturality_left
    _ _).trans (Eq.trans ?_ ((Scheme.Modules.pullbackPushforwardAdjunction
      (chartSchemeMap g)).homEquiv_naturality_right _ _).symm)
  have h : ∀ N : Modules.{u, u} B S hS X.1 X.2,
      (Scheme.Modules.pullbackPushforwardAdjunction (chartSchemeMap g)).homEquiv
        ((restrictToChartSchemeFunctor B S hS X.1 X.2 U).obj N) _
        (restrictToChartSchemePullbackComparison B S hS X.1 X.2 N g) =
      restrictToChartSchemePushforwardComparison B S hS X.1 X.2 N g :=
    fun _ => Equiv.apply_symm_apply _ _
  rw [h, h]
  exact restrictToChartSchemePushforwardComparison_naturality X φ g

/-- A sieve generated by a family of arrows along each of which a section restricts into a
submodule is contained in the sieve of that section. -/
theorem ofArrows_le_sieveOfSection {M : Modules.{u, u} B S hS X.1 X.2} (K : M.Submodule)
    {V : SmallEtale B S hS X.1} {ι : Type*} {Y : ι → SmallEtale B S hS X.1} (a : ∀ j, Y j ⟶ V)
    (y : M.val.obj (op V)) (h : ∀ j, M.val.map (a j).op y ∈ K.obj (op (Y j))) :
    Sieve.ofArrows Y a ≤ K.toSubfunctor.sieveOfSection y := by
  rintro Z _ ⟨T, g, _, ⟨j⟩, rfl⟩
  change M.val.map ((a j).op ≫ g.op) y ∈ K.obj (op Z)
  have e := ConcreteCategory.congr_hom (M.val.map_comp (a j).op g.op) y
  exact (congrArg (· ∈ K.obj (op Z)) e).mpr (K.map_mem g.op (h j))

/-- A section lies in a submodule `K` if its restrictions along a covering family of arrows do. -/
private theorem mem_of_ofArrows_mem_topology {M : Modules.{u, u} B S hS X.1 X.2} (K : M.Submodule)
    {V : SmallEtale B S hS X.1} {ι : Type*} {Y : ι → SmallEtale B S hS X.1} (a : ∀ j, Y j ⟶ V)
    (y : M.val.obj (op V)) (h : ∀ j, M.val.map (a j).op y ∈ K.obj (op (Y j)))
    (hc : Sieve.ofArrows Y a ∈ SmallEtale.topology B S hS X.1 V) : y ∈ K.obj (op V) :=
  K.isSheaf y (GrothendieckTopology.superset_covering _ (ofArrows_le_sieveOfSection X K a y h) hc)

/-- **A section of `M` over the chart cut out by a Zariski open lies in a submodule `K` iff its
reading lies in the chart restriction of `K`.** -/
theorem chartSectionsToRestrict_mem_restrictSubmoduleToChart_iff
    (M : Modules.{u, u} B S hS X.1 X.2) (K : M.Submodule) (W : SmallEtale B S hS X.1)
    (O : (chartScheme W).Opens) (y : M.val.obj (op (openChart B S hS X.1 W O))) :
    chartSectionsToRestrict X M W O y ∈ (restrictSubmoduleToChart M K W).obj (op O) ↔
      y ∈ K.obj (op (openChart B S hS X.1 W O)) := by
  constructor
  · intro hx
    rw [mem_restrictSubmoduleToChart] at hx
    refine mem_of_ofArrows_mem_topology X K _ y (fun j => ?_)
      (ofArrows_openChartHomOfLE_mem_topology B S hS X.1 W
        (fun j : {p : Σ O' : (chartScheme W).Opens, O' ⟶ O //
          ((Stacks.SheafOfModules.presheafRangeSubmodule
            ((restrictToChartSchemeFunctor B S hS X.1 X.2 W).map
              K.ι).val).toSubfunctor.sieveOfSection
              (chartSectionsToRestrict X M W O y)).arrows p.2} => j.1.1)
        (fun j => j.1.2.le) fun x hxO => by
          obtain ⟨O', f, hf, hxO'⟩ := hx x hxO
          exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨O', f⟩, hf⟩, hxO'⟩)
    obtain ⟨⟨O', f⟩, hf⟩ := j
    have hf' : (restrictToChartScheme B S hS X.1 X.2 M W).val.map f.op
        (chartSectionsToRestrict X M W O y) ∈ (Stacks.SheafOfModules.presheafRangeSubmodule
          ((restrictToChartSchemeFunctor B S hS X.1 X.2 W).map K.ι).val).obj (op O') := hf
    have hm' : ∃ z : K.toSheafOfModules.val.obj (op (openChart B S hS X.1 W O')),
        ((restrictToChartSchemeFunctor B S hS X.1 X.2 W).map K.ι).val.app (op O')
          (chartSectionsToRestrict X K.toSheafOfModules W O' z) =
        (restrictToChartScheme B S hS X.1 X.2 M W).val.map f.op
          (chartSectionsToRestrict X M W O y) := by
      obtain ⟨m, hm⟩ := (Stacks.SheafOfModules.mem_presheafRangeSubmodule_obj _ (op O') _).1 hf'
      obtain ⟨z, hz⟩ := (bijective_chartSectionsToRestrict X K.toSheafOfModules W O').2 m
      exact ⟨z, hz ▸ hm⟩
    obtain ⟨z, hm⟩ := hm'
    have e : chartSectionsToRestrict X M W O' (K.ι.val.app _ z) =
        chartSectionsToRestrict X M W O'
          (M.val.map ((openChartFunctor B S hS X.1 W).map f).op y) := by
      rw [← restrictToChartSchemeFunctor_map_chartSectionsToRestrict X K.ι W O' z,
        ← chartSectionsToRestrict_naturality X M W f y, ← hm]
    exact ((bijective_chartSectionsToRestrict X M W O').1 e ▸ z.2 :
      M.val.map ((openChartFunctor B S hS X.1 W).map f).op y ∈
        K.obj (op (openChart B S hS X.1 W O')))
  · intro hy
    have h := app_mem_restrictSubmoduleToChart M K W (op O)
      (chartSectionsToRestrict X K.toSheafOfModules W O ⟨y, hy⟩)
    rw [restrictToChartSchemeFunctor_map_chartSectionsToRestrict X K.ι W O ⟨y, hy⟩] at h
    exact h

/-- **The chart restriction of submodules reflects inclusions.** -/
theorem le_of_forall_restrictSubmoduleToChart_le (M : Modules.{u, u} B S hS X.1 X.2)
    {K₁ K₂ : M.Submodule}
    (h : ∀ W, restrictSubmoduleToChart M K₁ W ≤ restrictSubmoduleToChart M K₂ W) : K₁ ≤ K₂ := by
  intro V x hx
  obtain ⟨W⟩ := V
  have hy : M.val.map (openChartInclusion B S hS X.1 W ⊤).op x ∈
      K₂.obj (op (openChart B S hS X.1 W ⊤)) :=
    (chartSectionsToRestrict_mem_restrictSubmoduleToChart_iff X M K₂ W ⊤ _).1
      (h W (op ⊤) ((chartSectionsToRestrict_mem_restrictSubmoduleToChart_iff X M K₁ W ⊤ _).2
        (K₁.map_mem _ hx)))
  exact mem_of_ofArrows_mem_topology X K₂ _ x (fun _ => hy)
    (ofArrows_openChartInclusion_mem_topology B S hS X.1 W (fun _ : Unit => ⊤) iSup_const)

/-- The chart restriction of submodules is an order embedding: `K₁ ≤ K₂` iff `K₁|_W ≤ K₂|_W` for
every étale chart `W`. -/
theorem restrictSubmoduleToChart_le_iff (M : Modules.{u, u} B S hS X.1 X.2)
    {K₁ K₂ : M.Submodule} :
    (∀ W, restrictSubmoduleToChart M K₁ W ≤ restrictSubmoduleToChart M K₂ W) ↔ K₁ ≤ K₂ :=
  ⟨le_of_forall_restrictSubmoduleToChart_le X M,
    fun h W => restrictSubmoduleToChart_mono M h W⟩

end AlgebraicGeometry.Space

end
