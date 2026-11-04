module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartReadingInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement

/-!
# The pullback of a glued module is the glued module of the pulled-back system

Let `a : X' ⟶ X` be a morphism of algebraic spaces, `𝓜` a chart-scheme module system on `X` and
`𝓜'` one on `X'` (`AlgebraicGeometry.Space.ChartSchemeModuleSystem`).  Suppose given, for every
chart square `q : W ⟶ V` of `a` (`AlgebraicGeometry.Space.ChartSchemeModuleSystem.ChartSquare`),
an identification `c q : g^*(M V) ≅ M' W`, compatible with the transitions of both systems
(`…ComparisonCompatTarget`, `…ComparisonCompatSource`).  Then

`a^*(glue 𝓜) ≅ glue 𝓜'`.

The proof glues isomorphisms over a covering family of the small étale site of `X'` by the
gluing form of Stacks 03EM (`exists_iso_of_isCompatible`).  The family is that of the charts `W`
of `X'` carrying a chart square; it covers the final object
(`AlgebraicGeometry.Space.coversTop_affineChartDiagramCharts`).  Over the chart of a chart square
`q` the restrictions of the two modules are identified through `c q`
(`AlgebraicGeometry.Space.ChartSchemeModuleSystem.chartSquareIso`).  The family is compatible:

* restricting the identification at `q` along a morphism `l : W₁ ⟶ W` of charts gives the
  identification at the square `q.precomp l` (`…chartSquareIso_precomp`), by the
  associativity of the comparisons of Stacks 03LU, the composition law of the identification
  `g^*(M^a) ≅ (g^*M)^a` of Stacks 03DX (2), the compatibility of the glued module of `𝓜'` with
  its transitions, and `ComparisonCompatSource`;
* the identification at `q.postcomp k` is the one at `q` (`…chartSquareIso_postcomp`), by the
  same coherences on the side of `X` and `ComparisonCompatTarget`;
* two chart squares with the same chart `W` of `X'` are both of the form `q.postcomp k` for the
  square through the fibre product of their two charts of `X`
  (`AlgebraicGeometry.Space.SmallEtale.prodObj`), so they give the same identification.

## Main definitions

* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.chartSquareRestrictionIso`: the restriction of
  `a^*(glue 𝓜)` to the chart of a chart square, read as the module attached to `g^*(M V)`.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.chartSquareIso`: the restrictions of
  `a^*(glue 𝓜)` and of `glue 𝓜'` to the chart of a chart square, identified through `c q`.
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.modulePullbackGlueIso`: **`a^*(glue 𝓜) ≅
  glue 𝓜'`.**
* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.baseChangeModuleGlueIsoOfComparisons`: its
  consequence for the base change of the glued module to a scheme over `X`.

## Main results

* `AlgebraicGeometry.Space.ChartSchemeModuleSystem.coversTop_chartSquare`: the charts carrying a
  chart square cover the final object of the small étale site of `X'`.
* `…chartModuleRestriction_map_modulePullbackGlueIso_hom`: the global isomorphism restricts to
  `chartSquareIso q` on every chart square.

## Implementation notes

Every coherence is proved in two layers: an abstract pasting lemma over arbitrary categories
(`postcomp_aux`, `precomp_aux`, `precompE_aux`), and a lemma at *variable* represented spaces,
morphisms and modules (`postcomp_core`, `precomp_core`, `precompE_core`) in which the library
lemmas are instantiated. Only the second layer is instantiated at the charts. Comparing morphisms —
`Iso.hom` of comparisons of Stacks 03LU — across the two spellings of a chart space (`chartSpace`
and the represented space of `chartFppfObject`) or of a morphism of charts (`chartMap` and
`representedSpaceMap`) does not terminate within the heartbeat budget, in the elaborator, and for
`AlgebraicGeometry.Space.QuasiCoherentDescent.restrictForm` also in the kernel; equations of
*isomorphisms* are compared argument by argument and are cheap. So the statements at the charts are
equations of isomorphisms wherever possible, the identifications at the charts enter the variable
layer as variables with defining equations (`precompE_core'`), and `restrictForm` is unfolded only
at variables (`AlgebraicGeometry.Space.restrictForm_eq_comp`).

`modulePullbackGlueIso` is the isomorphism chosen in the existence statement
`exists_modulePullbackGlueIso`: the gluing form of Stacks 03EM in the library is an existence
statement.  Its defining property is `chartModuleRestriction_map_modulePullbackGlueIso_hom`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Slice readings of chart restrictions -/

/-- The slice reading of a morphism of chart restrictions is the inverse of the reading of
Stacks 04M0 (`AlgebraicGeometry.Space.chartHomEquiv`), on underlying presheaf morphisms. -/
theorem chartSliceHom_eq_chartHomEquiv_symm (X : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS X.1) (M N : Modules.{u, u} B S hS X.1 X.2)
    (a : (chartModuleRestriction B S hS X W).obj M ⟶ (chartModuleRestriction B S hS X W).obj N) :
    chartSliceHom B S hS X W M N a = ((chartHomEquiv B S hS M N W).symm a).val := by
  refine congrArg SheafOfModules.Hom.val ?_
  apply (chartModuleSliceReindex B S hS X W).map_injective
  rw [Functor.map_preimage]
  set β := (chartHomEquiv B S hS M N W).symm a with hβ
  have h : a = ((chartModuleRestrictionSliceIso B S hS X W).app M).hom ≫
      (chartModuleSliceReindex B S hS X W).map β ≫
        ((chartModuleRestrictionSliceIso B S hS X W).app N).inv :=
    ((chartHomEquiv B S hS M N W).apply_symm_apply a).symm.trans
      (chartHomEquiv_apply B S hS M N W β)
  rw [h]
  simp only [Iso.app_hom, Iso.app_inv, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- **Relocalizing a slice reading is the slice reading of the restricted reading.**  For a
morphism `f : Z ⟶ W` of charts, the relocalization along `f` of the slice reading of a morphism
`a` of the restrictions to `W` is the slice reading of the restricted reading of `a` along the
morphism of chart spaces. -/
theorem homRestr_chartSliceHom (X : AlgebraicSpaces B S hS) {Z W : SmallEtale B S hS X.1}
    (f : Z ⟶ W) (M N : Modules.{u, u} B S hS X.1 X.2)
    (a : (chartModuleRestriction B S hS X W).obj M ⟶ (chartModuleRestriction B S hS X W).obj N) :
    homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val f
        (chartSliceHom B S hS X W M N a) =
      chartSliceHom B S hS X Z M N
        (QuasiCoherentDescent.restrictForm B S hS (chartMap B S hS X f) (chartToSpace B S hS X W)
          (chartToSpace B S hS X Z) (chartMap_comp_chartToSpace B S hS X f) a) := by
  rw [chartSliceHom_eq_chartHomEquiv_symm, ← chartSliceHomRestrict_val]
  refine (congrArg SheafOfModules.Hom.val ?_).trans
    (chartSliceHom_eq_chartHomEquiv_symm B S hS X Z M N _).symm
  apply (chartHomEquiv B S hS M N Z).injective
  refine (chartHomEquiv_sliceRestrict B S hS M N f _).trans ?_
  exact (congrArg (QuasiCoherentDescent.restrictForm B S hS (chartMap B S hS X f)
      (chartToSpace B S hS X W) (chartToSpace B S hS X Z) (chartMap_comp_chartToSpace B S hS X f))
      ((chartHomEquiv B S hS M N W).apply_symm_apply a)).trans
    ((chartHomEquiv B S hS M N Z).apply_symm_apply _).symm

/-- The pullback of an isomorphism of quasi-coherent modules along a morphism `g` of the site, as
an isomorphism of quasi-coherent modules on the scheme of the source. -/
abbrev quasicoherentPullbackIso {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (e : M ≅ N) :
    quasicoherentPullbackObj B S hS g M ≅ quasicoherentPullbackObj B S hS g N :=
  ObjectProperty.isoMk _ ((Scheme.Modules.pullback
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).mapIso
      ((ObjectProperty.ι _).mapIso e))

/-- The restricted reading of Stacks 04W3, written out as a composite. -/
theorem restrictForm_eq_comp {A P Q : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS A.1 A.2} (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    (w : (modulePullback B S hS k).obj M ⟶ (modulePullback B S hS k).obj N) :
    QuasiCoherentDescent.restrictForm B S hS p k r hr w =
      (QuasiCoherentDescent.pullbackComparison B S hS p k r hr M).hom ≫
        (modulePullback B S hS p).map w ≫
        (QuasiCoherentDescent.pullbackComparison B S hS p k r hr N).inv :=
  rfl

namespace ChartSchemeModuleSystem

variable {B S hS} {X : AlgebraicSpaces B S hS} (𝓜 : ChartSchemeModuleSystem B S hS X)

/-! ### Chart squares -/

namespace ChartSquare

variable {X' : AlgebraicSpaces B S hS} {a : X' ⟶ X}

/-- The square of a chart square, read as a commuting square of algebraic spaces. -/
theorem hom_eq (q : ChartSquare a) :
    representedSpaceMap B S hS q.g ≫ chartToSpace B S hS X q.V =
      chartToSpace B S hS X' q.W ≫ a :=
  ObjectProperty.hom_ext _ q.w

/-- **The chart square through the fibre product of two charts of the target.**  For a chart
square `q` and a second morphism `g₂` from the chart `q.W` to a chart `V₂` of `X` over `a`, the
pair `(q.g, g₂)` is a morphism to the fibre product `q.V ×_X V₂`, which is an étale chart of
`X` (`AlgebraicGeometry.Space.SmallEtale.prodObj`). -/
def pair (q : ChartSquare a) (V₂ : SmallEtale B S hS X.1)
    (g₂ : (SmallEtale.toOver B S hS X'.1).obj q.W ⟶ (SmallEtale.toOver B S hS X.1).obj V₂)
    (w₂ : yoneda.map g₂ ≫ V₂.obj.hom = q.W.obj.hom ≫ a.hom) : ChartSquare a where
  W := q.W
  V := SmallEtale.prodObj B S hS X.1 q.V V₂
  g := q.V.property.rep.lift' q.g g₂ (q.w.trans w₂.symm)
  w := by
    change yoneda.map _ ≫ (yoneda.map (q.V.property.rep.snd V₂.obj.hom) ≫ V₂.obj.hom) = _
    rw [← Functor.map_comp_assoc, Functor.relativelyRepresentable.lift'_snd]
    exact w₂

end ChartSquare

/-- **The charts carrying a chart square cover the final object** of the small étale site of
`X'`: they include the charts carrying an affine chart diagram over `a`, which cover it by
`AlgebraicGeometry.Space.coversTop_affineChartDiagramCharts`. -/
theorem coversTop_chartSquare {X' : AlgebraicSpaces B S hS} (a : X' ⟶ X) :
    (SmallEtale.topology B S hS X'.1).CoversTop (fun q : ChartSquare a ↦ q.W) :=
  (coversTop_affineChartDiagramCharts B S hS a).of_exists_hom fun W ↦ by
    obtain ⟨-, V, g, hg, -⟩ := W.2
    exact ⟨⟨W.1, V, g, hg⟩, ⟨𝟙 W.1⟩⟩

/-! ### The restriction of the pulled-back glued module to a chart square -/

variable {X' : AlgebraicSpaces B S hS} (a : X' ⟶ X)

/-- **The restriction of `a^*(glue 𝓜)` to the chart of a chart square `q`** is the module
attached through Stacks 03DX (2) to `g^*(M V)`: the comparisons of Stacks 03LU along the two
sides of the square, the counit of Stacks 03LY at `V`, and the identification
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`.  This is
`AlgebraicGeometry.Space.ChartSchemeModuleSystem.chartModuleRestrictionModulePullbackGlueIso`
with the comparisons written as factorization comparisons. -/
def chartSquareRestrictionIso (q : ChartSquare a) :
    (chartModuleRestriction B S hS X' q.W).obj ((modulePullback B S hS a).obj 𝓜.glue) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X' q.W)).functor.obj
        (quasicoherentPullbackObj B S hS q.g (𝓜.qcohObj q.V))).obj :=
  (QuasiCoherentDescent.pullbackComparison B S hS (chartToSpace B S hS X' q.W) a
      (chartToSpace B S hS X' q.W ≫ a) rfl 𝓜.glue).symm ≪≫
    QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS q.g)
      (chartToSpace B S hS X q.V) (chartToSpace B S hS X' q.W ≫ a) q.hom_eq 𝓜.glue ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS q.g)).mapIso (𝓜.glueChartModuleIso q.V) ≪≫
    modulePullbackRepresentedQuasicoherentIso B S hS q.g (𝓜.qcohObj q.V)

/-- The pasting behind `chartSquareRestrictionIso_postcomp`, at variables. -/
private theorem postcomp_aux {C D E : Type*} [Category C] [Category D] [Category E]
    (Rg : D ⥤ C) (Rk : E ⥤ D) (Rg' : E ⥤ C)
    {B₀ T₀ : C} {Q₀ N₀ : E} {QV NV KV : D} {Y Y₁ Y₂ : C}
    (i : T₀ ≅ B₀) (a₁ : T₀ ≅ Rg'.obj Q₀) (x₀ : Q₀ ≅ N₀) (bI : Rg'.obj N₀ ≅ Y)
    (πQ : Rg'.obj Q₀ ≅ Rg.obj (Rk.obj Q₀)) (πN : Rg'.obj N₀ ≅ Rg.obj (Rk.obj N₀))
    (ρN : Rg.obj (Rk.obj N₀) ≅ Rg'.obj N₀)
    (c₁ : T₀ ≅ Rg.obj QV) (d : QV ≅ Rk.obj Q₀) (mkI : Rk.obj N₀ ≅ KV) (mgI : Rg.obj KV ≅ Y₁)
    (wI : Y₁ ≅ Y) (aτI : KV ≅ NV) (aτ : KV ⟶ NV) (xV : QV ≅ NV) (mgV : Rg.obj NV ≅ Y₂)
    (yI : Y₁ ≅ Y₂) (y : Y₁ ⟶ Y₂) (trI : Rk.obj Q₀ ≅ QV)
    (h1 : c₁.hom ≫ Rg.map d.hom = a₁.hom ≫ πQ.hom)
    (h2 : Rg'.map x₀.hom ≫ πN.hom = πQ.hom ≫ Rg.map (Rk.map x₀.hom))
    (hρ : ρN = πN.symm)
    (h3 : ρN ≪≫ bI = Rg.mapIso mkI ≪≫ mgI ≪≫ wI)
    (h5 : Rg.map aτ ≫ mgV.hom = mgI.hom ≫ y)
    (hy : yI.hom = y) (haτ : aτI.hom = aτ)
    (htr : trI = d.symm)
    (h6 : Rk.mapIso x₀ ≪≫ mkI ≪≫ aτI = trI ≪≫ xV) :
    (i.symm ≪≫ a₁ ≪≫ Rg'.mapIso x₀ ≪≫ bI) ≪≫ wI.symm ≪≫ yI =
      i.symm ≪≫ c₁ ≪≫ Rg.mapIso xV ≪≫ mgV := by
  subst hρ htr hy haτ
  refine Iso.ext ?_
  have h3' : bI.hom = πN.hom ≫ Rg.map mkI.hom ≫ mgI.hom ≫ wI.hom := by
    have h := congrArg Iso.hom h3
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h
    rw [← h, Iso.hom_inv_id_assoc]
  have h6' : Rk.map x₀.hom ≫ mkI.hom ≫ aτI.hom = d.inv ≫ xV.hom := by
    simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using congrArg Iso.hom h6
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, h3',
    Iso.hom_inv_id_assoc, reassoc_of% h2]
  refine congrArg (i.inv ≫ ·) ?_
  calc a₁.hom ≫ πQ.hom ≫ Rg.map (Rk.map x₀.hom) ≫ Rg.map mkI.hom ≫ mgI.hom ≫ yI.hom
      = (a₁.hom ≫ πQ.hom) ≫ Rg.map (Rk.map x₀.hom) ≫ Rg.map mkI.hom ≫ (mgI.hom ≫ yI.hom) := by
        simp only [Category.assoc]
    _ = c₁.hom ≫ Rg.map (d.hom ≫ Rk.map x₀.hom ≫ mkI.hom ≫ aτI.hom) ≫ mgV.hom := by
        rw [← h1, ← h5]; simp only [Functor.map_comp, Category.assoc]
    _ = c₁.hom ≫ Rg.map xV.hom ≫ mgV.hom := by rw [h6', Iso.hom_inv_id_assoc]

/-- The composition isomorphism of the inverse images along represented morphisms is the inverse
of the comparison of Stacks 03LU, at the module of a quasi-coherent module. -/
private theorem representedModulePullbackCompIso_app_eq {Tw Tv Tv₀ : BigFppfOver B S hS}
    (g : Tw ⟶ Tv) (κ : Tv ⟶ Tv₀)
    (M₀ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tv₀).ringCatSheaf).FullSubcategory) :
    (representedModulePullbackCompIso B S hS g κ).app
        ((representedQuasicoherentSchemeEquivalence B S hS Tv₀).functor.obj M₀).obj =
      (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g)
        (representedSpaceMap B S hS κ) (representedSpaceMap B S hS (g ≫ κ))
        (representedSpaceMap_comp B S hS g κ)
        ((representedQuasicoherentSchemeEquivalence B S hS Tv₀).functor.obj M₀).obj).symm := by
  rw [QuasiCoherentDescent.pullbackComparison_representedSpaceMap_comp, Iso.symm_symm_eq]

/-- The transition of the restrictions of a module to charts along `k` is the inverse of the
comparison of Stacks 03LU along the represented morphism of charts. -/
private theorem chartModuleRestrictionTransitions_eq_symm_pullbackComparison
    (Y : AlgebraicSpaces B S hS) {V V₀ : SmallEtale B S hS Y.1} (k : V ⟶ V₀)
    (F : Modules.{u, u} B S hS Y.1 Y.2) :
    chartModuleRestrictionTransitions B S hS Y F k =
      (QuasiCoherentDescent.pullbackComparison B S hS
        (representedSpaceMap B S hS ((SmallEtale.toOver B S hS Y.1).map k))
        (chartToSpace B S hS Y V₀) (chartToSpace B S hS Y V)
        (chartMap_comp_chartToSpace B S hS Y k) F).symm :=
  (Iso.symm_symm_eq _).symm.trans
    (congrArg Iso.symm (pullbackComparison_chartMap B S hS k F)).symm

/-- The coherence behind `chartSquareRestrictionIso_postcomp`, at variables: the comparisons of
Stacks 03LU along a square of represented spaces, the composition law of
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso` and its naturality, and the
compatibility `h6` of the chart identifications with a transition. -/
private theorem postcomp_core {X X' : AlgebraicSpaces B S hS} (a : X' ⟶ X)
    {Tw Tv Tv₀ : BigFppfOver B S hS} (g : Tw ⟶ Tv) (κ : Tv ⟶ Tv₀)
    (tW : (⟨yoneda.obj Tw, isAlgebraicSpace_yoneda B S hS Tw⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (tV : (⟨yoneda.obj Tv, isAlgebraicSpace_yoneda B S hS Tv⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (tV₀ : (⟨yoneda.obj Tv₀, isAlgebraicSpace_yoneda B S hS Tv₀⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (hq : representedSpaceMap B S hS g ≫ tV = tW ≫ a)
    (hk : representedSpaceMap B S hS κ ≫ tV₀ = tV)
    (hq' : representedSpaceMap B S hS (g ≫ κ) ≫ tV₀ = tW ≫ a)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (M₀ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tv₀).ringCatSheaf).FullSubcategory)
    (MV : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tv).ringCatSheaf).FullSubcategory)
    (τ : quasicoherentPullbackObj B S hS κ M₀ ≅ MV)
    (x₀ : (modulePullback B S hS tV₀).obj F ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tv₀).functor.obj M₀).obj)
    (xV : (modulePullback B S hS tV).obj F ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tv).functor.obj MV).obj)
    (h6 : (modulePullback B S hS (representedSpaceMap B S hS κ)).mapIso x₀ ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS κ M₀ ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS Tv).functor.mapIso τ) =
      (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS κ) tV₀ tV hk
        F).symm ≪≫ xV) :
    ((QuasiCoherentDescent.pullbackComparison B S hS tW a (tW ≫ a) rfl F).symm ≪≫
        QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS (g ≫ κ)) tV₀
          (tW ≫ a) hq' F ≪≫
        (modulePullback B S hS (representedSpaceMap B S hS (g ≫ κ))).mapIso x₀ ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS (g ≫ κ) M₀) ≪≫
      ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
        Tw).functor.mapIso (quasicoherentPullbackCompIso B S hS g κ M₀))).symm ≪≫
      (ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
        Tw).functor.mapIso (quasicoherentPullbackIso B S hS g τ)) =
    (QuasiCoherentDescent.pullbackComparison B S hS tW a (tW ≫ a) rfl F).symm ≪≫
      QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) tV (tW ≫ a)
        hq F ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS g)).mapIso xV ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS g MV := by
  have hs := representedSpaceMap_comp B S hS g κ
  have h1 := QuasiCoherentDescent.pullbackComparison_trans_hom B S hS
    (representedSpaceMap B S hS g) (representedSpaceMap B S hS κ) tV₀ tV hk
    (representedSpaceMap B S hS (g ≫ κ)) hs (tW ≫ a) hq hq' F
  have h2 := QuasiCoherentDescent.pullbackComparison_naturality B S hS
    (representedSpaceMap B S hS g) (representedSpaceMap B S hS κ)
    (representedSpaceMap B S hS (g ≫ κ)) hs x₀.hom
  have h3 := modulePullbackRepresentedQuasicoherentIso_comp B S hS g κ M₀
  have h5 := modulePullbackRepresentedQuasicoherentIso_naturality B S hS g τ.hom
  exact postcomp_aux _ _ _ _ _ x₀ _ _ _ _ _ _ _ _ _
    ((ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS Tv).functor.mapIso τ)) _ xV _
    ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
      Tw).functor.mapIso (quasicoherentPullbackIso B S hS g τ))) _ _ h1 h2
    (representedModulePullbackCompIso_app_eq g κ M₀) h3 h5 rfl rfl rfl h6

/-- The compatibility of the glued module with the transitions along a morphism `k` of charts,
as an equation of isomorphisms. -/
theorem glueChartModuleIso_transition_iso {V V₀ : SmallEtale B S hS X.1} (k : V ⟶ V₀) :
    (chartModuleInverseImage B S hS X k).mapIso (𝓜.glueChartModuleIso V₀) ≪≫
        𝓜.chartTransition k =
      chartModuleRestrictionTransitions B S hS X 𝓜.glue k ≪≫ 𝓜.glueChartModuleIso V :=
  Iso.ext (𝓜.glueChartModuleIso_hom_transition k)

/-- **The restriction of `a^*(glue 𝓜)` to a chart square, along a morphism of charts of the
target.**  For a chart square `q` and a morphism `k : q.V ⟶ V₀` of charts of `X`, the
identification at the composite square `q.postcomp k`, followed by the module attached to the
inverse of the contraction `g^*(k^*M V₀) ≅ (g ≫ k)^*M V₀` and to `g^*τ_k`, is the
identification at `q`. -/
theorem chartSquareRestrictionIso_postcomp (q : ChartSquare a) {V₀ : SmallEtale B S hS X.1}
    (k : q.V ⟶ V₀) :
    𝓜.chartSquareRestrictionIso a (q.postcomp k) ≪≫
        ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X' q.W)).functor.mapIso
          (quasicoherentPullbackCompIso B S hS q.g ((SmallEtale.toOver B S hS X.1).map k)
            (𝓜.qcohObj V₀)))).symm ≪≫
        (ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
          (chartFppfObject B S hS X' q.W)).functor.mapIso
          (quasicoherentPullbackIso B S hS q.g (𝓜.qcohTransition k))) =
      𝓜.chartSquareRestrictionIso a q := by
  have hk : representedSpaceMap B S hS ((SmallEtale.toOver B S hS X.1).map k) ≫
      chartToSpace B S hS X V₀ = chartToSpace B S hS X q.V :=
    chartMap_comp_chartToSpace B S hS X k
  have h6 := 𝓜.glueChartModuleIso_transition_iso k
  rw [chartModuleRestrictionTransitions_eq_symm_pullbackComparison] at h6
  exact postcomp_core a q.g ((SmallEtale.toOver B S hS X.1).map k)
    (chartToSpace B S hS X' q.W) (chartToSpace B S hS X q.V) (chartToSpace B S hS X V₀)
    q.hom_eq hk (q.postcomp k).hom_eq 𝓜.glue (𝓜.qcohObj V₀) (𝓜.qcohObj q.V)
    (𝓜.qcohTransition k) (𝓜.glueChartModuleIso V₀) (𝓜.glueChartModuleIso q.V) h6

/-- The pasting behind `chartSquareRestrictionIso_precomp`, at variables. -/
private theorem precomp_aux {C D E : Type*} [Category C] [Category D] [Category E]
    (Rm : D ⥤ C) (Rg : E ⥤ D) (Rg₁ : E ⥤ C)
    {A₁ B₁ Y Y' : C} {A B K : D} {QV NV : E}
    (i₁ : A₁ ≅ B₁) (j : B₁ ≅ Rm.obj B) (i : A ≅ B) (κ₁ : A₁ ≅ Rm.obj A)
    (c : A ≅ Rg.obj QV) (c₁ : A₁ ≅ Rg₁.obj QV)
    (πQ : Rg₁.obj QV ≅ Rm.obj (Rg.obj QV)) (πN : Rg₁.obj NV ≅ Rm.obj (Rg.obj NV))
    (ρN : Rm.obj (Rg.obj NV) ≅ Rg₁.obj NV)
    (x : QV ≅ NV) (mg : Rg.obj NV ≅ K) (mg₁ : Rg₁.obj NV ≅ Y) (ml : Rm.obj K ≅ Y') (w : Y' ≅ Y)
    (G1 : κ₁.hom ≫ Rm.map i.hom = i₁.hom ≫ j.hom)
    (G2 : κ₁.hom ≫ Rm.map c.hom = c₁.hom ≫ πQ.hom)
    (G3 : Rg₁.map x.hom ≫ πN.hom = πQ.hom ≫ Rm.map (Rg.map x.hom))
    (hρ : ρN = πN.symm)
    (G4 : ρN ≪≫ mg₁ = Rm.mapIso mg ≪≫ ml ≪≫ w) :
    j ≪≫ Rm.mapIso (i.symm ≪≫ c ≪≫ Rg.mapIso x ≪≫ mg) ≪≫ ml ≪≫ w =
      i₁.symm ≪≫ c₁ ≪≫ Rg₁.mapIso x ≪≫ mg₁ := by
  subst hρ
  refine Iso.ext ?_
  have hm : mg₁.hom = πN.hom ≫ Rm.map mg.hom ≫ ml.hom ≫ w.hom := by
    have h := congrArg Iso.hom G4
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h
    rw [← h, Iso.hom_inv_id_assoc]
  have hG1 : i₁.inv ≫ κ₁.hom = j.hom ≫ Rm.map i.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% G1, Iso.map_hom_inv_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    hm]
  rw [reassoc_of% G3, ← reassoc_of% G2, reassoc_of% hG1]

/-- The coherence behind `chartSquareIso_precomp`, on the side of `X`, at variables: the
comparisons of Stacks 03LU along a square of represented spaces and the composition law of
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`. -/
private theorem precomp_core {X X' : AlgebraicSpaces B S hS} (a : X' ⟶ X)
    {Tw₁ Tw Tv : BigFppfOver B S hS} (l : Tw₁ ⟶ Tw) (g : Tw ⟶ Tv)
    (tW₁ : (⟨yoneda.obj Tw₁, isAlgebraicSpace_yoneda B S hS Tw₁⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (tW : (⟨yoneda.obj Tw, isAlgebraicSpace_yoneda B S hS Tw⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (tV : (⟨yoneda.obj Tv, isAlgebraicSpace_yoneda B S hS Tv⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (hl : representedSpaceMap B S hS l ≫ tW = tW₁)
    (hq : representedSpaceMap B S hS g ≫ tV = tW ≫ a)
    (hq₁ : representedSpaceMap B S hS (l ≫ g) ≫ tV = tW₁ ≫ a)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (MV : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tv).ringCatSheaf).FullSubcategory)
    (xV : (modulePullback B S hS tV).obj F ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tv).functor.obj MV).obj) :
    QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS l) tW tW₁ hl
        ((modulePullback B S hS a).obj F) ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS l)).mapIso
        ((QuasiCoherentDescent.pullbackComparison B S hS tW a (tW ≫ a) rfl F).symm ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) tV
            (tW ≫ a) hq F ≪≫
          (modulePullback B S hS (representedSpaceMap B S hS g)).mapIso xV ≪≫
          modulePullbackRepresentedQuasicoherentIso B S hS g MV) ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS l (quasicoherentPullbackObj B S hS g MV) ≪≫
      (ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
        Tw₁).functor.mapIso (quasicoherentPullbackCompIso B S hS l g MV)) =
    (QuasiCoherentDescent.pullbackComparison B S hS tW₁ a (tW₁ ≫ a) rfl F).symm ≪≫
      QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS (l ≫ g)) tV
        (tW₁ ≫ a) hq₁ F ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS (l ≫ g))).mapIso xV ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS (l ≫ g) MV := by
  have ht : representedSpaceMap B S hS l ≫ (tW ≫ a) = tW₁ ≫ a := by
    rw [← Category.assoc, hl]
  have hs := representedSpaceMap_comp B S hS l g
  have G1 := QuasiCoherentDescent.pullbackComparison_trans_hom B S hS
    (representedSpaceMap B S hS l) tW a (tW ≫ a) rfl tW₁ hl (tW₁ ≫ a) ht rfl F
  have G2 := QuasiCoherentDescent.pullbackComparison_trans_hom B S hS
    (representedSpaceMap B S hS l) (representedSpaceMap B S hS g) tV (tW ≫ a) hq
    (representedSpaceMap B S hS (l ≫ g)) hs (tW₁ ≫ a) ht hq₁ F
  have G3 := QuasiCoherentDescent.pullbackComparison_naturality B S hS
    (representedSpaceMap B S hS l) (representedSpaceMap B S hS g)
    (representedSpaceMap B S hS (l ≫ g)) hs xV.hom
  have G4 := modulePullbackRepresentedQuasicoherentIso_comp B S hS l g MV
  exact precomp_aux _ _ _ _ _ _ _ _ _ _ _ _ xV _ _ _ _ G1 G2 G3
    (representedModulePullbackCompIso_app_eq l g MV) G4

/-- The pasting behind `chartSquareIso_precomp`, at variables. -/
private theorem precompE_aux {C D : Type*} [Category C] [Category D] (Rm : D ⥤ C)
    {B₁ Y Y' L₁ L' G₁ : C} {B K L G₀ : D}
    (jP : B₁ ≅ Rm.obj B) (jG : G₁ ≅ Rm.obj G₀) (Φ : B ≅ K) (Φ₁ : B₁ ≅ Y) (cq : K ≅ L)
    (γ : G₀ ≅ L) (γ₁ : G₁ ≅ L₁) (c₁ : Y ≅ L₁) (ml : Rm.obj K ≅ Y') (w : Y' ≅ Y)
    (mlN : Rm.obj L ≅ L') (τ' : L' ≅ L₁) (lcq : Y' ≅ L') (cqh : K ⟶ L) (lcqh : Y' ⟶ L')
    (hA : jP ≪≫ Rm.mapIso Φ ≪≫ ml ≪≫ w = Φ₁)
    (H1 : Rm.mapIso γ ≪≫ mlN ≪≫ τ' = jG.symm ≪≫ γ₁)
    (H3 : Rm.map cqh ≫ mlN.hom = ml.hom ≫ lcqh) (hcq : cq.hom = cqh) (hlcq : lcq.hom = lcqh)
    (H4 : w ≪≫ c₁ = lcq ≪≫ τ') :
    jP.hom ≫ Rm.map (Φ ≪≫ cq ≪≫ γ.symm).hom ≫ jG.inv = (Φ₁ ≪≫ c₁ ≪≫ γ₁.symm).hom := by
  subst hcq hlcq hA
  have h1 : Rm.map γ.inv ≫ jG.inv = mlN.hom ≫ τ'.hom ≫ γ₁.inv := by
    have h := congrArg Iso.hom H1
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at h
    have h' : jG.inv = Rm.map γ.hom ≫ mlN.hom ≫ τ'.hom ≫ γ₁.inv := by
      rw [reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
    rw [h', Iso.map_inv_hom_id_assoc]
  have h4 : w.hom ≫ c₁.hom = lcq.hom ≫ τ'.hom := by
    simpa only [Iso.trans_hom] using congrArg Iso.hom H4
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Functor.mapIso_hom, Category.assoc,
    h1, reassoc_of% H3, reassoc_of% h4]

/-- The coherence behind `chartSquareIso_precomp`, at variables: `precomp_core` on the side of
`X`, the compatibility `H1` of the chart identifications of the system on `X'` with a transition,
the naturality of `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`, and the
compatibility `H4` of the comparisons with the transition. -/
private theorem precompE_core {X X' : AlgebraicSpaces B S hS} (a : X' ⟶ X)
    {Tw₁ Tw Tv : BigFppfOver B S hS} (l : Tw₁ ⟶ Tw) (g : Tw ⟶ Tv)
    (tW₁ : (⟨yoneda.obj Tw₁, isAlgebraicSpace_yoneda B S hS Tw₁⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (tW : (⟨yoneda.obj Tw, isAlgebraicSpace_yoneda B S hS Tw⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (tV : (⟨yoneda.obj Tv, isAlgebraicSpace_yoneda B S hS Tv⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (hl : representedSpaceMap B S hS l ≫ tW = tW₁)
    (hq : representedSpaceMap B S hS g ≫ tV = tW ≫ a)
    (hq₁ : representedSpaceMap B S hS (l ≫ g) ≫ tV = tW₁ ≫ a)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS X'.1 X'.2)
    (MV : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tv).ringCatSheaf).FullSubcategory)
    (MW : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tw).ringCatSheaf).FullSubcategory)
    (MW₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tw₁).ringCatSheaf).FullSubcategory)
    (xV : (modulePullback B S hS tV).obj F ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tv).functor.obj MV).obj)
    (γ : (modulePullback B S hS tW).obj G ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tw).functor.obj MW).obj)
    (γ₁ : (modulePullback B S hS tW₁).obj G ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tw₁).functor.obj MW₁).obj)
    (cq : quasicoherentPullbackObj B S hS g MV ≅ MW)
    (cq₁ : quasicoherentPullbackObj B S hS (l ≫ g) MV ≅ MW₁)
    (τ' : quasicoherentPullbackObj B S hS l MW ≅ MW₁)
    (H1 : (modulePullback B S hS (representedSpaceMap B S hS l)).mapIso γ ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS l MW ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS Tw₁).functor.mapIso τ') =
      (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS l) tW tW₁ hl
        G).symm ≪≫ γ₁)
    (H4 : quasicoherentPullbackCompIso B S hS l g MV ≪≫ cq₁ =
      quasicoherentPullbackIso B S hS l cq ≪≫ τ') :
    (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS l) tW tW₁ hl
        ((modulePullback B S hS a).obj F)).hom ≫
      (modulePullback B S hS (representedSpaceMap B S hS l)).map
        (((QuasiCoherentDescent.pullbackComparison B S hS tW a (tW ≫ a) rfl F).symm ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) tV
            (tW ≫ a) hq F ≪≫
          (modulePullback B S hS (representedSpaceMap B S hS g)).mapIso xV ≪≫
          modulePullbackRepresentedQuasicoherentIso B S hS g MV) ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS Tw).functor.mapIso cq) ≪≫
        γ.symm).hom ≫
      (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS l) tW tW₁ hl
        G).inv =
      (((QuasiCoherentDescent.pullbackComparison B S hS tW₁ a (tW₁ ≫ a) rfl F).symm ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS (l ≫ g)) tV
            (tW₁ ≫ a) hq₁ F ≪≫
          (modulePullback B S hS (representedSpaceMap B S hS (l ≫ g))).mapIso xV ≪≫
          modulePullbackRepresentedQuasicoherentIso B S hS (l ≫ g) MV) ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS Tw₁).functor.mapIso cq₁) ≪≫
        γ₁.symm).hom := by
  have H4' := congrArg (fun e ↦ (ObjectProperty.ι _).mapIso
    ((representedQuasicoherentSchemeEquivalence B S hS Tw₁).functor.mapIso e)) H4
  simp only [Functor.mapIso_trans] at H4'
  exact precompE_aux (modulePullback B S hS (representedSpaceMap B S hS l))
    (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS l) tW tW₁ hl
      ((modulePullback B S hS a).obj F))
    (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS l) tW tW₁ hl G)
    _ _ _ γ γ₁ _ _ _ _ _ _ _ _
    (precomp_core a l g tW₁ tW tV hl hq hq₁ F MV xV) H1
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS l cq.hom) rfl rfl H4'

/-- `precompE_core` with the morphism of chart spaces, the identification at the chart square and
the one at the restricted chart square as variables, given by their defining equations. -/
private theorem precompE_core' {X X' : AlgebraicSpaces B S hS} (a : X' ⟶ X)
    {Tw₁ Tw Tv : BigFppfOver B S hS} (l : Tw₁ ⟶ Tw) (g : Tw ⟶ Tv)
    (tW₁ : (⟨yoneda.obj Tw₁, isAlgebraicSpace_yoneda B S hS Tw₁⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (tW : (⟨yoneda.obj Tw, isAlgebraicSpace_yoneda B S hS Tw⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (tV : (⟨yoneda.obj Tv, isAlgebraicSpace_yoneda B S hS Tv⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (m : (⟨yoneda.obj Tw₁, isAlgebraicSpace_yoneda B S hS Tw₁⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj Tw, isAlgebraicSpace_yoneda B S hS Tw⟩)
    (hm : m = representedSpaceMap B S hS l) (hl : m ≫ tW = tW₁)
    (hq : representedSpaceMap B S hS g ≫ tV = tW ≫ a)
    (hq₁ : representedSpaceMap B S hS (l ≫ g) ≫ tV = tW₁ ≫ a)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS X'.1 X'.2)
    (MV : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tv).ringCatSheaf).FullSubcategory)
    (MW : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tw).ringCatSheaf).FullSubcategory)
    (MW₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Tw₁).ringCatSheaf).FullSubcategory)
    (xV : (modulePullback B S hS tV).obj F ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tv).functor.obj MV).obj)
    (γ : (modulePullback B S hS tW).obj G ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tw).functor.obj MW).obj)
    (γ₁ : (modulePullback B S hS tW₁).obj G ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Tw₁).functor.obj MW₁).obj)
    (cq : quasicoherentPullbackObj B S hS g MV ≅ MW)
    (cq₁ : quasicoherentPullbackObj B S hS (l ≫ g) MV ≅ MW₁)
    (τ' : quasicoherentPullbackObj B S hS l MW ≅ MW₁)
    (H1 : (modulePullback B S hS (representedSpaceMap B S hS l)).mapIso γ ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS l MW ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS Tw₁).functor.mapIso τ') =
      (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS l) tW tW₁
        (hm ▸ hl) G).symm ≪≫ γ₁)
    (H4 : quasicoherentPullbackCompIso B S hS l g MV ≪≫ cq₁ =
      quasicoherentPullbackIso B S hS l cq ≪≫ τ')
    (E : (modulePullback B S hS tW).obj ((modulePullback B S hS a).obj F) ≅
      (modulePullback B S hS tW).obj G)
    (hE : E = ((QuasiCoherentDescent.pullbackComparison B S hS tW a (tW ≫ a) rfl F).symm ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) tV
            (tW ≫ a) hq F ≪≫
          (modulePullback B S hS (representedSpaceMap B S hS g)).mapIso xV ≪≫
          modulePullbackRepresentedQuasicoherentIso B S hS g MV) ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS Tw).functor.mapIso cq) ≪≫
        γ.symm)
    (E₁ : (modulePullback B S hS tW₁).obj ((modulePullback B S hS a).obj F) ≅
      (modulePullback B S hS tW₁).obj G)
    (hE₁ : E₁ = ((QuasiCoherentDescent.pullbackComparison B S hS tW₁ a (tW₁ ≫ a) rfl F).symm ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS (l ≫ g)) tV
            (tW₁ ≫ a) hq₁ F ≪≫
          (modulePullback B S hS (representedSpaceMap B S hS (l ≫ g))).mapIso xV ≪≫
          modulePullbackRepresentedQuasicoherentIso B S hS (l ≫ g) MV) ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS Tw₁).functor.mapIso cq₁) ≪≫
        γ₁.symm) :
    QuasiCoherentDescent.restrictForm B S hS m tW tW₁ hl E.hom = E₁.hom := by
  subst hm
  rw [restrictForm_eq_comp]
  subst hE hE₁
  exact precompE_core a l g tW₁ tW tV hl hq hq₁ F G MV MW MW₁ xV γ γ₁ cq cq₁ τ' H1 H4

/-! ### The chartwise identification of `a^*(glue 𝓜)` with `glue 𝓜'` -/

variable (𝓜' : ChartSchemeModuleSystem B S hS X')
  (c : ∀ q : ChartSquare a,
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map q.g)).obj (𝓜.M q.V) ≅ 𝓜'.M q.W)

/-- **The restrictions of `a^*(glue 𝓜)` and of `glue 𝓜'` to the chart of a chart square `q`,
identified through the comparison `c q : g^*(M V) ≅ M' W`**:
`chartSquareRestrictionIso`, the module attached to `c q`, and the counit of Stacks 03LY for
`𝓜'` at `W`. -/
def chartSquareIso (q : ChartSquare a) :
    (chartModuleRestriction B S hS X' q.W).obj ((modulePullback B S hS a).obj 𝓜.glue) ≅
      (chartModuleRestriction B S hS X' q.W).obj 𝓜'.glue :=
  𝓜.chartSquareRestrictionIso a q ≪≫
    (ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
      (chartFppfObject B S hS X' q.W)).functor.mapIso
        (ObjectProperty.isoMk _ (c q) :
          quasicoherentPullbackObj B S hS q.g (𝓜.qcohObj q.V) ≅ 𝓜'.qcohObj q.W)) ≪≫
    (𝓜'.glueChartModuleIso q.W).symm

/-- Replacing the comparison of the attached modules, at variables. -/
private theorem postcompE_aux {C : Type*} [Category C] {B₀ K' K₁ K L G₀ : C}
    (Φ' : B₀ ≅ K') (Φ : B₀ ≅ K) (z₁ : K' ≅ K₁) (z₂ : K₁ ≅ K) (cq' : K' ≅ L) (cq : K ≅ L)
    (γ : G₀ ≅ L) (hP : Φ' ≪≫ z₁ ≪≫ z₂ = Φ) (hc : cq' = z₁ ≪≫ z₂ ≪≫ cq) :
    Φ' ≪≫ cq' ≪≫ γ.symm = Φ ≪≫ cq ≪≫ γ.symm := by
  subst hc hP
  simp only [Iso.trans_assoc]

/-- **The chartwise identification is unchanged by a morphism of charts of the target**: for a
chart square `q` and `k : q.V ⟶ V₀`, the identification at `q.postcomp k` is the one at `q`. -/
theorem chartSquareIso_postcomp (hc₁ : 𝓜.ComparisonCompatTarget 𝓜' c) (q : ChartSquare a)
    {V₀ : SmallEtale B S hS X.1} (k : q.V ⟶ V₀) :
    𝓜.chartSquareIso a 𝓜' c (q.postcomp k) = 𝓜.chartSquareIso a 𝓜' c q := by
  have hcq : (ObjectProperty.isoMk _ (c (q.postcomp k)) :
        quasicoherentPullbackObj B S hS (q.g ≫ (SmallEtale.toOver B S hS X.1).map k)
          (𝓜.qcohObj V₀) ≅ 𝓜'.qcohObj q.W) =
      (quasicoherentPullbackCompIso B S hS q.g ((SmallEtale.toOver B S hS X.1).map k)
        (𝓜.qcohObj V₀)).symm ≪≫ quasicoherentPullbackIso B S hS q.g (𝓜.qcohTransition k) ≪≫
        (ObjectProperty.isoMk _ (c q) :
          quasicoherentPullbackObj B S hS q.g (𝓜.qcohObj q.V) ≅ 𝓜'.qcohObj q.W) := by
    refine Iso.ext (ObjectProperty.hom_ext _ ?_)
    show (c (q.postcomp k)).hom =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map q.g)
          (chartSchemeMap k)).inv.app (𝓜.M V₀) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map q.g)).map (𝓜.τ k).hom ≫
          (c q).hom
    exact hc₁ q k
  have hc := congrArg (fun e ↦ (ObjectProperty.ι _).mapIso
    ((representedQuasicoherentSchemeEquivalence B S hS
      (chartFppfObject B S hS X' q.W)).functor.mapIso e)) hcq
  simp only [Functor.mapIso_trans, Functor.mapIso_symm] at hc
  exact postcompE_aux (𝓜.chartSquareRestrictionIso a (q.postcomp k))
    (𝓜.chartSquareRestrictionIso a q) _ _ _ _ (𝓜'.glueChartModuleIso q.W)
    (𝓜.chartSquareRestrictionIso_postcomp a q k) hc

/-- **The chartwise identification restricts along a morphism of charts of the source**: for a
chart square `q` and `l : W₁ ⟶ q.W`, the restricted reading along the morphism of chart spaces
of the identification at `q` is the identification at `q.precomp l`. -/
theorem chartSquareIso_precomp (hc₂ : 𝓜.ComparisonCompatSource 𝓜' c) (q : ChartSquare a)
    {W₁ : SmallEtale B S hS X'.1} (l : W₁ ⟶ q.W) :
    QuasiCoherentDescent.restrictForm B S hS (chartMap B S hS X' l)
        (chartToSpace B S hS X' q.W) (chartToSpace B S hS X' W₁)
        (chartMap_comp_chartToSpace B S hS X' l) (𝓜.chartSquareIso a 𝓜' c q).hom =
      (𝓜.chartSquareIso a 𝓜' c (q.precomp l)).hom := by
  have H1 := 𝓜'.glueChartModuleIso_transition_iso l
  rw [chartModuleRestrictionTransitions_eq_symm_pullbackComparison] at H1
  have H4 : quasicoherentPullbackCompIso B S hS ((SmallEtale.toOver B S hS X'.1).map l) q.g
        (𝓜.qcohObj q.V) ≪≫
      (ObjectProperty.isoMk _ (c (q.precomp l)) :
        quasicoherentPullbackObj B S hS ((SmallEtale.toOver B S hS X'.1).map l ≫ q.g)
          (𝓜.qcohObj q.V) ≅ 𝓜'.qcohObj W₁) =
      quasicoherentPullbackIso B S hS ((SmallEtale.toOver B S hS X'.1).map l)
        (ObjectProperty.isoMk _ (c q) :
          quasicoherentPullbackObj B S hS q.g (𝓜.qcohObj q.V) ≅ 𝓜'.qcohObj q.W) ≪≫
        𝓜'.qcohTransition l := by
    refine Iso.ext (ObjectProperty.hom_ext _ ?_)
    show (Scheme.Modules.pullbackComp (chartSchemeMap l)
          ((BigFppfOver.toScheme B S hS).map q.g)).hom.app (𝓜.M q.V) ≫ (c (q.precomp l)).hom =
      (Scheme.Modules.pullback (chartSchemeMap l)).map (c q).hom ≫ (𝓜'.τ l).hom
    rw [hc₂ q l]
    exact Iso.hom_inv_id_app_assoc _ _ _
  exact precompE_core' a ((SmallEtale.toOver B S hS X'.1).map l) q.g
    (chartToSpace B S hS X' W₁) (chartToSpace B S hS X' q.W) (chartToSpace B S hS X q.V)
    (chartMap B S hS X' l) rfl
    (chartMap_comp_chartToSpace B S hS X' l) q.hom_eq (q.precomp l).hom_eq 𝓜.glue 𝓜'.glue
    (𝓜.qcohObj q.V) (𝓜'.qcohObj q.W) (𝓜'.qcohObj W₁) (𝓜.glueChartModuleIso q.V)
    (𝓜'.glueChartModuleIso q.W) (𝓜'.glueChartModuleIso W₁) _ _ (𝓜'.qcohTransition l) H1 H4
    (𝓜.chartSquareIso a 𝓜' c q) rfl (𝓜.chartSquareIso a 𝓜' c (q.precomp l)) rfl

/-- A chart square with prescribed fields is unchanged under a morphism of charts of the target
compatible with them. -/
theorem chartSquareIso_eq_of_postcomp (hc₁ : 𝓜.ComparisonCompatTarget 𝓜' c) (q : ChartSquare a)
    {V₀ : SmallEtale B S hS X.1} (k : q.V ⟶ V₀)
    (g' : (SmallEtale.toOver B S hS X'.1).obj q.W ⟶ (SmallEtale.toOver B S hS X.1).obj V₀)
    (hg' : q.g ≫ (SmallEtale.toOver B S hS X.1).map k = g')
    (w' : yoneda.map g' ≫ V₀.obj.hom = q.W.obj.hom ≫ a.hom) :
    𝓜.chartSquareIso a 𝓜' c ⟨q.W, V₀, g', w'⟩ = 𝓜.chartSquareIso a 𝓜' c q := by
  subst hg'
  exact 𝓜.chartSquareIso_postcomp a 𝓜' c hc₁ q k

/-- **Two chart squares with the same chart of the source give the same identification**: both
are composites of the chart square through the fibre product of their two charts of the target
(`ChartSquare.pair`) with its two projections. -/
theorem chartSquareIso_eq_of_W (hc₁ : 𝓜.ComparisonCompatTarget 𝓜' c) (q : ChartSquare a)
    (V₂ : SmallEtale B S hS X.1)
    (g₂ : (SmallEtale.toOver B S hS X'.1).obj q.W ⟶ (SmallEtale.toOver B S hS X.1).obj V₂)
    (w₂ : yoneda.map g₂ ≫ V₂.obj.hom = q.W.obj.hom ≫ a.hom) :
    𝓜.chartSquareIso a 𝓜' c q = 𝓜.chartSquareIso a 𝓜' c ⟨q.W, V₂, g₂, w₂⟩ := by
  have e₁ : 𝓜.chartSquareIso a 𝓜' c q = 𝓜.chartSquareIso a 𝓜' c (q.pair V₂ g₂ w₂) :=
    𝓜.chartSquareIso_eq_of_postcomp a 𝓜' c hc₁ (q.pair V₂ g₂ w₂)
      (SmallEtale.prodFst B S hS X.1 q.V V₂) q.g
      (Functor.relativelyRepresentable.lift'_fst _ _ _ _) q.w
  have e₂ : 𝓜.chartSquareIso a 𝓜' c ⟨q.W, V₂, g₂, w₂⟩ =
      𝓜.chartSquareIso a 𝓜' c (q.pair V₂ g₂ w₂) :=
    𝓜.chartSquareIso_eq_of_postcomp a 𝓜' c hc₁ (q.pair V₂ g₂ w₂)
      (SmallEtale.prodSnd B S hS X.1 q.V V₂) g₂
      (Functor.relativelyRepresentable.lift'_snd _ _ _ _) w₂
  exact e₁.trans e₂.symm

/-! ### Gluing the chartwise identifications -/

/-- The chartwise identification at a chart square, read on the slice of the small étale site of
`X'` at its chart: the preimage under the comparison of Stacks 04M0 of `chartSquareIso`. -/
def chartSquareSliceIso (q : ChartSquare a) :
    (restrFun (smallEtaleStructurePresheaf B S hS X'.1 X'.2) q.W).obj
        ((modulePullback B S hS a).obj 𝓜.glue).val ≅
      (restrFun (smallEtaleStructurePresheaf B S hS X'.1 X'.2) q.W).obj 𝓜'.glue.val :=
  (SheafOfModules.forget _).mapIso ((chartModuleSliceReindex B S hS X' q.W).preimageIso
    (((chartModuleRestrictionSliceIso B S hS X' q.W).app
        ((modulePullback B S hS a).obj 𝓜.glue)).symm ≪≫ 𝓜.chartSquareIso a 𝓜' c q ≪≫
      (chartModuleRestrictionSliceIso B S hS X' q.W).app 𝓜'.glue))

/-- The slice identification is the slice reading of the chartwise identification. -/
theorem chartSquareSliceIso_hom (q : ChartSquare a) :
    (𝓜.chartSquareSliceIso a 𝓜' c q).hom =
      chartSliceHom B S hS X' q.W ((modulePullback B S hS a).obj 𝓜.glue) 𝓜'.glue
        (𝓜.chartSquareIso a 𝓜' c q).hom :=
  rfl

/-- **The slice identifications agree on every common refinement.**  For a chart `Z` of `X'`
with morphisms to the charts of two chart squares, the two relocalizations are the slice readings
of the identifications at the two restricted chart squares (`chartSquareIso_precomp`), which have
the same chart `Z` and therefore agree (`chartSquareIso_eq_of_W`). -/
theorem chartSquareSliceIso_compatible (hc₁ : 𝓜.ComparisonCompatTarget 𝓜' c)
    (hc₂ : 𝓜.ComparisonCompatSource 𝓜' c) {Z : SmallEtale B S hS X'.1} (q₁ q₂ : ChartSquare a)
    (f : Z ⟶ q₁.W) (g : Z ⟶ q₂.W) :
    homRestr (smallEtaleStructurePresheaf B S hS X'.1 X'.2)
        ((modulePullback B S hS a).obj 𝓜.glue).val 𝓜'.glue.val f
        (𝓜.chartSquareSliceIso a 𝓜' c q₁).hom =
      homRestr (smallEtaleStructurePresheaf B S hS X'.1 X'.2)
        ((modulePullback B S hS a).obj 𝓜.glue).val 𝓜'.glue.val g
        (𝓜.chartSquareSliceIso a 𝓜' c q₂).hom := by
  rw [chartSquareSliceIso_hom, chartSquareSliceIso_hom, homRestr_chartSliceHom,
    homRestr_chartSliceHom, 𝓜.chartSquareIso_precomp a 𝓜' c hc₂ q₁ f,
    𝓜.chartSquareIso_precomp a 𝓜' c hc₂ q₂ g,
    𝓜.chartSquareIso_eq_of_W a 𝓜' c hc₁ (q₁.precomp f) (q₂.precomp g).V (q₂.precomp g).g
      (q₂.precomp g).w]
  rfl

/-- **The pullback of the glued module is the glued module of the system on the source**, up to
an isomorphism restricting to the chartwise identification on every chart square.  The
identifications glue by the gluing form of Stacks 03EM (`exists_iso_of_isCompatible`) over the
charts carrying a chart square, which cover the final object of the small étale site of `X'`
(`coversTop_chartSquare`). -/
theorem exists_modulePullbackGlueIso (hc₁ : 𝓜.ComparisonCompatTarget 𝓜' c)
    (hc₂ : 𝓜.ComparisonCompatSource 𝓜' c) :
    ∃ φ : (modulePullback B S hS a).obj 𝓜.glue ≅ 𝓜'.glue, ∀ q : ChartSquare a,
      (chartModuleRestriction B S hS X' q.W).map φ.hom = (𝓜.chartSquareIso a 𝓜' c q).hom := by
  have he : Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom (smallEtaleStructurePresheaf B S hS X'.1 X'.2)
        ((modulePullback B S hS a).obj 𝓜.glue).val 𝓜'.glue.val).presheaf ⋙
          CategoryTheory.forget _)
      (fun q : ChartSquare a ↦ (𝓜.chartSquareSliceIso a 𝓜' c q).hom) := by
    intro Z q₁ q₂ f g
    exact (internalHomForget_map_apply _ _ _ f _).trans
      ((𝓜.chartSquareSliceIso_compatible a 𝓜' c hc₁ hc₂ q₁ q₂ f g).trans
        (internalHomForget_map_apply _ _ _ g _).symm)
  obtain ⟨φ, hφ⟩ := _root_.exists_iso_of_isCompatible
    (smallEtaleStructurePresheaf B S hS X'.1 X'.2) ((modulePullback B S hS a).obj 𝓜.glue).val
    𝓜'.glue.val (coversTop_chartSquare a) ((modulePullback B S hS a).obj 𝓜.glue).isSheaf
    𝓜'.glue.isSheaf (fun q ↦ 𝓜.chartSquareSliceIso a 𝓜' c q) he
  refine ⟨Iso.mk (SheafOfModules.Hom.mk φ.hom) (SheafOfModules.Hom.mk φ.inv)
    (SheafOfModules.hom_ext φ.hom_inv_id) (SheafOfModules.hom_ext φ.inv_hom_id), fun q ↦ ?_⟩
  exact (chartModuleRestriction_map_eq_iff B S hS X' q.W _ _ _
    (SheafOfModules.Hom.mk φ.hom)).2
    ((hφ q).trans (𝓜.chartSquareSliceIso_hom a 𝓜' c q))

/-- **The pullback of the glued module along `a : X' ⟶ X` is the glued module of a system on
`X'` identified with it on chart squares**: `a^*(glue 𝓜) ≅ glue 𝓜'`, given comparisons
`c q : g^*(M V) ≅ M' W` on the chart squares of `a` compatible with the transitions of both
systems.  It restricts to `chartSquareIso q` on every chart square
(`chartModuleRestriction_map_modulePullbackGlueIso_hom`). -/
def modulePullbackGlueIso (hc₁ : 𝓜.ComparisonCompatTarget 𝓜' c)
    (hc₂ : 𝓜.ComparisonCompatSource 𝓜' c) :
    (modulePullback B S hS a).obj 𝓜.glue ≅ 𝓜'.glue :=
  (𝓜.exists_modulePullbackGlueIso a 𝓜' c hc₁ hc₂).choose

/-- The isomorphism `a^*(glue 𝓜) ≅ glue 𝓜'` restricts on every chart square to the chartwise
identification through the comparison. -/
theorem chartModuleRestriction_map_modulePullbackGlueIso_hom
    (hc₁ : 𝓜.ComparisonCompatTarget 𝓜' c) (hc₂ : 𝓜.ComparisonCompatSource 𝓜' c)
    (q : ChartSquare a) :
    (chartModuleRestriction B S hS X' q.W).map (𝓜.modulePullbackGlueIso a 𝓜' c hc₁ hc₂).hom =
      (𝓜.chartSquareIso a 𝓜' c q).hom :=
  (𝓜.exists_modulePullbackGlueIso a 𝓜' c hc₁ hc₂).choose_spec q

end ChartSchemeModuleSystem

/-! ### The base change of a glued module to a scheme -/

namespace ChartSchemeModuleSystem

variable {B S hS} {X : AlgebraicSpaces B S hS} (𝓜 : ChartSchemeModuleSystem B S hS X)

/-- **The base change of the glued module to a scheme `T` over `X` is the value at the identity
chart of a system on `T`.**  For `p : yoneda.obj T ⟶ X`, a chart-scheme module system `𝓜'` on
the algebraic space represented by `T` and comparisons `c q : g^*(M V) ≅ M' W` on the chart
squares of `p` compatible with the transitions of both systems, the base change
`AlgebraicGeometry.Space.baseChangeModule` of the glued module along `p` is
`𝓜'.M (idEtaleChart T)`: the restriction to the identity chart of
`modulePullbackGlueIso`, followed by `restrictToChartSchemeGlueIso`. -/
def baseChangeModuleGlueIsoOfComparisons (T : BigFppfOver B S hS) (p : yoneda.obj T ⟶ X.1)
    (𝓜' : ChartSchemeModuleSystem B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (c : ∀ q : ChartSquare (X' := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
        (ObjectProperty.homMk p : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :
          AlgebraicSpaces B S hS) ⟶ X),
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map q.g)).obj (𝓜.M q.V) ≅
        𝓜'.M q.W)
    (hc₁ : 𝓜.ComparisonCompatTarget 𝓜' c) (hc₂ : 𝓜.ComparisonCompatSource 𝓜' c) :
    baseChangeModule B S hS 𝓜.glue T p ≅ 𝓜'.M (idEtaleChart B S hS T) :=
  (restrictToChartSchemeFunctor B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
      (idEtaleChart B S hS T)).mapIso (𝓜.modulePullbackGlueIso _ 𝓜' c hc₁ hc₂) ≪≫
    𝓜'.restrictToChartSchemeGlueIso (idEtaleChart B S hS T)

end ChartSchemeModuleSystem

end AlgebraicGeometry.Space

end
