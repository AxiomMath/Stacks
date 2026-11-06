module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartsBoundedRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystemSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismPropertiesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeComposite

/-!
# Supplement to `SeparatedDescent`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `BigFppfOver.SizeBound.prod_left`
* `BigFppfOver.SizeBound.prod_right`
* `exists_isClosedImmersion_comp_prodMap_π_of_chartsBounded`
* `exists_isClosedImmersion_pullback_snd_prodMap_of_chartsBounded`
* `exists_isAbsolutelySeparated_system_obj_of_isAffine_of_chartsBounded`
* `exists_isAbsolutelySeparated_system_obj_of_chartsBounded`
* `ChartsBounded.baseChangeOver`
* `DescentSituation.exists_isSeparated_system_app_of_chartsBounded`
-/

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_of_chartsBounded` (or `OfChartsBounded` for a definition). -/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_separatedDescentSupplement :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_separatedDescentSupplement
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_separatedDescentSupplement B S hS).has_limit _

/-! ### Separatedness over an affine base is absolute separatedness -/

/-! ### Products of affine objects over an affine base -/

/-- Multiplying a size-bounded diagram in the big fppf site of `S` by a fixed object on the
left keeps it size-bounded: each product is no larger than the larger of its two factors, and
both the fixed object and the supremum of the diagram lie below the cutoff. -/
theorem BigFppfOver.SizeBound.prod_left {K : Type u} [Category.{u} K]
    {V : K ⥤ BigFppfOver B S hS} (h : BigFppfOver.SizeBound V) (W : BigFppfOver B S hS) :
    BigFppfOver.SizeBound (V ⋙ prod.functor.obj W) where
  mk_lt := h.mk_lt
  iSup_size_lt := by
    refine lt_of_le_of_lt (ciSup_le' fun j =>
      (size_toScheme_obj_prod_le B S hS W (V.obj j)).trans
        (max_le_max le_rfl (le_ciSup (Cardinal.bddAbove_range _) j))) ?_
    exact max_lt W.left.property h.iSup_size_lt

/-- Multiplying a size-bounded diagram in the big fppf site of `S` by a fixed object on the
right keeps it size-bounded. -/
theorem BigFppfOver.SizeBound.prod_right {K : Type u} [Category.{u} K]
    {V : K ⥤ BigFppfOver B S hS} (h : BigFppfOver.SizeBound V) (W : BigFppfOver B S hS) :
    BigFppfOver.SizeBound (V ⋙ prod.functor.flip.obj W) where
  mk_lt := h.mk_lt
  iSup_size_lt := by
    refine lt_of_le_of_lt (ciSup_le' fun j =>
      (size_toScheme_obj_prod_le B S hS (V.obj j) W).trans
        (max_le_max (le_ciSup (Cardinal.bddAbove_range _) j) le_rfl)) ?_
    exact max_lt h.iSup_size_lt W.left.property

/-! ### Charts of two stages of an inverse system -/

/-! ### The kernel pair of a finer chart as a base change -/

/-! ### Descending a closed immersion into a product of charts -/

section ProductDiagrams

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (hSaff : IsAffine S)
  (V : K ⥤ BigFppfOver B S hS)
  (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hK : BigFppfOver.SizeBound V)

include hSaff hVaff in
/-- **Stacks 081B** for the products of a cofiltered limit of affine charts with the charts of
the stages. A closed immersion into `U ×_S U`, where `U` is the limit of the charts, whose
composite with the first projection is locally of finite type, is already a closed immersion
into `U ×_S U_k` for all sufficiently late stages `k`. -/
theorem exists_isClosedImmersion_comp_prodMap_π_of_chartsBounded (hK : BigFppfOver.SizeBound V)
    {c : Cone V} (hc : IsLimit c)
    (hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {R : Scheme.{u}} (g : R ⟶ (BigFppfOver.toScheme B S hS).obj (c.pt ⨯ c.pt))
    (hg : _root_.AlgebraicGeometry.IsClosedImmersion g) (k₀ : K)
    (hft : LocallyOfFiniteType (g ≫ (BigFppfOver.toScheme B S hS).map prod.fst)) :
    ∃ k₁ : K, ∀ (k : K) (_ : k ⟶ k₁),
      _root_.AlgebraicGeometry.IsClosedImmersion
        (g ≫ (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k))) := by
  have hconn : IsConnected K := IsCofiltered.isConnected K
  have hpres := prod_preservesConnectedLimits (J := K) c.pt
  have hprodlim : IsLimit ((prod.functor.obj c.pt).mapCone c) := isLimitOfPreserves _ hc
  have hpaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.obj c.pt).obj j)) := fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ hcaff (hVaff j)
  have := BigFppfOver.preservesLimit_toScheme_of_sizeBound (V ⋙ prod.functor.obj c.pt) hpaff
    (BigFppfOver.SizeBound.prod_left B S hS hK c.pt)
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.obj c.pt).mapCone c)) := isLimitOfPreserves _ hprodlim
  have hEaff : ∀ j, IsAffine
      (((V ⋙ prod.functor.obj c.pt) ⋙ BigFppfOver.toScheme B S hS).obj j) := hpaff
  have hπ : ∀ k : K, ((BigFppfOver.toScheme B S hS).mapCone
        ((prod.functor.obj c.pt).mapCone c)).π.app k
      = (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k)) := fun k => rfl
  have hgft : LocallyOfFiniteType (g ≫
      ((BigFppfOver.toScheme B S hS).mapCone ((prod.functor.obj c.pt).mapCone c)).π.app k₀) := by
    have hcomp2 : LocallyOfFiniteType ((g ≫ (BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 c.pt) (c.π.app k₀))) ≫
        (BigFppfOver.toScheme B S hS).map prod.fst) := by
      rw [Category.assoc, ← Functor.map_comp,
        show prod.map (𝟙 c.pt) (c.π.app k₀) ≫ (prod.fst : c.pt ⨯ V.obj k₀ ⟶ c.pt)
          = (prod.fst : c.pt ⨯ c.pt ⟶ c.pt) by simp]
      exact hft
    rw [hπ k₀]
    exact @locallyOfFiniteType_of_comp _ _ _ _
      ((BigFppfOver.toScheme B S hS).map prod.fst) hcomp2
  obtain ⟨k₁, hk₁⟩ := EventualLimit.exists_isClosedImmersion_comp_π_app_of_isAffine
    ((V ⋙ prod.functor.obj c.pt) ⋙ BigFppfOver.toScheme B S hS) _ he g hg k₀ hgft
  exact ⟨k₁, fun k hk => hk₁ k hk⟩

include hSaff hVaff in
/-- **Stacks 01ZP** for the products of the charts of the stages with the chart of one stage. A
morphism to `U_k ×_S U_k` whose source is quasi-compact and quasi-separated and which is
locally of finite type becomes a closed immersion after base change to `U_j ×_S U_k` for some
`j`, as soon as it is one after base change to `U ×_S U_k`, where `U` is the limit of the
charts. -/
theorem exists_isClosedImmersion_pullback_snd_prodMap_of_chartsBounded
    (hK : BigFppfOver.SizeBound V) {c : Cone V} (hc : IsLimit c) (k : K)
    {T : BigFppfOver B S hS} (m : T ⟶ V.obj k ⨯ V.obj k)
    (hmft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map m))
    (hmqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hmqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hlim : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (c.π.app k) (𝟙 (V.obj k)))))) :
    ∃ (i : K) (hi : i ⟶ k), _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (V.map hi) (𝟙 (V.obj k))))) := by
  have hconn : IsConnected K := IsCofiltered.isConnected K
  have hiso : prod.functor.obj (V.obj k) ≅ prod.functor.flip.obj (V.obj k) :=
    NatIso.ofComponents (fun W => prod.braiding (V.obj k) W)
      (fun {W W'} f => braid_natural (𝟙 (V.obj k)) f)
  have h1 := prod_preservesConnectedLimits (J := K) (V.obj k)
  have h2 : PreservesLimitsOfShape K (prod.functor.flip.obj (V.obj k)) :=
    @preservesLimitsOfShape_of_natIso _ _ _ _ _ _ _ _ hiso h1
  have hprodlim : IsLimit ((prod.functor.flip.obj (V.obj k)).mapCone c) :=
    isLimitOfPreserves _ hc
  have hpaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.flip.obj (V.obj k)).obj j)) := fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hVaff j) (hVaff k)
  have := BigFppfOver.preservesLimit_toScheme_of_sizeBound (V ⋙ prod.functor.flip.obj (V.obj k))
    hpaff (BigFppfOver.SizeBound.prod_right B S hS hK (V.obj k))
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.flip.obj (V.obj k)).mapCone c)) := isLimitOfPreserves _ hprodlim
  set E := (V ⋙ prod.functor.flip.obj (V.obj k)) ⋙ BigFppfOver.toScheme B S hS with hE
  have hEaff : ∀ j, IsAffine (E.obj j) := hpaff
  have hEhom : ∀ {i j : K} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map g) := by
    intro i j g
    have := hEaff i
    have := hEaff j
    exact isAffineHom_of_isAffine _
  have hk₀ : IsAffine (E.obj k) := hEaff k
  have hkc : CompactSpace (E.obj k) := Scheme.compactSpace_of_isAffine _
  have hkqs : QuasiSeparatedSpace (E.obj k) := inferInstance
  have hX₀c : CompactSpace
      ((Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k))).left := hmqc
  have hX₀qs : QuasiSeparatedSpace
      ((Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k))).left := hmqs
  have hY₀c : CompactSpace (Over.mk (𝟙 (E.obj k))).left := hkc
  have hY₀qs : QuasiSeparatedSpace (Over.mk (𝟙 (E.obj k))).left := hkqs
  have hf₀ft : LocallyOfFiniteType
      (Over.homMk ((BigFppfOver.toScheme B S hS).map m) (Category.comp_id _) :
        (Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k)) ⟶
          Over.mk (𝟙 (E.obj k))).left := hmft
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((Over.pullback (((BigFppfOver.toScheme B S hS).mapCone
        ((prod.functor.flip.obj (V.obj k)).mapCone c)).π.app k)).map
        (Over.homMk ((BigFppfOver.toScheme B S hS).map m) (Category.comp_id _) :
          (Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k)) ⟶
            Over.mk (𝟙 (E.obj k)))).left :=
    (prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsClosedImmersion) _ _).mpr hlim
  obtain ⟨i, hi, hres⟩ := exists_isClosedImmersion_baseChange_of_isLimit E _ he k
    (Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k)) (Over.mk (𝟙 (E.obj k)))
    (Over.homMk ((BigFppfOver.toScheme B S hS).map m) (Category.comp_id _))
  exact ⟨i, hi, (prop_overPullback_map_left_iff_pullback_snd
    (@_root_.AlgebraicGeometry.IsClosedImmersion) _ _).mp hres⟩

end ProductDiagrams

/-! ### Relocalization to a larger base scheme -/

/-! ### The view over the terminal scheme is already absolute -/

/-! ### Separatedness descends to a stage -/

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u}))

namespace DescentSituation

/-- **Stacks 084T over an affine base scheme.** In the situation of Stacks 084R over an affine
base scheme, if the limit `X` of the inverse system is separated then some stage `X_i` is
separated. The affineness hypothesis is removed in
`DescentSituation.exists_isAbsolutelySeparated_system_obj_of_chartsBounded`, the form the source
states and the one carrying the tag.

An affine étale surjective chart of the distinguished stage induces, by base change, a directed
system of affine charts with limit `U`; the kernel pair of the limit chart is of finite type
over `U`, so the closed immersion it gives into `U ×_S U` already lands in `U ×_S U_i` for some
stage `i` by Stacks 081B, descends to a closed immersion `R_j ⟶ U_j ×_S U_i` for some `j ≥ i`
by Stacks 01ZP, and there loses the separated factor `U_j ×_S U_j ⟶ U_j ×_S U_i`. -/
theorem exists_isAbsolutelySeparated_system_obj_of_isAffine_of_chartsBounded (hSaff : IsAffine S)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hI : ChartsBounded B S hS D.system)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  have : Nonempty I := ⟨D.base⟩
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  -- separatedness of the canonical limit presheaf
  have e : D.limitCone.pt ≅ limit D.system :=
    D.isLimit.conePointUniqueUpToIso (limit.isLimit _)
  have hlimAS : IsAlgebraicSpace B S hS (limit D.system) := D.limitAlgebraicSpace.of_iso e
  have hlimSep : IsSeparatedOver B S hS (limit D.system) :=
    (isAbsolutelySeparated_iff_isSeparatedOver B S hS hZ hSaff hlimAS).mp
      (isAbsolutelySeparated_of_isSeparated B S hS hZ hX (isSeparated_of_isIso B S hS e.inv))
  -- an affine étale surjective chart of the distinguished stage
  obtain ⟨U₀, chart, hU₀, hchartS, hchartE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (D.system.obj (op D.base)) (D.algebraicSpace D.base)).mp (D.quasiCompact D.base)
  have hchartE' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) chart :=
    (isEtale_iff_presheaf_of_yoneda B S hS chart).mp hchartE
  set C := affineChartSystem B S hS (op D.base) D.system ⟨U₀, hU₀⟩ chart
    (fun {_ _} g ↦ D.transition_affine g) with hC
  set L : AffineChartSystem.LimitBridge C :=
    AffineChartSystem.limitBridgeOfSizeBound C (hI.sizeBound C) with hL
  have hKsize : BigFppfOver.SizeBound C.siteDiagram := hI.sizeBound C
  set j₀ : Over (op D.base) := Over.mk (𝟙 (op D.base)) with hj₀
  -- the charts of the stages and of the limit, with their properties
  have hq : ∀ j : Over (op D.base), yoneda.relativelyRepresentable (C.stageMap j) := fun j =>
    (D.algebraicSpace j.left.unop).diagonal_representable.of_diag (C.stageMap j)
  have hqE : ∀ j : Over (op D.base), (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (C.stageMap j) := fun j =>
    presheaf_of_isPullback B S hS (C.isPullback j).flip hchartE'
  have hqS : ∀ j : Over (op D.base), (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (C.stageMap j) := fun j =>
    presheaf_of_isPullback B S hS (C.isPullback j).flip hchartS
  have hqLim : yoneda.relativelyRepresentable L.toLimit :=
    hlimAS.diagonal_representable.of_diag L.toLimit
  have hqLimE : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) L.toLimit :=
    presheaf_of_isPullback B S hS (L.isPullback_stage j₀).flip (hqE j₀)
  -- the kernel pair of the limit chart is a closed immersion into `U ×_S U`
  have hkpLim : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hqLim)) :=
    isClosedImmersion_kernelPairToProd_of_isSeparatedOver B S hS hlimSep hqLim
  have hUaff : ∀ j : Over (op D.base),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) := fun j =>
    C.isAffine_obj j
  have hmono : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ≤
      (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) := by
    intro Vv Ww g hg
    have hgE : Etale ((BigFppfOver.toScheme B S hS).map g) := hg
    exact (inferInstance : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g))
  have hfstLim : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (hqLim.fst' L.toLimit)) := by
    refine property_kernelPair_fst B S hS (@LocallyOfFiniteType.{u}) hqLim ?_
    exact MorphismProperty.relative_monotone hmono _ (presheaf_of_isPullback B S hS
      (IsPullback.of_hasPullback L.toLimit L.toLimit).flip hqLimE)
  have hftLim : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hqLim) ≫
        (BigFppfOver.toScheme B S hS).map prod.fst) := by
    rw [← Functor.map_comp,
      show kernelPairToProd B S hS hqLim ≫ prod.fst = hqLim.fst' L.toLimit from by
        simp [kernelPairToProd]]
    exact hfstLim
  -- Stacks 081B: the closed immersion already lands in a product with a stage
  obtain ⟨k₁, hk₁⟩ := exists_isClosedImmersion_comp_prodMap_π_of_chartsBounded B S hS hSaff
    C.siteDiagram hUaff hKsize L.isLimit L.isAffine_pt _ hkpLim j₀ hftLim
  have hRespects : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨ρ, hρ⟩ := exists_isPullback_kernelPairToProd_prodMap B S hS
    (limit.π D.system k₁.left) (hq k₁) hqLim (L.cone.π.app k₁) (L.isPullback_stage k₁)
  have hlimci : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
        ((BigFppfOver.toScheme B S hS).map
          (prod.map (L.cone.π.app k₁) (𝟙 (C.siteDiagram.obj k₁))))) := by
    refine (prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (hρ.map (BigFppfOver.toScheme B S hS)) (IsPullback.of_hasPullback _ _)).mp ?_
    rw [Functor.map_comp]
    exact hk₁ k₁ (𝟙 k₁)
  -- quasi-compactness and quasi-separatedness of the kernel pair at the stage
  have hUc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj k₁)) :=
    have := hUaff k₁; Scheme.compactSpace_of_isAffine _
  have hmqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((hq k₁).pullback (C.stageMap k₁))) :=
    compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ (D.quasiSeparated k₁.left.unop)
      ((hq k₁).isPullback' (C.stageMap k₁)) hUc hUc
  have hmft : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁))) :=
    (locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS (C.stageMap k₁) (hqE k₁)).1
  have hmqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj
      ((hq k₁).pullback (C.stageMap k₁))) := by
    have hmm : Mono ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁))) :=
      (locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS (C.stageMap k₁)
        (hqE k₁)).2
    have hprodaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (C.siteDiagram.obj k₁ ⨯ C.siteDiagram.obj k₁)) :=
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj k₁)
        (C.isAffine_obj k₁)
    exact quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
  -- Stacks 01ZP: the closed immersion descends to a stage
  obtain ⟨i, hi, hires⟩ :=
    exists_isClosedImmersion_pullback_snd_prodMap_of_chartsBounded B S hS hSaff
    C.siteDiagram hUaff hKsize L.isLimit k₁
    (kernelPairToProd B S hS (hq k₁)) hmft hmqc hmqs hlimci
  obtain ⟨ρ', hρ'⟩ := exists_isPullback_kernelPairToProd_prodMap B S hS
    (D.system.map hi.left) (hq k₁) (hq i) (C.siteDiagram.map hi)
    (AffineChartSystem.isPullback_map B S hS (op D.base) D.system ⟨U₀, hU₀⟩ chart C hi)
  have hcomp : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i) ≫
        prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) :=
    (prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (hρ'.map (BigFppfOver.toScheme B S hS)) (IsPullback.of_hasPullback _ _)).mpr hires
  -- cancel the separated morphism `U_i ×_S U_i ⟶ U_i ×_S U_{k₁}`
  have hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map
      (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) := by
    have h1 : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (C.siteDiagram.obj i ⨯ C.siteDiagram.obj i)) :=
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj i)
        (C.isAffine_obj i)
    have h2 : IsAffine ((BigFppfOver.toScheme B S hS).obj
        (C.siteDiagram.obj i ⨯ C.siteDiagram.obj k₁)) :=
      isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj i)
        (C.isAffine_obj k₁)
    have h3 : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) :=
      isAffineHom_of_isAffine _
    exact _root_.AlgebraicGeometry.IsSeparated.of_isAffineHom _
  have hkpi : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i))) := by
    rw [Functor.map_comp] at hcomp
    exact _root_.AlgebraicGeometry.IsClosedImmersion.of_comp
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i)))
      ((BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi)))
  refine ⟨i.left.unop, leOfHom i.hom.unop, ?_⟩
  refine (isAbsolutelySeparated_iff_isSeparatedOver B S hS hZ hSaff
    (D.algebraicSpace i.left.unop)).mpr ?_
  exact isSeparatedOver_of_isClosedImmersion_kernelPairToProd B S hS
    (D.algebraicSpace i.left.unop) (hqS i) (hqE i) hkpi

/-- **Stacks 084T.** In the situation of Stacks 084R, over an arbitrary base scheme, if the
limit `X` of the inverse system is separated then some stage `X_i` is separated.

Separatedness is the absolute notion, taken over the terminal scheme, so the whole descent may
be read there: the relocalization along `S ⟶ Spec ℤ` carries the descent situation over `S` to
one over the terminal scheme, which is affine, and the absolute separatedness of a presheaf and
of its view over the terminal scheme are the same condition. -/
theorem exists_isAbsolutelySeparated_system_obj_of_chartsBounded {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hI : ChartsBounded B S hS D.system)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  obtain ⟨i, hi, hres⟩ := exists_isAbsolutelySeparated_system_obj_of_isAffine_of_chartsBounded
    B (⊤_ Scheme.{u}) hZ hZ inferInstance (D.viewOverIntegers B S hS hZ)
    (hI.viewOverIntegers hZ)
    ((isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ D.limitCone.pt).2 hX)
  exact ⟨i, hi, (isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ
    (D.system.obj (op i))).1 hres⟩

end DescentSituation

end Descent

/-! ### Separatedness over a base algebraic space at a late stage -/

section SeparatedOverBase

variable (hZ : B.Contains (⊤_ Scheme.{u})) {T Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable {I : Type u} [Preorder I]

section BaseChangeOver

variable [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
  (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
  (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (g : D.limitCone.pt ⟶ Y)
  (hg : ∀ j, D.limitCone.π.app j ≫ t.app j = g) (U : BigFppfOver B S hS)
  (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (u : yoneda.obj U ⟶ Y)

section BaseChangeCharts

variable {B S hS}
variable {I' : Type u} [Preorder I']
  {T' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {E : I'ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Boundedness of the systems of affine charts passes to a base-changed system.** Let `E` be
an inverse system of presheaves over `Y`, given by a natural transformation `t` to the constant
system at `Y`, and let `u : T ⟶ Y` be a morphism. If the systems of affine charts of `E` are
size-bounded then so are those of the system `j ↦ T ×_Y E j` of base changes.

The index category is the same for both systems, so the two conditions on it are inherited
verbatim. For the bound itself, a scheme-valued point `f₀` of the stage `T ×_Y E i₀` has the
scheme-valued point `f₀ ≫ pr` of the stage `E i₀` under the projection, and each base change of
`f₀` along a transition morphism of the base-changed system is a base change of `f₀ ≫ pr` along
the corresponding transition morphism of `E`: the stage `T ×_Y E j` is the fibre product of
`T ×_Y E i₀` with `E j` over `E i₀`
(`AlgebraicGeometry.Space.isPullback_baseChangeOverMap`), so the two squares paste to one
cartesian square. The cardinal that `E` provides therefore serves for the base changes too. -/
theorem ChartsBounded.baseChangeOver (h : ChartsBounded B S hS E)
    (t : E ⟶ (Functor.const I'ᵒᵖ).obj Y') (u : T' ⟶ Y') :
    ChartsBounded B S hS (baseChangeOverSystem B S hS E t u) where
  mk_lt := h.mk_lt
  mk_over_lt := h.mk_over_lt
  bound i₀ U₀ f₀ := by
    obtain ⟨mu, hmu, hb⟩ := h.bound i₀ U₀ (f₀ ≫ pullback.fst (t.app i₀) u)
    refine ⟨mu, hmu, fun j a W e => hb j a W (e.trans (IsPullback.paste_horiz
      (IsPullback.of_hasPullback ((baseChangeOverSystem B S hS E t u).map a) f₀)
      (isPullback_baseChangeOverMap B S hS (t.app j) (t.app i₀) (E.map a) (by simp) u).flip
      ).isoPullback)⟩

end BaseChangeCharts

end BaseChangeOver

/-- **Stacks 086X.** Let `Y` be a quasi-separated algebraic space over `S` and let `X = lim X_i`
be a directed limit, over `Y` and with affine transition morphisms, of quasi-compact and
quasi-separated algebraic spaces over `S`, as in the standing situation of Stacks 084R. If
`X ⟶ Y` is separated then `X_i ⟶ Y` is separated for all `i` large enough.

Fix the distinguished stage `0` of the system and choose an affine étale surjective chart
`U ⟶ X_0`, which exists because `X_0` is quasi-compact, and let `u : U ⟶ Y` be its composite
with the structure morphism. Base changing the whole situation along `u` is again a situation of
Stacks 084R — the stages stay quasi-compact because `U` is quasi-compact and `Y` is
quasi-separated — whose limit `X ×_Y U` is separated over the affine scheme `U`, hence a
separated algebraic space. So some stage `X_i ×_Y U` is separated by Stacks 084T, that is,
`X_i ×_Y U ⟶ U` is separated. Affineness of the transition morphism `X_i ⟶ X_0` turns the chart
`U ⟶ X_0` into a chart `U_i = U ×_{X_0} X_i ⟶ X_i` of that stage, again surjective and étale and
with `U_i ⟶ X_i ⟶ Y` factoring through `u`; separatedness of `X_i ⟶ Y` therefore descends from
that of `X_i ×_Y U ⟶ U`. Finally the transition morphisms are affine, hence separated, so
`X_k ⟶ Y` is separated for every `k ≥ i`. -/
theorem DescentSituation.exists_isSeparated_system_app_of_chartsBounded [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hI : ChartsBounded B S hS D.system)
    (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (hsep : IsSeparated B S hS f) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)) := by
  have : Nonempty I := ⟨D.base⟩
  -- an affine étale surjective chart of the distinguished stage, and its image point of `Y`
  obtain ⟨U₀, q₀, hU₀, hq₀S, hq₀E⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (D.system.obj (op D.base)) (D.algebraicSpace D.base)).mp (D.quasiCompact D.base)
  have hq₀E' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q₀ :=
    (isEtale_iff_presheaf_of_yoneda B S hS q₀).mp hq₀E
  -- the base changed descent situation and the separatedness of its limit
  have hlim : IsAbsolutelySeparated B S hS hZ
      (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base))).limitCone.pt :=
    isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ U₀ hU₀
      (pullback.snd f (q₀ ≫ t.app (op D.base)))
      (isSeparated_pullbackSnd B S hS (q₀ ≫ t.app (op D.base)) hsep)
  obtain ⟨i, hbi₀, hi⟩ := exists_isAbsolutelySeparated_system_obj_of_chartsBounded B S hS hZ
    (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base)))
    (hI.baseChangeOver t (q₀ ≫ t.app (op D.base))) hlim
  have hbi : D.base ≤ i := hbi₀
  -- the base change of the stage along the chart of `Y` is separated
  have hsepi : IsSeparated B S hS (pullback.snd (t.app (op i)) (q₀ ≫ t.app (op D.base))) :=
    (isSeparated_pullbackSnd_iff_isAbsolutelySeparated B S hS hZ (D.algebraicSpace i)
      (t.app (op i)) U₀ hU₀ (q₀ ≫ t.app (op D.base))).mpr hi
  -- the chart of the distinguished stage, base changed to the stage `i` along the affine
  -- transition morphism
  have hτ : D.system.map (homOfLE hbi).op ≫ t.app (op D.base) = t.app (op i) := by simp
  obtain ⟨W, v, wq, hpb⟩ :=
    D.transition_affine (homOfLE hbi).op ⟨U₀, hU₀⟩ q₀
  -- descend separatedness to the stage itself
  have hstage : IsSeparated B S hS (t.app (op i)) := by
    refine isSeparated_of_isSeparated_pullbackSnd_of_etaleChart_factorization B S hS
      (D.algebraicSpace i) (t.app (op i))
      (presheaf_of_isPullback B S hS hpb.flip hq₀S)
      (presheaf_of_isPullback B S hS hpb.flip hq₀E') (yoneda.map wq) ?_ hsepi
    rw [← hτ]
    simp only [← Category.assoc, hpb.w]
  -- and propagate it to all later stages along the affine transition morphisms
  refine ⟨i, hbi, fun k hik => ?_⟩
  have hk : D.system.map (homOfLE hik).op ≫ t.app (op i) = t.app (op k) := by simp
  rw [← hk]
  exact isSeparated_comp B S hS _ _
    (isSeparated_of_isAffineHom B S hS (D.system.map (homOfLE hik).op)
      (D.algebraicSpace k) (D.algebraicSpace i) (D.transition_affine _)) hstage

end SeparatedOverBase

end AlgebraicGeometry.Space

end
