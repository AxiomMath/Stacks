module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitContainment

/-!
# Descending separatedness along a limit with contained chart limits

The descent of separatedness of Stacks 084T and Stacks 086X, in the generality where the affine
charts of the inverse system have limits in the site
(`AlgebraicGeometry.Space.HasContainedChartLimits`) rather than the index set being smaller than
the cofinality of the cutoff. The index-size forms are
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj` and
`AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_system_app`.

## Main results

* `AlgebraicGeometry.Space.HasContainedChartLimits.of_relocalize`: the condition for the system
  read over `Spec ℤ` gives the condition over `S`.
* `AlgebraicGeometry.Space.exists_isClosedImmersion_comp_prodMap_π_of_isLimit_toScheme` and
  `AlgebraicGeometry.Space.exists_isClosedImmersion_pullback_snd_prodMap_of_isLimit_toScheme`:
  Stacks 081B and 01ZP for products of charts, for a limit preserved by the underlying scheme
  functor.
* `DescentSituation.exists_isAbsolutelySeparated_system_obj_of_hasContainedChartLimits`:
  Stacks 084T under contained chart limits.
* `DescentSituation.exists_isSeparated_system_app_of_hasContainedChartLimits`:
  Stacks 086X under contained chart limits.

## References

* [Stacks Project, Tag 084T](https://stacks.math.columbia.edu/tag/084T)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site times out otherwise
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_separatedDescentChartLimits :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_separatedDescentChartLimits
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Reading the system over `Spec ℤ` -/

section Relocalize

variable {B S hS} (hZ : B.Contains (⊤_ Scheme.{u})) {I : Type u} [Category.{u} I]

/-- **Contained chart limits over `Spec ℤ` give contained chart limits over `S`.** Relocalizing
along `S ⟶ Spec ℤ` keeps the underlying schemes and preserves fibre products, and it carries
representable presheaves to representable presheaves, so a cartesian chart system over `S`
relocalizes to one over `Spec ℤ` with the same diagram of schemes. -/
theorem HasContainedChartLimits.of_relocalize {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hD : HasContainedChartLimits B (⊤_ Scheme.{u}) hZ
      (D ⋙ OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ))) :
    HasContainedChartLimits B S hS D := by
  intro i₀ U₀ f₀ V π b hV hpb
  set g := integersMap B S hS hZ
  set Λ := OverShriek.relocalizePresheafFunctor g
  set e := OverShriek.relocalizeYonedaIso g
  let π' : (V ⋙ Over.map g) ⋙ yoneda ⟶ Over.forget i₀ ⋙ D ⋙ Λ :=
    { app := fun j => e.inv.app (V.obj j) ≫ Λ.map (π.app j)
      naturality := fun j j' t => by
        have h1 := e.inv.naturality (V.map t)
        have h2 := π.naturality t
        dsimp only [Functor.comp_obj, Functor.comp_map] at h1 h2 ⊢
        rw [← Category.assoc, h1, Category.assoc, ← Λ.map_comp, h2, Λ.map_comp,
          Category.assoc] }
  let b' : (V ⋙ Over.map g) ⋙ yoneda ⟶
      (Functor.const (Over i₀)).obj (yoneda.obj ((Over.map g).obj U₀)) :=
    { app := fun j => e.inv.app (V.obj j) ≫ Λ.map (b.app j) ≫ e.hom.app U₀
      naturality := fun j j' t => by
        have h1 := e.inv.naturality (V.map t)
        have h2 := b.naturality t
        dsimp only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
          Functor.const_obj_map] at h1 h2 ⊢
        rw [Category.comp_id] at h2
        rw [Category.comp_id, ← Category.assoc, h1, Category.assoc, ← Λ.map_comp_assoc, h2] }
  have hpb' : ∀ j : Over i₀, IsPullback (π'.app j) (b'.app j) ((D ⋙ Λ).map j.hom)
      (e.inv.app U₀ ≫ Λ.map f₀) := fun j =>
    ((hpb j).map Λ).of_iso (e.app (V.obj j)) (Iso.refl _) (e.app U₀) (Iso.refl _)
      (by simp [π']) (by simp [b']) (by simp) (by simp)
  obtain ⟨c, hc, hcont⟩ := hD i₀ ((Over.map g).obj U₀) (e.inv.app U₀ ≫ Λ.map f₀)
    (V ⋙ Over.map g) π' b' hV hpb'
  exact ⟨c, hc, hcont⟩

end Relocalize

/-! ### Descending a closed immersion into a product of charts -/

section ProductDiagrams

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (hSaff : IsAffine S)
  (V : K ⥤ BigFppfOver B S hS)
  (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))

include hSaff hVaff in
/-- **Stacks 081B** for the products of a cofiltered limit of affine charts with the charts of
the stages. A closed immersion into `U ×_S U`, where `U` is the limit of the charts, whose
composite with the first projection is locally of finite type, is already a closed immersion
into `U ×_S U_k` for all sufficiently late stages `k`. -/
theorem exists_isClosedImmersion_comp_prodMap_π_of_isLimit_toScheme {c : Cone V}
    (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {R : Scheme.{u}} (g : R ⟶ (BigFppfOver.toScheme B S hS).obj (c.pt ⨯ c.pt))
    (hg : _root_.AlgebraicGeometry.IsClosedImmersion g) (k₀ : K)
    (hft : LocallyOfFiniteType (g ≫ (BigFppfOver.toScheme B S hS).map prod.fst)) :
    ∃ k₁ : K, ∀ (k : K) (_ : k ⟶ k₁),
      _root_.AlgebraicGeometry.IsClosedImmersion
        (g ≫ (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k))) := by
  have hconn : IsConnected K := IsCofiltered.isConnected K
  have hpaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.obj c.pt).obj j)) := fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ hcaff (hVaff j)
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.obj c.pt).mapCone c)) := BigFppfOver.isLimitToSchemeMapConeProd hcS c.pt
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
theorem exists_isClosedImmersion_pullback_snd_prodMap_of_isLimit_toScheme {c : Cone V}
    (hcS : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (k : K)
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
  have hpaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.flip.obj (V.obj k)).obj j)) := fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hVaff j) (hVaff k)
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.flip.obj (V.obj k)).mapCone c)) :=
    BigFppfOver.isLimitToSchemeMapConeProdFlip hcS (V.obj k)
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

/-! ### Separatedness of a late stage -/

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A quasi-compact algebraic space has an affine chart which is surjective and étale, stated
with the presheaf-level properties. -/
private theorem exists_affine_surjective_etale_presheaf_chart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hqc : IsQuasiCompactSpace B S hS F) :
    ∃ (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q := by
  obtain ⟨U, q, hU, hqS, hqE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).mp hqc
  exact ⟨U, q, hU, hqS, (isEtale_iff_presheaf_of_yoneda B S hS q).mp hqE⟩

namespace DescentSituation

/-- **Stacks 084T over an affine base scheme, under contained chart limits.** In the situation
of Stacks 084R over an affine base scheme, if the affine charts of the system have limits in the
site and the limit `X` of the inverse system is separated then some stage `X_i` is
separated. The affineness hypothesis is removed in
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj`, the form
the source states and the one carrying the tag.

An affine étale surjective chart of the distinguished stage induces, by base change, a directed
system of affine charts with limit `U`; the kernel pair of the limit chart is of finite type
over `U`, so the closed immersion it gives into `U ×_S U` already lands in `U ×_S U_i` for some
stage `i` by Stacks 081B, descends to a closed immersion `R_j ⟶ U_j ×_S U_i` for some `j ≥ i`
by Stacks 01ZP, and there loses the separated factor `U_j ×_S U_j ⟶ U_j ×_S U_i`. -/
theorem exists_isAbsolutelySeparated_system_obj_of_isAffine_of_hasContainedChartLimits
    (hSaff : IsAffine S)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I)
    (hD : HasContainedChartLimits B S hS D.system)
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
  obtain ⟨U₀, chart, hU₀, hchartS, hchartE'⟩ :=
    exists_affine_surjective_etale_presheaf_chart B S hS (D.algebraicSpace D.base)
      (D.quasiCompact D.base)
  set C := affineChartSystem B S hS (op D.base) D.system ⟨U₀, hU₀⟩ chart
    (fun {_ _} g ↦ D.transition_affine g) with hC
  set L : AffineChartSystem.LimitBridge C :=
    hD.limitBridge C with hL
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
  have hprodaff : ∀ a b : Over (op D.base), IsAffine ((BigFppfOver.toScheme B S hS).obj
      (C.siteDiagram.obj a ⨯ C.siteDiagram.obj b)) := fun a b =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hUaff a) (hUaff b)
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
  obtain ⟨k₁, hk₁⟩ := exists_isClosedImmersion_comp_prodMap_π_of_isLimit_toScheme B S hS hSaff
    C.siteDiagram hUaff L.schemeIsLimit L.isAffine_pt _ hkpLim j₀ hftLim
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
    have := hprodaff k₁ k₁
    exact quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
  -- Stacks 01ZP: the closed immersion descends to a stage
  obtain ⟨i, hi, hires⟩ :=
    exists_isClosedImmersion_pullback_snd_prodMap_of_isLimit_toScheme B S hS hSaff
      C.siteDiagram hUaff L.schemeIsLimit k₁
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
    have := hprodaff i i
    have := hprodaff i k₁
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

/-- **Stacks 084T under contained chart limits.** In the situation of Stacks 084R, over an
arbitrary base scheme, if the affine charts of the system read over `Spec ℤ` have limits in the
site and the limit `X` of the inverse system is separated, then some stage `X_i` is separated.
The relocalization along `S ⟶ Spec ℤ` carries the situation to one over the affine terminal
scheme. -/
theorem exists_isAbsolutelySeparated_system_obj_of_hasContainedChartLimits {I : Type u}
    [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hD : HasContainedChartLimits B (⊤_ Scheme.{u}) hZ
      (D.system ⋙ OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)))
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  obtain ⟨i, hi, hres⟩ :=
    exists_isAbsolutelySeparated_system_obj_of_isAffine_of_hasContainedChartLimits
      B (⊤_ Scheme.{u}) hZ hZ inferInstance (D.viewOverIntegers B S hS hZ) hD
      ((isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ D.limitCone.pt).2 hX)
  exact ⟨i, hi, (isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ
    (D.system.obj (op i))).1 hres⟩

end DescentSituation

end Descent

/-! ### Separatedness over a base algebraic space at a late stage -/

section SeparatedOverBase

variable (hZ : B.Contains (⊤_ Scheme.{u})) {T Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {I : Type u} [Preorder I]

/-- **Stacks 086X under contained chart limits.** Let `Y` be a quasi-separated algebraic space over
`S` and let `X = lim X_i` be a directed limit, over `Y` and with affine transition morphisms, of
quasi-compact and quasi-separated algebraic spaces over `S`, as in the standing situation of Stacks
084R. If `X ⟶ Y` is separated then `X_i ⟶ Y` is separated for all `i` large enough.

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
theorem DescentSituation.exists_isSeparated_system_app_of_hasContainedChartLimits
    [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hD : HasContainedChartLimits B (⊤_ Scheme.{u}) hZ
      (D.system ⋙ OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)))
    (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (hsep : IsSeparated B S hS f) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)) := by
  have : Nonempty I := ⟨D.base⟩
  -- an affine étale surjective chart of the distinguished stage, and its image point of `Y`
  obtain ⟨U₀, q₀, hU₀, hq₀S, hq₀E'⟩ :=
    exists_affine_surjective_etale_presheaf_chart B S hS (D.algebraicSpace D.base)
      (D.quasiCompact D.base)
  -- the base changed descent situation and the separatedness of its limit
  have hlim : IsAbsolutelySeparated B S hS hZ
      (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base))).limitCone.pt :=
    isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ U₀ hU₀
      (pullback.snd f (q₀ ≫ t.app (op D.base)))
      (isSeparated_pullbackSnd B S hS (q₀ ≫ t.app (op D.base)) hsep)
  have hD' : HasContainedChartLimits B (⊤_ Scheme.{u}) hZ
      ((D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base))).system ⋙
        OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)) :=
    HasContainedChartLimits.of_cartesian
      (Functor.whiskerRight (baseChangeOverProj B S hS D.system t (q₀ ≫ t.app (op D.base)))
        (OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ)))
      (fun {i j} g => (isPullback_baseChangeOverMap B S hS (t.app i) (t.app j) (D.system.map g)
        (by simp) (q₀ ≫ t.app (op D.base))).map
          (OverShriek.relocalizePresheafFunctor (integersMap B S hS hZ))) hD
  obtain ⟨i, hbi₀, hi⟩ := exists_isAbsolutelySeparated_system_obj_of_hasContainedChartLimits
    B S hS hZ (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base))) hD'
    hlim
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
